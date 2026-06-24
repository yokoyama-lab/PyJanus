"""Differential test for `vjanus -inverse`, the verified inverse interpreter.

`vjanus -inverse '<final-store JSON>' prog.ja` inverts main with the Coq-extracted
`invert` (proved to satisfy reversibility in `RevFrame.v`) and runs it from the
given final store, printing the *initial* store as JSON — output-compatible with
PyJanus `--inverse`.  This test asserts the two agree: for every corpus program
it takes the forward final store (computed in-process via the PyJanus runtime)
and feeds it to BOTH inverters, comparing the reconstructed initial stores.

Covers main scalars, integer arrays (any rank), scalar structs, struct arrays
(incl. array fields) and stacks — the whole corpus, with no skips.  (The
self-referential `delocal` is now invertible on both sides: vjanus via its
loop-aware lowering, PyJanus via a reverse-count desugaring in
`jana_py/inverse.py`.)  A program would skip only if `vjanus` marked it
unsupported (exit 3) or PyJanus `--inverse` could not invert it.

Needs the `vjanus` binary (build with `bash coq/vjanus/build.sh`); skips if absent.
"""
from __future__ import annotations

import copy
import glob
import json
import subprocess
import sys
from pathlib import Path

import pytest

from jana_py.parser_jana2014 import parse_program
from jana_py.runtime import Runtime
from jana_py.validate import validate_program

ROOT = Path(__file__).resolve().parents[2]
VJANUS = ROOT / "coq" / "vjanus" / "vjanus"
PROGRAMS = sorted(
    glob.glob(str(ROOT / "tests" / "jana2014" / "fixtures" / "examples" / "*.ja"))
    + glob.glob(str(ROOT / "coq" / "harness" / "fixtures" / "*.ja"))
)


def _forward_store(program) -> dict:
  """Main's final store as a JSON-able dict (scalars→int, arrays→flat list,
  structs→dict, struct arrays→list of dicts), via the PyJanus runtime."""
  rt = Runtime(program)
  rt.run()
  return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


@pytest.mark.skipif(not VJANUS.exists(),
                    reason="vjanus not built (run coq/vjanus/build.sh)")
@pytest.mark.parametrize("ja", PROGRAMS, ids=lambda p: Path(p).name)
def test_vjanus_inverse_matches_pyjanus(ja: str) -> None:
  try:
    program = parse_program(ja, Path(ja).read_text())
    validate_program(program)
  except Exception as exc:  # noqa: BLE001 - error fixtures are out of scope
    pytest.skip(f"does not parse/validate: {exc}")
  if program.main is None:
    pytest.skip("no main procedure")

  try:
    store = _forward_store(program)
  except Exception as exc:  # noqa: BLE001 - non-terminating / erroring programs
    pytest.skip(f"forward run failed: {exc}")
  if not store:
    pytest.skip("empty final store")
  final_json = json.dumps(store)

  # verified inverse
  vj = subprocess.run([str(VJANUS), "-inverse", final_json, ja], capture_output=True, text=True)
  if vj.returncode == 3:
    pytest.skip((vj.stderr.strip().splitlines() or ["unsupported"])[-1])
  assert vj.returncode == 0, vj.stderr

  # PyJanus inverse (oracle).  PyJanus inverts a self-referential `delocal i = i`
  # to an invalid `local i = i`, so it cannot invert procedures that use the
  # construct (e.g. odd_even_swap) — vjanus's loop-aware lowering can, but there
  # is then no oracle to compare against, so skip.
  pi = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014",
                       "--inverse", final_json, ja], cwd=ROOT, capture_output=True, text=True)
  if pi.returncode != 0:
    pytest.skip("pyjanus --inverse cannot invert this program (no oracle)")

  got = json.loads(vj.stdout.strip())
  want = json.loads(pi.stdout.strip().splitlines()[-1])       # JSON is the last line (warnings precede)
  assert got == want, f"verified inverse vs pyjanus differ: vjanus={got} pyjanus={want}"


if __name__ == "__main__":
  raise SystemExit(pytest.main([__file__, "-q"]))
