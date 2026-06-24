"""Differential test for `vjanus -inverse`, the verified inverse interpreter.

`vjanus -inverse '<final-store JSON>' prog.ja` inverts main with the Coq-extracted
`invert` (proved to satisfy reversibility in `RevFrame.v`) and runs it from the
given final store, printing the *initial* store as JSON — output-compatible with
PyJanus `--inverse`.  This test asserts the two agree: for every corpus program
it takes the forward final store and feeds it to BOTH inverters, comparing the
reconstructed initial stores.

Scope mirrors the inverter's: only programs whose main holds scalars and integer
arrays are checked.  Stacks are out (PyJanus `--inverse` can't seed them) and
structs are deferred (PyJanus `--inverse` mishandles nested struct stores), so
those programs skip — as does anything `vjanus` marks unsupported (exit 3).

Needs the `vjanus` binary (build with `bash coq/vjanus/build.sh`); skips if absent.
"""
from __future__ import annotations

import glob
import json
import re
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
VJANUS = ROOT / "coq" / "vjanus" / "vjanus"
PROGRAMS = sorted(
    glob.glob(str(ROOT / "tests" / "jana2014" / "fixtures" / "examples" / "*.ja"))
    + glob.glob(str(ROOT / "coq" / "harness" / "fixtures" / "*.ja"))
)


def _final_store(out: str) -> dict | None:
  """Parse a PyJanus `-s` dump into a JSON-able {name: int | nested-list}.

  Returns None if the store holds anything outside the inverse subset (a stack
  `<…]`/`nil`, or a struct `{… = …}`), signalling "skip this program".
  """
  store: dict[str, object] = {}
  for line in out.splitlines():
    line = line.strip()
    if not line or line.startswith(("Warning", "PyJanus")):
      continue
    m = re.match(r"^(\w+)\s*=\s*(-?\d+)$", line)              # scalar
    if m:
      store[m.group(1)] = int(m.group(2)); continue
    m = re.match(r"^(\w+)(?:\[\d+\])+\s*=\s*(\{[^=]*\})$", line)  # numeric array (no '=' inside)
    if m:
      store[m.group(1)] = json.loads(m.group(2).replace("{", "[").replace("}", "]"))
      continue
    return None                                              # stack / struct / nil
  return store


@pytest.mark.skipif(not VJANUS.exists(),
                    reason="vjanus not built (run coq/vjanus/build.sh)")
@pytest.mark.parametrize("ja", PROGRAMS, ids=lambda p: Path(p).name)
def test_vjanus_inverse_matches_pyjanus(ja: str) -> None:
  # forward (PyJanus) to obtain the final store
  fwd = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", ja],
                       cwd=ROOT, capture_output=True, text=True)
  if fwd.returncode != 0:
    pytest.skip("pyjanus forward run failed (error fixture)")
  store = _final_store(fwd.stdout)
  if store is None:
    pytest.skip("final store has a stack/struct (outside the inverse subset)")
  if not store:
    pytest.skip("empty final store")
  final_json = json.dumps(store)

  # verified inverse
  vj = subprocess.run([str(VJANUS), "-inverse", final_json, ja], capture_output=True, text=True)
  if vj.returncode == 3:
    pytest.skip((vj.stderr.strip().splitlines() or ["unsupported"])[-1])
  assert vj.returncode == 0, vj.stderr

  # PyJanus inverse (oracle)
  pi = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014",
                       "--inverse", final_json, ja], cwd=ROOT, capture_output=True, text=True)
  assert pi.returncode == 0, pi.stderr

  got = json.loads(vj.stdout.strip())
  want = json.loads(pi.stdout.strip().splitlines()[-1])      # JSON is the last line (warnings precede)
  assert got == want, f"verified inverse vs pyjanus differ: vjanus={got} pyjanus={want}"


if __name__ == "__main__":
  raise SystemExit(pytest.main([__file__, "-q"]))
