"""Conformance test for `vjanus`, the standalone verified jana2014 interpreter.

`vjanus` (coq/vjanus/) has its own OCaml jana2014 parser and evaluates with the
Coq-extracted, machine-checked `run` — no Python at runtime.  This test asserts
it agrees with PyJanus on the whole jana2014 corpus: same final store for every
main scalar / array / stack.  Programs outside the verified subset make `vjanus`
exit 3 (clean "unsupported"); those skip, mirroring `test_verified_corpus.py`.

Needs the `vjanus` binary (build with `bash coq/vjanus/build.sh`); skips if absent.
"""
from __future__ import annotations

import glob
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


def _parse_store(out: str) -> dict[str, str]:
  """Normalise a `-s` store dump into {name: canonical-value-string}."""
  d: dict[str, str] = {}
  for line in out.splitlines():
    line = line.strip()
    m = re.match(r"^(\w+)((?:\[\d+\])+)\s*=\s*(\{.*\})$", line)
    if m:
      d[m.group(1)] = re.sub(r"\s", "", m.group(3)); continue
    m = re.match(r"^(\w+)\s*=\s*<(.*)\]$", line)
    if m:
      d[m.group(1)] = "<" + re.sub(r"\s", "", m.group(2)) + "]"; continue
    m = re.match(r"^(\w+)\s*=\s*nil$", line)
    if m:
      d[m.group(1)] = "nil"; continue
    m = re.match(r"^(\w+)\s*=\s*(-?\d+)$", line)
    if m and not line.startswith(("Warning", "PyJanus")):
      d[m.group(1)] = m.group(2)
  return d


@pytest.mark.skipif(not VJANUS.exists(),
                    reason="vjanus not built (run coq/vjanus/build.sh)")
@pytest.mark.parametrize("ja", PROGRAMS, ids=lambda p: Path(p).name)
def test_vjanus_matches_pyjanus(ja: str) -> None:
  vj = subprocess.run([str(VJANUS), "-s", ja], capture_output=True, text=True)
  if vj.returncode == 3:                          # clean "unsupported construct"
    pytest.skip((vj.stderr.strip().splitlines() or ["unsupported"])[-1])
  assert vj.returncode == 0, vj.stderr
  pj = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", ja],
                      cwd=ROOT, capture_output=True, text=True)
  assert pj.returncode == 0, pj.stderr
  got, want = _parse_store(vj.stdout), _parse_store(pj.stdout)
  # vjanus reports exactly main's variables; compare those against PyJanus.
  diffs = {k: (got[k], want.get(k)) for k in got if got[k] != want.get(k)}
  assert not diffs, f"verified vs pyjanus differ: {diffs}"


if __name__ == "__main__":
  raise SystemExit(pytest.main([__file__, "-q"]))
