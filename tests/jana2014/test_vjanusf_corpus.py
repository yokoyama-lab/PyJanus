"""Conformance test for `vjanusf`, the verified *frame*-core jana2014 interpreter.

`vjanusf` (coq/vjanus/, built from lower_frame.ml + the RevExtractFrame.v core)
is the Phase 2a successor to `vjanus`: it classifies variables into the frame
core's refs (global RG / depth-d local RL / positional formal RF), so a `local`
survives recursion.  This test asserts it agrees with PyJanus on every program
it can lower; programs outside its current coverage (arrays, stacks) exit 3 and
skip, exactly like test_vjanus_corpus.py.  `vjanusf` reports only main's scalar
variables, so we compare those.

Needs the `vjanusf` binary (build with `bash coq/vjanus/build.sh`); skips if absent.
"""
from __future__ import annotations

import glob
import re
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
VJANUSF = ROOT / "coq" / "vjanus" / "vjanusf"
PROGRAMS = sorted(
    glob.glob(str(ROOT / "tests" / "jana2014" / "fixtures" / "examples" / "*.ja"))
    + glob.glob(str(ROOT / "coq" / "harness" / "fixtures" / "*.ja"))
)


def _scalars(out: str) -> dict[str, str]:
  """Pick out `name = integer` lines (what vjanusf emits)."""
  d: dict[str, str] = {}
  for line in out.splitlines():
    m = re.match(r"^(\w+)\s*=\s*(-?\d+)$", line.strip())
    if m and not line.startswith(("Warning", "PyJanus")):
      d[m.group(1)] = m.group(2)
  return d


@pytest.mark.skipif(not VJANUSF.exists(),
                    reason="vjanusf not built (run coq/vjanus/build.sh)")
@pytest.mark.parametrize("ja", PROGRAMS, ids=lambda p: Path(p).name)
def test_vjanusf_matches_pyjanus(ja: str) -> None:
  vj = subprocess.run([str(VJANUSF), "-s", ja], capture_output=True, text=True)
  if vj.returncode == 3:                          # clean "unsupported construct"
    pytest.skip((vj.stderr.strip().splitlines() or ["unsupported"])[-1])
  assert vj.returncode == 0, vj.stderr
  pj = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", ja],
                      cwd=ROOT, capture_output=True, text=True)
  assert pj.returncode == 0, pj.stderr
  got, want = _scalars(vj.stdout), _scalars(pj.stdout)
  # vjanusf reports exactly main's scalars; each must match PyJanus.
  diffs = {k: (got[k], want.get(k)) for k in got if got[k] != want.get(k)}
  assert not diffs, f"verified-frame vs pyjanus differ: {diffs}"


if __name__ == "__main__":
  raise SystemExit(pytest.main([__file__, "-q"]))
