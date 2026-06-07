from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[2]
HASKELL_CMD = ["runhaskell", "-isrc", "src/Main.hs"]
# The Haskell reference implementation lives outside the repo; without it the
# comparison is vacuous (both sides exit non-zero), so skip outright.
HAVE_HASKELL = shutil.which("runhaskell") is not None and (ROOT / "src" / "Main.hs").exists()


def run_haskell(path: Path) -> subprocess.CompletedProcess[str]:
  return subprocess.run(
    [*HASKELL_CMD, str(path)],
    cwd=ROOT,
    text=True,
    capture_output=True,
    check=False,
    timeout=5,
  )


def run_python(path: Path) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT / "src")
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", str(path)],
    cwd=ROOT,
    text=True,
    capture_output=True,
    env=env,
    check=False,
    timeout=5,
  )


@unittest.skipUnless(HAVE_HASKELL, "requires the Haskell reference implementation (runhaskell + src/Main.hs)")
class ControlFlowParityTests(unittest.TestCase):
  maxDiff = None

  def assert_matches_haskell(self, relative_path: str) -> None:
    path = ROOT / relative_path
    haskell = run_haskell(path)
    python = run_python(path)
    self.assertEqual(python.returncode, haskell.returncode, f"Return code mismatch for {relative_path}")
    if haskell.returncode == 0:
      self.assertEqual(
        (python.stdout, python.stderr),
        (haskell.stdout, haskell.stderr),
        f"Output mismatch for {relative_path}",
      )

  def test_if_forward_assertion_failure_matches(self) -> None:
    self.assert_matches_haskell("tests/errors/assertion-fail-if-fwd.ja")

  def test_if_backward_assertion_failure_matches(self) -> None:
    self.assert_matches_haskell("tests/errors/assertion-fail-if-bwd.ja")

  def test_from_forward_assertion_failure_matches(self) -> None:
    self.assert_matches_haskell("tests/errors/assertion-fail-from-fwd.ja")

  def test_from_backward_assertion_failure_matches(self) -> None:
    self.assert_matches_haskell("tests/errors/assertion-fail-from-bwd.ja")


if __name__ == "__main__":
  unittest.main()
