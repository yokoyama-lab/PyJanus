"""`tools/step1_differential.py` used to `return 0` unconditionally, so a run
with real mismatches was indistinguishable from a clean run to any caller that
gates on the exit status (CI, an `&&` chain).  This pins the exit code without
needing an actual Haskell `jana` binary: `run_haskell`/`run_python` are faked.
"""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))

import step1_differential as step1  # noqa: E402


class Step1ExitCodeTests(unittest.TestCase):

  def setUp(self) -> None:
    self._orig_find = step1.find_binary
    self._orig_haskell = step1.run_haskell
    self._orig_python = step1.run_python
    step1.find_binary = lambda: "/fake/jana"

  def tearDown(self) -> None:
    step1.find_binary = self._orig_find
    step1.run_haskell = self._orig_haskell
    step1.run_python = self._orig_python

  def _run(self, argv: list[str]) -> int:
    orig_argv = sys.argv
    sys.argv = ["step1_differential.py", *argv]
    try:
      return step1.main()
    finally:
      sys.argv = orig_argv

  def test_returns_nonzero_when_programs_disagree(self) -> None:
    step1.run_haskell = lambda binary, path: (0, "1")
    step1.run_python = lambda path: (0, "2")   # disagrees with every program
    self.assertNotEqual(self._run(["--limit", "1"]), 0)

  def test_returns_zero_when_programs_agree(self) -> None:
    step1.run_haskell = lambda binary, path: (0, "same")
    step1.run_python = lambda path: (0, "same")
    self.assertEqual(self._run(["--limit", "1"]), 0)


if __name__ == "__main__":
  unittest.main()
