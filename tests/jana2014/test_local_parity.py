from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[2]
HASKELL_CMD = ["runhaskell", "-isrc", "src/Main.hs"]


def run_haskell(path: Path, debug_input: str | None = None) -> subprocess.CompletedProcess[str]:
  return subprocess.run(
    ([*HASKELL_CMD, "-d", str(path)] if debug_input is not None else [*HASKELL_CMD, str(path)]),
    cwd=ROOT,
    text=True,
    input=debug_input,
    capture_output=True,
    check=False,
    timeout=5,
  )


def run_python(path: Path, debug_input: str | None = None) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT / "src")
  return subprocess.run(
    ([sys.executable, "-m", "jana_py.cli", "-d", str(path)] if debug_input is not None else [sys.executable, "-m", "jana_py.cli", str(path)]),
    cwd=ROOT,
    text=True,
    input=debug_input,
    capture_output=True,
    env=env,
    check=False,
    timeout=5,
  )


class LocalParityTests(unittest.TestCase):
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

  def test_delocal_wrong_value_matches(self) -> None:
    self.assert_matches_haskell("tests/errors/delocal-wrong-value.ja")

  def test_delocal_wrong_name_matches(self) -> None:
    self.assert_matches_haskell("tests/errors/delocal-wrong-name.ja")

  def test_delocal_wrong_type_matches(self) -> None:
    self.assert_matches_haskell("tests/errors/delocal-wrong-type.ja")


if __name__ == "__main__":
  unittest.main()
