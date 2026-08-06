from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[2]
FIB_EXAMPLE = "tests/jana2014/fixtures/examples/fib_c.ja"


def run_python(args: list[str]) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", "--std", "jana2014", *args],
    cwd=ROOT,
    text=True,
    capture_output=True,
    env=env,
    check=False,
  )


class M4Tests(unittest.TestCase):
  def test_cpp_codegen_for_fib(self) -> None:
    result = run_python(["-c", FIB_EXAMPLE])
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertIn("void fib(", result.stdout)
    self.assertIn("int main()", result.stdout)
    self.assertIn("fib(x1, x2, n);", result.stdout)

  def test_cpp_codegen_with_header(self) -> None:
    result = run_python(["-c", "-h", "custom.h", FIB_EXAMPLE])
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertIn('#include "custom.h"', result.stdout)


if __name__ == "__main__":
  unittest.main()
