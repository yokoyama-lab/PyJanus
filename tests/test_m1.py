from __future__ import annotations

import subprocess
import sys
import os
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]
PYTHONPATH = str(ROOT)


def run_python(args: list[str]) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = PYTHONPATH
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", *args],
    cwd=ROOT,
    text=True,
    capture_output=True,
    env=env,
    check=False,
  )


class M1Tests(unittest.TestCase):
  def test_parse_fib_ast(self) -> None:
    result = run_python(["-a", "examples/fib.ja"])
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertIn('"procname"', result.stdout)
    self.assertIn('"main"', result.stdout)
    self.assertIn('"fib"', result.stdout)

  def test_invert_fib(self) -> None:
    result = run_python(["-i", "examples/fib.ja"])
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertIn("procedure fib(", result.stdout)
    self.assertIn("uncall fib(x1, x2, n)", result.stdout)

  def test_parser_error(self) -> None:
    result = run_python(["tests/fixtures_errors/parser-error.ja"])
    self.assertNotEqual(result.returncode, 0)
    self.assertIn("Expecting", result.stdout)


if __name__ == "__main__":
  unittest.main()
