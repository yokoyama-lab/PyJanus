from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[1]


def run_python(program_path: str) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", program_path],
    cwd=ROOT,
    text=True,
    capture_output=True,
    env=env,
    check=False,
  )


class M2Tests(unittest.TestCase):
  def test_forward_call_and_printf(self) -> None:
    with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
      handle.write(textwrap.dedent(
        """\
        procedure fib(int x1, int x2, int n)
            if n = 0 then
                x1 += 1
                x2 += 1
            else
                n -= 1
                call fib(x1, x2, n)
                x1 += x2
                x1 <=> x2
            fi x1 = x2

        procedure main()
            int x1
            int x2
            int n
            n += 5
            call fib(x1, x2, n)
            printf("%d %d %d\\n", n, x1, x2)
        """
      ))
      tmp_path = Path(handle.name)
    try:
      result = run_python(str(tmp_path))
      self.assertEqual(result.returncode, 0, result.stderr)
      self.assertEqual(result.stdout, "0 8 13\n\nn = 0\nx1 = 8\nx2 = 13\n")
    finally:
      tmp_path.unlink(missing_ok=True)

  def test_division_by_zero(self) -> None:
    result = run_python("tests/fixtures_errors/division-by-zero.ja")
    self.assertNotEqual(result.returncode, 0)
    self.assertIn("Division by zero", result.stdout)

  def test_no_main_proc(self) -> None:
    result = run_python("tests/fixtures_errors/no-main-proc.ja")
    self.assertNotEqual(result.returncode, 0)
    self.assertIn("No main procedure has been defined", result.stdout)


if __name__ == "__main__":
  unittest.main()
