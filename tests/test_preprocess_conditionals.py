from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[1]


def run_python(args: list[str]) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", *args],
    cwd=ROOT,
    text=True,
    capture_output=True,
    env=env,
    check=False,
  )


class PreprocessConditionalsTests(unittest.TestCase):
  def run_case(self, source: str) -> subprocess.CompletedProcess[str]:
    with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
      handle.write(textwrap.dedent(source))
      path = handle.name
    try:
      return run_python([path])
    finally:
      Path(path).unlink(missing_ok=True)

  def test_ifdef_takes_true_branch(self) -> None:
    result = self.run_case(
      """\
      #define FLAG 1
      procedure main()
      #ifdef FLAG
          print("on")
      #else
          print("off")
      #endif
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "on\n")

  def test_ifndef_takes_true_branch(self) -> None:
    result = self.run_case(
      """\
      procedure main()
      #ifndef FLAG
          print("off")
      #else
          print("on")
      #endif
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "off\n")

  def test_inactive_branch_does_not_define_macro(self) -> None:
    result = self.run_case(
      """\
      #define FLAG 1
      procedure main()
      #ifndef FLAG
      #define X 9
      #endif
          int x = 4
          printf("%d", x)
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "4\nx = 4\n")

  def test_nested_conditionals_work(self) -> None:
    result = self.run_case(
      """\
      #define A 1
      procedure main()
      #ifdef A
      #ifndef B
          print("nested")
      #else
          print("wrong")
      #endif
      #else
          print("wrong")
      #endif
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "nested\n")

  def test_unexpected_else_fails(self) -> None:
    result = self.run_case(
      """\
      procedure main()
      #else
          skip
      """
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("Unexpected #else", result.stdout)

  def test_unterminated_conditional_fails(self) -> None:
    result = self.run_case(
      """\
      procedure main()
      #ifdef FLAG
          skip
      """
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("Unterminated conditional block", result.stdout)


if __name__ == "__main__":
  unittest.main()
