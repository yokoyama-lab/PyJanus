from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[1]


def run_pyjanus(args: list[str]) -> subprocess.CompletedProcess[str]:
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


def run_program(source: str, args: list[str]) -> subprocess.CompletedProcess[str]:
  with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
    handle.write(textwrap.dedent(source))
    path = handle.name
  try:
    return run_pyjanus([*args, path])
  finally:
    Path(path).unlink(missing_ok=True)


class ErrorReportingTests(unittest.TestCase):
  def test_runtime_error_includes_repair_context(self) -> None:
    result = run_pyjanus([
      "--std", "jana2014_in_out",
      "tests/jana2014_in_out/programs/read_nonzero_error.ja",
      "9",
    ])

    self.assertEqual(result.returncode, 1)
    self.assertIn("PyJanus execution error", result.stdout)
    self.assertIn("message: `read` target `x' must be zero", result.stdout)
    self.assertIn("location: tests/jana2014_in_out/programs/read_nonzero_error.ja:", result.stdout)
    self.assertIn("Source:", result.stdout)
    self.assertIn(">", result.stdout)
    self.assertIn("read x", result.stdout)
    self.assertIn("Context:", result.stdout)
    self.assertIn("where x = 5", result.stdout)
    self.assertIn("Fix hints:", result.stdout)
    self.assertIn("read x` is reversible only when `x` is zero", result.stdout)

  def test_parse_error_includes_source_excerpt(self) -> None:
    result = run_pyjanus(["--std", "jana2014", "tests/jana2014/fixtures_errors/parser-error.ja"])

    self.assertEqual(result.returncode, 1)
    self.assertIn("PyJanus parsing error", result.stdout)
    self.assertIn("message: Expecting identifier", result.stdout)
    self.assertIn("location: tests/jana2014/fixtures_errors/parser-error.ja:", result.stdout)
    self.assertIn("Source:", result.stdout)
    self.assertIn("%#=)#(%", result.stdout)

  def test_undeclared_variable_error_includes_hint(self) -> None:
    with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
      handle.write(textwrap.dedent("""\
        void main() {
            x += 1;
        }
      """))
      path = handle.name
    try:
      result = run_pyjanus(["--std", "janus2026", path])
    finally:
      Path(path).unlink(missing_ok=True)

    self.assertEqual(result.returncode, 1)
    self.assertIn("PyJanus execution error", result.stdout)
    self.assertIn("Variable `x' has not been declared", result.stdout)
    self.assertIn("Declare the variable before use", result.stdout)


class AssertionDiagnosticsTests(unittest.TestCase):
  def test_fi_failure_reports_operand_values(self) -> None:
    result = run_program(
      """\
      procedure main()
          int x = 5
          if x = 5 then
              x += 1
          fi x = 5
      """,
      ["--std", "jana2014"],
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("Assertion failed: should be true", result.stdout)
    self.assertIn("actual: x = 6, 5 = 5", result.stdout)

  def test_assert_scalar_failure_reports_operand_values(self) -> None:
    result = run_program(
      """\
      procedure main()
          int x = 3
          assert x = 4
      """,
      ["--std", "jana2014"],
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("Assertion failed: should be true", result.stdout)
    self.assertIn("actual: x = 3, 4 = 4", result.stdout)

  def test_assert_array_equality_reports_diff(self) -> None:
    result = run_program(
      """\
      procedure main()
          int a[3] = {1, 2, 3}
          int b[3] = {1, 9, 3}
          assert a = b
      """,
      ["--std", "jana2014"],
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("Assertion failed: values should be equal", result.stdout)
    self.assertIn("left:  a = {1, 2, 3}", result.stdout)
    self.assertIn("right: b = {1, 9, 3}", result.stdout)

  def test_assert_array_equality_passes_when_equal(self) -> None:
    result = run_program(
      """\
      procedure main()
          int a[3] = {1, 2, 3}
          int b[3] = {1, 2, 3}
          assert a = b
      """,
      ["--std", "jana2014"],
    )
    self.assertEqual(result.returncode, 0)

  def test_assert_struct_equality_reports_diff(self) -> None:
    result = run_program(
      """\
      struct pt {
          int x,
          int y
      }
      void main() {
          pt a;
          pt b;
          a.x += 1;
          b.x += 2;
          assert(a == b);
      }
      """,
      ["--std", "janus2026"],
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("Assertion failed: values should be equal", result.stdout)
    self.assertIn("left:  a = {x=1, y=0}", result.stdout)
    self.assertIn("right: b = {x=2, y=0}", result.stdout)


class NoMainFlagTests(unittest.TestCase):
  LIBRARY = """\
    procedure inc(int x)
        x += 1
    """

  def test_missing_main_errors_without_flag(self) -> None:
    result = run_program(self.LIBRARY, ["--std", "jana2014"])
    self.assertEqual(result.returncode, 1)
    self.assertIn("No main procedure has been defined", result.stdout)

  def test_no_main_flag_allows_library_ast(self) -> None:
    result = run_program(self.LIBRARY, ["--std", "jana2014", "--no-main", "-a"])
    self.assertEqual(result.returncode, 0)
    self.assertIn('"name": "inc"', result.stdout)


if __name__ == "__main__":
  unittest.main()
