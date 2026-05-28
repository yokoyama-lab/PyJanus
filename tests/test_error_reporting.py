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


if __name__ == "__main__":
  unittest.main()
