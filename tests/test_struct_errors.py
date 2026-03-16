from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[1]


def run_python(path: str) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", path],
    cwd=ROOT,
    text=True,
    capture_output=True,
    env=env,
    check=False,
  )


class StructErrorTests(unittest.TestCase):
  def run_case(self, source: str) -> subprocess.CompletedProcess[str]:
    with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
      handle.write(textwrap.dedent(source))
      path = handle.name
    try:
      return run_python(path)
    finally:
      Path(path).unlink(missing_ok=True)

  def test_duplicate_field_names_fail(self) -> None:
    result = self.run_case(
      """\
      struct Pair {
          int x,
          int x
      }

      procedure main()
          skip
      """
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("Field `x' is already defined in struct `Pair'", result.stdout)

  def test_unknown_struct_type_fails(self) -> None:
    result = self.run_case(
      """\
      procedure main()
          Pair p
          skip
      """
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("Struct `Pair' is not defined", result.stdout)

  def test_unknown_field_fails(self) -> None:
    result = self.run_case(
      """\
      struct Pair {
          int x
      }

      procedure main()
          Pair p
          p.y += 1
      """
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("does not have field `y'", result.stdout)

  def test_wrong_struct_argument_type_fails(self) -> None:
    result = self.run_case(
      """\
      struct Pair {
          int x
      }

      struct Other {
          int x
      }

      procedure bump(Pair p)
          skip

      procedure main()
          Other p
          call bump(p)
      """
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("Couldn't match expected type `Pair'", result.stdout)

  def test_ternary_condition_must_be_bool(self) -> None:
    result = self.run_case(
      """\
      procedure main()
          int x = 1
          int y
          y += x ? 3 : 4
      """
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("Couldn't match expected type `bool'", result.stdout)


if __name__ == "__main__":
  unittest.main()
