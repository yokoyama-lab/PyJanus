from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[2]


def run_python(path: str, *args: str) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT / "src")
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", *args, path],
    cwd=ROOT,
    text=True,
    capture_output=True,
    env=env,
    check=False,
  )


class CliStoreOutputTests(unittest.TestCase):
  def run_case(self, source: str, *args: str) -> subprocess.CompletedProcess[str]:
    with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
      handle.write(textwrap.dedent(source))
      path = handle.name
    try:
      return run_python(path, *args)
    finally:
      Path(path).unlink(missing_ok=True)

  def test_default_execution_hides_final_store(self) -> None:
    result = self.run_case(
      """\
      void main() {
          int x = 5;
          printf("%d", x);
      }
      """
    )
    self.assertEqual(result.returncode, 0)
    # Without -s the store dump is hidden: stdout is just the printf output.
    self.assertEqual(result.stdout, "5\n")
    self.assertNotIn("x = 5", result.stdout)

  def test_store_flag_shows_final_store(self) -> None:
    result = self.run_case(
      """\
      void main() {
          int x = 5;
          printf("%d", x);
      }
      """,
      "-s",
    )
    self.assertEqual(result.returncode, 0)
    # With -s the final store is appended after the printf output.
    self.assertEqual(result.stdout, "5\nx = 5\n")

  def test_nonzero_final_values_emit_warning(self) -> None:
    result = self.run_case(
      """\
      void main() {
          int x = 5;
      }
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "")
    self.assertEqual(result.stderr, "Warning: non-zero values remain at end of execution: x\n")


if __name__ == "__main__":
  unittest.main()
