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


class StructShowTests(unittest.TestCase):
  def run_case(self, source: str) -> subprocess.CompletedProcess[str]:
    with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
      handle.write(textwrap.dedent(source))
      path = handle.name
    try:
      return run_python(path)
    finally:
      Path(path).unlink(missing_ok=True)

  def test_show_and_store_render_struct_fields(self) -> None:
    result = self.run_case(
      """\
      struct Pair {
          int x,
          int y
      }

      procedure main()
          Pair p
          p.x += 1
          p.y += 2
          show(p)
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "p = {x = 1, y = 2}\np = {x = 1, y = 2}\n")
    self.assertEqual(result.stderr, "")

  def test_show_and_store_render_struct_array_fields(self) -> None:
    result = self.run_case(
      """\
      struct Entry {
          int k
      }

      struct Dict {
          int size,
          Entry entries[2]
      }

      procedure main()
          Dict d
          d.size += 2
          d.entries[1].k += 7
          show(d)
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "d = {size = 2, entries = {{k = 0}, {k = 7}}}\nd = {size = 2, entries = {{k = 0}, {k = 7}}}\n")
    self.assertEqual(result.stderr, "")


  def test_show_struct_array_from_bracket_syntax(self) -> None:
    result = self.run_case(
      """\
      struct Pair {
          int x,
          int y
      }

      procedure main()
          Pair[2] ps
          ps[0].x += 1
          ps[1].y += 2
          show(ps)
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertIn("ps[2] = {{x = 1, y = 0}, {x = 0, y = 2}}", result.stdout)
    self.assertEqual(result.stderr, "")


if __name__ == "__main__":
  unittest.main()
