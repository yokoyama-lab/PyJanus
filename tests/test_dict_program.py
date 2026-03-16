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


class DictProgramTests(unittest.TestCase):
  def run_example(self, relative_path: str) -> subprocess.CompletedProcess[str]:
    return run_python(str(ROOT / relative_path))

  def run_case(self, source: str) -> subprocess.CompletedProcess[str]:
    with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
      handle.write(textwrap.dedent(source))
      path = handle.name
    try:
      return run_python(path)
    finally:
      Path(path).unlink(missing_ok=True)

  def test_build_dict_style_program_runs(self) -> None:
    result = self.run_case(
      """\
      #define ALPHABET_SIZE 2
      #define NONE 0
      #define NULL 0
      #define code int
      #define codes code[]

      struct entry {
          int c,
          char k,
          char fst,
          int len
      }

      struct dict {
          int size,
          entry entries[5]
      }

      procedure init_dict(dict d)
          d.size ^= ALPHABET_SIZE + 1
          iterate int i = 1 to d.size - 1
              d.entries[i].k ^= i
              d.entries[i].fst ^= i
              d.entries[i].len ^= 1
          end

      procedure add_to_dict(code c, char k, dict d)
          local int n = d.size, char fst = d.entries[c].fst, int len = d.entries[c].len + 1
              d.entries[n].c ^= c
              d.entries[n].k ^= k
              d.entries[n].fst ^= fst
              fst ^= d.entries[n].fst
              d.entries[n].len ^= len
              len ^= d.entries[n].len
          delocal int n = d.size, char fst = 0, int len = 0
          d.size += 1

      procedure build_dict(codes out, int i, int j, dict d)
          local char k = 0
              call init_dict(d)
              from j = 0 loop
                  j += 1
                  k ^= d.entries[out[j]].k = NONE ? d.entries[out[j-1]].fst : d.entries[out[j]].fst
                  call add_to_dict(out[j-1], k, d)
                  k ^= d.entries[d.size-1].k
                  i += d.entries[out[j]].len
              until out[j+1] = NULL
          delocal char k = 0

      procedure main()
          codes out[3]
          int i
          int j
          dict d
          out[0] += 1
          out[1] += 2
          call build_dict(out, i, j, d)
      """
    )
    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
    self.assertIn("d = {size = 4", result.stdout)
    self.assertIn("entries = {{c = 0, k = 0, fst = 0, len = 0}, {c = 0, k = 1, fst = 1, len = 1}, {c = 0, k = 2, fst = 2, len = 1}, {c = 1, k = 2, fst = 1, len = 2}", result.stdout)
    self.assertIn("i = 1", result.stdout)
    self.assertIn("j = 1", result.stdout)

  def test_build_dict_example_file_runs(self) -> None:
    result = self.run_example("examples/build-dict.ja")
    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
    self.assertIn("d = {size = 4", result.stdout)
    self.assertIn("i = 1", result.stdout)
    self.assertIn("j = 1", result.stdout)


if __name__ == "__main__":
  unittest.main()
