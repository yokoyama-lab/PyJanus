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


class PreprocessIncludeTests(unittest.TestCase):
  def run_files(self, files: dict[str, str], main_name: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(dir=ROOT) as tmpdir:
      root = Path(tmpdir)
      for name, source in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(textwrap.dedent(source), encoding="utf-8")
      return run_python([str(root / main_name)])

  def test_include_expands_relative_file(self) -> None:
    result = self.run_files(
      {
        "defs.ja": """\
        #define X 333
        """,
        "main.ja": """\
        #include "defs.ja"
        procedure main()
            int x = X
            printf("%d", x)
        """,
      },
      "main.ja",
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "333\nx = 333\n")

  def test_include_cycle_fails(self) -> None:
    result = self.run_files(
      {
        "a.ja": """\
        #include "b.ja"
        procedure main()
            skip
        """,
        "b.ja": """\
        #include "a.ja"
        """,
      },
      "a.ja",
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("Cyclic include detected", result.stdout)

  def test_include_after_code_fails(self) -> None:
    result = self.run_files(
      {
        "defs.ja": """\
        #define X 1
        """,
        "main.ja": """\
        procedure main()
            skip
        #include "defs.ja"
        """,
      },
      "main.ja",
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("#include is only allowed", result.stdout)

  def test_unsupported_directive_fails(self) -> None:
    with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
      handle.write(textwrap.dedent(
        """\
        #include <x.h>
        procedure main()
            skip
        """
      ))
      path = handle.name
    try:
      result = run_python([path])
    finally:
      Path(path).unlink(missing_ok=True)
    self.assertEqual(result.returncode, 1)
    self.assertIn("Unsupported preprocessor directive", result.stdout)


if __name__ == "__main__":
  unittest.main()
