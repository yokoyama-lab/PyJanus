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


class PreprocessSourceMapTests(unittest.TestCase):
  def run_files(self, files: dict[str, str], main_name: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(dir=ROOT) as tmpdir:
      root = Path(tmpdir)
      for name, source in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(textwrap.dedent(source), encoding="utf-8")
      return run_python([str(root / main_name)])

  def test_include_parse_error_reports_original_file(self) -> None:
    result = self.run_files(
      {
        "defs.ja": """\
        @
        """,
        "main.ja": """\
        #include "defs.ja"
        procedure main()
            skip
        """,
      },
      "main.ja",
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn('defs.ja" in line 1', result.stdout)


if __name__ == "__main__":
  unittest.main()
