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


class PreprocessEscapeTests(unittest.TestCase):
  def run_case(self, source: str) -> subprocess.CompletedProcess[str]:
    with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
      handle.write(textwrap.dedent(source))
      path = handle.name
    try:
      return run_python([path])
    finally:
      Path(path).unlink(missing_ok=True)

  def run_files(self, files: dict[str, str], main_name: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(dir=ROOT) as tmpdir:
      root = Path(tmpdir)
      for name, source in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(textwrap.dedent(source), encoding="utf-8")
      return run_python([str(root / main_name)])

  def test_define_does_not_expand_inside_string_or_comment(self) -> None:
    result = self.run_case(
      """\
      #define MSG 42
      procedure main()
          // MSG should not expand here
          print("MSG")
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "MSG\n")
    self.assertEqual(result.stderr, "")

  def test_define_does_not_expand_inside_escaped_string(self) -> None:
    result = self.run_case(
      """\
      #define MSG 42
      procedure main()
          print("MSG \\\" MSG \\\\ MSG")
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, 'MSG " MSG \\ MSG\n')
    self.assertEqual(result.stderr, "")

  def test_include_macro_preserves_escaped_string_literal(self) -> None:
    result = self.run_files(
      {
        "defs.ja": """\
        #define MSG "a\\n\\\\\\\"b"
        """,
        "main.ja": """\
        #include "defs.ja"
        procedure main()
            print(MSG)
        """,
      },
      "main.ja",
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, 'a\n\\"b\n')
    self.assertEqual(result.stderr, "")

  def test_function_macro_argument_preserves_escaped_string_literal(self) -> None:
    result = self.run_case(
      """\
      #define ID(x) x
      procedure main()
          print(ID("a\\n\\\\\\\"b"))
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, 'a\n\\"b\n')
    self.assertEqual(result.stderr, "")

  def test_function_macro_argument_allows_comma_inside_string_literal(self) -> None:
    result = self.run_case(
      """\
      #define ID(x) x
      procedure main()
          print(ID("a,b"))
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "a,b\n")
    self.assertEqual(result.stderr, "")


if __name__ == "__main__":
  unittest.main()
