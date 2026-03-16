from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from jana_py.format import format_program
from jana_py.parser import parse_program


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


class CharArraySupportTests(unittest.TestCase):
  def run_case(self, source: str) -> subprocess.CompletedProcess[str]:
    with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
      handle.write(textwrap.dedent(source))
      path = handle.name
    try:
      return run_python(path)
    finally:
      Path(path).unlink(missing_ok=True)

  def test_parser_and_formatter_preserve_char_string_init(self) -> None:
    program = parse_program(
      "char_format.ja",
      textwrap.dedent(
        """\
        procedure main()
            char s[] = "abc"
            printf("%s", s)
        """
      ),
    )
    self.assertEqual(
      format_program(program),
      textwrap.dedent(
        """\
        procedure main()
            char s[] = "abc"
            printf("%s", s)
        """
      ),
    )

  def test_parser_and_formatter_preserve_escaped_char_string_init(self) -> None:
    program = parse_program(
      "char_escape_format.ja",
      textwrap.dedent(
        """\
        procedure main()
            char s[] = "a\\n\\\\\\\"b\\u0000"
            printf("%s", s)
        """
      ),
    )
    self.assertEqual(
      format_program(program),
      textwrap.dedent(
        """\
        procedure main()
            char s[] = "a\\n\\\\\\\"b\\u0000"
            printf("%s", s)
        """
      ),
    )

  def test_char_array_infers_size_and_supports_printf_s(self) -> None:
    result = self.run_case(
      """\
      procedure main()
          char s[] = "abc"
          printf("%s", s)
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "abc\ns[4] = {97, 98, 99, 0}\n")
    self.assertEqual(result.stderr, "")

  def test_char_array_fixed_size_zero_pads(self) -> None:
    result = self.run_case(
      """\
      procedure main()
          char s[5] = "abc"
          skip
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "s[5] = {97, 98, 99, 0, 0}\n")
    self.assertEqual(result.stderr, "")

  def test_string_alias_fixed_size_accepts_string_initializer(self) -> None:
    result = self.run_case(
      """\
      procedure main()
          string in[9] = "bananana"
          printf("%s", in)
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "bananana\nin[9] = {98, 97, 110, 97, 110, 97, 110, 97, 0}\n")
    self.assertEqual(result.stderr, "")

  def test_string_alias_infers_size_from_string_initializer(self) -> None:
    result = self.run_case(
      """\
      procedure main()
          string in[] = "bananana"
          printf("%s", in)
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "bananana\nin[9] = {98, 97, 110, 97, 110, 97, 110, 97, 0}\n")
    self.assertEqual(result.stderr, "")

  def test_local_char_array_round_trips(self) -> None:
    result = self.run_case(
      """\
      procedure main()
          local char s[] = "abc"
              printf("%s", s)
          delocal char s[4] = "abc"
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "abc\n")
    self.assertEqual(result.stderr, "")

  def test_printf_s_stops_at_embedded_nul(self) -> None:
    result = self.run_case(
      """\
      procedure main()
          char s[] = "ab\\u0000c"
          printf("%s", s)
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "ab\ns[5] = {97, 98, 0, 99, 0}\n")
    self.assertEqual(result.stderr, "")

  def test_char_array_handles_escape_sequences(self) -> None:
    result = self.run_case(
      """\
      procedure main()
          char s[] = "a\\n\\\\\\\"b"
          printf("%s", s)
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, 'a\n\\"b\ns[6] = {97, 10, 92, 34, 98, 0}\n')
    self.assertEqual(result.stderr, "")

  def test_printf_percent_and_backslash_escapes(self) -> None:
    result = self.run_case(
      """\
      procedure main()
          char s[] = "xy"
          printf("path=\\\\tmp %% %s", s)
      """
    )
    self.assertEqual(result.returncode, 0)
    self.assertEqual(result.stdout, "path=\\tmp % xy\ns[3] = {120, 121, 0}\n")
    self.assertEqual(result.stderr, "")

  def test_printf_reports_unrecognized_percent_with_escapes(self) -> None:
    result = self.run_case(
      """\
      procedure main()
          char s[] = "xy"
          printf("path=\\\\tmp %q %s", s)
      """
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("Unrecognized format specifier: `%q'", result.stdout)

  def test_char_array_size_too_small_fails(self) -> None:
    result = self.run_case(
      """\
      procedure main()
          char s[3] = "abc"
          skip
      """
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("Initializer is too large for variable `s'", result.stdout)

  def test_printf_s_requires_char_array(self) -> None:
    result = self.run_case(
      """\
      procedure main()
          int s[4] = {97, 98, 99, 0}
          printf("%s", s)
      """
    )
    self.assertEqual(result.returncode, 1)
    self.assertIn("Type mismatch for `%s' format specifier", result.stdout)


if __name__ == "__main__":
  unittest.main()
