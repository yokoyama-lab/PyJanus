from __future__ import annotations

from pathlib import Path
import sys
import textwrap
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_programs import _safe_test_name, parse_specs  # noqa: E402


class ProgramSpecParserTests(unittest.TestCase):
  def test_legacy_single_case(self) -> None:
    specs = parse_specs(textwrap.dedent("""
      // in: 3 7
      // out: 10 7
    """))

    self.assertEqual(specs, [{"case": "default", "in": "3 7", "out": "10 7"}])

  def test_multiple_named_cases(self) -> None:
    specs = parse_specs(textwrap.dedent("""
      // case: small
      // in: 1
      // out: 2
      // case: negative
      // in: -3
      // out: -2
    """))

    self.assertEqual(
      specs,
      [
        {"case": "small", "in": "1", "out": "2"},
        {"case": "negative", "in": "-3", "out": "-2"},
      ],
    )

  def test_error_case(self) -> None:
    specs = parse_specs(textwrap.dedent("""
      // case: nonzero
      // in: 9
      // error: must be zero
    """))

    self.assertEqual(specs, [{"case": "nonzero", "in": "9", "error": "must be zero"}])

  def test_rejects_missing_input(self) -> None:
    with self.assertRaisesRegex(ValueError, "must declare `// in:`"):
      parse_specs(textwrap.dedent("""
        // case: bad
        // out: 1
      """))

  def test_rejects_missing_out_or_error(self) -> None:
    with self.assertRaisesRegex(ValueError, "must declare `// out:` or `// error:`"):
      parse_specs(textwrap.dedent("""
        // case: bad
        // in: 1
      """))

  def test_rejects_out_and_error_together(self) -> None:
    with self.assertRaisesRegex(ValueError, "cannot declare both"):
      parse_specs(textwrap.dedent("""
        // case: bad
        // in: 1
        // out: 1
        // error: no
      """))

  def test_rejects_duplicate_fields(self) -> None:
    with self.assertRaisesRegex(ValueError, "duplicate `// in:`"):
      parse_specs(textwrap.dedent("""
        // case: bad
        // in: 1
        // in: 2
        // out: 1
      """))

  def test_rejects_duplicate_case_names(self) -> None:
    with self.assertRaisesRegex(ValueError, "duplicate case name"):
      parse_specs(textwrap.dedent("""
        // case: dup
        // in: 1
        // out: 1
        // case: dup
        // in: 2
        // out: 2
      """))


class ProgramSpecNameTests(unittest.TestCase):
  def test_safe_test_name_preserves_simple_names(self) -> None:
    self.assertEqual(_safe_test_name("zero_left"), "zero_left")

  def test_safe_test_name_replaces_non_word_characters(self) -> None:
    self.assertEqual(_safe_test_name("zero-left case"), "zero_left_case")

  def test_safe_test_name_handles_empty_names(self) -> None:
    self.assertEqual(_safe_test_name("---"), "case")

  def test_safe_test_name_prefixes_digit(self) -> None:
    self.assertEqual(_safe_test_name("1st"), "_1st")


if __name__ == "__main__":
  unittest.main()
