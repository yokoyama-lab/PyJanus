"""The example corpus's metadata headers say what each program computes.

Every other corpus test in this directory checks a self-consistency property --
run-then-invert restores the store, the C++ back-end agrees with the
interpreter, the formatter round-trips.  A program that computes the wrong
thing, reversibly, passes all of them.  The `// @expect:` lines of a metadata
header are the missing oracle: they pin the program's actual output.

Annotating the corpus is incremental, so a file with no header is skipped
rather than failed; `tools/check_corpus_meta.py report` is the progress meter.
A file with a *partial* header is a failure -- see `docs/corpus-annotation-manual.md`.
"""

from __future__ import annotations

import glob
import sys
import textwrap
import unittest
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))

from check_corpus_meta import (  # noqa: E402
  FILENAME_RE,
  TECHNIQUES,
  check_file,
  diff_expect,
  evaluate_oracle,
  normalized_text,
  parse_meta,
  parse_store,
  parse_value,
)

EXAMPLES = sorted(glob.glob(str(ROOT / "tests" / "jana2014" / "fixtures" / "examples" / "*.ja")))


@pytest.mark.parametrize("ja", EXAMPLES, ids=lambda p: Path(p).name)
def test_metadata_header(ja: str) -> None:
  path = Path(ja)
  if not parse_meta(path).annotated:
    pytest.skip("no metadata header yet")
  problems = check_file(path)
  assert not problems, f"{path.name}:\n  " + "\n  ".join(problems)


@pytest.mark.parametrize("ja", EXAMPLES, ids=lambda p: Path(p).name)
def test_filename_is_lowercase_with_underscores(ja: str) -> None:
  # Unlike the header, naming is not incremental: it applies to every file now.
  assert FILENAME_RE.match(Path(ja).name)


@pytest.mark.parametrize("ja", EXAMPLES, ids=lambda p: Path(p).name)
def test_header_is_in_house_style(ja: str) -> None:
  # `normalize` is idempotent, so a file already in house style is its own fixpoint.
  text = Path(ja).read_text()
  assert normalized_text(text) == text, f"{Path(ja).name}: run tools/check_corpus_meta.py normalize"


class MetaParserTests(unittest.TestCase):
  """Unit tests for the header parser, independent of the corpus."""

  def _write(self, text: str) -> Path:
    import tempfile

    handle = tempfile.NamedTemporaryFile("w", suffix=".ja", delete=False)
    handle.write(textwrap.dedent(text).lstrip("\n"))
    handle.close()
    self.addCleanup(lambda: Path(handle.name).unlink(missing_ok=True))
    return Path(handle.name)

  def test_unannotated_file_is_not_an_error(self) -> None:
    meta = parse_meta(self._write("procedure main()\n  int x\n"))
    self.assertFalse(meta.annotated)
    self.assertEqual(meta.errors, [])

  def test_complete_header_parses(self) -> None:
    meta = parse_meta(self._write("""
      // @summary:   adds one
      // @technique: clean-accumulation
      // @source:    original
      // @confirmed: 0 + 1 = 1
      // @expect: x = 1
      procedure main()
    """))
    self.assertEqual(meta.errors, [])
    self.assertEqual(meta.one("summary"), "adds one")
    self.assertEqual(meta.fields["expect"], ["x = 1"])

  def test_partial_header_is_an_error(self) -> None:
    meta = parse_meta(self._write("// @summary: adds one\nprocedure main()\n"))
    self.assertTrue(meta.annotated)
    self.assertIn("missing `@technique:`", meta.errors)
    self.assertIn("missing `@expect:`", meta.errors)

  def test_unknown_technique_is_an_error(self) -> None:
    meta = parse_meta(self._write("""
      // @summary:   adds one
      // @technique: magic
      // @source:    original
      // @confirmed: 0 + 1 = 1
      // @expect: x = 1
    """))
    self.assertTrue(any("magic" in e for e in meta.errors))
    self.assertIn("clean-accumulation", ", ".join(TECHNIQUES))

  def test_unknown_field_is_an_error(self) -> None:
    meta = parse_meta(self._write("// @summry: typo\n"))
    self.assertTrue(any("@summry" in e for e in meta.errors))

  def test_non_repeatable_field_given_twice(self) -> None:
    meta = parse_meta(self._write("// @summary: a\n// @summary: b\n"))
    self.assertTrue(any("given twice" in e for e in meta.errors))

  def test_expect_keeps_leading_spaces_but_prose_is_stripped(self) -> None:
    meta = parse_meta(self._write("// @expect:   indented\n// @summary:   padded\n"))
    self.assertEqual(meta.fields["expect"], ["  indented"])
    self.assertEqual(meta.one("summary"), "padded")

  def test_fields_must_lead_the_file_contiguously_and_in_order(self) -> None:
    out_of_order = parse_meta(self._write("""
      // @technique: plain
      // @summary:   adds one
      // @source:    original
      // @confirmed: obvious
      // @expect: x = 1
    """))
    self.assertTrue(any("in the order" in e for e in out_of_order.errors))

    not_first = parse_meta(self._write("procedure main()\n// @summary: adds one\n"))
    self.assertTrue(any("must start on line 1" in e for e in not_first.errors))

    gapped = parse_meta(self._write("// @summary: adds one\n\n// @technique: plain\n"))
    self.assertTrue(any("contiguous" in e for e in gapped.errors))

  def test_diff_expect_reports_each_kind_of_mismatch(self) -> None:
    self.assertEqual(diff_expect(["a"], ["a"]), [])
    self.assertTrue(diff_expect(["a"], ["b"])[0].startswith("line 1: expected"))
    self.assertIn("output ended", diff_expect(["a", "b"], ["a"])[0])
    self.assertIn("extra output", diff_expect(["a"], ["a", "b"])[0])


class StoreParserTests(unittest.TestCase):
  """`@oracle` sees the final store; this is the grammar `pyjanus -s` prints."""

  def test_scalars_arrays_structs_and_stacks(self) -> None:
    store = parse_store([
      "n = 5",
      "a[3] = {1, 2, 3}",
      "m[2][2] = {{1, 2}, {3, 4}}",
      "p = {x = 10, y = 4}",
      "s = <7, 8]",
      "empty = nil",
    ])
    self.assertEqual(store["n"], 5)
    self.assertEqual(store["a"], [1, 2, 3])
    self.assertEqual(store["m"], [[1, 2], [3, 4]])
    self.assertEqual(store["p"], {"x": 10, "y": 4})
    self.assertEqual(store["s"], [7, 8])
    self.assertEqual(store["empty"], [])

  def test_struct_fields_are_reachable_as_attributes(self) -> None:
    store = parse_store(["p = {x = 10, y = 4}"])
    self.assertEqual(store["p"].x, 10)

  def test_nested_structs_and_arrays_of_structs(self) -> None:
    self.assertEqual(parse_value("{v = {1, 2}, w = 3}"), {"v": [1, 2], "w": 3})
    self.assertEqual(parse_value("{{v = 1}, {v = 2}}"), [{"v": 1}, {"v": 2}])

  def test_negative_numbers(self) -> None:
    self.assertEqual(parse_store(["n = -3"])["n"], -3)

  def test_unparseable_line_raises(self) -> None:
    with self.assertRaises(ValueError):
      parse_store(["not a store line"])


class OracleTests(unittest.TestCase):
  def test_true_and_false(self) -> None:
    self.assertEqual(evaluate_oracle("x == 1", {"x": 1})[0], True)
    ok, detail = evaluate_oracle("x == 2", {"x": 1})
    self.assertFalse(ok)
    self.assertIn("x=1", detail)

  def test_allowed_helpers(self) -> None:
    self.assertTrue(evaluate_oracle("a == sorted([3, 1, 2])", {"a": [1, 2, 3]})[0])
    self.assertTrue(evaluate_oracle("g == gcd(12, 18)", {"g": 6})[0])

  def test_non_boolean_result_is_a_problem(self) -> None:
    ok, detail = evaluate_oracle("x + 1", {"x": 1})
    self.assertFalse(ok)
    self.assertIn("not True or False", detail)

  def test_errors_are_reported_not_raised(self) -> None:
    ok, detail = evaluate_oracle("nosuchname == 1", {})
    self.assertFalse(ok)
    self.assertIn("NameError", detail)

  def test_dangerous_builtins_are_unavailable(self) -> None:
    ok, detail = evaluate_oracle("__import__('os').listdir('.') == []", {})
    self.assertFalse(ok)
    self.assertIn("NameError", detail)


class NormalizeTests(unittest.TestCase):
  def test_banner_and_block_comments_become_line_comments(self) -> None:
    text = normalized_text("////////////\n/* one\n * two\n */\nprocedure main()\n")
    self.assertEqual(text, "// one\n// two\n\nprocedure main()\n")

  def test_at_block_is_hoisted_above_the_prose_and_ordered(self) -> None:
    text = normalized_text("// prose\n// @technique: plain\n// @summary: s\nprocedure main()\n")
    self.assertEqual(
      text.splitlines()[:4],
      ["// @summary: s", "// @technique: plain", "//", "// prose"],
    )

  def test_code_is_untouched(self) -> None:
    body = "procedure main()\n    int x\n    x += 1 // trailing comment stays\n"
    self.assertEqual(normalized_text(body), body)

  def test_idempotent(self) -> None:
    once = normalized_text("/////\n/* a\n *\n * b */\nprocedure main()\n")
    self.assertEqual(normalized_text(once), once)


if __name__ == "__main__":
  unittest.main()
