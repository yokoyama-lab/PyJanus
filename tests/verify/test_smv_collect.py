"""`smv.collect_unsupported` reports EVERY blocker, not just the first.

Why this exists at all: the coverage tallies this project sizes features with
are built from `compile_to_smv`'s FIRST refusal, and a first-refusal tally is
not an upper bound on what implementing a feature would admit — one program can
hold any number of blockers.  Four estimates were built that way and three
missed (`docs/loop-queue.md`, items 21-28).  So the collector has to be right
about two things, and both are tested here:

1. it finds the blockers that come *after* the first one, and
2. it does not change what the checker accepts or rejects — a diagnostic that
   perturbs the thing it measures is worse than no diagnostic.
"""
import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py import parser_jana2014, preprocess  # noqa: E402
from jana_py.smv import (SmvUnsupported, collect_unsupported,  # noqa: E402
                         compile_to_smv)


def parse(src: str):
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  return parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)


# Two blockers, in this order: `^=` first, then a stack operation.  The first
# refusal alone would report `^=` and say nothing about the second.
TWO_BLOCKERS = """
procedure main()
    int x
    int s[4]
    x ^= 3
    x <=> s[0]
    x += 1
"""

INSIDE_FRAGMENT = """
procedure main()
    int x
    x += 1
    if x = 1 then
        x += 2
    else
        x -= 1
    fi x = 3
"""

ONE_BLOCKER = """
procedure main()
    int x
    x ^= 3
    x += 1
"""


class CollectsMoreThanTheFirst(unittest.TestCase):
  def test_first_refusal_reports_one_reason(self):
    with self.assertRaises(SmvUnsupported) as cm:
      compile_to_smv(parse(TWO_BLOCKERS), init="zero")
    self.assertIn("^=", str(cm.exception))

  def test_collection_reports_both(self):
    reasons = collect_unsupported(parse(TWO_BLOCKERS), init="zero")
    self.assertGreaterEqual(len(reasons), 2, reasons)
    self.assertTrue(any("^=" in r for r in reasons), reasons)

  def test_a_single_blocker_is_still_one_reason(self):
    """The collector must not manufacture blockers that are not there."""
    reasons = collect_unsupported(parse(ONE_BLOCKER), init="zero")
    self.assertEqual(len(reasons), 1, reasons)
    self.assertIn("^=", reasons[0])

  def test_a_program_inside_the_fragment_has_no_reasons(self):
    self.assertEqual(collect_unsupported(parse(INSIDE_FRAGMENT), init="zero"), [])


class DoesNotPerturbTheChecker(unittest.TestCase):
  """The diagnostic must leave `compile_to_smv` exactly as it was."""

  def test_the_model_is_unchanged_after_a_collection(self):
    before = compile_to_smv(parse(INSIDE_FRAGMENT), init="zero")
    collect_unsupported(parse(TWO_BLOCKERS), init="zero")
    after = compile_to_smv(parse(INSIDE_FRAGMENT), init="zero")
    self.assertEqual(before, after)

  def test_rejection_still_raises_after_a_collection(self):
    collect_unsupported(parse(TWO_BLOCKERS), init="zero")
    with self.assertRaises(SmvUnsupported):
      compile_to_smv(parse(TWO_BLOCKERS), init="zero")

  def test_the_flag_is_cleared_even_when_compilation_raises(self):
    """A leaked flag would silently turn every later refusal into a skip —
    the checker would stop refusing anything."""
    from jana_py import smv
    collect_unsupported(parse(TWO_BLOCKERS), init="zero")
    self.assertIsNone(smv._COLLECT)


if __name__ == "__main__":
  unittest.main()
