"""Keep `docs/corpus-coverage.md` honest about which programs exist.

The matrix itself is generated from a pytest `--junitxml` report, which means
regenerating it costs a full run and cannot happen inside the suite. What can be
checked cheaply is that the document has not gone stale in the one way it
silently would: a program renamed, added or removed, leaving a table that
quietly describes a corpus that no longer exists.
"""

from __future__ import annotations

import glob
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / "docs" / "corpus-coverage.md"
EXAMPLES = sorted(Path(p).name for p in
                  glob.glob(str(ROOT / "tests" / "jana2014" / "fixtures" / "examples" / "*.ja")))


class CoverageDocTests(unittest.TestCase):
  def setUp(self) -> None:
    self.assertTrue(DOC.exists(), f"{DOC.relative_to(ROOT)} is missing; regenerate it (see its header)")
    self.text = DOC.read_text()

  def test_every_example_has_a_row(self) -> None:
    missing = [name for name in EXAMPLES if f"| `{name}` |" not in self.text]
    self.assertEqual(missing, [], "programs with no row in the coverage matrix -- regenerate it")

  def test_no_row_names_a_program_that_is_gone(self) -> None:
    rows = {line.split("`")[1] for line in self.text.splitlines()
            if line.startswith("| `") and line.split("`")[1].endswith(".ja")}
    self.assertEqual(sorted(rows - set(EXAMPLES)), [], "rows for programs that no longer exist")

  def test_says_how_to_regenerate_itself(self) -> None:
    self.assertIn("tools/corpus_coverage.py", self.text)


if __name__ == "__main__":
  unittest.main()
