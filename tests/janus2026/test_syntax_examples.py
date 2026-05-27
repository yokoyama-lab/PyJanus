from __future__ import annotations

from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from jana_py.format import format_program
from jana_py.parser_janus2026 import parse_program


SYNTAX_DIR = ROOT / "tests" / "janus2026" / "fixtures" / "examples"


class SyntaxExampleTests(unittest.TestCase):
  def test_all_syntax_examples_parse_and_format_canonically(self) -> None:
    for path in sorted(SYNTAX_DIR.glob("*.ja")):
      with self.subTest(path=path.name):
        source = path.read_text()
        program = parse_program(str(path), source)
        canonical = format_program(program)
        reparsed = parse_program(str(path), canonical)
        self.assertEqual(format_program(reparsed), canonical)


if __name__ == "__main__":
  unittest.main()
