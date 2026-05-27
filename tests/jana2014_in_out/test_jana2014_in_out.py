"""Parser-level checks for the jana2014_in_out dialect.

End-to-end execution (forward/backward I/O) is covered by the real `.ja`
programs in `programs/` via test_programs.py.
"""
from __future__ import annotations

from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py.parser_jana2014_in_out import parse_program
from jana_py.ast import PrintsStmt


class ParseTests(unittest.TestCase):
  def test_read_write_parse_to_prints(self) -> None:
    prog = parse_program("io.ja", "procedure main()\n    int x\n    read x\n    write x\n")
    kinds = [s.prints.kind for s in prog.main.stmts if isinstance(s, PrintsStmt)]
    self.assertEqual(kinds, ["read", "write"])

  def test_inherits_jana2014_printf(self) -> None:
    # printf/show remain available for non-consuming debug output.
    parse_program("io.ja", 'procedure main()\n    int x\n    read x\n    printf("%d", x)\n    write x\n')


if __name__ == "__main__":
  unittest.main()
