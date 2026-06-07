"""Jana 2014 parser extended with reversible I/O (`jana2014_in_out`).

Identical to the `jana2014` (full) parser — implemented as a thin subclass so
every jana2014 feature (structs, ternary, `char`/`string`, `*=`/`/=`, ...)
is inherited automatically — plus the classic reversible I/O statement pair:
  - `read x`  — consume an input value into the (zero) variable `x`
  - `write x` — emit `x` as output and clear it back to zero

These are exact inverses of each other (see `invert.py`), so a program can be
run forwards (input -> output) or backwards (output -> input) and verified.
For non-consuming debug output, the inherited `printf` / `show` remain available.
"""
from __future__ import annotations

from typing import Sequence

from .ast import Prints
from .ast import PrintsStmt
from .ast import Program
from .parser_jana2014 import KEYWORDS as _JANA2014_KEYWORDS
from .parser_jana2014 import Parser as _Jana2014Parser
from .preprocess import LineOrigin

KEYWORDS = _JANA2014_KEYWORDS | {"read", "write"}


class Parser(_Jana2014Parser):
  KEYWORDS = KEYWORDS

  def parse_statement(self, end_keywords: set[str] = set()):
    token = self.tokens.peek()
    if token.kind == "KW":
      if token.value == "read":
        return self.parse_read_stmt()
      if token.value == "write":
        return self.parse_write_stmt()
    return super().parse_statement(end_keywords)

  def parse_read_stmt(self) -> PrintsStmt:
    pos = self.expect_kw("read").pos
    lval = self.parse_lval()
    return PrintsStmt(Prints("read", args=[lval], reversible=True), pos)

  def parse_write_stmt(self) -> PrintsStmt:
    pos = self.expect_kw("write").pos
    lval = self.parse_lval()
    return PrintsStmt(Prints("write", args=[lval], reversible=True), pos)


def parse_program(filename: str, text: str, line_origins: Sequence[LineOrigin] | None = None) -> Program:
  return Parser(filename, text, line_origins).parse_program()
