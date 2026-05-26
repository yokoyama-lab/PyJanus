"""Strict Janus 1982 parser — janus.pdf compliant.

Only supports features from Lutz & Derby's original 1982 paper:
  - Types: int only (unbounded)
  - Statements: +=, -=, ^= (!=), =, swap (: and <=>), if/fi, from/until,
                call, uncall, skip, read, write
  - Procedures: no parameters (global variables only)
  - Arrays: int a[N], a[i] access
  - Expressions: arithmetic, comparison, logical, bitwise, shift, exponent
  - Comments: //, ;, /* */

For the extended 1982-style parser (sized ints, bool, stack, struct, local/delocal,
switch, for, push/pop, etc.), use --std=janus1982ext.
"""
from __future__ import annotations

from dataclasses import dataclass
import re
from typing import Sequence

from .ast import AssignStmt
from .ast import BinExpr
from .ast import BinOpKind
from .ast import CallStmt
from .ast import DeclType
from .ast import Expr
from .ast import FromStmt
from .ast import Ident
from .ast import IfStmt
from .ast import IntType
from .ast import Lval
from .ast import LvalExpr
from .ast import LvalField
from .ast import LvalIndex
from .ast import ModOp
from .ast import Number
from .ast import Prints
from .ast import PrintsStmt
from .ast import Proc
from .ast import ProcMain
from .ast import Program
from .ast import SkipStmt
from .ast import SourcePos
from .ast import SwapStmt
from .ast import Type
from .ast import UncallStmt
from .ast import UnaryExpr
from .ast import UnaryOpKind
from .ast import Vdecl
from .errors import JanaError
from .preprocess import LineOrigin


KEYWORDS = {
  "procedure", "main", "int", "if", "then", "else", "fi",
  "from", "do", "loop", "until", "call", "uncall",
  "skip", "read", "write",
}

TOKEN_RE = re.compile(
  r"""
  (?P<SPACE>\s+)
  |(?P<COMMENT>//[^\n]*|;[^\n]*)
  |(?P<MCOMMENT>/\*.*?\*/)
  |(?P<NUMBER>0b[01]+|\d+)
  |(?P<OP><=>|==|\+=|-=|\^=|!=|<<|>>|<=|>=|&&|\|\||\*\*|=|<|>|\+|-|\*|/|\\|%|\^|&|\||!|\#|,|\.|\?|:|\(|\)|\[|\]|\{|\}|;)
  |(?P<IDENT>[A-Za-z][A-Za-z0-9_']*)
  |(?P<MISMATCH>.)
  """,
  re.DOTALL | re.VERBOSE,
)

BIN_PRECEDENCE = [
  {"ops": {"||": BinOpKind.LOR}, "assoc": "left"},
  {"ops": {"&&": BinOpKind.LAND}, "assoc": "left"},
  {"ops": {"&": BinOpKind.AND, "|": BinOpKind.OR, "^": BinOpKind.XOR}, "assoc": "left"},
  {"ops": {"<=": BinOpKind.LE, "<": BinOpKind.LT, ">=": BinOpKind.GE, ">": BinOpKind.GT, "==": BinOpKind.EQ, "=": BinOpKind.EQ, "#": BinOpKind.NEQ}, "assoc": "left"},
  {"ops": {"<<": BinOpKind.SL, ">>": BinOpKind.SR}, "assoc": "left"},
  {"ops": {"+": BinOpKind.ADD, "-": BinOpKind.SUB}, "assoc": "left"},
  {"ops": {"*": BinOpKind.MUL, "/": BinOpKind.DIV, "\\": BinOpKind.MOD, "%": BinOpKind.MOD}, "assoc": "left"},
  {"ops": {"**": BinOpKind.EXP}, "assoc": "left"},
]


@dataclass(frozen=True)
class Token:
  kind: str
  value: str
  pos: SourcePos


class TokenStream:
  def __init__(self, tokens: list[Token]):
    self.tokens = tokens
    self.index = 0

  def peek(self, n: int = 0) -> Token:
    idx = self.index + n
    if idx >= len(self.tokens):
      return self.tokens[-1]
    return self.tokens[idx]

  def consume(self) -> Token:
    token = self.peek()
    self.index += 1
    return token

  def match(self, kind: str, value: str | None = None) -> Token | None:
    token = self.peek()
    if token.kind != kind:
      return None
    if value is not None and token.value != value:
      return None
    self.index += 1
    return token

  def expect(self, kind: str, value: str | None = None) -> Token:
    token = self.peek()
    if token.kind != kind or (value is not None and token.value != value):
      if value is not None:
        shown = token.value[0] if token.kind in {"IDENT", "KW"} and token.value else token.value
        if token.kind == "EOF":
          shown = "end of input"
        raise JanaError(token.pos, f'Unexpected "{shown}"\n    Expecting "{value}"')
      raise JanaError(token.pos, f'Unexpected "{token.value}"\n    Expecting {kind}')
    self.index += 1
    return token


def tokenize(filename: str, text: str, line_origins: Sequence[LineOrigin] | None = None) -> list[Token]:
  line = 1
  col = 1
  tokens: list[Token] = []
  for match in TOKEN_RE.finditer(text):
    kind = match.lastgroup
    value = match.group()
    origin = None
    if line_origins is not None and 1 <= line <= len(line_origins):
      origin = line_origins[line - 1]
    pos = SourcePos(origin.filename if origin is not None else filename, origin.line if origin is not None else line, col)
    line_breaks = value.count("\n")
    if line_breaks:
      col = len(value.rsplit("\n", 1)[-1]) + 1
      line += line_breaks
    else:
      col += len(value)
    if kind in {"SPACE", "COMMENT", "MCOMMENT"}:
      continue
    if kind == "IDENT":
      val_lower = value.lower()
      if val_lower in KEYWORDS:
        tokens.append(Token("KW", val_lower, pos))
        continue
    tokens.append(Token(kind, value, pos))
  origin = None
  if line_origins is not None and line_origins:
    idx = min(max(line - 1, 0), len(line_origins) - 1)
    origin = line_origins[idx]
  eof_line = line if col == 1 else line + 1
  eof_col = 1
  if line_origins is not None and line_origins:
    last_idx = len(line_origins) - 1
    last_origin = line_origins[last_idx]
    overshoot = eof_line - len(line_origins)
    if overshoot > 0:
      origin = LineOrigin(filename=last_origin.filename, line=last_origin.line + overshoot)
    else:
      origin = line_origins[min(max(eof_line - 1, 0), last_idx)]
  tokens.append(Token("EOF", "", SourcePos(origin.filename if origin is not None else filename, origin.line if origin is not None else eof_line, eof_col)))
  return tokens


class Parser:
  def __init__(self, filename: str, text: str, line_origins: Sequence[LineOrigin] | None = None):
    self.tokens = TokenStream(tokenize(filename, text, line_origins))

  def parse_program(self) -> Program:
    mains: list[ProcMain] = []
    procs: list[Proc] = []
    global_vdecls: list[Vdecl] = []
    while self.tokens.peek().kind != "EOF":
      if self.tokens.peek().kind == "IDENT" and self.tokens.peek(1).value not in {"(", "{"}:
        # Top-level variable declaration in janus1982
        global_vdecls.append(self._parse_typeless_vdecl())
        continue

      proc_or_main = self.parse_procedure()
      if isinstance(proc_or_main, ProcMain):
        mains.append(proc_or_main)
      else:
        procs.append(proc_or_main)

    if global_vdecls:
      if not mains:
        mains.append(ProcMain(global_vdecls, [], SourcePos(self.tokens.peek().pos.filename, 0, 0)))
      else:
        mains[0] = ProcMain(global_vdecls + mains[0].vdecls, mains[0].stmts, mains[0].pos)

    if len(mains) > 1:
      raise JanaError(self.tokens.peek().pos, 'Unexpected end of input\n    Expecting "procedure" or end of input\n    Multiple main procedures has been defined')
    return Program(mains[0] if mains else None, procs, [])

  def parse_procedure(self) -> ProcMain | Proc:
    start = self.tokens.peek()
    if start.kind != "KW" or start.value != "procedure":
      raise JanaError(start.pos, f'Unexpected "{start.value}"\n    Expecting "procedure"')
    self.tokens.consume()
    ident = self.parse_ident(allow_main=True)
    if ident.name == "main":
      pos = ident.pos
      # Optional empty parens for compatibility
      if self.tokens.peek().value == "(":
        self.expect_op("(")
        self.expect_op(")")
      stmts = self.parse_stmt_block({"procedure", "EOF"}, semicolons=False)
      if not stmts:
        raise JanaError(pos, "Expecting statement")
      return ProcMain([], stmts, pos)
    # No parameters in strict 1982 mode
    if self.tokens.peek().value == "(":
      raise JanaError(self.tokens.peek().pos, 'Procedure parameters not supported in strict janus1982 mode\n    Use --std=janus1982ext for parameterized procedures')
    body = self.parse_stmt_block({"procedure", "EOF"}, semicolons=False)
    if not body:
      raise JanaError(ident.pos, "Expecting statement")
    return Proc(ident, [], body)

  def parse_read_stmt(self) -> PrintsStmt:
    pos = self.expect_kw("read").pos
    lval = self.parse_lval()
    return PrintsStmt(Prints("read", args=[lval]), pos)

  def parse_write_stmt(self) -> PrintsStmt:
    pos = self.expect_kw("write").pos
    lval = self.parse_lval()
    return PrintsStmt(Prints("write", args=[lval]), pos)

  def _parse_typeless_vdecl(self) -> Vdecl:
    pos = self.tokens.peek().pos
    ident = self.parse_ident()
    dimensions = self._parse_decl_dimensions()
    return Vdecl(DeclType.VARIABLE, Type("int", pos, IntType.UNBOUND), ident, dimensions, None, pos)

  def parse_stmt_block(self, end_keywords: set[str], semicolons: bool = False) -> list:
    stmts = []
    while True:
      token = self.tokens.peek()
      if token.kind == "EOF":
        break
      if token.kind == "KW" and token.value in end_keywords:
        break
      if token.kind == "OP" and token.value == "}":
        break

      stmt = self.parse_statement(end_keywords)
      stmts.append(stmt)

      if not semicolons:
        self.tokens.match("OP", ";")

    return stmts

  def parse_statement(self, end_keywords: set[str] = set()):
    token = self.tokens.peek()
    if token.kind == "KW":
      dispatch = {
        "if": self.parse_if_stmt,
        "from": self.parse_from_stmt,
        "call": self.parse_call_stmt,
        "uncall": self.parse_uncall_stmt,
        "skip": self.parse_skip_stmt,
        "read": self.parse_read_stmt,
        "write": self.parse_write_stmt,
      }
      if token.value in dispatch:
        return dispatch[token.value]()
      # Reject extended features with helpful error
      _EXTENDED_KEYWORDS = {
        "local", "delocal", "ancilla", "constant", "switch", "for",
        "iterate", "push", "pop", "print", "printf", "scanf", "show",
        "assert", "error",
      }
      if token.value in _EXTENDED_KEYWORDS:
        raise JanaError(token.pos, f'"{token.value}" is not available in strict janus1982 mode\n    Use --std=janus1982ext for extended features')

    res = self.parse_assign_or_swap()
    return res

  def parse_assign_or_swap(self):
    try:
      left = self.parse_lval()
    except JanaError as err:
      token = self.tokens.peek()
      if token.kind == "OP" and token.value == "]":
        raise JanaError(token.pos, 'Unexpected "]"\n    Expecting statement')
      if err.message.endswith("Expecting expression"):
        raise JanaError(token.pos, f'Unexpected "{token.value}"\n    Expecting statement')
      raise err
    pos = self.tokens.peek().pos
    if op := self.tokens.match("OP", "<=>"):
      right = self.parse_lval()
      return SwapStmt(left, right, op.pos)
    # 1982 Janus: colon is the swap operator
    if op := self.tokens.match("OP", ":"):
      right = self.parse_lval()
      return SwapStmt(left, right, op.pos)
    for value, modop in [("+=", ModOp.ADD_EQ), ("-=", ModOp.SUB_EQ), ("^=", ModOp.XOR_EQ), ("!=", ModOp.XOR_EQ), ("=", ModOp.ADD_EQ)]:
      if self.tokens.match("OP", value):
        expr = self.parse_expression()
        return AssignStmt(modop, left, expr, pos)
    raise JanaError(self.tokens.peek().pos, "Expecting statement")

  def parse_if_stmt(self) -> IfStmt:
    pos = self.expect_kw("if").pos
    entry = self.parse_expression()
    self.tokens.match("KW", "then")
    if_part = self.parse_stmt_block({"else", "fi"}, semicolons=False)
    else_part: list = []
    if self.tokens.match("KW", "else"):
      else_part = self.parse_stmt_block({"fi"}, semicolons=False)
    if self.tokens.match("KW", "fi"):
      if self._looks_like_expr():
        exit_cond = self.parse_expression()
      else:
        exit_cond = entry
    else:
      exit_cond = entry
    return IfStmt(entry, if_part, else_part, exit_cond, pos)

  def _looks_like_expr(self) -> bool:
    token = self.tokens.peek()
    if token.kind == "KW" and token.value in {
      "if", "from", "call", "uncall",
      "procedure", "skip",
    }:
      return False
    if token.kind == "EOF" or (token.kind == "OP" and token.value in {"}", ";"}):
      return False
    return True

  def parse_from_stmt(self) -> FromStmt:
    pos = self.expect_kw("from").pos
    entry = self.parse_expression()
    do_part: list = []
    loop_part: list = []
    if self.tokens.match("KW", "do"):
      do_part = self.parse_stmt_block({"loop", "until"}, semicolons=False)
    if self.tokens.match("KW", "loop"):
      loop_part = self.parse_stmt_block({"until"}, semicolons=False)
    self.expect_kw("until")
    exit_cond = self.parse_expression()
    return FromStmt(entry, do_part, loop_part, exit_cond, pos)

  def parse_call_stmt(self) -> CallStmt:
    pos = self.expect_kw("call").pos
    ident = self.parse_ident(allow_main=True)
    # No arguments in strict 1982 mode
    if self.tokens.peek().kind == "OP" and self.tokens.peek().value == "(":
      raise JanaError(self.tokens.peek().pos, 'Call arguments not supported in strict janus1982 mode\n    Use --std=janus1982ext for parameterized calls')
    return CallStmt(ident, [], False, pos)

  def parse_uncall_stmt(self) -> UncallStmt:
    pos = self.expect_kw("uncall").pos
    ident = self.parse_ident(allow_main=True)
    # No arguments in strict 1982 mode
    if self.tokens.peek().kind == "OP" and self.tokens.peek().value == "(":
      raise JanaError(self.tokens.peek().pos, 'Uncall arguments not supported in strict janus1982 mode\n    Use --std=janus1982ext for parameterized calls')
    return UncallStmt(ident, [], False, pos)

  def parse_skip_stmt(self) -> SkipStmt:
    pos = self.expect_kw("skip").pos
    return SkipStmt(pos)

  def parse_expression(self) -> Expr:
    return self.parse_binary_level(0)

  def parse_binary_level(self, level: int) -> Expr:
    if level == len(BIN_PRECEDENCE):
      return self.parse_prefix_expr()
    left = self.parse_binary_level(level + 1)
    while True:
      token = self.tokens.peek()
      ops = BIN_PRECEDENCE[level]["ops"]
      if token.kind == "OP" and token.value in ops:
        self.tokens.consume()
        right = self.parse_binary_level(level + 1)
        left = BinExpr(ops[token.value], left, right, token.pos)
      else:
        return left

  def parse_prefix_expr(self) -> Expr:
    token = self.tokens.peek()
    if token.kind == "OP" and token.value in {"!", "~", "-"}:
      self.tokens.consume()
      expr = self.parse_prefix_expr()
      if token.value == "-":
        return BinExpr(BinOpKind.SUB, Number(0, token.pos), expr, token.pos)
      op = UnaryOpKind.NOT if token.value == "!" else UnaryOpKind.BW_NEG
      return UnaryExpr(op, expr, token.pos)
    return self.parse_term()

  def parse_term(self) -> Expr:
    token = self.tokens.peek()
    if token.kind == "OP" and token.value == "(":
      self.expect_op("(")
      expr = self.parse_expression()
      self.expect_op(")")
      return expr
    if token.kind == "NUMBER":
      self.tokens.consume()
      if token.value.startswith("0b"):
        return Number(int(token.value[2:], 2), token.pos)
      return Number(int(token.value), token.pos)
    if token.kind in {"IDENT", "KW"}:
      lval = self.parse_lval()
      return LvalExpr(lval, lval.ident.pos)
    raise JanaError(token.pos, f'Unexpected "{token.value}"\n    Expecting expression')

  def parse_lval(self) -> Lval:
    ident = self.parse_ident()
    selectors = []
    while True:
      if self.tokens.match("OP", "["):
        selectors.append(LvalIndex(self.parse_expression()))
        self.expect_op("]")
        continue
      break
    return Lval(ident, selectors)

  def _parse_decl_dimensions(self) -> list[Expr | None]:
    dimensions: list[Expr | None] = []
    while self.tokens.match("OP", "["):
      if self.tokens.match("OP", "]"):
        dimensions.append(None)
      else:
        dimensions.append(self.parse_expression())
        self.expect_op("]")
    return dimensions

  def parse_ident(self, allow_main: bool = False) -> Ident:
    token = self.tokens.peek()
    if token.kind == "IDENT":
      self.tokens.consume()
      return Ident(token.value, token.pos)
    if allow_main and token.kind == "KW" and token.value == "main":
      self.tokens.consume()
      return Ident(token.value, token.pos)
    raise JanaError(token.pos, "Expecting identifier")

  def expect_kw(self, value: str) -> Token:
    return self.tokens.expect("KW", value)

  def expect_op(self, value: str) -> Token:
    return self.tokens.expect("OP", value)


def parse_program(filename: str, text: str, line_origins: Sequence[LineOrigin] | None = None) -> Program:
  return Parser(filename, text, line_origins).parse_program()
