from __future__ import annotations

from dataclasses import dataclass
import json
import re
from enum import Enum
from typing import Sequence

from .ast import ArrayExpr
from .ast import AssertStmt
from .ast import AssignStmt
from .ast import BinExpr
from .ast import BinOpKind
from .ast import Boolean
from .ast import CallStmt
from .ast import DeclType
from .ast import EmptyExpr
from .ast import Expr
from .ast import FromStmt
from .ast import Ident
from .ast import IfStmt
from .ast import IntType
from .ast import IterateStmt
from .ast import LocalDecl
from .ast import LocalStmt
from .ast import Lval
from .ast import LvalField
from .ast import LvalIndex
from .ast import LvalExpr
from .ast import ModOp
from .ast import NilExpr
from .ast import Number
from .ast import PopStmt
from .ast import Prints
from .ast import PrintsStmt
from .ast import Proc
from .ast import ProcMain
from .ast import Program
from .ast import PushStmt
from .ast import SizeExpr
from .ast import SkipStmt
from .ast import SourcePos
from .ast import StringLiteral
from .ast import StructDef
from .ast import StructField
from .ast import SwapStmt
from .ast import TernaryExpr
from .ast import TopExpr
from .ast import Type
from .ast import TypeCastExpr
from .ast import UnaryExpr
from .ast import UnaryOpKind
from .ast import UncallStmt
from .ast import UserErrorStmt
from .ast import Vdecl
from .errors import JanaError
from .preprocess import LineOrigin


KEYWORDS = {
  "procedure", "main", "int", "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64",
  "char", "string", "struct",
  "ancilla", "constant", "bool", "true", "false", "if", "then", "else", "fi",
  "from", "do", "loop", "until", "push", "pop", "local", "delocal", "call", "uncall",
  "external", "error", "skip", "stack", "empty", "top", "size", "show", "print",
  "printf", "nil", "assert", "iterate", "by", "to", "end",
}

TOKEN_RE = re.compile(
  r"""
  (?P<SPACE>\s+)
  |(?P<COMMENT>//[^\n]*)
  |(?P<MCOMMENT>/\*.*?\*/)
  |(?P<STRING>"(?:\\.|[^"\\])*")
  |(?P<NUMBER>0b[01]+|\d+)
  |(?P<OP><=>|\+=|-=|\^=|<<|>>|<=|>=|!=|&&|\|\||\*\*|=|<|>|\+|-|\*|/|%|\^|&|\||!|,|\.|\?|:|\(|\)|\[|\]|\{|\})
  |(?P<IDENT>[A-Za-z][A-Za-z0-9_']*)
  |(?P<MISMATCH>.)
  """,
  re.DOTALL | re.VERBOSE,
)

BIN_PRECEDENCE = [
  {"ops": {"||": BinOpKind.LOR}, "assoc": "left"},
  {"ops": {"&&": BinOpKind.LAND}, "assoc": "left"},
  {"ops": {"&": BinOpKind.AND, "|": BinOpKind.OR, "^": BinOpKind.XOR}, "assoc": "left"},
  {"ops": {"<=": BinOpKind.LE, "<": BinOpKind.LT, ">=": BinOpKind.GE, ">": BinOpKind.GT, "=": BinOpKind.EQ, "!=": BinOpKind.NEQ}, "assoc": "left"},
  {"ops": {"<<": BinOpKind.SL, ">>": BinOpKind.SR}, "assoc": "left"},
  {"ops": {"+": BinOpKind.ADD, "-": BinOpKind.SUB}, "assoc": "left"},
  {"ops": {"*": BinOpKind.MUL, "/": BinOpKind.DIV, "%": BinOpKind.MOD}, "assoc": "left"},
  {"ops": {"**": BinOpKind.EXP}, "assoc": "left"},
]

TYPE_KEYWORDS = {
  "int": IntType.UNBOUND,
  "i8": IntType.I8,
  "i16": IntType.I16,
  "i32": IntType.I32,
  "i64": IntType.I64,
  "u8": IntType.U8,
  "u16": IntType.U16,
  "u32": IntType.U32,
  "u64": IntType.U64,
}


@dataclass(frozen=True)
class Token:
  kind: str
  value: str
  pos: SourcePos


class TokenStream:
  def __init__(self, tokens: list[Token]):
    self.tokens = tokens
    self.index = 0

  def peek(self) -> Token:
    return self.tokens[self.index]

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
    if kind == "IDENT" and value in KEYWORDS:
      tokens.append(Token("KW", value, pos))
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
    # eof_line may be past the last mapped line; preserve the overshoot
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
    self.struct_names: set[str] = set()

  def parse_program(self) -> Program:
    struct_defs: list[StructDef] = []
    mains: list[ProcMain] = []
    procs: list[Proc] = []
    while self.tokens.peek().kind != "EOF":
      if self.tokens.peek().kind == "KW" and self.tokens.peek().value == "struct":
        struct_def = self.parse_struct_def()
        struct_defs.append(struct_def)
        self.struct_names.add(struct_def.ident.name)
        continue
      proc_or_main = self.parse_procedure()
      if isinstance(proc_or_main, ProcMain):
        mains.append(proc_or_main)
      else:
        procs.append(proc_or_main)
    if len(mains) > 1:
      raise JanaError(self.tokens.peek().pos, 'Unexpected end of input\n    Expecting "procedure" or end of input\n    Multiple main procedures has been defined')
    return Program(mains[0] if mains else None, procs, struct_defs)

  def parse_struct_def(self) -> StructDef:
    pos = self.expect_kw("struct").pos
    ident = self.parse_ident(allow_field_keywords=True)
    self.expect_op("{")
    fields = [self.parse_struct_field()]
    while self.tokens.match("OP", ","):
      fields.append(self.parse_struct_field())
    self.expect_op("}")
    return StructDef(ident, fields, pos)

  def parse_struct_field(self) -> StructField:
    pos = self.tokens.peek().pos
    typ = self.parse_type()
    dimensions = self._parse_decl_dimensions()
    ident = self.parse_ident(allow_field_keywords=True)
    dimensions = self._merge_decl_dimensions(dimensions, self._parse_decl_dimensions())
    return StructField(typ, ident, pos, dimensions)

  def parse_procedure(self) -> ProcMain | Proc:
    self.expect_kw("procedure")
    ident = self.parse_ident(allow_main=True)
    if ident.name == "main":
      pos = ident.pos
      self.expect_op("(")
      self.expect_op(")")
      vdecls: list[Vdecl] = []
      while self._starts_vdecl():
        vdecls.append(self.parse_main_vdecl())
      stmts = self.parse_stmt_block({"procedure", "EOF"})
      if not stmts:
        raise JanaError(pos, "Expecting statement")
      return ProcMain(vdecls, stmts, pos)
    params = self.parse_params()
    body = self.parse_stmt_block({"procedure", "EOF"})
    if not body:
      raise JanaError(ident.pos, "Expecting statement")
    return Proc(ident, params, body)

  def parse_params(self) -> list[Vdecl]:
    self.expect_op("(")
    params: list[Vdecl] = []
    if not self.tokens.match("OP", ")"):
      params.append(self.parse_vdecl(False))
      while self.tokens.match("OP", ","):
        params.append(self.parse_vdecl(False))
      self.expect_op(")")
    return params

  def parse_main_vdecl(self) -> Vdecl:
    return self.parse_vdecl(True)

  def parse_vdecl(self, allow_init: bool) -> Vdecl:
    pos = self.tokens.peek().pos
    decl_type = self.parse_decl_type()
    typ = self.parse_type()
    dimensions = self._parse_decl_dimensions()
    ident = self.parse_ident()
    dimensions = self._merge_decl_dimensions(dimensions, self._parse_decl_dimensions())
    init_expr = None
    if allow_init and self.tokens.match("OP", "="):
      init_expr = self.parse_array_or_expr()
    return Vdecl(decl_type, typ, ident, dimensions, init_expr, pos)

  def parse_decl_type(self) -> DeclType:
    if self.tokens.match("KW", "ancilla"):
      return DeclType.ANCILLA
    if self.tokens.match("KW", "constant"):
      return DeclType.CONSTANT
    return DeclType.VARIABLE

  def parse_type(self) -> Type:
    token = self.tokens.peek()
    if token.kind == "IDENT":
      self.tokens.consume()
      return Type("struct", token.pos, name=token.value)
    if token.kind != "KW":
      raise JanaError(token.pos, "Expecting type")
    if token.value in TYPE_KEYWORDS:
      self.tokens.consume()
      return Type("int", token.pos, TYPE_KEYWORDS[token.value])
    if token.value in {"char", "string"}:
      self.tokens.consume()
      return Type("int", token.pos, IntType.U8, is_char=True)
    if token.value == "stack":
      self.tokens.consume()
      return Type("stack", token.pos)
    if token.value == "bool":
      self.tokens.consume()
      return Type("bool", token.pos)
    raise JanaError(token.pos, "Expecting type")

  def parse_stmt_block(self, end_keywords: set[str]) -> list:
    stmts = []
    while True:
      token = self.tokens.peek()
      if token.kind == "EOF":
        break
      if token.kind == "KW" and token.value in end_keywords:
        break
      stmts.append(self.parse_statement())
    return stmts

  def parse_statement(self):
    token = self.tokens.peek()
    if token.kind not in {"KW", "IDENT"}:
      raise JanaError(
        token.pos,
        f'Unexpected "{token.value}"\n    Expecting "ancilla", "constant", "int", "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "stack" or statement',
      )
    if token.kind == "KW":
      dispatch = {
        "ancilla": self.parse_ancilla_stmt,
        "constant": self.parse_constant_stmt,
        "if": self.parse_if_stmt,
        "from": self.parse_from_stmt,
        "iterate": self.parse_iterate_stmt,
        "push": self.parse_push_stmt,
        "pop": self.parse_pop_stmt,
        "local": self.parse_local_stmt,
        "call": self.parse_call_stmt,
        "uncall": self.parse_uncall_stmt,
        "error": self.parse_error_stmt,
        "print": self.parse_print_stmt,
        "printf": self.parse_printf_stmt,
        "show": self.parse_show_stmt,
        "skip": self.parse_skip_stmt,
        "assert": self.parse_assert_stmt,
      }
      if token.value in dispatch:
        return dispatch[token.value]()
    return self.parse_assign_or_swap()

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
    for value, modop in [("+=", ModOp.ADD_EQ), ("-=", ModOp.SUB_EQ), ("^=", ModOp.XOR_EQ)]:
      if self.tokens.match("OP", value):
        expr = self.parse_expression()
        return AssignStmt(modop, left, expr, pos)
    raise JanaError(self.tokens.peek().pos, "Expecting statement")

  def parse_if_stmt(self) -> IfStmt:
    pos = self.expect_kw("if").pos
    entry = self.parse_expression()
    self.expect_kw("then")
    if_part = self.parse_stmt_block({"else", "fi"})
    else_part: list = []
    if self.tokens.match("KW", "else"):
      else_part = self.parse_stmt_block({"fi"})
    self.expect_kw("fi")
    exit_cond = self.parse_expression()
    return IfStmt(entry, if_part, else_part, exit_cond, pos)

  def parse_from_stmt(self) -> FromStmt:
    pos = self.expect_kw("from").pos
    entry = self.parse_expression()
    do_part: list = []
    loop_part: list = []
    if self.tokens.match("KW", "do"):
      do_part = self.parse_stmt_block({"loop", "until"})
    if self.tokens.match("KW", "loop"):
      loop_part = self.parse_stmt_block({"until"})
    self.expect_kw("until")
    exit_cond = self.parse_expression()
    return FromStmt(entry, do_part, loop_part, exit_cond, pos)

  def parse_iterate_stmt(self) -> IterateStmt:
    pos = self.expect_kw("iterate").pos
    typ = self.parse_type()
    ident = self.parse_ident()
    self.expect_op("=")
    start = self.parse_expression()
    step = Number(1, pos)
    if self.tokens.match("KW", "by"):
      step = self.parse_expression()
    self.expect_kw("to")
    end = self.parse_expression()
    body = self.parse_stmt_block({"end"})
    self.expect_kw("end")
    return IterateStmt(typ, ident, start, step, end, body, pos)

  def parse_push_stmt(self) -> PushStmt:
    pos = self.expect_kw("push").pos
    self.expect_op("(")
    expr = self.parse_expression()
    self.expect_op(",")
    ident = self.parse_ident()
    self.expect_op(")")
    return PushStmt(expr, ident, pos)

  def parse_pop_stmt(self) -> PopStmt:
    pos = self.expect_kw("pop").pos
    self.expect_op("(")
    expr = self.parse_expression()
    self.expect_op(",")
    ident = self.parse_ident()
    self.expect_op(")")
    return PopStmt(expr, ident, pos)

  def parse_ancilla_stmt(self) -> LocalStmt:
    return self._parse_single_decl_local("ancilla", DeclType.ANCILLA)

  def parse_constant_stmt(self) -> LocalStmt:
    return self._parse_single_decl_local("constant", DeclType.CONSTANT)

  def _parse_single_decl_local(self, keyword: str, decl_type: DeclType) -> LocalStmt:
    pos = self.expect_kw(keyword).pos
    decl = self.parse_local_decl_with_known_type(decl_type, pos)
    body = self.parse_stmt_block({"procedure", "EOF", "else", "fi", "loop", "until", "delocal", "end"})
    return LocalStmt(decl, body, decl, pos)

  def parse_local_stmt(self) -> LocalStmt:
    pos = self.expect_kw("local").pos
    enters = [self.parse_local_decl()]
    while self.tokens.match("OP", ","):
      enters.append(self.parse_local_decl())
    body = self.parse_stmt_block({"delocal"})
    self.expect_kw("delocal")
    exits = [self.parse_local_decl()]
    while len(exits) < len(enters):
      self.expect_op(",")
      exits.append(self.parse_local_decl())
    stmt = body
    for enter_decl, exit_decl in reversed(list(zip(enters, exits))):
      stmt = [LocalStmt(enter_decl, stmt, exit_decl, pos)]
    return stmt[0]

  def parse_local_decl(self) -> LocalDecl:
    pos = self.tokens.peek().pos
    return self.parse_local_decl_with_known_type(DeclType.VARIABLE, pos)

  def parse_local_decl_with_known_type(self, decl_type: DeclType, pos: SourcePos) -> LocalDecl:
    typ = self.parse_type()
    dimensions = self._parse_decl_dimensions()
    ident = self.parse_ident()
    dimensions = self._merge_decl_dimensions(dimensions, self._parse_decl_dimensions())
    init_expr = None
    if self.tokens.match("OP", "="):
      init_expr = self.parse_array_or_expr()
    return LocalDecl(decl_type, typ, ident, dimensions, init_expr, pos)

  def parse_call_stmt(self) -> CallStmt:
    pos = self.expect_kw("call").pos
    external = self.tokens.match("KW", "external") is not None
    ident = self.parse_ident(allow_main=True)
    args = self.parse_arg_list()
    return CallStmt(ident, args, external, pos)

  def parse_uncall_stmt(self) -> UncallStmt:
    pos = self.expect_kw("uncall").pos
    external = self.tokens.match("KW", "external") is not None
    ident = self.parse_ident(allow_main=True)
    args = self.parse_arg_list()
    return UncallStmt(ident, args, external, pos)

  def parse_arg_list(self) -> list[Expr]:
    self.expect_op("(")
    args: list[Expr] = []
    if not self.tokens.match("OP", ")"):
      args.append(self.parse_expression())
      while self.tokens.match("OP", ","):
        args.append(self.parse_expression())
      self.expect_op(")")
    return args

  def parse_error_stmt(self) -> UserErrorStmt:
    pos = self.expect_kw("error").pos
    self.expect_op("(")
    message = self.parse_string()
    self.expect_op(")")
    return UserErrorStmt(message, pos)

  def parse_print_stmt(self) -> PrintsStmt:
    pos = self.expect_kw("print").pos
    self.expect_op("(")
    text = self.parse_string()
    self.expect_op(")")
    return PrintsStmt(Prints("print", text=text), pos)

  def parse_printf_stmt(self) -> PrintsStmt:
    pos = self.expect_kw("printf").pos
    self.expect_op("(")
    text = self.parse_string()
    args: list[Ident | Lval] = []
    if self.tokens.match("OP", ","):
      args.append(self._parse_printf_arg())
      while self.tokens.match("OP", ","):
        args.append(self._parse_printf_arg())
    self.expect_op(")")
    return PrintsStmt(Prints("printf", text=text, args=args), pos)

  def parse_show_stmt(self) -> PrintsStmt:
    pos = self.expect_kw("show").pos
    self.expect_op("(")
    args: list[Ident | Lval] = [self._parse_printf_arg()]
    while self.tokens.match("OP", ","):
      args.append(self._parse_printf_arg())
    self.expect_op(")")
    return PrintsStmt(Prints("show", args=args), pos)

  def _parse_printf_arg(self) -> Ident | Lval:
    """Parse a printf/show argument: simple ident or lvalue (arr[i], p.x)."""
    lval = self.parse_lval()
    if not lval.selectors:
      return lval.ident
    return lval

  def parse_skip_stmt(self) -> SkipStmt:
    pos = self.expect_kw("skip").pos
    return SkipStmt(pos)

  def parse_assert_stmt(self) -> AssertStmt:
    pos = self.expect_kw("assert").pos
    expr = self.parse_expression()
    return AssertStmt(expr, pos)

  def parse_expression(self) -> Expr:
    expr = self.parse_binary_level(0)
    if self.tokens.match("OP", "?"):
      then_expr = self.parse_expression()
      self.expect_op(":")
      else_expr = self.parse_expression()
      return TernaryExpr(expr, then_expr, else_expr, expr.pos)
    return expr

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
    if token.kind == "OP" and token.value == "(" and self._looks_like_type_cast():
      self.expect_op("(")
      typ = self.parse_type()
      self.expect_op(")")
      expr = self.parse_prefix_expr()
      return TypeCastExpr(typ, expr, token.pos)
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
    if token.kind == "KW" and token.value in {"true", "false"}:
      self.tokens.consume()
      return Boolean(token.value == "true", token.pos)
    if token.kind == "KW" and token.value == "empty":
      self.tokens.consume()
      self.expect_op("(")
      ident = self.parse_ident()
      self.expect_op(")")
      return EmptyExpr(ident, token.pos)
    if token.kind == "KW" and token.value == "top":
      self.tokens.consume()
      self.expect_op("(")
      ident = self.parse_ident()
      self.expect_op(")")
      return TopExpr(ident, token.pos)
    if token.kind == "KW" and token.value == "size":
      self.tokens.consume()
      self.expect_op("(")
      ident = self.parse_ident()
      self.expect_op(")")
      return SizeExpr(ident, token.pos)
    if token.kind == "KW" and token.value == "nil":
      self.tokens.consume()
      return NilExpr(token.pos)
    if token.kind == "OP" and token.value == "{":
      return self.parse_array_expr()
    if token.kind in {"IDENT", "KW"}:
      lval = self.parse_lval()
      return LvalExpr(lval, lval.ident.pos)
    raise JanaError(token.pos, f'Unexpected "{token.value}"\n    Expecting expression')

  def parse_array_expr(self) -> Expr:
    pos = self.expect_op("{").pos
    items = [self.parse_array_or_expr()]
    while self.tokens.match("OP", ","):
      items.append(self.parse_array_or_expr())
    self.expect_op("}")
    return ArrayExpr(items, pos)

  def parse_array_or_expr(self) -> Expr:
    if self.tokens.peek().kind == "OP" and self.tokens.peek().value == "{":
      return self.parse_array_expr()
    if self.tokens.peek().kind == "STRING":
      token = self.tokens.consume()
      return StringLiteral(json.loads(token.value), token.pos)
    return self.parse_expression()

  def parse_lval(self) -> Lval:
    ident = self.parse_ident()
    selectors = []
    while True:
      if self.tokens.match("OP", "."):
        selectors.append(LvalField(self.parse_ident(allow_field_keywords=True)))
        continue
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

  def _merge_decl_dimensions(self, prefix: list[Expr | None], suffix: list[Expr | None]) -> list[Expr | None]:
    merged = list(prefix)
    remaining = list(suffix)
    for index, dim in enumerate(merged):
      if dim is None and remaining:
        merged[index] = remaining.pop(0)
    merged.extend(remaining)
    return merged

  def parse_ident(self, allow_main: bool = False, allow_field_keywords: bool = False) -> Ident:
    token = self.tokens.peek()
    if token.kind == "IDENT":
      self.tokens.consume()
      return Ident(token.value, token.pos)
    if allow_main and token.kind == "KW" and token.value == "main":
      self.tokens.consume()
      return Ident(token.value, token.pos)
    if allow_field_keywords and token.kind == "KW" and token.value in {"size"}:
      self.tokens.consume()
      return Ident(token.value, token.pos)
    raise JanaError(token.pos, "Expecting identifier")

  def parse_string(self) -> str:
    token = self.tokens.expect("STRING")
    return json.loads(token.value)

  def expect_kw(self, value: str) -> Token:
    return self.tokens.expect("KW", value)

  def expect_op(self, value: str) -> Token:
    return self.tokens.expect("OP", value)

  def _starts_vdecl(self) -> bool:
    idx = self.tokens.index
    if self.tokens.tokens[idx].kind == "KW" and self.tokens.tokens[idx].value in {"ancilla", "constant"}:
      idx += 1
    token = self.tokens.tokens[idx]
    if token.kind == "IDENT":
      next_idx = idx + 1
      # Skip bracket pairs for struct array dimensions: Pair[3] ps, Pair[2][2] ps
      while (next_idx < len(self.tokens.tokens)
             and self.tokens.tokens[next_idx].kind == "OP"
             and self.tokens.tokens[next_idx].value == "["):
        depth = 1
        next_idx += 1
        while next_idx < len(self.tokens.tokens) and depth > 0:
          v = self.tokens.tokens[next_idx].value
          if v == "[": depth += 1
          elif v == "]": depth -= 1
          next_idx += 1
      return (next_idx < len(self.tokens.tokens)
              and self.tokens.tokens[next_idx].kind == "IDENT")
    return token.kind == "KW" and token.value in set(TYPE_KEYWORDS) | {"stack", "bool", "char", "string"}

  def _looks_like_type_cast(self) -> bool:
    idx = self.tokens.index + 1
    token = self.tokens.tokens[idx]
    return token.kind == "KW" and token.value in set(TYPE_KEYWORDS) | {"stack", "bool", "char", "string"}


def parse_program(filename: str, text: str, line_origins: Sequence[LineOrigin] | None = None) -> Program:
  return Parser(filename, text, line_origins).parse_program()
