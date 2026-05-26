from __future__ import annotations

from dataclasses import dataclass
import json
import re
from enum import Enum
from typing import Sequence

from .ast import ArrayExpr
from .ast import AssertStmt
from .ast import AssignStmt
from .ast import BareDelocalStmt
from .ast import BareLocalStmt
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
from .ast import AncillaBlockStmt
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
from .ast import SwitchCase
from .ast import SwitchStmt
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
  "procedure", "main", "int", "if", "then", "else", "fi",
  "from", "do", "loop", "until", "call", "uncall",
  "skip", "read", "write", "show", "printf",
}

TOKEN_RE = re.compile(
  r"""
  (?P<SPACE>\s+)
  |(?P<COMMENT>//[^\n]*|;[^\n]*)
  |(?P<MCOMMENT>/\*.*?\*/)
  |(?P<STRING>"(?:\\.|[^"\\])*")
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
    global_vdecls: list[Vdecl] = []
    while self.tokens.peek().kind != "EOF":
      if self.tokens.peek().kind == "KW" and self.tokens.peek().value == "struct":
        struct_def = self.parse_struct_def()
        struct_defs.append(struct_def)
        self.struct_names.add(struct_def.ident.name)
        continue
      
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
      raise JanaError(self.tokens.peek().pos, 'Unexpected end of input\n    Expecting "void", "procedure" or end of input\n    Multiple main procedures has been defined')
    return Program(mains[0] if mains else None, procs, struct_defs)

  def parse_struct_def(self) -> StructDef:
    pos = self.expect_kw("struct").pos
    ident = self.parse_ident(allow_field_keywords=True)
    self.expect_op("{")
    fields = []
    while not (self.tokens.peek().kind == "OP" and self.tokens.peek().value == "}"):
      fields.append(self.parse_struct_field())
      if self.tokens.match("OP", ","):
        continue
      self.tokens.match("OP", ";")
    self.expect_op("}")
    self.tokens.match("OP", ";")
    return StructDef(ident, fields, pos)

  def parse_struct_field(self) -> StructField:
    pos = self.tokens.peek().pos
    typ = self.parse_type()
    dimensions = self._parse_decl_dimensions()
    ident = self.parse_ident(allow_field_keywords=True)
    dimensions = self._merge_decl_dimensions(dimensions, self._parse_decl_dimensions())
    return StructField(typ, ident, pos, dimensions)

  def parse_procedure(self) -> ProcMain | Proc:
    start = self.tokens.peek()
    if start.kind != "KW" or start.value not in {"void", "procedure"}:
      raise JanaError(start.pos, f'Unexpected "{start.value}"\n    Expecting "void" or "procedure"')
    self.tokens.consume()
    c_style = start.value == "void"
    ident = self.parse_ident(allow_main=True)
    if ident.name == "main":
      pos = ident.pos
      if self.tokens.peek().value == "(":
        self.expect_op("(")
        self.expect_op(")")
      vdecls: list[Vdecl] = []
      if c_style:
        self.expect_op("{")
        while self._starts_vdecl():
          vdecls.extend(self.parse_main_vdecls())
          self.expect_op(";")
        stmts = self.parse_stmt_block({"void", "procedure", "EOF"}, require_braces=False, semicolons=True)
        self.expect_op("}")
      else:
        while self._starts_vdecl():
          vdecls.extend(self.parse_main_vdecls())
        stmts = self.parse_stmt_block({"void", "procedure", "EOF"}, semicolons=False)
      if not stmts:
        raise JanaError(pos, "Expecting statement")
      return ProcMain(vdecls, stmts, pos)
    params = self.parse_params()
    if c_style:
      body = self.parse_stmt_block({"void", "procedure", "EOF"}, require_braces=True, semicolons=True)
    else:
      body = self.parse_stmt_block({"void", "procedure", "EOF"}, semicolons=False)
    if not body:
      raise JanaError(ident.pos, "Expecting statement")
    return Proc(ident, params, body)

  def parse_params(self) -> list[Vdecl]:
    if self.tokens.peek().value != "(":
      return []
    self.expect_op("(")
    params: list[Vdecl] = []
    if not self.tokens.match("OP", ")"):
      if not self._looks_like_type():
        params.append(self._parse_typeless_vdecl())
        while self.tokens.match("OP", ","):
          params.append(self._parse_typeless_vdecl())
      else:
        params.extend(self.parse_vdecls(False))
        while self.tokens.match("OP", ","):
          params.extend(self.parse_vdecls(False))
      self.expect_op(")")
    return params

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

  def parse_main_vdecls(self) -> list[Vdecl]:
    return self.parse_vdecls(True)

  def parse_vdecl(self, allow_init: bool) -> Vdecl:
    return self.parse_vdecls(allow_init)[0]

  def parse_vdecls(self, allow_init: bool) -> list[Vdecl]:
    pos = self.tokens.peek().pos
    decl_type = self.parse_decl_type()
    typ = self.parse_type()
    shared_dimensions = self._parse_decl_dimensions()
    vdecls = [self._parse_vdecl_tail(pos, decl_type, typ, shared_dimensions, allow_init)]
    while self.tokens.peek().kind == "OP" and self.tokens.peek().value == ",":
      if not self._starts_shared_vdecl_tail():
        break
      self.expect_op(",")
      vdecls.append(self._parse_vdecl_tail(pos, decl_type, typ, shared_dimensions, allow_init))
    return vdecls

  def _parse_vdecl_tail(
    self,
    pos: SourcePos,
    decl_type: DeclType,
    typ: Type,
    shared_dimensions: list[Expr | None],
    allow_init: bool,
  ) -> Vdecl:
    ident = self.parse_ident()
    dimensions = self._merge_decl_dimensions(shared_dimensions, self._parse_decl_dimensions())
    init_expr = None
    if allow_init and self.tokens.match("OP", "="):
      init_expr = self.parse_array_or_expr()
    return Vdecl(decl_type, typ, ident, dimensions, init_expr, pos)

  def _starts_shared_vdecl_tail(self) -> bool:
    return self.tokens.peek(1).kind == "IDENT"

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

  def parse_stmt_block(self, end_keywords: set[str], require_braces: bool = False, semicolons: bool | None = None) -> list:
    if semicolons is None:
      semicolons = require_braces
    if require_braces:
      self.expect_op("{")
    
    stmts = []
    while True:
      token = self.tokens.peek()
      if token.kind == "EOF":
        break
      if not require_braces and token.kind == "KW" and token.value in end_keywords:
        break
      if token.kind == "OP" and token.value == "}":
        break
      
      stmt = self.parse_statement(end_keywords)
      stmts.append(stmt)

      if semicolons and self._stmt_requires_semicolon(stmt):
        self.expect_op(";")
      elif not semicolons:
        self.tokens.match("OP", ";")
        
    if require_braces:
      self.expect_op("}")
    return stmts

  def parse_statement(self, end_keywords: set[str] = set()):
    token = self.tokens.peek()
    if token.kind == "KW":
      dispatch = {
        "ancilla": self.parse_ancilla_stmt,
        "constant": self.parse_constant_stmt,
        "if": self.parse_if_stmt,
        "switch": self.parse_switch_stmt,
        "from": self.parse_from_stmt,
        "iterate": self.parse_iterate_stmt,
        "for": self.parse_for_stmt,
        "push": self.parse_push_stmt,
        "pop": self.parse_pop_stmt,
        "local": self.parse_local_stmt,
        "delocal": self.parse_bare_delocal_stmt,
        "call": self.parse_call_stmt,
        "uncall": self.parse_uncall_stmt,
        "error": self.parse_error_stmt,
        "print": self.parse_print_stmt,
        "printf": self.parse_printf_stmt,
        "scanf": self.parse_scanf_stmt,
        "show": self.parse_show_stmt,
        "skip": self.parse_skip_stmt,
        "assert": self.parse_assert_stmt,
        "read": self.parse_read_stmt,
        "write": self.parse_write_stmt,
      }
      if token.value in dispatch:
        return dispatch[token.value]()
    if token.kind == "IDENT" and self.tokens.peek(1).kind == "OP" and self.tokens.peek(1).value == "(":
      return self.parse_bare_call_stmt()
    
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
        rhs_starts_with_paren = self.tokens.peek().kind == "OP" and self.tokens.peek().value == "("
        expr = self.parse_array_or_expr()
        if isinstance(expr, TernaryExpr) and not rhs_starts_with_paren:
          raise JanaError(
            expr.pos,
            "Ternary expressions in update statements must be parenthesized",
          )
        # If it's '=', we treat it as bulk initialization (ADD_EQ to zeroed array)
        return AssignStmt(modop, left, expr, pos)
    raise JanaError(self.tokens.peek().pos, "Expecting statement")

  def parse_if_stmt(self) -> IfStmt:
    # 1982 Janus: if expr [then stmts] [else stmts] fi expr  (no braces)
    pos = self.expect_kw("if").pos
    entry = self.parse_expression()
    self.tokens.match("KW", "then")  # 'then' is optional per the grammar
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
      "if", "from", "switch", "push", "pop", "local", "delocal", "call", "uncall", 
      "procedure", "void", "skip", "error", "printf", "show", "iterate"
    }:
      return False
    if token.kind == "EOF" or (token.kind == "OP" and token.value in {"}", ";"}):
      return False
    return True

  def parse_from_stmt(self) -> FromStmt:
    # 1982 Janus: always non-C-style  (no brace-delimited blocks)
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
    body = self.parse_stmt_block({"end"}, semicolons=False)
    self.expect_kw("end")
    return IterateStmt(typ, ident, start, step, end, body, pos)

  def parse_for_stmt(self) -> IterateStmt:
    pos = self.expect_kw("for").pos
    self.expect_op("(")
    typ = self.parse_type()
    ident = self.parse_ident()
    self.expect_op("=")
    start = self.parse_expression()
    self.expect_op(";")
    cond = self.parse_expression()
    self.expect_op(";")
    lval = self.parse_lval()
    if lval.ident.name != ident.name or lval.selectors:
      raise JanaError(lval.ident.pos, f"Expected loop update for `{ident.name}`")
    if self.tokens.match("OP", "+="):
      step = self.parse_expression()
    else:
      raise JanaError(self.tokens.peek().pos, 'Unexpected token in for-update\n    Expecting "+="')
    self.expect_op(")")
    body = self.parse_stmt_block(set(), require_braces=True, semicolons=True)
    end = self._for_cond_to_end_expr(cond, ident)
    return IterateStmt(typ, ident, start, step, end, body, pos)

  def _for_cond_to_end_expr(self, cond: Expr, ident: Ident) -> Expr:
    if (
      isinstance(cond, BinExpr)
      and isinstance(cond.left, LvalExpr)
      and not cond.left.lval.selectors
      and cond.left.lval.ident.name == ident.name
      and cond.op == BinOpKind.LT
    ):
      return cond.right
    raise JanaError(
      cond.pos,
      f"Unsupported for-loop condition for `{ident.name}`\n    Expecting `{ident.name} < expr`",
    )

  def parse_switch_stmt(self) -> SwitchStmt:
    pos = self.expect_kw("switch").pos
    self.expect_op("(")
    expr = self.parse_expression()
    self.expect_op(")")
    self.expect_op("{")
    cases = []
    default_part = []
    while self.tokens.peek().kind != "EOF" and not (self.tokens.peek().kind == "OP" and self.tokens.peek().value == "}"):
      if self.tokens.match("KW", "case"):
        case_pos = self.tokens.peek().pos
        val = self.parse_expression()
        self.expect_op(":")
        body = self._parse_switch_case_body()
        cases.append(SwitchCase(val, body, case_pos))
      elif self.tokens.match("KW", "default"):
        self.expect_op(":")
        default_part = self._parse_switch_case_body()
      else:
        token = self.tokens.peek()
        raise JanaError(token.pos, f'Unexpected "{token.value}"\n    Expecting "case", "default" or "}}"')
    
    self.expect_op("}")
    if self.tokens.match("KW", "switch"):
      if self.tokens.match("OP", "("):
        exit_expr = self.parse_expression()
        self.expect_op(")")
      else:
        exit_expr = expr
    else:
      exit_expr = expr
    self.tokens.match("OP", ";")
    return SwitchStmt(expr, cases, default_part, exit_expr, pos)

  def _parse_switch_case_body(self) -> list[Stmt]:
    body: list[Stmt] = []
    while True:
      token = self.tokens.peek()
      if token.kind == "KW" and token.value == "break":
        self.tokens.consume()
        self.expect_op(";")
        return body
      if token.kind == "EOF":
        break
      if token.kind == "KW" and token.value in {"case", "default"}:
        break
      if token.kind == "OP" and token.value == "}":
        break
      stmt = self.parse_statement()
      body.append(stmt)
      if self._stmt_requires_semicolon(stmt):
        self.expect_op(";")
    raise JanaError(token.pos, 'Unexpected end of switch case\n    Expecting "break"')

  def _stmt_requires_semicolon(self, stmt) -> bool:
    return not isinstance(
      stmt,
      (IfStmt, FromStmt, IterateStmt, LocalStmt, BareLocalStmt, SwitchStmt, AncillaBlockStmt),
    )

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

  def parse_ancilla_stmt(self) -> LocalStmt | AncillaBlockStmt:
    pos = self.tokens.peek().pos
    if self.tokens.peek(1).kind == "OP" and self.tokens.peek(1).value == "(":
      self.expect_kw("ancilla")
      self.expect_op("(")
      decls = [self.parse_local_decl_with_known_type(DeclType.ANCILLA, pos)]
      while self.tokens.match("OP", ","):
        decls.append(self.parse_local_decl_with_known_type(DeclType.ANCILLA, self.tokens.peek().pos))
      self.expect_op(")")
      self.expect_op("{")
      body = self.parse_stmt_block({"}"}, semicolons=True)
      self.expect_op("}")
      self.expect_op(";")
      return AncillaBlockStmt(decls, body, pos)
    return self._parse_single_decl_local("ancilla", DeclType.ANCILLA)

  def parse_constant_stmt(self) -> LocalStmt:
    return self._parse_single_decl_local("constant", DeclType.CONSTANT)

  def _parse_single_decl_local(self, keyword: str, decl_type: DeclType) -> LocalStmt:
    pos = self.expect_kw(keyword).pos
    decl = self.parse_local_decl_with_known_type(decl_type, pos)
    body = self.parse_stmt_block(
      {"void", "procedure", "EOF", "else", "fi", "loop", "until", "delocal", "end"},
      semicolons=False,
    )
    return LocalStmt(decl, body, decl, pos)

  _OUTER_TERMINATORS = {"fi", "else", "until", "loop", "end", "void", "procedure", "EOF"}

  def parse_local_stmt(self):
    pos = self.expect_kw("local").pos
    enters = [self.parse_local_decl()]
    while self.tokens.match("OP", ","):
      enters.append(self.parse_local_decl())
    if self.tokens.peek().kind == "OP" and self.tokens.peek().value == "{":
      body = self.parse_stmt_block(set(), require_braces=True, semicolons=True)
      self.expect_kw("delocal")
      exits = [self.parse_local_decl()]
      while len(exits) < len(enters):
        self.expect_op(",")
        exits.append(self.parse_local_decl())
      self.expect_op(";")
      stmt = body
      for enter_decl, exit_decl in reversed(list(zip(enters, exits))):
        stmt = [LocalStmt(enter_decl, stmt, exit_decl, pos)]
      return stmt[0]
    body = self.parse_stmt_block({"delocal"} | self._OUTER_TERMINATORS, semicolons=False)
    tok = self.tokens.peek()
    if tok.kind == "KW" and tok.value == "delocal":
      self.expect_kw("delocal")
      exits = [self.parse_local_decl()]
      while len(exits) < len(enters):
        self.expect_op(",")
        exits.append(self.parse_local_decl())
      self.tokens.match("OP", ";")
      stmt = body
      for enter_decl, exit_decl in reversed(list(zip(enters, exits))):
        stmt = [LocalStmt(enter_decl, stmt, exit_decl, pos)]
      return stmt[0]
    else:
      if len(enters) != 1:
        raise JanaError(pos, "Multi-local not supported for crossing local/delocal")
      return BareLocalStmt(enters[0], body, pos)

  def parse_bare_delocal_stmt(self):
    pos = self.expect_kw("delocal").pos
    decl = self.parse_local_decl()
    if self.tokens.peek().kind == "OP" and self.tokens.peek().value == "{":
      body = self.parse_stmt_block(set(), require_braces=True, semicolons=True)
    else:
      body = self.parse_stmt_block(set(), semicolons=False)
    return BareDelocalStmt(decl, body, pos)

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

  def parse_bare_call_stmt(self) -> CallStmt:
    ident = self.parse_ident(allow_main=True)
    args = self.parse_arg_list()
    return CallStmt(ident, args, False, ident.pos)

  def parse_uncall_stmt(self) -> UncallStmt:
    pos = self.expect_kw("uncall").pos
    external = self.tokens.match("KW", "external") is not None
    ident = self.parse_ident(allow_main=True)
    args = self.parse_arg_list()
    return UncallStmt(ident, args, external, pos)

  def parse_arg_list(self) -> list[Expr]:
    # In 1982 Janus, call/uncall have no arguments (procedures have no parameters)
    # Parens are optional for compatibility with modern syntax
    if self.tokens.peek().kind != "OP" or self.tokens.peek().value != "(":
      return []
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

  def parse_scanf_stmt(self) -> PrintsStmt:
    pos = self.expect_kw("scanf").pos
    self.expect_op("(")
    text = self.parse_string()
    args: list[Ident | Lval] = []
    if self.tokens.match("OP", ","):
      args.append(self._parse_printf_arg())
      while self.tokens.match("OP", ","):
        args.append(self._parse_printf_arg())
    self.expect_op(")")
    return PrintsStmt(Prints("scanf", text=text, args=args), pos)

  def parse_show_stmt(self) -> PrintsStmt:
    pos = self.expect_kw("show").pos
    self.expect_op("(")
    args: list[Ident | Lval] = [self._parse_printf_arg()]
    while self.tokens.match("OP", ","):
      args.append(self._parse_printf_arg())
    self.expect_op(")")
    return PrintsStmt(Prints("show", args=args), pos)

  def _parse_printf_arg(self) -> Ident | Lval:
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

  def _looks_like_type(self, offset: int = 0) -> bool:
    idx = self.tokens.index + offset
    if idx >= len(self.tokens.tokens):
      return False
    token = self.tokens.tokens[idx]
    if token.kind == "IDENT":
      next_idx = idx + 1
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

  def _starts_vdecl(self) -> bool:
    idx = 0
    if self.tokens.peek(idx).kind == "KW" and self.tokens.peek(idx).value in {"ancilla", "constant"}:
      idx += 1
    return self._looks_like_type(idx)

  def _looks_like_type_cast(self) -> bool:
    idx = self.tokens.index + 1
    token = self.tokens.tokens[idx]
    return token.kind == "KW" and token.value in set(TYPE_KEYWORDS) | {"stack", "bool", "char", "string"}


def parse_program(filename: str, text: str, line_origins: Sequence[LineOrigin] | None = None) -> Program:
  return Parser(filename, text, line_origins).parse_program()
