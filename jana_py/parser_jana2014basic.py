"""Jana 2014 "basic" parser, tracking the original project's `ParserBasic.hs`.

A 1982-flavored hybrid grammar: `;` line comments, `#` for not-equal, `\\` for
modulo, `:` as a swap operator, typeless global/parameter declarations,
optional `then`/`fi` expressions, and both `procedure` and C-style `void`
definitions. Implemented as a subclass of the jana2014 parser: only the
divergent productions are overridden (see parser_jana2014_in_out.py for the
pattern); `janus1982ext` re-exports this module.
"""
from __future__ import annotations

import re
from typing import Sequence

from .ast import AssignStmt
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
from .ast import LocalStmt
from .ast import Lval
from .ast import LvalExpr
from .ast import ModOp
from .ast import NilExpr
from .ast import Number
from .ast import Prints
from .ast import PrintsStmt
from .ast import Proc
from .ast import ProcMain
from .ast import Program
from .ast import SizeExpr
from .ast import SourcePos
from .ast import StructDef
from .ast import SwapStmt
from .ast import SwitchCase
from .ast import SwitchStmt
from .ast import TernaryExpr
from .ast import TopExpr
from .ast import Type
from .ast import Vdecl
from .errors import JanaError
from .preprocess import LineOrigin
from .parser_jana2014 import TYPE_KEYWORDS  # noqa: F401  (referenced by inherited methods)
from .parser_jana2014 import Parser as _Jana2014Parser
from .parser_jana2014 import Token, TokenStream  # noqa: F401  (re-export for compat)
from .parser_jana2014 import tokenize as _base_tokenize


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


def tokenize(filename: str, text: str, line_origins: Sequence[LineOrigin] | None = None) -> list[Token]:
  return _base_tokenize(filename, text, line_origins, keywords=KEYWORDS, token_re=TOKEN_RE)


class Parser(_Jana2014Parser):
  KEYWORDS = KEYWORDS
  TOKEN_RE = TOKEN_RE
  BIN_PRECEDENCE = BIN_PRECEDENCE

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

  def _starts_shared_vdecl_tail(self) -> bool:
    return self.tokens.peek(1).kind == "IDENT"

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

  def _stmt_requires_semicolon(self, stmt) -> bool:
    return not isinstance(
      stmt,
      (IfStmt, FromStmt, IterateStmt, LocalStmt, BareLocalStmt, SwitchStmt, AncillaBlockStmt),
    )

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

  def parse_bare_call_stmt(self) -> CallStmt:
    ident = self.parse_ident(allow_main=True)
    args = self.parse_arg_list()
    return CallStmt(ident, args, False, ident.pos)

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


def parse_program(filename: str, text: str, line_origins: Sequence[LineOrigin] | None = None) -> Program:
  return Parser(filename, text, line_origins).parse_program()
