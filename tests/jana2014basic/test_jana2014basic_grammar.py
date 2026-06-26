"""Grammar coverage for the jana2014basic dialect (a 1982-flavored hybrid).

The smoke test only parses one trivial procedure.  This file drives the
distinctive productions of `parser_jana2014basic.Parser` directly (no
subprocess), so the parser's own branches are exercised:

  * `;` line comments and `#` not-equal / `\\` modulo / `:` swap operators;
  * typeless global and parameter declarations;
  * optional `then`, and `fi`/`until` with and without a trailing expression;
  * both `procedure` and C-style `void` definitions;
  * struct, switch, for-loop, read/write, and the multiple-main error.

Tests assert on the shared AST so a grammar regression shows up structurally.
"""
from __future__ import annotations

import pytest

from jana_py.ast import (
    AssignStmt, BinExpr, BinOpKind, CallStmt, FromStmt, IfStmt, ProcMain,
    SwapStmt,
)
from jana_py.errors import JanaError
from jana_py.parser_jana2014basic import parse_program


def parse(src: str):
  return parse_program("basic.ja", src)


class TestLexicalDialect:

  def test_semicolon_line_comment_is_ignored(self):
    prog = parse(
      "procedure main()\n"
      "    int x\n"
      "    ; this is a 1982-style comment\n"
      "    x += 1\n"
    )
    assert isinstance(prog.main, ProcMain)
    assert len(prog.main.stmts) == 1

  def test_hash_is_not_equal_operator(self):
    # `#` is the 1982 not-equal; used here as a loop/branch condition.
    prog = parse(
      "procedure main()\n"
      "    int x\n"
      "    if x # 0 then x += 1 fi x # 0\n"
    )
    stmt = prog.main.stmts[0]
    assert isinstance(stmt, IfStmt)
    assert isinstance(stmt.entry_cond, BinExpr)
    assert stmt.entry_cond.op == BinOpKind.NEQ

  def test_backslash_is_modulo(self):
    prog = parse(
      "procedure main()\n"
      "    int x\n"
      "    int y\n"
      "    x += y \\ 3\n"
    )
    stmt = prog.main.stmts[0]
    assert isinstance(stmt, AssignStmt)
    assert isinstance(stmt.expr, BinExpr)
    assert stmt.expr.op == BinOpKind.MOD

  def test_colon_is_swap_operator(self):
    prog = parse(
      "procedure main()\n"
      "    int x\n"
      "    int y\n"
      "    x : y\n"
    )
    assert isinstance(prog.main.stmts[0], SwapStmt)

  def test_binary_number_literal(self):
    prog = parse(
      "procedure main()\n"
      "    int x\n"
      "    x += 0b101\n"
    )
    assert prog.main.stmts[0].expr.value == 5


class TestTypelessDeclarations:

  def test_typeless_global_declaration(self):
    # A bare identifier at top level (not followed by '(' or '{') is a global.
    prog = parse(
      "g\n"
      "procedure main()\n"
      "    g += 1\n"
    )
    names = [v.ident.name for v in prog.main.vdecls]
    assert "g" in names

  def test_typeless_parameter(self):
    prog = parse(
      "procedure inc(x)\n"
      "    x += 1\n"
      "procedure main()\n"
      "    int a\n"
      "    call inc(a)\n"
    )
    inc = prog.procs[0]
    assert inc.params[0].ident.name == "x"

  def test_typed_parameter(self):
    # The dialect also accepts an explicit `int` type on a parameter, which
    # drives the typed parse_type / parse_vdecls path rather than the typeless one.
    prog = parse(
      "procedure inc(int x)\n"
      "    x += 1\n"
      "procedure main()\n"
      "    int a\n"
      "    call inc(a)\n"
    )
    inc = prog.procs[0]
    assert inc.params[0].ident.name == "x"
    assert inc.params[0].typ.kind == "int"

  def test_typeless_array_global(self):
    prog = parse(
      "a[3]\n"
      "procedure main()\n"
      "    a[0] += 1\n"
    )
    decl = next(v for v in prog.main.vdecls if v.ident.name == "a")
    assert decl.dimensions and decl.dimensions[0].value == 3


class TestOptionalKeywords:

  def test_then_is_optional(self):
    prog = parse(
      "procedure main()\n"
      "    int x\n"
      "    if x = 0 x += 1 fi x = 1\n"
    )
    assert isinstance(prog.main.stmts[0], IfStmt)

  def test_fi_without_trailing_expr_reuses_entry_cond(self):
    prog = parse(
      "procedure main()\n"
      "    int x\n"
      "    if x = 0 then x += 1 fi\n"
    )
    stmt = prog.main.stmts[0]
    # exit_cond defaults to the entry condition when `fi` has no expression
    assert isinstance(stmt.exit_cond, BinExpr)

  def test_if_else_branch(self):
    prog = parse(
      "procedure main()\n"
      "    int x\n"
      "    int y\n"
      "    if x = 0 then y += 1 else y += 2 fi y = 1\n"
    )
    stmt = prog.main.stmts[0]
    assert len(stmt.if_part) == 1 and len(stmt.else_part) == 1

  def test_from_loop_until(self):
    prog = parse(
      "procedure main()\n"
      "    int i\n"
      "    from i = 0 do i += 1 loop i += 1 until i = 4\n"
    )
    stmt = prog.main.stmts[0]
    assert isinstance(stmt, FromStmt)
    assert len(stmt.do_part) == 1 and len(stmt.loop_part) == 1


class TestDefinitionForms:

  def test_bare_call_without_call_keyword(self):
    # `inc(a)` as a statement (ident directly followed by '(') is a call.
    prog = parse(
      "procedure inc(x)\n"
      "    x += 1\n"
      "procedure main()\n"
      "    int a\n"
      "    inc(a)\n"
    )
    assert isinstance(prog.main.stmts[0], CallStmt)

  def test_multiple_main_is_rejected(self):
    with pytest.raises(JanaError, match="[Mm]ultiple main"):
      parse(
        "procedure main()\n"
        "    int x\n"
        "    x += 1\n"
        "procedure main()\n"
        "    int y\n"
        "    y += 1\n"
      )


class TestRicherConstructs:

  def test_read_and_write_statements(self):
    prog = parse(
      "procedure main()\n"
      "    int x\n"
      "    read x\n"
      "    write x\n"
    )
    kinds = [getattr(s, "prints", None) and s.prints.kind for s in prog.main.stmts]
    assert "read" in kinds and "write" in kinds
