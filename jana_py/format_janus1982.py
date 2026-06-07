"""Strict Janus 1982 source formatter.

Subclasses the procedure-style formatter; the strict 1982 surface syntax
additionally has: typeless top-level global declarations (main's vdecls are
hoisted out of `procedure main`), parameterless paren-less procedures,
paren-less `call`/`uncall`, and `#` for not-equal (`!=` is the XOR-update
operator in 1982).
"""
from __future__ import annotations

from .ast import BinOpKind
from .ast import CallStmt
from .ast import Proc
from .ast import ProcMain
from .ast import Program
from .ast import UncallStmt
from .ast import Vdecl
from .format_jana2014 import ProcedureFormatter


class Janus1982Formatter(ProcedureFormatter):
  """AST -> strict janus1982 Janus source."""

  def format_program(self, program: Program) -> str:
    blocks: list[str] = []
    if program.main is not None and program.main.vdecls:
      # Globals are typeless top-level declarations in strict 1982.
      blocks.append("\n".join(self._format_global(vdecl) for vdecl in program.main.vdecls))
    if program.main is not None:
      blocks.append(self.format_main(program.main))
    blocks.extend(self.format_proc(proc) for proc in program.procs)
    return "\n\n".join(blocks) + "\n"

  def _format_global(self, vdecl: Vdecl) -> str:
    dims = "".join(f"[{self.format_expr(dim) if dim is not None else ''}]" for dim in vdecl.dimensions)
    return f"{vdecl.ident.name}{dims}"

  def format_main(self, main: ProcMain) -> str:
    # vdecls are emitted as globals by format_program, not inside main.
    lines = ["procedure main"]
    lines.extend(self.format_stmt(stmt, 1) for stmt in main.stmts)
    return "\n".join(lines)

  def format_proc(self, proc: Proc) -> str:
    # Strict 1982 procedures take no parameters and no parens.
    lines = [f"procedure {proc.procname.name}"]
    lines.extend(self.format_stmt(stmt, 1) for stmt in proc.body)
    return "\n".join(lines)

  def format_call(self, stmt: CallStmt | UncallStmt, keyword: str, pad: str) -> str:
    if stmt.args or stmt.external:
      return super().format_call(stmt, keyword, pad)
    return f"{pad}{keyword} {stmt.ident.name}"

  def format_bin_op(self, op: BinOpKind) -> str:
    if op == BinOpKind.NEQ:
      return "#"  # `!=` is the XOR-update statement operator in 1982
    return op.value
