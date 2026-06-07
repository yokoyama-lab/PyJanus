"""Procedure-style (classic Janus) source formatter.

`ProcedureFormatter` subclasses the C-style `CFormatter`, overriding only the
productions whose surface syntax differs: `procedure`-based headers (no
braces/semicolons), `if..then..fi`, `from..do..loop..until`, `iterate..end`,
and statement-terminator-free statements. Expression/lvalue/type/decl
formatting is inherited. `-i` output for the jana2014-family dialects goes
through this class (see `format.formatter_for_std`).
"""
from __future__ import annotations

from .ast import AncillaBlockStmt
from .ast import AssertStmt
from .ast import AssignStmt
from .ast import BareDelocalStmt
from .ast import BareLocalStmt
from .ast import CallStmt
from .ast import FromStmt
from .ast import IfStmt
from .ast import IterateStmt
from .ast import LocalStmt
from .ast import PopStmt
from .ast import PrintsStmt
from .ast import Proc
from .ast import ProcMain
from .ast import Program
from .ast import PushStmt
from .ast import SkipStmt
from .ast import SwapStmt
from .ast import UncallStmt
from .ast import UserErrorStmt
from .format import CFormatter


class ProcedureFormatter(CFormatter):
  """AST -> procedure-style (jana2014-family) Janus source."""

  def format_main(self, main: ProcMain) -> str:
    lines = ["procedure main()"]
    lines.extend(f"    {self.format_vdecl(vdecl)}" for vdecl in main.vdecls)
    lines.extend(self.format_stmt(stmt, 1) for stmt in main.stmts)
    return "\n".join(lines)

  def format_proc(self, proc: Proc) -> str:
    params = ", ".join(self.format_vdecl(param, allow_init=False) for param in proc.params)
    lines = [f"procedure {proc.procname.name}({params})"]
    lines.extend(self.format_stmt(stmt, 1) for stmt in proc.body)
    return "\n".join(lines)

  def format_call(self, stmt: CallStmt | UncallStmt, keyword: str, pad: str) -> str:
    ext = "external " if stmt.external else ""
    args = ", ".join(self.format_expr(arg) for arg in stmt.args)
    return f"{pad}{keyword} {ext}{stmt.ident.name}({args})"

  def format_stmt(self, stmt, indent: int) -> str:
    pad = "    " * indent
    if isinstance(stmt, AssignStmt):
      return f"{pad}{self.format_lval(stmt.lval)} {stmt.mod_op.value} {self.format_expr(stmt.expr)}"
    if isinstance(stmt, IfStmt):
      lines = [f"{pad}if {self.format_expr(stmt.entry_cond)} then"]
      lines.extend(self.format_stmt(s, indent + 1) for s in stmt.if_part)
      if stmt.else_part:
        lines.append(f"{pad}else")
        lines.extend(self.format_stmt(s, indent + 1) for s in stmt.else_part)
      lines.append(f"{pad}fi {self.format_expr(stmt.exit_cond)}")
      return "\n".join(lines)
    if isinstance(stmt, FromStmt):
      lines = [f"{pad}from {self.format_expr(stmt.entry_cond)}"]
      if stmt.do_part:
        lines.append(f"{pad}do")
        lines.extend(self.format_stmt(s, indent + 1) for s in stmt.do_part)
      if stmt.loop_part:
        lines.append(f"{pad}loop")
        lines.extend(self.format_stmt(s, indent + 1) for s in stmt.loop_part)
      lines.append(f"{pad}until {self.format_expr(stmt.exit_cond)}")
      return "\n".join(lines)
    if isinstance(stmt, IterateStmt):
      lines = [f"{pad}iterate {self.format_type(stmt.typ)} {stmt.ident.name} = {self.format_expr(stmt.start_expr)} by {self.format_expr(stmt.step_expr)} to {self.format_expr(stmt.end_expr)}"]
      lines.extend(self.format_stmt(s, indent + 1) for s in stmt.body)
      lines.append(f"{pad}end")
      return "\n".join(lines)
    if isinstance(stmt, PushStmt):
      return f"{pad}push({self.format_expr(stmt.expr)}, {stmt.ident.name})"
    if isinstance(stmt, PopStmt):
      return f"{pad}pop({self.format_expr(stmt.expr)}, {stmt.ident.name})"
    if isinstance(stmt, LocalStmt):
      lines = [f"{pad}local {self.format_local_decl(stmt.enter_decl)}"]
      lines.extend(self.format_stmt(s, indent + 1) for s in stmt.body)
      lines.append(f"{pad}delocal {self.format_local_decl(stmt.exit_decl)}")
      return "\n".join(lines)
    if isinstance(stmt, BareLocalStmt):
      # Crossing local: the body statements are siblings in the source.
      lines = [f"{pad}local {self.format_local_decl(stmt.decl)}"]
      lines.extend(self.format_stmt(s, indent) for s in stmt.body)
      return "\n".join(lines)
    if isinstance(stmt, BareDelocalStmt):
      return f"{pad}delocal {self.format_local_decl(stmt.decl)}"
    if isinstance(stmt, AncillaBlockStmt):
      # The block form keeps braces/semicolons in every dialect.
      decls = ", ".join(self.format_local_decl(decl) for decl in stmt.decls)
      lines = [f"{pad}ancilla ({decls}) {{"]
      lines.extend(self.format_stmt(s, indent + 1) for s in stmt.body)
      lines.append(f"{pad}}};")
      return "\n".join(lines)
    if isinstance(stmt, CallStmt):
      return self.format_call(stmt, "call", pad)
    if isinstance(stmt, UncallStmt):
      return self.format_call(stmt, "uncall", pad)
    if isinstance(stmt, UserErrorStmt):
      return f'{pad}error("{stmt.message}")'
    if isinstance(stmt, SwapStmt):
      return f"{pad}{self.format_lval(stmt.left)} <=> {self.format_lval(stmt.right)}"
    if isinstance(stmt, PrintsStmt):
      kind = stmt.prints.kind
      if kind in {"printf", "scanf"}:
        args = ", ".join(self._format_print_arg(a) for a in stmt.prints.args)
        fmt = self._escape(stmt.prints.text or "")
        if args:
          return f'{pad}{kind}("{fmt}", {args})'
        return f'{pad}{kind}("{fmt}")'
      if kind == "print":
        return f'{pad}print("{self._escape(stmt.prints.text or "")}")'
      if kind == "show":
        args = ", ".join(self._format_print_arg(a) for a in stmt.prints.args)
        return f"{pad}show({args})"
      if kind == "read":
        return f"{pad}read {self._format_print_arg(stmt.prints.args[0])}"
      if kind == "write":
        return f"{pad}write {self._format_print_arg(stmt.prints.args[0])}"
      raise TypeError(f"Unsupported print form for canonical formatter: {kind!r}")
    if isinstance(stmt, SkipStmt):
      return f"{pad}skip"
    if isinstance(stmt, AssertStmt):
      return f"{pad}assert {self.format_expr(stmt.expr)}"
    raise TypeError(f"Unsupported stmt: {type(stmt)!r}")


_DEFAULT = ProcedureFormatter()


def format_program(program: Program) -> str:
  return _DEFAULT.format_program(program)
