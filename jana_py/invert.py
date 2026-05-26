from __future__ import annotations

from .ast import AssignStmt
from .ast import BareDelocalStmt
from .ast import BareLocalStmt
from .ast import BinExpr
from .ast import BinOpKind
from .ast import CallStmt
from .ast import FromStmt
from .ast import IfStmt
from .ast import IterateStmt
from .ast import LocalStmt
from .ast import ModOp
from .ast import Number
from .ast import PopStmt
from .ast import Proc
from .ast import Program
from .ast import PushStmt
from .ast import SwitchCase
from .ast import SwitchStmt
from .ast import AncillaBlockStmt
from .ast import Type
from .ast import UncallStmt


def invert_program(program: Program) -> Program:
  return Program(program.main, [invert_proc_globally(proc) for proc in program.procs])


def invert_proc_globally(proc: Proc) -> Proc:
  return Proc(proc.procname, proc.params, invert_stmts(proc.body, global_mode=True))


def invert_stmts(stmts: list, global_mode: bool) -> list:
  return [invert_stmt(stmt, global_mode) for stmt in reversed(stmts)]


def invert_stmt(stmt, global_mode: bool):
  if isinstance(stmt, AssignStmt):
    mod_op = {
      ModOp.ADD_EQ: ModOp.SUB_EQ,
      ModOp.SUB_EQ: ModOp.ADD_EQ,
      ModOp.XOR_EQ: ModOp.XOR_EQ,
      ModOp.MUL_EQ: ModOp.DIV_EQ,
      ModOp.DIV_EQ: ModOp.MUL_EQ,
    }[stmt.mod_op]
    return AssignStmt(mod_op, stmt.lval, stmt.expr, stmt.pos)
  if isinstance(stmt, IfStmt):
    return IfStmt(stmt.exit_cond, invert_stmts(stmt.if_part, global_mode), invert_stmts(stmt.else_part, global_mode), stmt.entry_cond, stmt.pos)
  if isinstance(stmt, SwitchStmt):
    inverted_cases = [SwitchCase(case.value, invert_stmts(case.body, global_mode), case.pos) for case in stmt.cases]
    return SwitchStmt(stmt.exit_expr, inverted_cases, invert_stmts(stmt.default_part, global_mode), stmt.expr, stmt.pos)
  if isinstance(stmt, AncillaBlockStmt):
    return AncillaBlockStmt(stmt.decls, invert_stmts(stmt.body, global_mode), stmt.pos)
  if isinstance(stmt, FromStmt):
    return FromStmt(stmt.exit_cond, invert_stmts(stmt.do_part, global_mode), invert_stmts(stmt.loop_part, global_mode), stmt.entry_cond, stmt.pos)
  if isinstance(stmt, IterateStmt):
    zero = Number(0, stmt.pos)
    return IterateStmt(
      stmt.typ,
      stmt.ident,
      stmt.end_expr,
      BinExpr(BinOpKind.SUB, zero, stmt.step_expr, stmt.pos),
      stmt.start_expr,
      invert_stmts(stmt.body, global_mode),
      stmt.pos,
    )
  if isinstance(stmt, PushStmt):
    return PopStmt(stmt.expr, stmt.ident, stmt.pos)
  if isinstance(stmt, PopStmt):
    return PushStmt(stmt.expr, stmt.ident, stmt.pos)
  if isinstance(stmt, LocalStmt):
    return LocalStmt(stmt.exit_decl, invert_stmts(stmt.body, global_mode), stmt.enter_decl, stmt.pos)
  if isinstance(stmt, BareLocalStmt):
    return BareDelocalStmt(stmt.decl, stmt.pos)
  if isinstance(stmt, BareDelocalStmt):
    return BareLocalStmt(stmt.decl, [], stmt.pos)
  if not global_mode and isinstance(stmt, CallStmt):
    return UncallStmt(stmt.ident, stmt.args, stmt.external, stmt.pos)
  if not global_mode and isinstance(stmt, UncallStmt):
    return CallStmt(stmt.ident, stmt.args, stmt.external, stmt.pos)
  return stmt
