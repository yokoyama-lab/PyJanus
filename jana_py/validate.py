from __future__ import annotations

from .ast import CallStmt
from .ast import FromStmt
from .ast import IfStmt
from .ast import IterateStmt
from .ast import LocalStmt
from .ast import LvalExpr
from .ast import Proc
from .ast import ProcMain
from .ast import Program
from .ast import SourcePos
from .ast import UncallStmt
from .ast import ArrayExpr
from .ast import BinExpr
from .ast import StructDef
from .ast import UnaryExpr
from .format import format_stmt
from .errors import JanaError


def validate_program(program: Program) -> None:
  _validate_struct_defs(program.struct_defs)
  known_structs = {struct_def.ident.name for struct_def in program.struct_defs}
  if program.main is None:
    filename = program.procs[0].procname.pos.filename if program.procs else ""
    raise JanaError(SourcePos(filename, 0, 0), "No main procedure has been defined")
  seen: dict[str, Proc] = {}
  for proc in program.procs:
    if proc.procname.name in seen:
      raise JanaError(proc.procname.pos, f"Procedure `{proc.procname.name}' is already defined")
    seen[proc.procname.name] = proc
    for param in proc.params:
      _validate_decl_type(param, known_structs)
    param_names = [param.ident.name for param in proc.params]
    if len(param_names) != len(set(param_names)):
      raise JanaError(proc.procname.pos, f"Procedure `{proc.procname.name}' has duplicate arguments")
    _validate_unique_bindings(param_names, proc.body, known_structs)
    _validate_stmt_calls(proc.body)
  if program.main is not None:
    for vdecl in program.main.vdecls:
      _validate_decl_type(vdecl, known_structs)
    main_names = [vdecl.ident.name for vdecl in program.main.vdecls]
    if len(main_names) != len(set(main_names)):
      seen_names: set[str] = set()
      dup_vdecl = None
      for vdecl in program.main.vdecls:
        if vdecl.ident.name in seen_names:
          dup_vdecl = vdecl
          break
        seen_names.add(vdecl.ident.name)
      assert dup_vdecl is not None
      raise JanaError(dup_vdecl.ident.pos, f"Variable name `{dup_vdecl.ident.name}' is already bound")
    _validate_stmt_calls(program.main.stmts)


def _validate_struct_defs(struct_defs: list[StructDef]) -> None:
  seen: set[str] = set()
  for struct_def in struct_defs:
    if struct_def.ident.name in seen:
      raise JanaError(struct_def.ident.pos, f"Struct `{struct_def.ident.name}' is already defined")
    seen.add(struct_def.ident.name)
    field_seen: set[str] = set()
    for field in struct_def.fields:
      if field.ident.name in field_seen:
        raise JanaError(field.ident.pos, f"Field `{field.ident.name}' is already defined in struct `{struct_def.ident.name}'")
      field_seen.add(field.ident.name)
      if field.typ.kind == "struct" and field.typ.name not in seen and field.typ.name not in {s.ident.name for s in struct_defs}:
        raise JanaError(field.typ.pos, f"Struct `{field.typ.name}' is not defined")


def _validate_decl_type(decl, known_structs: set[str]) -> None:
  if decl.typ.kind == "struct" and decl.typ.name not in known_structs:
    raise JanaError(decl.typ.pos, f"Struct `{decl.typ.name}' is not defined")


def _validate_unique_bindings(bound: list[str], stmts: list, known_structs: set[str]) -> None:
  for stmt in stmts:
    if isinstance(stmt, LocalStmt):
      name = stmt.enter_decl.ident.name
      _validate_decl_type(stmt.enter_decl, known_structs)
      _validate_decl_type(stmt.exit_decl, known_structs)
      if name in bound:
        raise JanaError(stmt.enter_decl.pos, f"Variable name `{name}' is already bound")
      _validate_unique_bindings(bound + [name], stmt.body, known_structs)
    elif isinstance(stmt, IfStmt):
      _validate_unique_bindings(bound, stmt.if_part, known_structs)
      _validate_unique_bindings(bound, stmt.else_part, known_structs)
    elif isinstance(stmt, FromStmt):
      _validate_unique_bindings(bound, stmt.do_part, known_structs)
      _validate_unique_bindings(bound, stmt.loop_part, known_structs)
    elif isinstance(stmt, IterateStmt):
      name = stmt.ident.name
      if name in bound:
        raise JanaError(stmt.pos, f"Variable name `{name}' is already bound")
      _validate_unique_bindings(bound + [name], stmt.body, known_structs)


def _validate_stmt_calls(stmts: list) -> None:
  for stmt in stmts:
    if isinstance(stmt, (CallStmt, UncallStmt)) and stmt.ident.name == "main":
      raise JanaError(stmt.pos, "It is not allowed to call the `main' procedure", [f"In statement:\n    {format_stmt(stmt, 0)}"], True)
    if isinstance(stmt, IfStmt):
      _validate_stmt_calls(stmt.if_part)
      _validate_stmt_calls(stmt.else_part)
    elif isinstance(stmt, FromStmt):
      _validate_stmt_calls(stmt.do_part)
      _validate_stmt_calls(stmt.loop_part)
    elif isinstance(stmt, IterateStmt):
      _validate_stmt_calls(stmt.body)
    elif isinstance(stmt, LocalStmt):
      _validate_stmt_calls(stmt.body)
