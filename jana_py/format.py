from __future__ import annotations

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
from .ast import IfStmt
from .ast import IterateStmt
from .ast import LocalDecl
from .ast import LocalStmt
from .ast import Lval
from .ast import LvalField
from .ast import LvalIndex
from .ast import LvalExpr
from .ast import NilExpr
from .ast import Number
from .ast import PopStmt
from .ast import PrintsStmt
from .ast import Proc
from .ast import ProcMain
from .ast import Program
from .ast import PushStmt
from .ast import SizeExpr
from .ast import SkipStmt
from .ast import StringLiteral
from .ast import StructDef
from .ast import StructField
from .ast import SwapStmt
from .ast import TernaryExpr
from .ast import TopExpr
from .ast import Type
from .ast import TypeCastExpr
from .ast import UnaryExpr
from .ast import UncallStmt
from .ast import UserErrorStmt
from .ast import Vdecl


TYPE_NAMES = {
  "int": {
    "Unbound": "int",
    "I8": "i8",
    "I16": "i16",
    "I32": "i32",
    "I64": "i64",
    "U8": "u8",
    "U16": "u16",
    "U32": "u32",
    "U64": "u64",
    "FreshVar": "int",
    "InferInt": "int",
  },
  "stack": "stack",
  "bool": "bool",
}

DECL_PREFIX = {
  DeclType.VARIABLE: "",
  DeclType.ANCILLA: "ancilla ",
  DeclType.CONSTANT: "constant ",
}

BIN_PREC = {
  BinOpKind.LOR: 0,
  BinOpKind.LAND: 0,
  BinOpKind.AND: 1,
  BinOpKind.OR: 1,
  BinOpKind.XOR: 1,
  BinOpKind.GE: 2,
  BinOpKind.GT: 2,
  BinOpKind.LE: 2,
  BinOpKind.LT: 2,
  BinOpKind.EQ: 2,
  BinOpKind.NEQ: 2,
  BinOpKind.ADD: 3,
  BinOpKind.SUB: 3,
  BinOpKind.MUL: 4,
  BinOpKind.DIV: 4,
  BinOpKind.MOD: 4,
  BinOpKind.EXP: 4,
  BinOpKind.SL: 4,
  BinOpKind.SR: 4,
}

UNARY_PREC = 5
CAST_PREC = 6
TERNARY_PREC = -1


def format_program(program: Program) -> str:
  blocks: list[str] = []
  blocks.extend(format_struct_def(struct_def) for struct_def in program.struct_defs)
  if program.main is not None:
    blocks.append(format_main(program.main))
  blocks.extend(format_proc(proc) for proc in program.procs)
  return "\n\n".join(blocks) + "\n"


def format_struct_def(struct_def: StructDef) -> str:
  lines = [f"struct {struct_def.ident.name} {{"]
  for index, field in enumerate(struct_def.fields):
    suffix = "," if index < len(struct_def.fields) - 1 else ""
    lines.append(f"    {format_struct_field(field)}{suffix}")
  lines.append("}")
  return "\n".join(lines)


def format_struct_field(field: StructField) -> str:
  dims = "".join(f"[{format_expr(dim) if dim is not None else ''}]" for dim in field.dimensions)
  return f"{format_type(field.typ)} {field.ident.name}{dims}"


def format_main(main: ProcMain) -> str:
  lines = ["procedure main()"]
  lines.extend(f"    {format_vdecl(vdecl)}" for vdecl in main.vdecls)
  lines.extend(format_stmt(stmt, 1) for stmt in main.stmts)
  return "\n".join(lines)


def format_proc(proc: Proc) -> str:
  params = ", ".join(format_vdecl(param, allow_init=False) for param in proc.params)
  lines = [f"procedure {proc.procname.name}({params})"]
  lines.extend(format_stmt(stmt, 1) for stmt in proc.body)
  return "\n".join(lines)


def format_vdecl(vdecl: Vdecl, allow_init: bool = True) -> str:
  return _format_decl(vdecl.decl_type, vdecl.typ, vdecl.ident.name, vdecl.dimensions, vdecl.init_expr if allow_init else None)


def format_local_decl(decl: LocalDecl) -> str:
  return _format_decl(decl.decl_type, decl.typ, decl.ident.name, decl.dimensions, decl.init_expr)


def _format_decl(decl_type: DeclType, typ: Type, ident: str, dimensions: list[Expr | None], init_expr: Expr | None) -> str:
  head = f"{DECL_PREFIX[decl_type]}{format_type(typ)} {ident}"
  dims = "".join(f"[{format_expr(dim) if dim is not None else ''}]" for dim in dimensions)
  if init_expr is None:
    return head + dims
  return f"{head}{dims} = {format_expr(init_expr)}"


def format_type(typ: Type) -> str:
  if typ.is_char:
    return "char"
  if typ.kind == "struct":
    return typ.name or "struct"
  if typ.kind == "int":
    return TYPE_NAMES["int"][typ.int_type.value]
  return TYPE_NAMES[typ.kind]


def format_stmt(stmt, indent: int) -> str:
  pad = "    " * indent
  if isinstance(stmt, AssignStmt):
    return f"{pad}{format_lval(stmt.lval)} {stmt.mod_op.value} {format_expr(stmt.expr)}"
  if isinstance(stmt, IfStmt):
    lines = [f"{pad}if {format_expr(stmt.entry_cond)} then"]
    lines.extend(format_stmt(s, indent + 1) for s in stmt.if_part)
    if stmt.else_part:
      lines.append(f"{pad}else")
      lines.extend(format_stmt(s, indent + 1) for s in stmt.else_part)
    lines.append(f"{pad}fi {format_expr(stmt.exit_cond)}")
    return "\n".join(lines)
  if isinstance(stmt, FromStmt):
    lines = [f"{pad}from {format_expr(stmt.entry_cond)}"]
    if stmt.do_part:
      lines.append(f"{pad}do")
      lines.extend(format_stmt(s, indent + 1) for s in stmt.do_part)
    if stmt.loop_part:
      lines.append(f"{pad}loop")
      lines.extend(format_stmt(s, indent + 1) for s in stmt.loop_part)
    lines.append(f"{pad}until {format_expr(stmt.exit_cond)}")
    return "\n".join(lines)
  if isinstance(stmt, IterateStmt):
    lines = [f"{pad}iterate {format_type(stmt.typ)} {stmt.ident.name} = {format_expr(stmt.start_expr)} by {format_expr(stmt.step_expr)} to {format_expr(stmt.end_expr)}"]
    lines.extend(format_stmt(s, indent + 1) for s in stmt.body)
    lines.append(f"{pad}end")
    return "\n".join(lines)
  if isinstance(stmt, PushStmt):
    return f"{pad}push({format_expr(stmt.expr)}, {stmt.ident.name})"
  if isinstance(stmt, PopStmt):
    return f"{pad}pop({format_expr(stmt.expr)}, {stmt.ident.name})"
  if isinstance(stmt, LocalStmt):
    lines = [f"{pad}local {format_local_decl(stmt.enter_decl)}"]
    lines.extend(format_stmt(s, indent + 1) for s in stmt.body)
    lines.append(f"{pad}delocal {format_local_decl(stmt.exit_decl)}")
    return "\n".join(lines)
  if isinstance(stmt, CallStmt):
    ext = "external " if stmt.external else ""
    args = ", ".join(format_expr(arg) for arg in stmt.args)
    return f"{pad}call {ext}{stmt.ident.name}({args})"
  if isinstance(stmt, UncallStmt):
    ext = "external " if stmt.external else ""
    args = ", ".join(format_expr(arg) for arg in stmt.args)
    return f"{pad}uncall {ext}{stmt.ident.name}({args})"
  if isinstance(stmt, UserErrorStmt):
    return f'{pad}error("{stmt.message}")'
  if isinstance(stmt, SwapStmt):
    return f"{pad}{format_lval(stmt.left)} <=> {format_lval(stmt.right)}"
  if isinstance(stmt, PrintsStmt):
    if stmt.prints.kind == "print":
      return f'{pad}print("{_escape(stmt.prints.text or "")}")'
    if stmt.prints.kind == "printf":
      args = ", ".join(_format_print_arg(a) for a in stmt.prints.args)
      if args:
        return f'{pad}printf("{_escape(stmt.prints.text or "")}", {args})'
      return f'{pad}printf("{_escape(stmt.prints.text or "")}")'
    args = ", ".join(_format_print_arg(a) for a in stmt.prints.args)
    return f"{pad}show({args})"
  if isinstance(stmt, SkipStmt):
    return f"{pad}skip"
  if isinstance(stmt, AssertStmt):
    return f"{pad}assert {format_expr(stmt.expr)}"
  raise TypeError(f"Unsupported stmt: {type(stmt)!r}")


def _format_print_arg(arg) -> str:
  from .ast import Ident, Lval
  if isinstance(arg, Ident):
    return arg.name
  return format_lval(arg)


def format_lval(lval: Lval) -> str:
  parts = [lval.ident.name]
  for selector in lval.selectors:
    if isinstance(selector, LvalField):
      parts.append(f".{selector.ident.name}")
    elif isinstance(selector, LvalIndex):
      parts.append(f"[{format_expr(selector.expr)}]")
  return "".join(parts)


def format_expr(expr: Expr, parent_prec: int = -1) -> str:
  if isinstance(expr, Number):
    return str(expr.value)
  if isinstance(expr, Boolean):
    return "true" if expr.value else "false"
  if isinstance(expr, LvalExpr):
    return format_lval(expr.lval)
  if isinstance(expr, EmptyExpr):
    return f"empty({expr.ident.name})"
  if isinstance(expr, TopExpr):
    return f"top({expr.ident.name})"
  if isinstance(expr, SizeExpr):
    return f"size({expr.ident.name})"
  if isinstance(expr, NilExpr):
    return "nil"
  if isinstance(expr, ArrayExpr):
    return "{ " + ", ".join(format_expr(item) for item in expr.items) + " }"
  if isinstance(expr, StringLiteral):
    return f'"{_escape(expr.value)}"'
  if isinstance(expr, UnaryExpr):
    text = expr.op.value + format_expr(expr.expr, UNARY_PREC)
    return f"({text})" if parent_prec > UNARY_PREC else text
  if isinstance(expr, TypeCastExpr):
    text = f"({format_type(expr.typ)}) {format_expr(expr.expr, CAST_PREC)}"
    return f"({text})" if parent_prec > CAST_PREC else text
  if isinstance(expr, BinExpr):
    prec = BIN_PREC[expr.op]
    text = f"{format_expr(expr.left, prec)} {expr.op.value} {format_expr(expr.right, prec)}"
    return f"({text})" if parent_prec > prec else text
  if isinstance(expr, TernaryExpr):
    text = f"{format_expr(expr.cond, TERNARY_PREC)} ? {format_expr(expr.then_expr, TERNARY_PREC)} : {format_expr(expr.else_expr, TERNARY_PREC)}"
    return f"({text})" if parent_prec > TERNARY_PREC else text
  raise TypeError(f"Unsupported expr: {type(expr)!r}")


def _escape(text: str) -> str:
  return text.replace("\\", "\\\\").replace('"', '\\"').replace("\0", "\\u0000").replace("\n", "\\n")
