from __future__ import annotations

from .ast import ArrayExpr
from .ast import AssertStmt
from .ast import AssignStmt
from .ast import BinExpr
from .ast import Boolean
from .ast import CallStmt
from .ast import DeclType
from .ast import EmptyExpr
from .ast import Expr
from .ast import FromStmt
from .ast import IfStmt
from .ast import IterateStmt
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
from .ast import Program
from .ast import PushStmt
from .ast import SizeExpr
from .ast import SkipStmt
from .ast import StringLiteral
from .ast import SwapStmt
from .ast import TernaryExpr
from .ast import TopExpr
from .ast import Type
from .ast import TypeCastExpr
from .ast import UnaryExpr
from .ast import UncallStmt
from .ast import UserErrorStmt
from .ast import Ident
from .ast import Vdecl


C_TYPES = {
  "Unbound": "int",
  "I8": "signed char",
  "I16": "signed short",
  "I32": "signed int",
  "I64": "signed long",
  "U8": "unsigned char",
  "U16": "unsigned short",
  "U32": "unsigned int",
  "U64": "unsigned long",
  "FreshVar": "int",
  "InferInt": "int",
}


def format_struct_def(sdef) -> str:
  lines = [f"struct {sdef.ident.name} {{"]
  for field in sdef.fields:
    dims = "".join(f"[{format_expr(d)}]" for d in field.dimensions if d is not None) if field.dimensions else ""
    lines.append(f"  {format_type(field.typ)} {field.ident.name}{dims};")
  lines.append("};")
  return "\n".join(lines)


def format_program(header: str | None, program: Program) -> str:
  lines = ["#include <iostream>", "#include <utility>"]
  if header:
    lines.append(f'#include "{header}"')
  lines.append("")
  for sdef in program.struct_defs:
    lines.append(format_struct_def(sdef))
    lines.append("")
  for proc in program.procs:
    lines.append(format_proc(proc))
    lines.append("")
  lines.append("int main() {")
  if program.main is not None:
    for vdecl in program.main.vdecls:
      lines.append("  " + format_vdecl(vdecl) + ";")
    for stmt in program.main.stmts:
      lines.extend(format_stmt(stmt, 1))
  lines.append("  return 1;")
  lines.append("}")
  return "\n".join(lines) + "\n"


def format_proc(proc: Proc) -> str:
  params = ", ".join(format_param(param) for param in proc.params)
  lines = [f"void {proc.procname.name}({params}) {{"]
  for stmt in proc.body:
    lines.extend(format_stmt(stmt, 1))
  lines.append("}")
  return "\n".join(lines)


def format_param(vdecl: Vdecl) -> str:
  if vdecl.dimensions:
    return f"{format_type(vdecl.typ)}* {vdecl.ident.name}"
  return f"{format_type(vdecl.typ)}& {vdecl.ident.name}"


def format_vdecl(vdecl: Vdecl) -> str:
  if vdecl.dimensions:
    dims = "".join(f"[{format_expr(dim)}]" for dim in vdecl.dimensions if dim is not None)
    init = ""
    if vdecl.init_expr is not None:
      init = f" = {format_expr(vdecl.init_expr)}"
    return f"{format_type(vdecl.typ)} {vdecl.ident.name}{dims}{init}"
  init = f" = {format_expr(vdecl.init_expr)}" if vdecl.init_expr is not None else ""
  return f"{format_type(vdecl.typ)} {vdecl.ident.name}{init}"


def format_type(typ: Type) -> str:
  if typ.is_char:
    return "char"
  if typ.kind == "struct":
    return typ.name or "struct"
  if typ.kind == "bool":
    return "bool"
  if typ.kind != "int":
    raise ValueError(f"C++ translation does not support {typ.kind}")
  return C_TYPES[typ.int_type.value]


def format_stmt(stmt, indent: int) -> list[str]:
  pad = "  " * indent
  if isinstance(stmt, AssignStmt):
    return [f"{pad}{format_lval(stmt.lval)} {stmt.mod_op.value} {format_expr(stmt.expr)};"]
  if isinstance(stmt, SwapStmt):
    return [f"{pad}std::swap({format_lval(stmt.left)}, {format_lval(stmt.right)});"]
  if isinstance(stmt, IfStmt):
    lines = [f"{pad}if ({format_expr(stmt.entry_cond)}) {{"]
    for nested in stmt.if_part:
      lines.extend(format_stmt(nested, indent + 1))
    lines.append(f"{pad}}}")
    if stmt.else_part:
      lines.append(f"{pad}else {{")
      for nested in stmt.else_part:
        lines.extend(format_stmt(nested, indent + 1))
      lines.append(f"{pad}}}")
    return lines
  if isinstance(stmt, FromStmt):
    lines = [f"{pad}while (!({format_expr(stmt.exit_cond)})) {{"]
    for nested in stmt.do_part:
      lines.extend(format_stmt(nested, indent + 1))
    for nested in stmt.loop_part:
      lines.extend(format_stmt(nested, indent + 1))
    lines.append(f"{pad}}}")
    return lines
  if isinstance(stmt, IterateStmt):
    lines = [f"{pad}for ({format_type(stmt.typ)} {stmt.ident.name} = {format_expr(stmt.start_expr)}; {stmt.ident.name} <= {format_expr(stmt.end_expr)}; {stmt.ident.name} += {format_expr(stmt.step_expr)}) {{"]
    for nested in stmt.body:
      lines.extend(format_stmt(nested, indent + 1))
    lines.append(f"{pad}}}")
    return lines
  if isinstance(stmt, LocalStmt):
    lines = [f"{pad}{{", f"{pad}  {format_local_decl(stmt.enter_decl)};"]
    for nested in stmt.body:
      lines.extend(format_stmt(nested, indent + 1))
    lines.append(f"{pad}}}")
    return lines
  if isinstance(stmt, CallStmt):
    args = ", ".join(format_expr(arg) for arg in stmt.args)
    return [f"{pad}{stmt.ident.name}({args});"]
  if isinstance(stmt, UncallStmt):
    return [f"{pad}/* uncall {stmt.ident.name} not supported in generated C++ */"]
  if isinstance(stmt, PrintsStmt):
    if stmt.prints.kind == "print":
      return [f'{pad}std::cout << "{escape_cpp(stmt.prints.text or "")}";']
    if stmt.prints.kind == "printf":
      parts = render_printf(stmt.prints.text or "", [_fmt_arg(a) for a in stmt.prints.args])
      return [f"{pad}std::cout << {parts};"]
    expr = ' << " " << '.join(_fmt_arg(a) for a in stmt.prints.args)
    return [f'{pad}std::cout << {expr};']
  if isinstance(stmt, SkipStmt):
    return [f"{pad};"]
  if isinstance(stmt, AssertStmt):
    return [f"{pad}/* assert {format_expr(stmt.expr)} */"]
  if isinstance(stmt, UserErrorStmt):
    return [f'{pad}throw "{escape_cpp(stmt.message)}";']
  if isinstance(stmt, (PushStmt, PopStmt)):
    return [f"{pad}/* stack operation not supported */"]
  raise ValueError(f"Unsupported statement {type(stmt).__name__}")


def format_local_decl(decl) -> str:
  if decl.dimensions:
    dims = "".join(f"[{format_expr(dim)}]" for dim in decl.dimensions if dim is not None)
    init = f" = {format_expr(decl.init_expr)}" if decl.init_expr is not None else ""
    return f"{format_type(decl.typ)} {decl.ident.name}{dims}{init}"
  init = f" = {format_expr(decl.init_expr)}" if decl.init_expr is not None else ""
  return f"{format_type(decl.typ)} {decl.ident.name}{init}"


def format_lval(lval: Lval) -> str:
  parts = [lval.ident.name]
  for selector in lval.selectors:
    if isinstance(selector, LvalField):
      parts.append(f".{selector.ident.name}")
    elif isinstance(selector, LvalIndex):
      parts.append(f"[{format_expr(selector.expr)}]")
  return "".join(parts)


def format_expr(expr: Expr) -> str:
  if isinstance(expr, Number):
    return str(expr.value)
  if isinstance(expr, Boolean):
    return "true" if expr.value else "false"
  if isinstance(expr, LvalExpr):
    return format_lval(expr.lval)
  if isinstance(expr, UnaryExpr):
    return f"{expr.op.value}{format_expr(expr.expr)}"
  if isinstance(expr, TypeCastExpr):
    return f"(({format_type(expr.typ)}) {format_expr(expr.expr)})"
  if isinstance(expr, BinExpr):
    op = "==" if expr.op.value == "=" else expr.op.value
    return f"({format_expr(expr.left)} {op} {format_expr(expr.right)})"
  if isinstance(expr, TernaryExpr):
    return f"({format_expr(expr.cond)} ? {format_expr(expr.then_expr)} : {format_expr(expr.else_expr)})"
  if isinstance(expr, SizeExpr):
    return f"{expr.ident.name}.size()"
  if isinstance(expr, ArrayExpr):
    return "{ " + ", ".join(format_expr(item) for item in expr.items) + " }"
  if isinstance(expr, StringLiteral):
    return f'"{escape_cpp(expr.value)}"'
  if isinstance(expr, (EmptyExpr, TopExpr, NilExpr)):
    raise ValueError("Stack expressions are not supported in generated C++")
  raise ValueError(f"Unsupported expression {type(expr).__name__}")


def _fmt_arg(arg) -> str:
  if isinstance(arg, Ident):
    return arg.name
  return format_lval(arg)


def render_printf(text: str, args: list[str]) -> str:
  rendered: list[str] = []
  arg_index = 0
  i = 0
  while i < len(text):
    if text[i] == "%" and i + 1 < len(text):
      kind = text[i + 1]
      if kind == "%":
        rendered.append(f'"%"')
      elif kind in {"d", "s"}:
        rendered.append(args[arg_index])
        arg_index += 1
      i += 2
      continue
    start = i
    while i < len(text) and text[i] != "%":
      i += 1
    rendered.append(f'"{escape_cpp(text[start:i])}"')
  return " << ".join(rendered) if rendered else '""'


def escape_cpp(text: str) -> str:
  return text.replace("\\", "\\\\").replace('"', '\\"').replace("\0", "\\0").replace("\n", "\\n")
