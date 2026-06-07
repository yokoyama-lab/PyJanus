"""Janus source formatters.

`CFormatter` emits C-style (janus2026) syntax. Dialect formatters subclass it
and override only the productions whose surface syntax differs:
`format_jana2014.ProcedureFormatter` (procedure-style) and
`format_janus1982.Janus1982Formatter` (strict 1982). `formatter_for_std`
returns the right instance for a `--std` value.

The module-level `format_*` functions delegate to a default `CFormatter`
instance for backwards compatibility.
"""
from __future__ import annotations

from .ast import AncillaBlockStmt
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
from .ast import SwitchStmt
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


class CFormatter:
  """AST -> C-style (janus2026) Janus source."""

  def format_program(self, program: Program) -> str:
    blocks: list[str] = []
    blocks.extend(self.format_struct_def(struct_def) for struct_def in program.struct_defs)
    if program.main is not None:
      blocks.append(self.format_main(program.main))
    blocks.extend(self.format_proc(proc) for proc in program.procs)
    return "\n\n".join(blocks) + "\n"

  def format_struct_def(self, struct_def: StructDef) -> str:
    lines = [f"struct {struct_def.ident.name} {{"]
    for field in struct_def.fields:
      lines.append(f"    {self.format_struct_field(field)};")
    lines.append("};")
    return "\n".join(lines)

  def format_struct_field(self, field: StructField) -> str:
    dims = "".join(f"[{self.format_expr(dim) if dim is not None else ''}]" for dim in field.dimensions)
    return f"{self.format_type(field.typ)} {field.ident.name}{dims}"

  def format_main(self, main: ProcMain) -> str:
    lines = ["void main() {"]
    lines.extend(f"    {self.format_vdecl(vdecl)};" for vdecl in main.vdecls)
    lines.extend(self.format_stmt(stmt, 1) for stmt in main.stmts)
    lines.append("}")
    return "\n".join(lines)

  def format_proc(self, proc: Proc) -> str:
    params = ", ".join(self.format_vdecl(param, allow_init=False) for param in proc.params)
    lines = [f"void {proc.procname.name}({params}) {{"]
    lines.extend(self.format_stmt(stmt, 1) for stmt in proc.body)
    lines.append("}")
    return "\n".join(lines)

  def format_vdecl(self, vdecl: Vdecl, allow_init: bool = True) -> str:
    return self._format_decl(vdecl.decl_type, vdecl.typ, vdecl.ident.name, vdecl.dimensions, vdecl.init_expr if allow_init else None)

  def format_local_decl(self, decl: LocalDecl) -> str:
    init_expr = decl.init_expr
    if self._is_implicit_zero_local_init(decl):
      init_expr = None
    return self._format_decl(decl.decl_type, decl.typ, decl.ident.name, decl.dimensions, init_expr)

  def _collect_local_chain(self, stmt: LocalStmt) -> tuple[list[LocalDecl], list[LocalDecl], list] | None:
    enters: list[LocalDecl] = []
    exits: list[LocalDecl] = []
    current = stmt
    while True:
      enters.append(current.enter_decl)
      exits.append(current.exit_decl)
      if len(current.body) != 1 or not isinstance(current.body[0], LocalStmt):
        return enters, exits, current.body
      current = current.body[0]

  def _format_decl(self, decl_type: DeclType, typ: Type, ident: str, dimensions: list[Expr | None], init_expr: Expr | None) -> str:
    head = f"{DECL_PREFIX[decl_type]}{self.format_type(typ)} {ident}"
    dims = "".join(f"[{self.format_expr(dim) if dim is not None else ''}]" for dim in dimensions)
    if init_expr is None:
      return head + dims
    return f"{head}{dims} = {self.format_expr(init_expr)}"

  def _is_implicit_zero_local_init(self, decl: LocalDecl) -> bool:
    if decl.dimensions:
      return False
    expr = decl.init_expr
    if expr is None:
      return False
    if decl.typ.kind == "int" and isinstance(expr, Number) and expr.value == 0:
      return True
    if decl.typ.kind == "bool" and isinstance(expr, Boolean) and not expr.value:
      return True
    if decl.typ.kind == "stack" and isinstance(expr, NilExpr):
      return True
    return False

  def format_type(self, typ: Type) -> str:
    if typ.is_char:
      return "char"
    if typ.kind == "struct":
      return typ.name or "struct"
    if typ.kind == "int":
      return TYPE_NAMES["int"][typ.int_type.value]
    return TYPE_NAMES[typ.kind]

  def format_stmt(self, stmt, indent: int) -> str:
    pad = "    " * indent
    if isinstance(stmt, AssignStmt):
      expr_text = self.format_expr(stmt.expr)
      if isinstance(stmt.expr, TernaryExpr):
        expr_text = f"({expr_text})"
      return f"{pad}{self.format_lval(stmt.lval)} {stmt.mod_op.value} {expr_text};"
    if isinstance(stmt, IfStmt):
      lines = [f"{pad}if ({self.format_expr(stmt.entry_cond)}) {{"]
      lines.extend(self.format_stmt(s, indent + 1) for s in stmt.if_part)
      lines.append(f"{pad}}}")
      if stmt.else_part:
        lines.append(f"{pad}else {{")
        lines.extend(self.format_stmt(s, indent + 1) for s in stmt.else_part)
        lines.append(f"{pad}}}")
      lines.append(f"{pad}fi ({self.format_expr(stmt.exit_cond)});")
      return "\n".join(lines)
    if isinstance(stmt, FromStmt):
      if stmt.do_part:
        lines = [f"{pad}from ({self.format_expr(stmt.entry_cond)}) {{"]
        lines.extend(self.format_stmt(s, indent + 1) for s in stmt.do_part)
        lines.append(f"{pad}}} loop {{")
      else:
        lines = [f"{pad}from ({self.format_expr(stmt.entry_cond)}) loop {{"]
      lines.extend(self.format_stmt(s, indent + 1) for s in stmt.loop_part)
      lines.append(f"{pad}}} until ({self.format_expr(stmt.exit_cond)});")
      return "\n".join(lines)
    if isinstance(stmt, IterateStmt):
      lines = [
        f"{pad}for ({self.format_type(stmt.typ)} {stmt.ident.name} = {self.format_expr(stmt.start_expr)}; "
        f"{stmt.ident.name} < {self.format_expr(stmt.end_expr)}; "
        f"{stmt.ident.name} += {self.format_expr(stmt.step_expr)}) {{"
      ]
      lines.extend(self.format_stmt(s, indent + 1) for s in stmt.body)
      lines.append(f"{pad}}}")
      return "\n".join(lines)
    if isinstance(stmt, PushStmt):
      return f"{pad}push({self.format_expr(stmt.expr)}, {stmt.ident.name});"
    if isinstance(stmt, PopStmt):
      return f"{pad}pop({self.format_expr(stmt.expr)}, {stmt.ident.name});"
    if isinstance(stmt, LocalStmt):
      chain = self._collect_local_chain(stmt)
      assert chain is not None
      enters, exits, body = chain
      lines = [f"{pad}local {', '.join(self.format_local_decl(decl) for decl in enters)} {{"]
      lines.extend(self.format_stmt(s, indent + 1) for s in body)
      lines.append(f"{pad}}} delocal {', '.join(self.format_local_decl(decl) for decl in exits)};")
      return "\n".join(lines)
    if isinstance(stmt, BareLocalStmt):
      # Crossing local: the body statements are siblings in the source.
      lines = [f"{pad}local {self.format_local_decl(stmt.decl)};"]
      lines.extend(self.format_stmt(s, indent) for s in stmt.body)
      return "\n".join(lines)
    if isinstance(stmt, BareDelocalStmt):
      return f"{pad}delocal {self.format_local_decl(stmt.decl)};"
    if isinstance(stmt, AncillaBlockStmt):
      decls = ", ".join(self.format_local_decl(decl) for decl in stmt.decls)
      lines = [f"{pad}ancilla ({decls}) {{"]
      lines.extend(self.format_stmt(s, indent + 1) for s in stmt.body)
      lines.append(f"{pad}}};")
      return "\n".join(lines)
    if isinstance(stmt, SwitchStmt):
      lines = [f"{pad}switch ({self.format_expr(stmt.expr)}) {{"]
      for case in stmt.cases:
        lines.append(f"{pad}    case {self.format_expr(case.value)}:")
        lines.extend(self.format_stmt(s, indent + 2) for s in case.body)
        lines.append(f"{pad}        break;")
      if stmt.default_part:
        lines.append(f"{pad}    default:")
        lines.extend(self.format_stmt(s, indent + 2) for s in stmt.default_part)
        lines.append(f"{pad}        break;")
      lines.append(f"{pad}}} switch ({self.format_expr(stmt.exit_expr)});")
      return "\n".join(lines)
    if isinstance(stmt, CallStmt):
      ext = "external " if stmt.external else ""
      args = ", ".join(self.format_expr(arg) for arg in stmt.args)
      return f"{pad}call {ext}{stmt.ident.name}({args});"
    if isinstance(stmt, UncallStmt):
      ext = "external " if stmt.external else ""
      args = ", ".join(self.format_expr(arg) for arg in stmt.args)
      return f"{pad}uncall {ext}{stmt.ident.name}({args});"
    if isinstance(stmt, UserErrorStmt):
      return f'{pad}error("{stmt.message}");'
    if isinstance(stmt, SwapStmt):
      return f"{pad}{self.format_lval(stmt.left)} <=> {self.format_lval(stmt.right)};"
    if isinstance(stmt, PrintsStmt):
      kind = stmt.prints.kind
      if kind in {"printf", "scanf"}:
        args = ", ".join(self._format_print_arg(a) for a in stmt.prints.args)
        fmt = self._escape(stmt.prints.text or "")
        if args:
          return f'{pad}{kind}("{fmt}", {args});'
        return f'{pad}{kind}("{fmt}");'
      if kind == "print":
        return f'{pad}print("{self._escape(stmt.prints.text or "")}");'
      if kind == "show":
        args = ", ".join(self._format_print_arg(a) for a in stmt.prints.args)
        return f"{pad}show({args});"
      if kind == "read":
        return f"{pad}read {self._format_print_arg(stmt.prints.args[0])};"
      if kind == "write":
        return f"{pad}write {self._format_print_arg(stmt.prints.args[0])};"
      raise TypeError(f"Unsupported print form for canonical formatter: {kind!r}")
    if isinstance(stmt, SkipStmt):
      return f"{pad}skip;"
    if isinstance(stmt, AssertStmt):
      return f"{pad}assert {self.format_expr(stmt.expr)};"
    raise TypeError(f"Unsupported stmt: {type(stmt)!r}")

  def _format_print_arg(self, arg) -> str:
    from .ast import Ident
    if isinstance(arg, Ident):
      return arg.name
    return self.format_lval(arg)

  def format_lval(self, lval: Lval) -> str:
    parts = [lval.ident.name]
    for selector in lval.selectors:
      if isinstance(selector, LvalField):
        parts.append(f".{selector.ident.name}")
      elif isinstance(selector, LvalIndex):
        parts.append(f"[{self.format_expr(selector.expr)}]")
    return "".join(parts)

  def format_bin_op(self, op: BinOpKind) -> str:
    return op.value

  def format_expr(self, expr: Expr, parent_prec: int = -1) -> str:
    if isinstance(expr, Number):
      return str(expr.value)
    if isinstance(expr, Boolean):
      return "true" if expr.value else "false"
    if isinstance(expr, LvalExpr):
      return self.format_lval(expr.lval)
    if isinstance(expr, EmptyExpr):
      return f"empty({expr.ident.name})"
    if isinstance(expr, TopExpr):
      return f"top({expr.ident.name})"
    if isinstance(expr, SizeExpr):
      return f"size({expr.ident.name})"
    if isinstance(expr, NilExpr):
      return "nil"
    if isinstance(expr, ArrayExpr):
      return "{ " + ", ".join(self.format_expr(item) for item in expr.items) + " }"
    if isinstance(expr, StringLiteral):
      return f'"{self._escape(expr.value)}"'
    if isinstance(expr, UnaryExpr):
      text = expr.op.value + self.format_expr(expr.expr, UNARY_PREC)
      return f"({text})" if parent_prec > UNARY_PREC else text
    if isinstance(expr, TypeCastExpr):
      text = f"({self.format_type(expr.typ)}) {self.format_expr(expr.expr, CAST_PREC)}"
      return f"({text})" if parent_prec > CAST_PREC else text
    if isinstance(expr, BinExpr):
      prec = BIN_PREC[expr.op]
      text = f"{self.format_expr(expr.left, prec)} {self.format_bin_op(expr.op)} {self.format_expr(expr.right, prec)}"
      return f"({text})" if parent_prec > prec else text
    if isinstance(expr, TernaryExpr):
      text = f"{self.format_expr(expr.cond, TERNARY_PREC)} ? {self.format_expr(expr.then_expr, TERNARY_PREC)} : {self.format_expr(expr.else_expr, TERNARY_PREC)}"
      return f"({text})" if parent_prec > TERNARY_PREC else text
    raise TypeError(f"Unsupported expr: {type(expr)!r}")

  def _escape(self, text: str) -> str:
    return text.replace("\\", "\\\\").replace('"', '\\"').replace("\0", "\\u0000").replace("\n", "\\n")


def formatter_for_std(std: str) -> CFormatter:
  """Return the source formatter matching a `--std` dialect value."""
  if std == "janus2026":
    return CFormatter()
  if std == "janus1982":
    from .format_janus1982 import Janus1982Formatter
    return Janus1982Formatter()
  from .format_jana2014 import ProcedureFormatter
  return ProcedureFormatter()


# ── Backwards-compatible module-level API (C-style) ───────────────────────
_DEFAULT = CFormatter()


def format_program(program: Program) -> str:
  return _DEFAULT.format_program(program)


def format_struct_def(struct_def: StructDef) -> str:
  return _DEFAULT.format_struct_def(struct_def)


def format_struct_field(field: StructField) -> str:
  return _DEFAULT.format_struct_field(field)


def format_main(main: ProcMain) -> str:
  return _DEFAULT.format_main(main)


def format_proc(proc: Proc) -> str:
  return _DEFAULT.format_proc(proc)


def format_vdecl(vdecl: Vdecl, allow_init: bool = True) -> str:
  return _DEFAULT.format_vdecl(vdecl, allow_init)


def format_local_decl(decl: LocalDecl) -> str:
  return _DEFAULT.format_local_decl(decl)


def format_type(typ: Type) -> str:
  return _DEFAULT.format_type(typ)


def format_stmt(stmt, indent: int) -> str:
  return _DEFAULT.format_stmt(stmt, indent)


def format_lval(lval: Lval) -> str:
  return _DEFAULT.format_lval(lval)


def format_expr(expr: Expr, parent_prec: int = -1) -> str:
  return _DEFAULT.format_expr(expr, parent_prec)


def _escape(text: str) -> str:
  return _DEFAULT._escape(text)
