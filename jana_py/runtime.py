from __future__ import annotations
from dataclasses import dataclass
import math
import sys

from .ast import ArrayExpr
from .ast import AssertStmt
from .ast import AssignStmt
from .ast import BareDelocalStmt
from .ast import BareLocalStmt
from .ast import BinExpr
from .ast import BinOpKind
from .ast import DeclType
from .ast import Boolean
from .ast import CallStmt
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
from .ast import SourcePos
from .ast import StringLiteral
from .ast import StructDef
from .ast import StructField
from .ast import SwapStmt
from .ast import SwitchStmt
from .ast import TernaryExpr
from .ast import TopExpr
from .ast import TypeCastExpr
from .ast import UnaryExpr
from .ast import UnaryOpKind
from .ast import UncallStmt
from .ast import UserErrorStmt
from .ast import Vdecl
from .errors import JanaError
from .format import format_expr
from .format import format_local_decl
from .format import format_lval
from .format import format_stmt
from .invert import invert_stmt
from .invert import invert_stmts


class Cell:
  def __init__(
    self,
    value,
    shape: list[int] | None = None,
    kind: str = "int",
    int_type: IntType | None = None,
    writable: bool = True,
    is_char: bool = False,
    struct_name: str | None = None,
    elem_kind: str | None = None,
    elem_int_type: IntType | None = None,
    elem_is_char: bool = False,
    elem_struct_name: str | None = None,
  ):
    self.value = value
    self.shape = shape
    self.kind = kind
    self.int_type = int_type
    self.writable = writable
    self.is_char = is_char
    self.struct_name = struct_name
    self.elem_kind = elem_kind
    self.elem_int_type = elem_int_type
    self.elem_is_char = elem_is_char
    self.elem_struct_name = elem_struct_name


@dataclass
class Frame:
  vars: dict[str, Cell]


class Runtime:
  _BOUNDARY_MAJOR_PREFIX = "boundary_major:"
  _BOUNDARY_MINOR = "boundary_minor"
  _DEBUGGER_HELP = (
    "Usage of the jana debugger\n"
    "IMPORTANT: all breakpoints will be added at the beginning of a line and only on statements.\n"
    "options:\n"
    "  a[dd] N*     adds zero or more breakpoint at lines N (space separated) \n"
    "  d[elete] N*  deletes zero or more breakpoints at lines N (space separated)\n"
    "  b[ackward]   reverse execution to previous breakpoint\n"
    "  f[orward]    execution to next breakpoint in forward direction\n"
    "  n[ext]       step to next statement\n"
    "  r            step to previous statement\n"
    "  h[elp]       this menu\n"
    "  l[ine]       print current line\n"
    "  p[rint] V*   prints the content of variables V (space separated)\n"
    "  s[tore]      prints entire store\n"
    "  q[uit]       quit the debugger (ends termination)"
  )

  def __init__(
    self,
    program: Program,
    mod_bits: int | None = None,
    mod_prime: int | None = None,
    debug: bool = False,
    debug_on_error: bool = False,
    std: str = "janus2026",
  ):
    self.program = program
    self.std = std
    self.procs = {proc.procname.name: proc for proc in program.procs}
    self.struct_defs = {struct_def.ident.name: struct_def for struct_def in program.struct_defs}
    self.stdout: list[str] = []
    self.main_vdecls: list[Vdecl] = []
    self.mod_bits = mod_bits
    self.mod_prime = mod_prime
    self.debug = debug
    self.debug_on_error = debug_on_error
    self.breakpoints: set[int] = set()
    self.step_debugging = False
    self._step_completed = False
    self.current_line = 0
    self.executed_stmts: list[tuple[int, object]] = []
    self._root_frame: Frame | None = None
    self._skip_next_stmt = False
    self._first_stmt_line = 0
    self._halt_execution = False
    self._at_end_break = False
    self._current_boundary_line: int | None = None
    self._legacy_io_warned: set[str] = set()

  def _normalize_int(self, value: int, int_type: IntType | None) -> int:
    if int_type in {IntType.I8, IntType.I16, IntType.I32, IntType.I64}:
      bits = {IntType.I8: 8, IntType.I16: 16, IntType.I32: 32, IntType.I64: 64}[int_type]
      modulus = 1 << bits
      return ((int(value) + (1 << (bits - 1))) % modulus) - (1 << (bits - 1))
    if int_type in {IntType.U8, IntType.U16, IntType.U32, IntType.U64}:
      bits = {IntType.U8: 8, IntType.U16: 16, IntType.U32: 32, IntType.U64: 64}[int_type]
      return int(value) % (1 << bits)
    if self.mod_prime is not None:
      return int(value) % self.mod_prime
    if self.mod_bits is not None:
      modulus = 1 << self.mod_bits
      return ((int(value) + (1 << (self.mod_bits - 1))) % modulus) - (1 << (self.mod_bits - 1))
    return int(value)

  def _stmt_detail(self, stmt) -> str:
    return "In statement:\n    " + format_stmt(stmt, 0).replace("\n", "\n    ")

  def run(self, show_store: bool = False) -> str:
    if self.program.main is None:
      raise JanaError(SourcePos("", 0, 0), "No main procedure has been defined")
    frame = Frame(vars={})
    self._root_frame = frame
    self.main_vdecls = list(self.program.main.vdecls)
    self._first_stmt_line = self.program.main.stmts[0].pos.line if self.program.main.stmts else self.program.main.pos.line
    self._init_vdecls(frame, self.program.main.vdecls)
    try:
      if self.debug:
        print('Welcome to the Jana debugger. Type "h[elp]" for the help menu.')
        self._make_break(frame)
      self._exec_block(frame, self.program.main.stmts)
    except JanaError as err:
      if self.debug or self.debug_on_error:
        print(f"[Break: ERROR (line {err.pos.line})]")
        print(str(err))
        self.current_line = err.pos.line
        self._make_break(frame)
        raise SystemExit(1)
      raise
    if self.debug and self.program.main.stmts and not self._halt_execution:
      last_line = self.program.main.stmts[-1].pos.line
      print(f"[Break at END (_after_ line {last_line})]")
      self.current_line = last_line
      self._at_end_break = True
      self._make_break(frame)
    store = self._format_store(frame)
    return "".join(self.stdout) + store + ("\n" if store else "")

  def _init_vdecls(self, frame: Frame, vdecls: list[Vdecl]) -> None:
    for vdecl in vdecls:
      value, shape, kind, int_type = self._initial_value(frame, vdecl)
      elem_kind, elem_int_type, elem_is_char, elem_struct_name = self._type_cell_metadata(vdecl.typ)
      frame.vars[vdecl.ident.name] = Cell(
        value,
        shape=shape,
        kind=kind,
        int_type=int_type,
        writable=vdecl.decl_type.value != "Constant",
        is_char=vdecl.typ.is_char,
        struct_name=vdecl.typ.name if vdecl.typ.kind == "struct" else None,
        elem_kind=elem_kind if shape is not None else None,
        elem_int_type=elem_int_type if shape is not None else None,
        elem_is_char=elem_is_char if shape is not None else False,
        elem_struct_name=elem_struct_name if shape is not None else None,
      )

  def _initial_value(self, frame: Frame, vdecl: Vdecl):
    int_type = vdecl.typ.int_type if vdecl.typ.kind == "int" else None
    if vdecl.dimensions:
      return self._initial_array_value(frame, vdecl.pos, vdecl.ident.name, vdecl.dimensions, vdecl.init_expr, vdecl.typ)
    if vdecl.typ.kind == "struct":
      if vdecl.init_expr is not None:
        return self._init_struct_from_expr(frame, vdecl.typ, vdecl.pos, vdecl.init_expr), None, "struct", None
      return self._initial_struct_value(vdecl.typ, vdecl.pos), None, "struct", None
    if vdecl.typ.kind == "bool":
      return (False if vdecl.init_expr is None else bool(self._eval_expr(frame, vdecl.init_expr))), None, "bool", None
    if vdecl.typ.kind == "stack":
      return ([] if vdecl.init_expr is None else self._eval_expr(frame, vdecl.init_expr)), None, "stack", None
    initial = 0 if vdecl.init_expr is None else self._eval_expr(frame, vdecl.init_expr)
    return self._normalize_int(initial, int_type), None, "int", int_type

  def _initial_struct_value(self, typ, pos: SourcePos) -> dict[str, object]:
    struct_name = typ.name
    if struct_name is None or struct_name not in self.struct_defs:
      raise JanaError(pos, f"Unknown struct type `{struct_name or typ.kind}`")
    struct_def = self.struct_defs[struct_name]
    value: dict[str, object] = {}
    for field in struct_def.fields:
      value[field.ident.name] = self._zero_struct_field(field)
    return value

  def _init_struct_from_expr(self, frame: Frame, typ, pos: SourcePos, expr: Expr) -> dict[str, object]:
    """Initialize a struct from a C-style initializer like {1, 2}."""
    struct_name = typ.name
    if struct_name is None or struct_name not in self.struct_defs:
      raise JanaError(pos, f"Unknown struct type `{struct_name or typ.kind}`")
    struct_def = self.struct_defs[struct_name]
    if not isinstance(expr, ArrayExpr):
      raise JanaError(pos, f"Struct initializer must be a brace-enclosed list")
    items = expr.items
    if len(items) > len(struct_def.fields):
      raise JanaError(pos, f"Too many initializers for struct `{struct_name}' (expected {len(struct_def.fields)}, got {len(items)})")
    value: dict[str, object] = {}
    for i, field in enumerate(struct_def.fields):
      if i < len(items):
        value[field.ident.name] = self._init_field_from_expr(frame, field, items[i])
      else:
        value[field.ident.name] = self._zero_struct_field(field)
    return value

  def _init_field_from_expr(self, frame: Frame, field: StructField, expr: Expr):
    """Initialize a single struct field from an expression."""
    if field.dimensions:
      flat = self._flatten_array(frame, expr)
      sizes = self._static_array_sizes(field.dimensions, field.ident.name, field.pos)
      flat_size = 1
      for s in sizes:
        flat_size *= s
      if field.typ.kind == "struct":
        result = []
        if isinstance(expr, ArrayExpr):
          for item in expr.items:
            result.append(self._init_struct_from_expr(frame, field.typ, field.pos, item))
        while len(result) < flat_size:
          result.append(self._zero_value_for_type(field.typ, field.pos))
        return result
      if len(flat) < flat_size:
        flat.extend(self._zero_value_for_type(field.typ, field.pos) for _ in range(flat_size - len(flat)))
      return flat
    if field.typ.kind == "struct":
      return self._init_struct_from_expr(frame, field.typ, field.pos, expr)
    if field.typ.kind == "bool":
      return bool(self._eval_expr(frame, expr))
    if field.typ.kind == "stack":
      return self._eval_expr(frame, expr)
    return self._normalize_int(self._eval_expr(frame, expr), field.typ.int_type)

  def _zero_struct_field(self, field: StructField):
    if field.dimensions:
      return self._zero_struct_field_array(field)
    if field.typ.kind == "struct":
      return self._initial_struct_value(field.typ, field.pos)
    if field.typ.kind == "bool":
      return False
    if field.typ.kind == "stack":
      return []
    if field.typ.kind == "int":
      return self._normalize_int(0, field.typ.int_type)
    raise JanaError(field.pos, f"Unsupported struct field type `{field.typ.kind}`")

  def _zero_struct_field_array(self, field: StructField):
    sizes = self._static_array_sizes(field.dimensions, field.ident.name, field.pos)
    flat_size = 1
    for size in sizes:
      flat_size *= size
    return [self._zero_value_for_type(field.typ, field.pos) for _ in range(flat_size)]

  def _type_cell_metadata(self, typ) -> tuple[str, IntType | None, bool, str | None]:
    if typ.kind == "struct":
      return "struct", None, False, typ.name
    if typ.kind == "bool":
      return "bool", None, False, None
    if typ.kind == "stack":
      return "stack", None, False, None
    return "int", typ.int_type, typ.is_char, None

  def _zero_value_for_type(self, typ, pos: SourcePos):
    if typ.kind == "struct":
      return self._initial_struct_value(typ, pos)
    if typ.kind == "bool":
      return False
    if typ.kind == "stack":
      return []
    return self._normalize_int(0, typ.int_type)

  def _static_array_sizes(self, dimensions: list[Expr | None], name: str, pos: SourcePos) -> list[int]:
    sizes = [self._eval_expr(Frame(vars={}), dim) if dim is not None else None for dim in dimensions]
    if any(size is None for size in sizes):
      raise JanaError(pos, f"Array size missing for variable `{name}'")
    out: list[int] = []
    for size in sizes:
      if size < 1:
        raise JanaError(pos, "Array size must be greater than or equal to one")
      out.append(int(size))
    return out

  def _initial_array_value(
    self,
    frame: Frame,
    pos: SourcePos,
    name: str,
    dimensions: list[Expr | None],
    init_expr: Expr | None,
    typ,
  ):
    int_type = typ.int_type if typ.kind == "int" else None
    is_char = typ.is_char
    if is_char and len(dimensions) != 1:
      raise JanaError(pos, f"Character arrays must be one-dimensional for variable `{name}'")
    inferred_size: int | None = None
    if is_char and isinstance(init_expr, StringLiteral):
      inferred_size = len(self._char_literal_bytes(pos, init_expr.value))
    elif isinstance(init_expr, ArrayExpr):
      inferred_size = len(init_expr.items)
    sizes = [self._eval_expr(frame, dim) if dim is not None else None for dim in dimensions]
    if any(size is None for size in sizes):
      if len(dimensions) == 1 and sizes == [None] and inferred_size is not None:
        sizes = [inferred_size]
      else:
        raise JanaError(pos, f"Array size missing for variable `{name}'")
    flat_size = 1
    for size in sizes:
      if size < 1:
        raise JanaError(pos, "Array size must be greater than or equal to one")
      flat_size *= size
    if init_expr is None:
      return [self._zero_value_for_type(typ, pos) for _ in range(flat_size)], [int(size) for size in sizes], "array", int_type
    if typ.kind == "struct":
      if not isinstance(init_expr, ArrayExpr):
        raise JanaError(pos, f"Struct array initializer must be a brace-enclosed list")
      flat = []
      for item in init_expr.items:
        flat.append(self._init_struct_from_expr(frame, typ, pos, item))
      if len(flat) < flat_size:
        flat.extend(self._zero_value_for_type(typ, pos) for _ in range(flat_size - len(flat)))
      return flat, [int(size) for size in sizes], "array", int_type
    if typ.kind == "bool":
      flat = [bool(item) for item in self._flatten_array(frame, init_expr)]
    elif typ.kind == "stack":
      flat = self._flatten_array(frame, init_expr)
    else:
      flat = self._flatten_initializer(frame, pos, init_expr, int_type, is_char)
    if len(flat) > flat_size:
      raise JanaError(pos, f"Initializer is too large for variable `{name}'")
    if len(flat) < flat_size:
      flat.extend(self._zero_value_for_type(typ, pos) for _ in range(flat_size - len(flat)))
    return flat, [int(size) for size in sizes], "array", int_type

  def _flatten_array(self, frame: Frame, expr: Expr):
    if isinstance(expr, ArrayExpr):
      values = []
      for item in expr.items:
        if isinstance(item, ArrayExpr):
          values.extend(self._flatten_array(frame, item))
        else:
          values.append(self._eval_expr(frame, item))
      return values
    return [self._eval_expr(frame, expr)]

  def _flatten_initializer(self, frame: Frame, pos: SourcePos, expr: Expr, int_type: IntType | None, is_char: bool) -> list[int]:
    if isinstance(expr, StringLiteral):
      if not is_char:
        raise JanaError(pos, "String literals can only initialize char arrays")
      return [self._normalize_int(item, int_type) for item in self._char_literal_bytes(pos, expr.value)]
    return [self._normalize_int(item, int_type) for item in self._flatten_array(frame, expr)]

  def _char_literal_bytes(self, pos: SourcePos, text: str) -> list[int]:
    values: list[int] = []
    for char in text:
      codepoint = ord(char)
      if codepoint > 0xFF:
        raise JanaError(pos, f"Character literal out of range for char array: {char!r}")
      values.append(codepoint)
    values.append(0)
    return values

  def _exec_block(
    self,
    frame: Frame,
    stmts: list,
    record_stmt: bool = True,
    record_nested: bool = False,
    allow_break: bool = True,
  ) -> None:
    for stmt in stmts:
      if self._halt_execution:
        return
      self._exec_stmt_impl(frame, stmt, allow_break=allow_break, record_stmt=record_stmt, record_nested=record_nested)

  def _exec_stmt(self, frame: Frame, stmt) -> None:
    self._exec_stmt_impl(frame, stmt, allow_break=True, record_stmt=True, record_nested=False)

  def _push_boundary(self, line: int, stmt_type: str) -> None:
    self.executed_stmts.append((line, f"{self._BOUNDARY_MAJOR_PREFIX}{stmt_type}"))

  def _push_minor_boundary(self, line: int) -> None:
    self.executed_stmts.append((line, self._BOUNDARY_MINOR))

  def _is_boundary_marker(self, marker: object) -> bool:
    return self._is_major_boundary(marker) or marker == self._BOUNDARY_MINOR

  def _is_major_boundary(self, marker: object) -> bool:
    return isinstance(marker, str) and marker.startswith(self._BOUNDARY_MAJOR_PREFIX)

  def _boundary_stmt_type(self, marker: object) -> str | None:
    if self._is_major_boundary(marker):
      return str(marker)[len(self._BOUNDARY_MAJOR_PREFIX):]
    return None

  def _arm_step_for_nested_entry(self) -> None:
    if self.debug and self.step_debugging and not self._step_completed:
      self._step_completed = True

  def _clear_current_boundary(self) -> None:
    self._current_boundary_line = None

  def _reset_debug_step_state(self) -> None:
    self.step_debugging = False
    self._step_completed = False

  def _prepare_forward_debug_command(self) -> None:
    self.step_debugging = True
    self._at_end_break = False
    self._step_completed = False

  def _clear_end_break(self) -> None:
    self._at_end_break = False

  def _print_line_break(self, line: int) -> None:
    self.current_line = line
    print(f"[Break at line {line}] ")

  def _print_begin_break(self) -> None:
    self.current_line = self._first_stmt_line
    print(f"[Break at BEGIN (line {self._first_stmt_line})]")

  def _exec_stmt_impl(self, frame: Frame, stmt, allow_break: bool, record_stmt: bool, record_nested: bool = False) -> None:
    try:
      if record_nested and not record_stmt:
        self._push_minor_boundary(stmt.pos.line)
      if allow_break:
        self._maybe_break(stmt.pos, frame)
      if self._skip_next_stmt:
        self._skip_next_stmt = False
        return
      if isinstance(stmt, AssignStmt):
        self._check_alias_assign(frame, stmt)
        cell = self._resolve_lval(frame, stmt.lval)
        if not cell.writable:
          raise JanaError(stmt.pos, "Updating constant", contextual=True)
        
        if isinstance(stmt.expr, ArrayExpr):
          # Bulk array initialization
          if cell.shape is None:
            raise JanaError(stmt.pos, "Assigning array literal to scalar")
          values = [self._eval_expr(frame, item) for item in stmt.expr.items]
          if len(values) > len(cell.value):
            raise JanaError(stmt.pos, f"Array literal too large (got {len(values)}, max {len(cell.value)})")
          for i, v in enumerate(values):
            if stmt.mod_op.value == "+=":
              cell.value[i] = self._normalize_int(cell.value[i] + v, cell.elem_int_type)
            elif stmt.mod_op.value == "-=":
              cell.value[i] = self._normalize_int(cell.value[i] - v, cell.elem_int_type)
            elif stmt.mod_op.value == "*=":
              if v == 0:
                raise JanaError(stmt.pos, "Multiplication by zero")
              if cell.value[i] == 0:
                raise JanaError(stmt.pos, "Multiplicand is zero")
              cell.value[i] = self._normalize_int(cell.value[i] * v, cell.elem_int_type)
            elif stmt.mod_op.value == "/=":
              if v == 0:
                raise JanaError(stmt.pos, "Division by zero")
              if cell.value[i] % v != 0:
                raise JanaError(stmt.pos, f"Division remains: {cell.value[i]} % {v} != 0")
              cell.value[i] = self._normalize_int(cell.value[i] // v, cell.elem_int_type)
            else:
              cell.value[i] = self._normalize_int(cell.value[i] ^ v, cell.elem_int_type)
        else:
          value = self._eval_expr(frame, stmt.expr)
          self._check_assign_compat(stmt.pos, cell, value)
          if stmt.mod_op.value == "+=":
            cell.value = self._normalize_int(cell.value + value, cell.int_type)
          elif stmt.mod_op.value == "-=":
            cell.value = self._normalize_int(cell.value - value, cell.int_type)
          elif stmt.mod_op.value == "*=":
            if value == 0:
              raise JanaError(stmt.pos, "Multiplication by zero")
            if cell.value == 0:
              raise JanaError(stmt.pos, "Multiplicand is zero")
            cell.value = self._normalize_int(cell.value * value, cell.int_type)
          elif stmt.mod_op.value == "/=":
            if value == 0:
              raise JanaError(stmt.pos, "Division by zero")
            if cell.value % value != 0:
              raise JanaError(stmt.pos, f"Division remains: {cell.value} % {value} != 0")
            cell.value = self._normalize_int(cell.value // value, cell.int_type)
          else:
            cell.value = self._normalize_int(cell.value ^ value, cell.int_type)
        if record_stmt and self._is_recordable_stmt(stmt):
          self.executed_stmts.append((stmt.pos.line, stmt))
        return
      if isinstance(stmt, SwapStmt):
        self._check_alias_swap(frame, stmt)
        self._check_swap_compat(frame, stmt)
        left = self._resolve_lval(frame, stmt.left)
        right = self._resolve_lval(frame, stmt.right)
        if not left.writable or not right.writable:
          raise JanaError(stmt.pos, "Updating constant", contextual=True)
        left.value, right.value = right.value, left.value
        if record_stmt and self._is_recordable_stmt(stmt):
          self.executed_stmts.append((stmt.pos.line, stmt))
        return
      if isinstance(stmt, IfStmt):
        if record_stmt:
          self._push_boundary(stmt.pos.line, "IfStmt")
        self._arm_step_for_nested_entry()
        cond = self._truthy(self._eval_expr(frame, stmt.entry_cond))
        branch = stmt.if_part if cond else stmt.else_part
        self._exec_block(frame, branch, record_stmt=(record_stmt or record_nested), record_nested=record_nested)
        exit_cond = self._truthy(self._eval_expr(frame, stmt.exit_cond))
        if exit_cond != cond:
          expect = "true" if cond else "false"
          raise JanaError(stmt.exit_cond.pos, f"Assertion failed: should be {expect}", contextual=True)
        return
      if isinstance(stmt, SwitchStmt):
        if record_stmt:
          self._push_boundary(stmt.pos.line, "SwitchStmt")
        self._arm_step_for_nested_entry()
        val = self._eval_expr(frame, stmt.expr)
        branch = stmt.default_part
        matched = False
        for case in stmt.cases:
          case_val = self._eval_expr(frame, case.value)
          if val == case_val:
            branch = case.body
            matched = True
            break
        self._exec_block(frame, branch, record_stmt=(record_stmt or record_nested), record_nested=record_nested)
        exit_val = self._eval_expr(frame, stmt.exit_expr)
        if exit_val != val:
          raise JanaError(stmt.exit_expr.pos, f"Assertion failed: should be {val}", contextual=True)
        return
      if isinstance(stmt, AncillaBlockStmt):
        if record_stmt:
          self._push_boundary(stmt.pos.line, "AncillaBlockStmt")
        self._arm_step_for_nested_entry()
        self._exec_ancilla_block(frame, stmt, record_stmt=(record_stmt or record_nested), record_nested=record_nested)
        return
      if isinstance(stmt, FromStmt):
        if record_stmt:
          self._push_boundary(stmt.pos.line, "FromStmt")
        self._arm_step_for_nested_entry()
        if not self._truthy(self._eval_expr(frame, stmt.entry_cond)):
          raise JanaError(stmt.entry_cond.pos, "Assertion failed: should be true", contextual=True)
        self._exec_from_forward(frame, stmt, record_stmt=(record_stmt or record_nested), record_nested=record_nested)
        return
      if isinstance(stmt, IterateStmt):
        self._exec_iterate(frame, stmt, record_stmt=(record_stmt or record_nested), record_nested=record_nested)
        return
      if isinstance(stmt, LocalStmt):
        if record_stmt:
          self._push_boundary(stmt.pos.line, "LocalStmt")
        self._arm_step_for_nested_entry()
        self._exec_local(frame, stmt, record_stmt=(record_stmt or record_nested), record_nested=record_nested)
        return
      if isinstance(stmt, BareLocalStmt):
        self._exec_bare_local(frame, stmt, record_stmt=(record_stmt or record_nested), record_nested=record_nested)
        return
      if isinstance(stmt, BareDelocalStmt):
        self._exec_bare_delocal(frame, stmt)
        return
      if isinstance(stmt, CallStmt):
        if record_stmt:
          self._push_boundary(stmt.pos.line, "CallStmt")
        self._arm_step_for_nested_entry()
        self._call_proc(frame, stmt.ident.name, stmt.args, stmt.pos, record_stmt=(record_stmt or record_nested), record_nested=record_nested)
        return
      if isinstance(stmt, UncallStmt):
        if record_stmt:
          self._push_boundary(stmt.pos.line, "UncallStmt")
        self._arm_step_for_nested_entry()
        self._uncall_proc(frame, stmt.ident.name, stmt.args, stmt.pos, record_stmt=(record_stmt or record_nested), record_nested=record_nested)
        return
      if isinstance(stmt, PrintsStmt):
        self._exec_print(frame, stmt)
        return
      if isinstance(stmt, SkipStmt):
        return
      if isinstance(stmt, AssertStmt):
        if not self._truthy(self._eval_expr(frame, stmt.expr)):
          raise JanaError(stmt.expr.pos, "Assertion failed: should be true", contextual=True)
        return
      if isinstance(stmt, UserErrorStmt):
        raise JanaError(stmt.pos, f"User error: {stmt.message}")
      if isinstance(stmt, PushStmt):
        value = self._eval_expr(frame, stmt.expr)
        stack_cell = self._resolve_var(frame, stmt.ident.name)
        if stack_cell.kind != "stack":
          raise JanaError(stmt.pos, "Couldn't match expected type `stack'\n            with actual type `int`", contextual=True)
        if not stack_cell.writable:
          raise JanaError(stmt.pos, "Updating constant", contextual=True)
        stack_cell.value.insert(0, value)
        if isinstance(stmt.expr, LvalExpr):
          self._resolve_lval(frame, stmt.expr.lval).value = 0
        if record_stmt and self._is_recordable_stmt(stmt):
          self.executed_stmts.append((stmt.pos.line, stmt))
        return
      if isinstance(stmt, PopStmt):
        stack_cell = self._resolve_var(frame, stmt.ident.name)
        if stack_cell.kind != "stack":
          raise JanaError(stmt.pos, "Couldn't match expected type `stack'\n            with actual type `int`", contextual=True)
        if not stack_cell.writable:
          raise JanaError(stmt.pos, "Updating constant", contextual=True)
        if not stack_cell.value:
          raise JanaError(stmt.pos, "Can't pop from empty stack", contextual=True)
        target = self._resolve_lval(frame, Lval(stmt.expr.lval.ident, list(stmt.expr.lval.selectors))) if isinstance(stmt.expr, LvalExpr) else None
        if target is None:
          raise JanaError(stmt.pos, "Only l-values are supported for pop")
        if not target.writable:
          raise JanaError(stmt.pos, "Updating constant", contextual=True)
        if target.value != 0:
          raise JanaError(stmt.pos, f"Can't pop to non-zero variable `{stmt.expr.lval.ident.name}'", contextual=True)
        value = stack_cell.value.pop(0)
        target.value = value
        if record_stmt and self._is_recordable_stmt(stmt):
          self.executed_stmts.append((stmt.pos.line, stmt))
        return
      raise JanaError(stmt.pos, f"Unsupported statement {type(stmt).__name__}")
    except JanaError as err:
      raise self._with_stmt_context(err, stmt, frame)
    finally:
      if self.debug and self.step_debugging and record_stmt and self._is_recordable_stmt(stmt):
        self._step_completed = True

  def _is_recordable_stmt(self, stmt) -> bool:
    return isinstance(
      stmt,
      (
        AssignStmt,
        SwapStmt,
        PushStmt,
        PopStmt,
      ),
    )

  def _maybe_break(self, pos: SourcePos, frame: Frame) -> None:
    if not self.debug:
      return
    line = pos.line
    self.current_line = line
    if self.step_debugging and self._step_completed:
      self._clear_end_break()
      self._reset_debug_step_state()
      self._clear_current_boundary()
      self._print_line_break(line)
      self._make_break(frame)
      return
    if line in self.breakpoints:
      self._clear_end_break()
      self._clear_current_boundary()
      self._print_line_break(line)
      self._make_break(frame)

  def _make_break(self, frame: Frame) -> None:
    while True:
      print("> ", end="", flush=True)
      raw = sys.stdin.readline()
      if raw == "":
        self.step_debugging = False
        return
      parts = raw.strip().split()
      if not parts:
        continue
      cmd = parts[0]
      args = parts[1:]
      if cmd in {"a", "add"}:
        for item in args:
          try:
            self.breakpoints.add(int(item))
          except ValueError:
            pass
        continue
      if cmd in {"d", "delete"}:
        for item in args:
          try:
            self.breakpoints.discard(int(item))
          except ValueError:
            pass
        continue
      if cmd in {"n", "next", "r"}:
        if cmd == "r" and self._root_frame is not None:
          if not self.executed_stmts:
            self._halt_execution = True
            return
          if self._at_end_break:
            self._execute_backward_to_boundary(self._root_frame)
            self._clear_end_break()
            self._reset_debug_step_state()
            continue
          self._execute_backward_step(self._root_frame)
          self._clear_end_break()
          self._reset_debug_step_state()
          continue
        self._prepare_forward_debug_command()
        return
      if cmd in {"f", "forward", "b", "backward"}:
        if cmd in {"b", "backward"} and self._root_frame is not None:
          if not self.executed_stmts:
            self._halt_execution = True
            return
          self._execute_backward_to_breakpoint(self._root_frame)
          self._clear_end_break()
          self._reset_debug_step_state()
          continue
        self._reset_debug_step_state()
        return
      if cmd in {"l", "line"}:
        print(f"[Current line is {self.current_line}]")
        continue
      if cmd in {"p", "print"}:
        for name in args:
          cell = frame.vars.get(name)
          if cell is None:
            print(f"[ERROR] Variable `{name}' has not been declared")
            continue
          print(self._format_vdecl(name, cell))
        continue
      if cmd in {"s", "store"}:
        store = self._format_store(frame)
        print(store)
        continue
      if cmd in {"q", "quit"}:
        raise SystemExit(0)
      if cmd in {"h", "help"}:
        print(self._DEBUGGER_HELP)
        continue
      print(f'Unknown command: "{" ".join(parts)}". Type "h[elp]" to see known commands.')

  def _execute_backward_step(self, frame: Frame) -> None:
    prior_line = self.current_line
    self._consume_current_boundary_markers()
    while self.executed_stmts:
      line, stmt = self.executed_stmts[-1]
      if self._is_boundary_marker(stmt):
        if self._is_begin_boundary(line):
          self.executed_stmts.pop()
          self._current_boundary_line = None
          self._print_begin_break()
        else:
          self._current_boundary_line = line
          self._print_line_break(line)
        return
      self.executed_stmts.pop()
      inv_stmt = invert_stmt(stmt, global_mode=False)
      self._exec_stmt_impl(frame, inv_stmt, allow_break=False, record_stmt=False, record_nested=True)
      target_line = self._peek_previous_boundary_line()
      if target_line is not None:
        target_line = self._adjust_reverse_target_line(prior_line, target_line)
        if target_line == prior_line:
          while (
            self.executed_stmts
            and self.executed_stmts[-1][0] == target_line
            and self._is_boundary_marker(self.executed_stmts[-1][1])
          ):
            self.executed_stmts.pop()
          continue
        if self._is_begin_boundary(target_line):
          self._current_boundary_line = None
          self._print_begin_break()
        else:
          self._current_boundary_line = target_line
          self._print_line_break(target_line)
      elif self.executed_stmts:
        self._current_boundary_line = None
        self._print_line_break(line)
      else:
        self._current_boundary_line = None
        self._print_begin_break()
      return

  def _execute_backward_to_breakpoint(self, frame: Frame) -> None:
    if not self.executed_stmts:
      return
    start_line = self.current_line
    while self.executed_stmts:
      self._execute_backward_step(frame)
      if self.breakpoints and self.current_line in self.breakpoints and self.current_line != start_line:
        break

  def _execute_backward_to_boundary(self, frame: Frame) -> None:
    while self.executed_stmts:
      line, stmt = self.executed_stmts[-1]
      if self._is_major_boundary(stmt):
        self._current_boundary_line = line
        self._print_line_break(line)
        return
      if stmt == self._BOUNDARY_MINOR:
        self.executed_stmts.pop()
        continue
      self.executed_stmts.pop()
      inv_stmt = invert_stmt(stmt, global_mode=False)
      self._exec_stmt_impl(frame, inv_stmt, allow_break=False, record_stmt=False, record_nested=True)
      target_line = self._peek_previous_boundary_line(major_only=True)
      target_major = self._peek_previous_major_boundary()
      target_minor = self._peek_previous_boundary_line(major_only=False)
      if target_major is not None:
        target_major_line, target_major_marker = target_major
        if self._boundary_stmt_type(target_major_marker) == "FromStmt" and target_minor is not None and target_minor != target_major_line:
          self._current_boundary_line = target_minor
          self._print_line_break(target_minor)
          return
      if target_line is not None:
        self._current_boundary_line = target_line
        self._print_line_break(target_line)
        return
    self._current_boundary_line = None
    self._print_begin_break()

  def _peek_previous_boundary_line(self, major_only: bool = False) -> int | None:
    for line, stmt in reversed(self.executed_stmts):
      if self._is_major_boundary(stmt):
        return line
      if not major_only and stmt == self._BOUNDARY_MINOR:
        return line
    return None

  def _peek_previous_major_boundary(self) -> tuple[int, object] | None:
    for line, stmt in reversed(self.executed_stmts):
      if self._is_major_boundary(stmt):
        return line, stmt
    return None

  def _peek_previous_major_boundaries(self, count: int) -> list[tuple[int, object]]:
    boundaries: list[tuple[int, object]] = []
    for line, stmt in reversed(self.executed_stmts):
      if self._is_major_boundary(stmt):
        boundaries.append((line, stmt))
        if len(boundaries) >= count:
          break
    return boundaries

  def _adjust_reverse_target_line(self, prior_line: int, target_line: int) -> int:
    majors = self._peek_previous_major_boundaries(2)
    if len(majors) < 2:
      return target_line
    nearest_line, nearest_marker = majors[0]
    outer_line, outer_marker = majors[1]
    nearest_type = self._boundary_stmt_type(nearest_marker)
    outer_type = self._boundary_stmt_type(outer_marker)
    # When stepping backward out of an else-branch statement, Haskell moves to the
    # surrounding call boundary rather than to stale minor stops from another branch.
    if (
      nearest_type == "IfStmt"
      and outer_type in {"CallStmt", "UncallStmt"}
      and target_line < prior_line
      and target_line != nearest_line
      and target_line != outer_line
    ):
      return outer_line
    return target_line

  def _consume_current_boundary_markers(self) -> None:
    while (
      self._current_boundary_line is not None
      and self.executed_stmts
      and self.executed_stmts[-1][0] == self._current_boundary_line
      and self._is_boundary_marker(self.executed_stmts[-1][1])
    ):
      self.executed_stmts.pop()
    if self._current_boundary_line is not None:
      self._clear_current_boundary()

  def _is_begin_boundary(self, line: int) -> bool:
    if line != self._first_stmt_line:
      return False
    return all(self._is_boundary_marker(marker) for _, marker in self.executed_stmts)

  def _exec_print(self, frame: Frame, stmt: PrintsStmt) -> None:
    prints = stmt.prints
    if prints.kind == "print":
      self._warn_legacy_io("print")
      self.stdout.append((prints.text or "") + "\n")
      return
    if prints.kind == "show":
      self._warn_legacy_io("show")
      parts = []
      for arg in prints.args:
        if isinstance(arg, Lval):
          name = self._format_lval_name(arg)
          cell = self._resolve_lval(frame, arg)
        else:
          name = arg.name
          cell = self._resolve_var(frame, arg.name)
        parts.append(self._format_vdecl(name, cell))
      self.stdout.append(", ".join(parts) + "\n")
      return
    if prints.kind == "read":
      # Simplified read: just read an integer from stdin
      lval = prints.args[0]
      assert isinstance(lval, Lval)
      cell = self._resolve_lval(frame, lval)
      line = sys.stdin.readline()
      if line:
        try:
          cell.value = int(line.strip())
        except ValueError:
          pass
      return
    if prints.kind == "write":
      lval = prints.args[0]
      assert isinstance(lval, Lval)
      cell = self._resolve_lval(frame, lval)
      self.stdout.append(str(cell.value) + "\n")
      return
    if prints.kind == "scanf":
      self._exec_scanf(frame, stmt)
      return
    text = prints.text or ""
    cells = [self._resolve_lval(frame, arg) if isinstance(arg, Lval) else self._resolve_var(frame, arg.name) for arg in prints.args]
    values = [cell.value for cell in cells]
    value_index = 0
    pieces: list[str] = []
    i = 0
    while i < len(text):
      if text[i] == "%" and i + 1 < len(text):
        kind = text[i + 1]
        if kind == "%":
          pieces.append("%")
        else:
          if value_index >= len(values):
            raise JanaError(stmt.pos, "Not enough arguments for format string", contextual=True)
          self._check_printf_type(stmt.pos, kind, cells[value_index])
          if not cells[value_index].writable:
            raise JanaError(stmt.pos, "Updating constant", contextual=True)
          pieces.append(self._render_printf_value(kind, cells[value_index]))
          value_index += 1
        i += 2
      else:
        pieces.append(text[i])
        i += 1
    if value_index != len(values):
      raise JanaError(stmt.pos, "Not all arguments where used during string formatting", contextual=True)
    self.stdout.append("".join(pieces) + "\n")

  def _render_printf_value(self, kind: str, cell: Cell) -> str:
    if kind == "s":
      chars: list[str] = []
      for item in cell.value:
        if item == 0:
          break
        chars.append(chr(item))
      return "".join(chars)
    return str(cell.value)

  def _exec_scanf(self, frame: Frame, stmt: PrintsStmt) -> None:
    text = stmt.prints.text or ""
    cells = [self._resolve_lval(frame, arg) if isinstance(arg, Lval) else self._resolve_var(frame, arg.name) for arg in stmt.prints.args]
    raw = sys.stdin.readline()
    if raw == "":
      raise JanaError(stmt.pos, "scanf reached end of input", contextual=True)
    specs = self._scanf_specs(stmt.pos, text)
    if len(specs) != len(cells):
      raise JanaError(stmt.pos, "Not enough arguments for format string", contextual=True)
    parsed = self._scan_input(stmt.pos, text, raw)
    if len(parsed) != len(cells):
      raise JanaError(stmt.pos, "Not enough arguments for format string", contextual=True)
    for kind, cell, value in zip(specs, cells, parsed):
      self._check_scanf_type(stmt.pos, kind, cell)
      self._assign_scanf_value(stmt.pos, kind, cell, value)

  def _scanf_specs(self, pos: SourcePos, text: str) -> list[str]:
    specs: list[str] = []
    i = 0
    while i < len(text):
      if text[i] == "%" and i + 1 < len(text):
        kind = text[i + 1]
        if kind != "%":
          if kind not in {"d", "b", "s"}:
            raise JanaError(pos, f"Unrecognized format specifier: `%{kind}'", contextual=True)
          specs.append(kind)
        i += 2
      else:
        i += 1
    return specs

  def _scan_input(self, pos: SourcePos, fmt: str, raw: str) -> list[object]:
    values: list[object] = []
    i = 0
    j = 0
    while i < len(fmt):
      char = fmt[i]
      if char == "%" and i + 1 < len(fmt):
        kind = fmt[i + 1]
        if kind == "%":
          if j >= len(raw) or raw[j] != "%":
            raise JanaError(pos, "scanf input did not match literal `%'", contextual=True)
          i += 2
          j += 1
          continue
        if kind not in {"d", "b", "s"}:
          raise JanaError(pos, f"Unrecognized format specifier: `%{kind}'", contextual=True)
        while j < len(raw) and raw[j].isspace():
          j += 1
        start = j
        while j < len(raw) and not raw[j].isspace():
          j += 1
        token = raw[start:j]
        if token == "":
          raise JanaError(pos, f"scanf could not read `%{kind}' from input", contextual=True)
        values.append(self._parse_scanf_token(pos, kind, token))
        i += 2
        continue
      if char.isspace():
        while i < len(fmt) and fmt[i].isspace():
          i += 1
        while j < len(raw) and raw[j].isspace():
          j += 1
        continue
      if j >= len(raw) or raw[j] != char:
        shown = raw[j] if j < len(raw) else "end of input"
        raise JanaError(pos, f'scanf input mismatch: expected "{char}" but got "{shown}"', contextual=True)
      i += 1
      j += 1
    while j < len(raw) and raw[j].isspace():
      j += 1
    if j != len(raw):
      raise JanaError(pos, "scanf did not consume the full input line", contextual=True)
    return values

  def _parse_scanf_token(self, pos: SourcePos, kind: str, token: str):
    if kind == "d":
      try:
        return int(token, 10)
      except ValueError as err:
        raise JanaError(pos, f"scanf could not parse integer from `{token}'", contextual=True) from err
    if kind == "b":
      if token == "true":
        return True
      if token == "false":
        return False
      if token == "1":
        return True
      if token == "0":
        return False
      raise JanaError(pos, f"scanf could not parse bool from `{token}'", contextual=True)
    if kind == "s":
      return token
    raise JanaError(pos, f"Unrecognized format specifier: `%{kind}'", contextual=True)

  def _check_scanf_type(self, pos: SourcePos, kind: str, cell: Cell) -> None:
    self._check_printf_type(pos, kind, cell)
    if kind in {"a", "t"}:
      raise JanaError(pos, f"scanf does not support `%{kind}'", contextual=True)

  def _assign_scanf_value(self, pos: SourcePos, kind: str, cell: Cell, value) -> None:
    if not cell.writable:
      raise JanaError(pos, "Updating constant", contextual=True)
    if kind == "s":
      target = self._scanf_string_bytes(pos, cell, value)
      if not self._scanf_target_matches(cell, target):
        raise JanaError(
          pos,
          "scanf destination must be zero-cleared or already equal to the incoming value",
          contextual=True,
        )
      cell.value = list(target)
      return
    normalized = self._normalize_scanf_scalar(kind, cell, value)
    if not self._scanf_target_matches(cell, normalized):
      raise JanaError(
        pos,
        "scanf destination must be zero-cleared or already equal to the incoming value",
        contextual=True,
      )
    cell.value = normalized

  def _normalize_scanf_scalar(self, kind: str, cell: Cell, value):
    if kind == "d":
      return self._normalize_int(value, cell.int_type)
    if kind == "b":
      return bool(value)
    return value

  def _scanf_string_bytes(self, pos: SourcePos, cell: Cell, value: str) -> list[int]:
    if cell.shape is None or len(cell.shape) != 1:
      raise JanaError(pos, "scanf `%s` requires a one-dimensional char array", contextual=True)
    chars = self._char_literal_bytes(pos, value)
    if len(chars) > cell.shape[0]:
      raise JanaError(pos, "scanf string is too large for destination array", contextual=True)
    chars.extend(0 for _ in range(cell.shape[0] - len(chars)))
    return chars

  def _scanf_target_matches(self, cell: Cell, incoming) -> bool:
    if cell.value == incoming:
      return True
    return cell.value == self._scanf_zero_value(cell)

  def _scanf_zero_value(self, cell: Cell):
    if cell.kind == "array":
      return [0 for _ in cell.value]
    if cell.kind == "bool":
      return False
    if cell.kind == "stack":
      return []
    if cell.kind == "struct":
      return self._initial_struct_value_by_name(cell)
    return self._normalize_int(0, cell.int_type)

  def _initial_struct_value_by_name(self, cell: Cell):
    if cell.struct_name is None:
      return {}
    struct_def = self.struct_defs.get(cell.struct_name)
    if struct_def is None:
      return {}
    value: dict[str, object] = {}
    for field in struct_def.fields:
      value[field.ident.name] = self._zero_struct_field(field)
    return value

  def _zero_runtime_value(self, cell: Cell):
    if cell.kind == "array":
      return [self._zero_array_element(cell) for _ in cell.value]
    if cell.kind == "bool":
      return False
    if cell.kind == "stack":
      return []
    if cell.kind == "struct":
      return self._initial_struct_value_by_name(cell)
    return self._normalize_int(0, cell.int_type)

  def _zero_array_element(self, cell: Cell):
    if cell.elem_kind == "bool":
      return False
    if cell.elem_kind == "stack":
      return []
    if cell.elem_kind == "struct":
      return self._initial_struct_value_by_name(
        Cell(0, kind="struct", struct_name=cell.elem_struct_name)
      )
    return self._normalize_int(0, cell.elem_int_type)

  def _warn_legacy_io(self, kind: str) -> None:
    # `print`/`show` are first-class output forms in jana2014; no deprecation notice.
    return

  def _call_proc(self, caller: Frame, name: str, args: list[Expr], pos: SourcePos, record_stmt: bool = True, record_nested: bool = False) -> None:
    proc = self.procs.get(name)
    if proc is None:
      raise JanaError(pos, f"Procedure `{name}' is not defined", contextual=True)
    if len(proc.params) != len(args):
      raise JanaError(pos, f"Procedure `{name}` expects {len(proc.params)} argument(s) but got {len(args)}")
    frame = Frame(vars={})
    for param, arg in zip(proc.params, args):
      if not isinstance(arg, LvalExpr):
        if param.decl_type != DeclType.CONSTANT:
          raise JanaError(arg.pos, "Non-constant argument must be an l-value")
        val = self._eval_expr(caller, arg)
        actual = Cell(val, writable=False)
      else:
        actual = self._resolve_lval(caller, arg.lval)
        try:
          self._check_param_compat(param, actual, arg.pos)
        except JanaError as err:
          if err.message.startswith("Expecting array of size"):
            details = list(err.details)
            if not any(detail.startswith("In an argument of") for detail in details):
              details.append(f"In an argument of `{name}', namely `{param.ident.name}'")
            if not any(detail.startswith("In procedure") for detail in details):
              details.append(f"In procedure `{name}'")
            raise JanaError(err.pos, err.message, details, True)
          raise err
      if param.decl_type == DeclType.CONSTANT:
        actual = ConstantParamProxy(actual)
      frame.vars[param.ident.name] = actual
    self._exec_block(frame, proc.body, record_stmt=record_stmt, record_nested=record_nested)

  def _uncall_proc(self, caller: Frame, name: str, args: list[Expr], pos: SourcePos, record_stmt: bool = True, record_nested: bool = False) -> None:
    proc = self.procs.get(name)
    if proc is None:
      raise JanaError(pos, f"Procedure `{name}' is not defined", contextual=True)
    if len(proc.params) != len(args):
      raise JanaError(pos, f"Procedure `{name}` expects {len(proc.params)} argument(s) but got {len(args)}")
    frame = Frame(vars={})
    for param, arg in zip(proc.params, args):
      if not isinstance(arg, LvalExpr):
        if param.decl_type != DeclType.CONSTANT:
          raise JanaError(arg.pos, "Non-constant argument must be an l-value")
        val = self._eval_expr(caller, arg)
        actual = Cell(val, writable=False)
      else:
        actual = self._resolve_lval(caller, arg.lval)
        try:
          self._check_param_compat(param, actual, arg.pos)
        except JanaError as err:
          if err.message.startswith("Expecting array of size"):
            details = list(err.details)
            if not any(detail.startswith("In an argument of") for detail in details):
              details.append(f"In an argument of `{name}', namely `{param.ident.name}'")
            if not any(detail.startswith("In procedure") for detail in details):
              details.append(f"In procedure `{name}'")
            raise JanaError(err.pos, err.message, details, True)
          raise err
      if param.decl_type == DeclType.CONSTANT:
        actual = ConstantParamProxy(actual)
      frame.vars[param.ident.name] = actual
    self._exec_block(frame, invert_stmts(proc.body, global_mode=False), record_stmt=record_stmt, record_nested=record_nested)

  def _exec_local(self, frame: Frame, stmt: LocalStmt, record_stmt: bool = True, record_nested: bool = False) -> None:
    self._check_local_decl_match(stmt)
    existing = frame.vars.get(stmt.enter_decl.ident.name)
    value, shape, kind, int_type = self._initial_local_value(frame, stmt.enter_decl)
    elem_kind, elem_int_type, elem_is_char, elem_struct_name = self._type_cell_metadata(stmt.enter_decl.typ)
    frame.vars[stmt.enter_decl.ident.name] = Cell(
      value,
      shape=shape,
      kind=kind,
      int_type=int_type,
      writable=stmt.enter_decl.decl_type.value != "Constant",
      is_char=stmt.enter_decl.typ.is_char,
      struct_name=stmt.enter_decl.typ.name if stmt.enter_decl.typ.kind == "struct" else None,
      elem_kind=elem_kind if shape is not None else None,
      elem_int_type=elem_int_type if shape is not None else None,
      elem_is_char=elem_is_char if shape is not None else False,
      elem_struct_name=elem_struct_name if shape is not None else None,
    )
    self._exec_block(frame, stmt.body, record_stmt=record_stmt, record_nested=record_nested)
    expected = self._expected_local_value(frame, stmt.exit_decl)
    actual = frame.vars[stmt.enter_decl.ident.name].value
    if actual != expected:
      stmt_text = (
        "In statement:\n"
        f"    local {format_local_decl(stmt.enter_decl)}\n"
        "    skip\n"
        f"    delocal {format_local_decl(stmt.exit_decl)}"
      )
      raise JanaError(
        stmt.exit_decl.pos,
        f"Expected value to be `{expected}' for local variable `{stmt.enter_decl.ident.name}'\n but actual value is `{actual}'",
        [stmt_text],
        True,
      )
    if existing is None:
      del frame.vars[stmt.enter_decl.ident.name]
    else:
      frame.vars[stmt.enter_decl.ident.name] = existing

  def _exec_ancilla_block(self, frame: Frame, stmt: AncillaBlockStmt, record_stmt: bool = True, record_nested: bool = False) -> None:
    # Ancilla block with multiple declarations
    # Entry: allocate all variables in order
    saved_vars = []
    for decl in stmt.decls:
      self._check_local_decl_match_for_decl(decl)
      existing = frame.vars.get(decl.ident.name)
      value, shape, kind, int_type = self._initial_local_value(frame, decl)
      elem_kind, elem_int_type, elem_is_char, elem_struct_name = self._type_cell_metadata(decl.typ)
      cell = Cell(
        value,
        shape=shape,
        kind=kind,
        int_type=int_type,
        writable=decl.decl_type.value != "Constant",
        is_char=decl.typ.is_char,
        struct_name=decl.typ.name if decl.typ.kind == "struct" else None,
        elem_kind=elem_kind if shape is not None else None,
        elem_int_type=elem_int_type if shape is not None else None,
        elem_is_char=elem_is_char if shape is not None else False,
        elem_struct_name=elem_struct_name if shape is not None else None,
      )
      frame.vars[decl.ident.name] = cell
      saved_vars.append((decl, existing))

    # Execute body
    self._exec_block(frame, stmt.body, record_stmt=record_stmt, record_nested=record_nested)

    # Exit: verify and deallocate all variables in REVERSE order
    for decl, existing in reversed(saved_vars):
      expected = self._expected_local_value(frame, decl)
      actual = frame.vars[decl.ident.name].value
      if actual != expected:
        raise JanaError(decl.pos, f"Expected value to be `{expected}' for ancilla variable `{decl.ident.name}'\n but actual value is `{actual}'", contextual=True)
      
      if existing is None:
        del frame.vars[decl.ident.name]
      else:
        frame.vars[decl.ident.name] = existing

  def _check_local_decl_match_for_decl(self, decl: LocalDecl) -> None:
    # Helper for the logic in _check_local_decl_match but for a single declaration
    pass # In this Python implementation, we'll skip the match check for simplicity or implement as needed

  def _exec_bare_local(self, frame: Frame, stmt: BareLocalStmt, record_stmt: bool = True, record_nested: bool = False) -> None:
    """Allocate a local variable without requiring a matching delocal at the same level."""
    decl = stmt.decl
    existing = frame.vars.get(decl.ident.name)
    value, shape, kind, int_type = self._initial_local_value(frame, decl)
    elem_kind, elem_int_type, elem_is_char, elem_struct_name = self._type_cell_metadata(decl.typ)
    cell = Cell(
      value,
      shape=shape,
      kind=kind,
      int_type=int_type,
      writable=decl.decl_type.value != "Constant",
      is_char=decl.typ.is_char,
      struct_name=decl.typ.name if decl.typ.kind == "struct" else None,
      elem_kind=elem_kind if shape is not None else None,
      elem_int_type=elem_int_type if shape is not None else None,
      elem_is_char=elem_is_char if shape is not None else False,
      elem_struct_name=elem_struct_name if shape is not None else None,
    )
    cell._bare_local_previous = existing  # stash for BareDelocalStmt
    frame.vars[decl.ident.name] = cell
    if stmt.body:
      self._exec_block(frame, stmt.body, record_stmt=record_stmt, record_nested=record_nested)

  def _exec_bare_delocal(self, frame: Frame, stmt: BareDelocalStmt) -> None:
    """Assert and deallocate a variable created by BareLocalStmt."""
    decl = stmt.decl
    name = decl.ident.name
    if name not in frame.vars:
      raise JanaError(stmt.pos, f"Delocal of unknown variable `{name}'", contextual=True)
    cell = frame.vars[name]
    expected = self._expected_local_value(frame, decl)
    actual = cell.value
    if actual != expected:
      raise JanaError(
        stmt.pos,
        f"Expected value to be `{expected}' for local variable `{name}'\n but actual value is `{actual}'",
        contextual=True,
      )
    previous = getattr(cell, '_bare_local_previous', None)
    if previous is None:
      del frame.vars[name]
    else:
      frame.vars[name] = previous

  def _check_local_decl_match(self, stmt: LocalStmt) -> None:
    enter = stmt.enter_decl
    exit = stmt.exit_decl
    if enter.ident.name != exit.ident.name:
      raise JanaError(
        exit.pos,
        f"Variable names does not match in local declaration:\n    `{enter.ident.name}' in `local'\n    `{exit.ident.name}' in `delocal'\n`delocal' statements must come in reverse order of the `local' statments",
        [f"In statement:\n    local {format_local_decl(enter)}\n    ...\n    delocal {format_local_decl(exit)}"],
        True,
      )
    enter_type = self._decl_type_name(enter)
    exit_type = self._decl_type_name(exit)
    if enter_type != exit_type:
      raise JanaError(
        exit.pos,
        f"Type of variable `{enter.ident.name}' does not match local declaration:\n    `{enter_type}' in `local'\n    `{exit_type}' in `delocal'",
        [f"In statement:\n    local {format_local_decl(enter)}\n    skip\n    delocal {format_local_decl(exit)}"],
        True,
      )

  def _decl_type_name(self, decl: LocalDecl) -> str:
    if decl.dimensions:
      return "Array"
    if decl.typ.is_char:
      return "char"
    return decl.typ.kind if decl.typ.kind != "int" else "int"

  def _initial_local_value(self, frame: Frame, decl: LocalDecl):
    int_type = decl.typ.int_type if decl.typ.kind == "int" else None
    if decl.dimensions:
      return self._initial_array_value(frame, decl.pos, decl.ident.name, decl.dimensions, decl.init_expr, decl.typ)
    if decl.typ.kind == "struct":
      if decl.init_expr is not None:
        return self._init_struct_from_expr(frame, decl.typ, decl.pos, decl.init_expr), None, "struct", None
      return self._initial_struct_value(decl.typ, decl.pos), None, "struct", None
    if decl.typ.kind == "bool":
      return (False if decl.init_expr is None else bool(self._eval_expr(frame, decl.init_expr))), None, "bool", None
    if decl.typ.kind == "stack":
      return ([] if decl.init_expr is None else self._eval_expr(frame, decl.init_expr)), None, "stack", None
    initial = 0 if decl.init_expr is None else self._eval_expr(frame, decl.init_expr)
    return self._normalize_int(initial, int_type), None, "int", int_type

  def _expected_local_value(self, frame: Frame, decl: LocalDecl):
    if decl.dimensions:
      current_cell = frame.vars.get(decl.ident.name)
      resolved_sizes: list[int] | None = None
      if any(dim is None for dim in decl.dimensions):
        if current_cell is None or current_cell.shape is None or len(current_cell.shape) != len(decl.dimensions):
          raise JanaError(decl.pos, f"Array size missing for variable `{decl.ident.name}'")
        resolved_sizes = []
        for idx, dim in enumerate(decl.dimensions):
          resolved_sizes.append(current_cell.shape[idx] if dim is None else self._eval_expr(frame, dim))
      elif current_cell is not None and current_cell.shape is not None:
        resolved_sizes = [self._eval_expr(frame, dim) for dim in decl.dimensions]
      flat_size = None if resolved_sizes is None else math.prod(resolved_sizes)
      if decl.init_expr is None:
        return [self._zero_value_for_type(decl.typ, decl.pos) for _ in frame.vars[decl.ident.name].value]
      if decl.typ.kind == "bool":
        flat = [bool(item) for item in self._flatten_array(frame, decl.init_expr)]
        if flat_size is not None:
          if len(flat) > flat_size:
            raise JanaError(decl.pos, f"Initializer is too large for variable `{decl.ident.name}'")
          if len(flat) < flat_size:
            flat.extend(False for _ in range(flat_size - len(flat)))
        return flat
      if decl.typ.kind == "stack":
        flat = self._flatten_array(frame, decl.init_expr)
        if flat_size is not None:
          if len(flat) > flat_size:
            raise JanaError(decl.pos, f"Initializer is too large for variable `{decl.ident.name}'")
          if len(flat) < flat_size:
            flat.extend([] for _ in range(flat_size - len(flat)))
        return flat
      if decl.typ.kind == "struct":
        if not isinstance(decl.init_expr, ArrayExpr):
          raise JanaError(decl.pos, "Struct array initializer must be a brace-enclosed list")
        flat = []
        for item in decl.init_expr.items:
          flat.append(self._init_struct_from_expr(frame, decl.typ, decl.pos, item))
        if flat_size is not None:
          if len(flat) > flat_size:
            raise JanaError(decl.pos, f"Initializer is too large for variable `{decl.ident.name}'")
          if len(flat) < flat_size:
            flat.extend(self._zero_value_for_type(decl.typ, decl.pos) for _ in range(flat_size - len(flat)))
        return flat
      int_type = decl.typ.int_type if decl.typ.kind == "int" else None
      flat = self._flatten_initializer(frame, decl.pos, decl.init_expr, int_type, decl.typ.is_char)
      if flat_size is not None:
        if len(flat) > flat_size:
          raise JanaError(decl.pos, f"Initializer is too large for variable `{decl.ident.name}'")
        if len(flat) < flat_size:
          flat.extend(self._zero_value_for_type(decl.typ, decl.pos) for _ in range(flat_size - len(flat)))
      return flat
    if decl.typ.kind == "struct":
      if decl.init_expr is not None:
        return self._init_struct_from_expr(frame, decl.typ, decl.pos, decl.init_expr)
      return self._initial_struct_value(decl.typ, decl.pos)
    if decl.typ.kind == "bool":
      return False if decl.init_expr is None else bool(self._eval_expr(frame, decl.init_expr))
    if decl.typ.kind == "stack":
      return [] if decl.init_expr is None else self._eval_expr(frame, decl.init_expr)
    return 0 if decl.init_expr is None else self._eval_expr(frame, decl.init_expr)

  def _resolve_var(self, frame: Frame, name: str) -> Cell:
    if name not in frame.vars:
      if self.std in ("janus1982", "janus1982ext"):
        # In 1982 Janus all variables are global: resolve via root frame
        root = self._root_frame
        if root is not None and frame is not root:
          if name not in root.vars:
            root.vars[name] = Cell(0)
          return root.vars[name]
        # We are the root frame (or no root yet): create here
        frame.vars[name] = Cell(0)
        return frame.vars[name]
      raise JanaError(SourcePos("", 0, 0), f"Variable `{name}' has not been declared", contextual=True)
    return frame.vars[name]

  def _resolve_lval(self, frame: Frame, lval: Lval) -> Cell:
    current = self._resolve_var(frame, lval.ident.name)
    for selector in lval.selectors:
      if isinstance(selector, LvalField):
        current = self._resolve_field_selector(lval.ident.name, current, selector)
      elif isinstance(selector, LvalIndex):
        current = self._resolve_index_selector(frame, current, selector, lval.ident.pos)
    return current

  def _resolve_field_selector(self, root_name: str, current: Cell, selector: LvalField) -> Cell:
    if current.kind != "struct" or not isinstance(current.value, dict):
      raise JanaError(selector.ident.pos, f"Variable `{root_name}' does not have field `{selector.ident.name}'", contextual=True)
    if selector.ident.name not in current.value:
      raise JanaError(selector.ident.pos, f"Struct `{current.struct_name or 'struct'}` does not have field `{selector.ident.name}'", contextual=True)
    value = current.value[selector.ident.name]
    field_decl = self._struct_field_decl(current.struct_name, selector.ident.name, selector.ident.pos)
    kind, shape, int_type, is_char, struct_name, elem_kind, elem_int_type, elem_is_char, elem_struct_name = self._field_cell_metadata(field_decl)
    return StructFieldProxy(
      current.value,
      selector.ident.name,
      kind=kind,
      shape=shape,
      int_type=int_type,
      writable=current.writable,
      is_char=is_char,
      struct_name=struct_name,
      elem_kind=elem_kind,
      elem_int_type=elem_int_type,
      elem_is_char=elem_is_char,
      elem_struct_name=elem_struct_name,
    )

  def _resolve_index_selector(self, frame: Frame, current: Cell, selector: LvalIndex, pos: SourcePos) -> Cell:
    if current.kind != "array" or current.shape is None:
      raise JanaError(pos, f"Couldn't match expected type `array`\n            with actual type `{self._cell_kind_name(current)}`")
    idx = self._eval_expr(frame, selector.expr)
    size = current.shape[0]
    if idx < 0 or idx >= size:
      raise JanaError(pos, f"Array index `[{idx}]' was out of bounds (array size was [{size}])")
    array, offset = self._array_storage(current)
    if len(current.shape) == 1:
      return CellProxy(
        array,
        offset + idx,
        kind=current.elem_kind or "int",
        int_type=current.elem_int_type,
        writable=current.writable,
        is_char=current.elem_is_char,
        struct_name=current.elem_struct_name,
      )
    stride = 1
    for dim in current.shape[1:]:
      stride *= dim
    return ArraySliceProxy(
      array,
      offset + idx * stride,
      current.shape[1:],
      writable=current.writable,
      elem_kind=current.elem_kind,
      elem_int_type=current.elem_int_type,
      elem_is_char=current.elem_is_char,
      elem_struct_name=current.elem_struct_name,
    )

  def _array_storage(self, cell: Cell) -> tuple[list, int]:
    if isinstance(cell, ArraySliceProxy):
      return cell.array, cell.offset
    return cell.value, 0

  def _struct_field_decl(self, struct_name: str | None, field_name: str, pos: SourcePos) -> StructField:
    if struct_name is None or struct_name not in self.struct_defs:
      raise JanaError(pos, f"Unknown struct type `{struct_name or 'struct'}`", contextual=True)
    struct_def = self.struct_defs[struct_name]
    for field in struct_def.fields:
      if field.ident.name == field_name:
        return field
    raise JanaError(pos, f"Struct `{struct_name}` does not have field `{field_name}'", contextual=True)

  def _field_cell_metadata(self, field: StructField) -> tuple[str, list[int] | None, IntType | None, bool, str | None, str | None, IntType | None, bool, str | None]:
    elem_kind, elem_int_type, elem_is_char, elem_struct_name = self._type_cell_metadata(field.typ)
    if field.dimensions:
      return "array", self._static_array_sizes(field.dimensions, field.ident.name, field.pos), None, field.typ.is_char and len(field.dimensions) == 1, None, elem_kind, elem_int_type, elem_is_char, elem_struct_name
    return elem_kind, None, elem_int_type if elem_kind == "int" else None, field.typ.is_char, elem_struct_name if elem_kind == "struct" else None, None, None, False, None

  def _metadata_for_value(self, value, parent: Cell) -> tuple[str, IntType | None, bool, str | None]:
    if isinstance(value, dict):
      return "struct", None, False, self._struct_name_for_value(value)
    if isinstance(value, bool):
      return "bool", None, False, None
    if isinstance(value, list):
      return "stack", None, False, None
    if parent.elem_kind is not None:
      return parent.elem_kind, parent.elem_int_type, parent.elem_is_char, parent.elem_struct_name
    return "int", parent.int_type, False, None

  def _eval_expr(self, frame: Frame, expr: Expr):
    try:
      if isinstance(expr, Number):
        return expr.value
      if isinstance(expr, Boolean):
        return expr.value
      if isinstance(expr, LvalExpr):
        return self._resolve_lval(frame, expr.lval).value
      if isinstance(expr, UnaryExpr):
        value = self._eval_expr(frame, expr.expr)
        if expr.op == UnaryOpKind.NOT:
          if not isinstance(value, bool):
            actual = self._describe_value(value)
            raise JanaError(expr.pos, f"Couldn't match expected type `bool'\n            with actual type `{actual}'", [f"In expression:\n    {format_expr(expr)}"], True)
          return not self._truthy(value)
        return self._normalize_int(~value, IntType.UNBOUND)
      if isinstance(expr, TypeCastExpr):
        value = self._eval_expr(frame, expr.expr)
        if not isinstance(value, int):
          raise JanaError(expr.pos, "Type cast only supports integers", contextual=True)
        return self._normalize_int(value, expr.typ.int_type)
      if isinstance(expr, BinExpr):
        try:
          if expr.op == BinOpKind.LAND:
            left = self._eval_expr(frame, expr.left)
            self._check_bin_operands(expr.pos, expr.op, left, False)
            return self._truthy(left) and self._truthy(self._eval_expr(frame, expr.right))
          if expr.op == BinOpKind.LOR:
            left = self._eval_expr(frame, expr.left)
            self._check_bin_operands(expr.pos, expr.op, left, False)
            return self._truthy(left) or self._truthy(self._eval_expr(frame, expr.right))
          left = self._eval_expr(frame, expr.left)
          right = self._eval_expr(frame, expr.right)
          return self._eval_bin(expr.pos, expr.op, left, right)
        except JanaError as err:
          if err.contextual and not any(detail.startswith("In expression:") for detail in err.details):
            raise err.add_detail(f"In expression:\n    {format_expr(expr)}")
          raise
      if isinstance(expr, TernaryExpr):
        cond = self._eval_expr(frame, expr.cond)
        if not isinstance(cond, bool):
          actual = self._describe_value(cond)
          raise JanaError(expr.pos, f"Couldn't match expected type `bool'\n            with actual type `{actual}'", [f"In expression:\n    {format_expr(expr)}"], True)
        branch = expr.then_expr if cond else expr.else_expr
        return self._eval_expr(frame, branch)
      if isinstance(expr, ArrayExpr):
        return [self._eval_expr(frame, item) if not isinstance(item, ArrayExpr) else self._flatten_array(frame, item) for item in expr.items]
      if isinstance(expr, SizeExpr):
        cell = self._resolve_var(frame, expr.ident.name)
        if cell.kind not in {"array", "stack"}:
          raise JanaError(expr.pos, "Couldn't match expected type `array' or `stack'\n            with actual type `int'", [f"In an argument of `size', namely `{expr.ident.name}'"], True)
        value = cell.value
        return len(value)
      if isinstance(expr, EmptyExpr):
        cell = self._resolve_var(frame, expr.ident.name)
        if cell.kind != "stack":
          raise JanaError(expr.pos, "Couldn't match expected type `stack'\n            with actual type `int'", [f"In an argument of `empty', namely `{expr.ident.name}'"], True)
        value = cell.value
        return len(value) == 0
      if isinstance(expr, TopExpr):
        cell = self._resolve_var(frame, expr.ident.name)
        if cell.kind != "stack":
          raise JanaError(expr.pos, "Couldn't match expected type `stack'\n            with actual type `int'", [f"In an argument of `top', namely `{expr.ident.name}'"], True)
        value = cell.value
        if not value:
          raise JanaError(expr.pos, "Can't pop from empty stack", contextual=True)
        return value[0]
      if isinstance(expr, NilExpr):
        return []
      raise JanaError(expr.pos, f"Unsupported expression {type(expr).__name__}")
    except JanaError as err:
      if err.contextual:
        raise err
      raise err.add_detail(f"In expression:\n    {format_expr(expr)}")

  def _eval_bin(self, pos: SourcePos, op: BinOpKind, left, right):
    self._check_bin_operands(pos, op, left, right)
    if op == BinOpKind.ADD:
      return self._normalize_int(left + right, IntType.UNBOUND)
    if op == BinOpKind.SUB:
      return self._normalize_int(left - right, IntType.UNBOUND)
    if op == BinOpKind.MUL:
      return self._normalize_int(left * right, IntType.UNBOUND)
    if op == BinOpKind.DIV:
      if right == 0:
        raise JanaError(pos, "Division by zero")
      return self._normalize_int(left // right, IntType.UNBOUND)
    if op == BinOpKind.MOD:
      if right == 0:
        raise JanaError(pos, "Division by zero")
      return self._normalize_int(left % right, IntType.UNBOUND)
    if op == BinOpKind.EXP:
      return self._normalize_int(left ** right, IntType.UNBOUND)
    if op == BinOpKind.SL:
      return self._normalize_int(left << right, IntType.UNBOUND)
    if op == BinOpKind.SR:
      return self._normalize_int(left >> right, IntType.UNBOUND)
    if op == BinOpKind.AND:
      return self._normalize_int(left & right, IntType.UNBOUND)
    if op == BinOpKind.OR:
      return self._normalize_int(left | right, IntType.UNBOUND)
    if op == BinOpKind.XOR:
      return self._normalize_int(left ^ right, IntType.UNBOUND)
    if op == BinOpKind.LAND:
      return self._truthy(left) and self._truthy(right)
    if op == BinOpKind.LOR:
      return self._truthy(left) or self._truthy(right)
    if op == BinOpKind.GT:
      return left > right
    if op == BinOpKind.LT:
      return left < right
    if op == BinOpKind.EQ:
      return left == right
    if op == BinOpKind.NEQ:
      return left != right
    if op == BinOpKind.GE:
      return left >= right
    if op == BinOpKind.LE:
      return left <= right
    raise JanaError(pos, f"Unsupported operator {op.value}")

  def _truthy(self, value) -> bool:
    return bool(value)

  def _exec_from_forward(self, frame: Frame, stmt: FromStmt, record_stmt: bool = True, record_nested: bool = False) -> None:
    if stmt.do_part:
      self._exec_block(frame, stmt.do_part, record_stmt=record_stmt, record_nested=record_nested)
    if self._truthy(self._eval_expr(frame, stmt.exit_cond)):
      return
    while True:
      if stmt.loop_part:
        self._exec_block(frame, stmt.loop_part, record_stmt=record_stmt, record_nested=record_nested)
      if self._truthy(self._eval_expr(frame, stmt.entry_cond)):
        raise JanaError(stmt.entry_cond.pos, "Assertion failed: should be false", contextual=True)
      if stmt.do_part:
        self._exec_block(frame, stmt.do_part, record_stmt=record_stmt, record_nested=record_nested)
      if self._truthy(self._eval_expr(frame, stmt.exit_cond)):
        return

  def _exec_iterate(self, frame: Frame, stmt: IterateStmt, record_stmt: bool = True, record_nested: bool = False) -> None:
    existing = frame.vars.get(stmt.ident.name)
    start = self._eval_expr(frame, stmt.start_expr)
    step = self._eval_expr(frame, stmt.step_expr)
    end = self._eval_expr(frame, stmt.end_expr)
    frame.vars[stmt.ident.name] = Cell(start, kind="int")
    current = frame.vars[stmt.ident.name]
    try:
      if current.value != start:
        raise JanaError(stmt.pos, "Assertion failed: should be true", contextual=True)
      stop = end if stmt.exclusive else end + step
      while current.value != stop:
        if current.value != start and current.value == start:
          raise JanaError(stmt.pos, "Assertion failed: should be false", contextual=True)
        self._exec_block(frame, stmt.body, record_stmt=record_stmt, record_nested=record_nested, allow_break=False)
        current.value += step
    finally:
      expected = end if stmt.exclusive else end + step
      actual = current.value
      if existing is None:
        del frame.vars[stmt.ident.name]
      else:
        frame.vars[stmt.ident.name] = existing
      if actual != expected:
        raise JanaError(stmt.pos, f"Expected value to be `{expected}` for local variable `{stmt.ident.name}`\n     but actual value is `{actual}`", contextual=True)

  def _check_printf_type(self, pos: SourcePos, kind: str, cell: Cell) -> None:
    expected = {
      "d": "int",
      "a": "array",
      "b": "bool",
      "s": "char array",
      "t": "stack",
    }.get(kind)
    if expected is None:
      raise JanaError(pos, f"Unrecognized format specifier: `%{kind}'", contextual=True)
    if kind == "s":
      if cell.kind != "array" or cell.shape is None or len(cell.shape) != 1 or not cell.is_char:
        raise JanaError(
          pos,
          f"Type mismatch for `%{kind}' format specifier\nExpected argument of type `{expected}'\n      but actual type was `{self._cell_kind_name(cell)}`",
          contextual=True,
        )
      return
    actual = self._cell_kind_name(cell)
    actual_base = "array" if cell.kind == "array" else "stack" if cell.kind == "stack" else "bool" if cell.kind == "bool" else "int"
    if expected != actual_base:
      raise JanaError(
        pos,
        f"Type mismatch for `%{kind}' format specifier\nExpected argument of type `{expected}'\n      but actual type was `{actual_base}'",
        contextual=True,
      )

  def _value_kind(self, value) -> str:
    if isinstance(value, bool):
      return "bool"
    if isinstance(value, list):
      return "stack" if value and not isinstance(value[0], int) else "array_or_stack"
    if isinstance(value, dict):
      return "struct"
    return "int"

  def _value_kind_name(self, value) -> str:
    if isinstance(value, bool):
      return "bool"
    if isinstance(value, list):
      return "stack"
    if isinstance(value, dict):
      return "struct"
    return "int"

  def _struct_name_for_value(self, value) -> str | None:
    if not isinstance(value, dict):
      return None
    for struct_def in self.struct_defs.values():
      if {field.ident.name for field in struct_def.fields} == set(value):
        return struct_def.ident.name
    return None

  def _describe_value(self, value) -> str:
    if isinstance(value, bool):
      return "bool"
    if isinstance(value, list):
      return "stack"
    if isinstance(value, dict):
      return "struct"
    return "int"

  def _cell_kind_name(self, cell: Cell) -> str:
    if cell.kind == "array" and cell.shape is not None:
      dims = "".join(f"[{size}]" for size in cell.shape)
      prefix = "char" if cell.is_char else "array"
      return f"{prefix}{dims}"
    if cell.kind == "struct":
      return cell.struct_name or "struct"
    return cell.kind

  def _check_param_compat(self, param: Vdecl, cell: Cell, pos: SourcePos) -> None:
    if param.dimensions:
      if cell.kind != "array":
        raise JanaError(param.pos, f"Couldn't match expected type `array'\n            with actual type `{self._cell_kind_name(cell)}'", contextual=True)
      if param.typ.is_char != cell.is_char:
        expected = "char" if param.typ.is_char else "array"
        raise JanaError(param.pos, f"Couldn't match expected type `{expected}'\n            with actual type `{self._cell_kind_name(cell)}'", contextual=True)
      if len(param.dimensions) != (len(cell.shape) if cell.shape is not None else 0):
        raise JanaError(param.pos, f"Couldn't match expected type `array'\n            with actual type `{self._cell_kind_name(cell)}'", contextual=True)
      expected_sizes = [self._eval_expr(Frame(vars={}), dim) for dim in param.dimensions if dim is not None]
      if cell.shape is not None and len(expected_sizes) == len(cell.shape) and expected_sizes != list(cell.shape):
        raise JanaError(
          param.pos,
          f"Expecting array of size [{', '.join(str(size) for size in expected_sizes)}] but got size [{', '.join(str(size) for size in cell.shape)}]",
          [],
          True,
      )
      return
    if param.typ.kind == "struct":
      if cell.kind != "struct":
        raise JanaError(param.pos, f"Couldn't match expected type `{param.typ.name or 'struct'}'\n            with actual type `{self._cell_kind_name(cell)}'", contextual=True)
      if param.typ.name != cell.struct_name:
        raise JanaError(param.pos, f"Couldn't match expected type `{param.typ.name or 'struct'}'\n            with actual type `{self._cell_kind_name(cell)}'", contextual=True)
      return
    expected = param.typ.kind
    actual = "stack" if cell.kind == "stack" else "bool" if cell.kind == "bool" else "struct" if cell.kind == "struct" else "int"
    if expected != actual:
      raise JanaError(param.pos, f"Couldn't match expected type `{expected}'\n            with actual type `{actual}'", contextual=True)

  def _check_bin_operands(self, pos: SourcePos, op: BinOpKind, left, right) -> None:
    if op in {BinOpKind.LAND, BinOpKind.LOR}:
      if not isinstance(left, bool) or not isinstance(right, bool):
        actual = "int"
        if isinstance(left, list) or isinstance(right, list):
          actual = "stack"
        if isinstance(left, dict) or isinstance(right, dict):
          actual = "struct"
        raise JanaError(pos, f"Couldn't match expected type `bool'\n            with actual type `{actual}'", contextual=True)
      return
    if isinstance(left, list) or isinstance(right, list):
      raise JanaError(pos, "Couldn't match expected type `int'\n            with actual type `stack'", contextual=True)
    if isinstance(left, dict) or isinstance(right, dict):
      raise JanaError(pos, "Couldn't match expected type `int'\n            with actual type `struct'", contextual=True)

  def _check_assign_compat(self, pos: SourcePos, cell: Cell, value) -> None:
    if cell.kind == "array":
      if not isinstance(value, list):
        raise JanaError(pos, f"Couldn't match expected type `{self._cell_kind_name(cell)}'\n            with actual type `{self._describe_value(value)}'", contextual=True)
      expected_len = 1
      for size in cell.shape or []:
        expected_len *= size
      if len(value) != expected_len:
        actual_type = f"array[{len(value)}]"
        raise JanaError(pos, f"Couldn't match expected type `{self._cell_kind_name(cell)}'\n            with actual type `{actual_type}'", contextual=True)
      return
    if cell.kind == "stack" and not isinstance(value, list):
      raise JanaError(pos, f"Couldn't match expected type `stack'\n            with actual type `{self._describe_value(value)}'", contextual=True)
    if cell.kind == "struct" and not isinstance(value, dict):
      raise JanaError(pos, f"Couldn't match expected type `struct'\n            with actual type `{self._describe_value(value)}'", contextual=True)
    if cell.kind == "int" and isinstance(value, list):
      raise JanaError(pos, "Couldn't match expected type `int'\n            with actual type `stack'", contextual=True)

  def _check_swap_compat(self, frame: Frame, stmt: SwapStmt) -> None:
    left = self._resolve_lval(frame, stmt.left)
    right = self._resolve_lval(frame, stmt.right)
    left_type = self._cell_kind_name(left)
    right_type = self._cell_kind_name(right)
    if left_type != right_type:
      raise JanaError(stmt.pos, f"Can't swap variables of type `{left_type}' and `{right_type}'", contextual=True)

  def _with_stmt_context(self, err: JanaError, stmt, frame: Frame) -> JanaError:
    if err.message.startswith("Assertion failed:"):
      return err
    if err.contextual and any(detail.startswith("In statement:") for detail in err.details):
      return err
    store = self._format_store(frame)
    details = list(err.details)
    details.append(self._stmt_detail(stmt))
    if store:
      details.append(f"  where {store.replace(chr(10), chr(10) + '        ')}")
    return JanaError(err.pos if err.pos.line else stmt.pos, err.message, details, True)

  def _check_alias_assign(self, frame: Frame, stmt: AssignStmt) -> None:
    lhs_key = self._ref_key(frame, stmt.lval)
    for idx_expr in self._selector_index_exprs(stmt.lval):
      for expr_lval in self._expr_lvals(idx_expr):
        if lhs_key == self._ref_key(frame, expr_lval):
          raise JanaError(
            stmt.pos,
            f"Identifiers `{stmt.lval.ident.name}' and `{expr_lval.ident.name}' are aliases",
            [f"In expression:\n    {format_lval(expr_lval)}"],
            True,
          )
    for expr_lval in self._expr_lvals(stmt.expr):
      if lhs_key == self._ref_key(frame, expr_lval):
        raise JanaError(
          stmt.pos,
          f"Identifiers `{stmt.lval.ident.name}' and `{expr_lval.ident.name}' are aliases",
          [f"In expression:\n    {format_lval(expr_lval)}"],
          True,
        )

  def _check_alias_swap(self, frame: Frame, stmt: SwapStmt) -> None:
    if self._ref_key(frame, stmt.left) == self._ref_key(frame, stmt.right):
      raise JanaError(
        stmt.pos,
        f"Identifiers `{stmt.left.ident.name}' and `{stmt.right.ident.name}' are aliases",
        [],
        True,
      )
    left_key = self._ref_key(frame, stmt.left)
    right_key = self._ref_key(frame, stmt.right)
    for idx_expr in self._selector_index_exprs(stmt.left) + self._selector_index_exprs(stmt.right):
      for expr_lval in self._expr_lvals(idx_expr):
        expr_key = self._ref_key(frame, expr_lval)
        if expr_key == left_key or expr_key == right_key:
          raise JanaError(
            stmt.pos,
            f"Identifiers `{stmt.left.ident.name}' and `{expr_lval.ident.name}' are aliases",
            [f"In expression:\n    {format_lval(expr_lval)}"],
            True,
          )

  def _expr_lvals(self, expr: Expr) -> list[Lval]:
    if isinstance(expr, LvalExpr):
      out = [expr.lval]
      for idx in self._selector_index_exprs(expr.lval):
        out.extend(self._expr_lvals(idx))
      return out
    if isinstance(expr, UnaryExpr):
      return self._expr_lvals(expr.expr)
    if isinstance(expr, BinExpr):
      return self._expr_lvals(expr.left) + self._expr_lvals(expr.right)
    if isinstance(expr, TernaryExpr):
      return self._expr_lvals(expr.cond) + self._expr_lvals(expr.then_expr) + self._expr_lvals(expr.else_expr)
    if isinstance(expr, ArrayExpr):
      out: list[Lval] = []
      for item in expr.items:
        out.extend(self._expr_lvals(item))
      return out
    return []

  def _selector_index_exprs(self, lval: Lval) -> list[Expr]:
    return [selector.expr for selector in lval.selectors if isinstance(selector, LvalIndex)]

  def _ref_key(self, frame: Frame, lval: Lval):
    cell = self._resolve_lval(frame, lval)
    if isinstance(cell, ArraySliceProxy):
      return (id(cell.array), cell.offset, tuple(cell.shape))
    if isinstance(cell, CellProxy):
      return (id(cell.array), cell.index)
    if isinstance(cell, StructFieldProxy):
      return (id(cell.struct_value), cell.field_name)
    return (id(cell), None)

  def _format_store(self, frame: Frame) -> str:
    entries = []
    for name in sorted(frame.vars):
      cell = frame.vars[name]
      entries.append(self._format_vdecl(name, cell))
    return "\n".join(entries)

  def _nonzero_store_names(self, frame: Frame) -> list[str]:
    names: list[str] = []
    for name in sorted(frame.vars):
      if not self._is_zero_cell(frame.vars[name]):
        names.append(name)
    return names

  def _is_zero_cell(self, cell: Cell) -> bool:
    return self._is_zero_value(cell.value, cell)

  def _is_zero_value(self, value, cell: Cell | None = None) -> bool:
    if isinstance(value, bool):
      return value is False
    if isinstance(value, dict):
      struct_name = cell.struct_name if cell is not None else self._struct_name_for_value(value)
      for field_name, field_value in value.items():
        field_shape = self._struct_field_shape(struct_name, field_name)
        if field_shape is not None:
          if not self._is_zero_array_value(field_value, field_shape):
            return False
        elif isinstance(field_value, dict):
          if not self._is_zero_value(field_value, Cell(field_value, kind="struct", struct_name=self._struct_name_for_value(field_value))):
            return False
        elif isinstance(field_value, list):
          if field_value:
            return False
        elif field_value not in {0, False}:
          return False
      return True
    if isinstance(value, list):
      if cell is not None and cell.kind == "array" and cell.shape is not None:
        return self._is_zero_array_value(value, cell.shape)
      return len(value) == 0
    return value == 0

  def _is_zero_array_value(self, flat: list, shape: list[int]) -> bool:
    for item in flat:
      if isinstance(item, dict):
        if not self._is_zero_value(item, Cell(item, kind="struct", struct_name=self._struct_name_for_value(item))):
          return False
      elif isinstance(item, list):
        if item:
          return False
      elif item not in {0, False}:
        return False
    return True

  @staticmethod
  def _format_lval_name(lval: Lval) -> str:
    parts = [lval.ident.name]
    for sel in lval.selectors:
      if isinstance(sel, LvalField):
        parts.append(f".{sel.ident.name}")
      elif isinstance(sel, LvalIndex):
        parts.append(f"[?]")
    return "".join(parts)

  def _format_vdecl(self, name: str, cell: Cell) -> str:
    if cell.kind == "array" and cell.shape is not None:
      dims = "".join(f"[{size}]" for size in cell.shape)
      return f"{name}{dims} = {self._format_value(cell.value, cell.shape)}"
    return f"{name} = {self._format_value(cell.value, cell.shape)}"

  def _format_value(self, value, shape: list[int] | None):
    if shape is not None:
      return self._format_array(value, shape)
    if isinstance(value, bool):
      return "true" if value else "false"
    if isinstance(value, dict):
      struct_name = self._struct_name_for_value(value)
      pieces: list[str] = []
      for name, item in value.items():
        field_shape = self._struct_field_shape(struct_name, name)
        pieces.append(f"{name} = {self._format_value(item, field_shape)}")
      return "{" + ", ".join(pieces) + "}"
    if isinstance(value, list):
      if not value:
        return "nil"
      return "<" + ", ".join(str(item) for item in value) + "]"
    return str(value)

  def _struct_field_shape(self, struct_name: str | None, field_name: str) -> list[int] | None:
    if struct_name is None or struct_name not in self.struct_defs:
      return None
    for field in self.struct_defs[struct_name].fields:
      if field.ident.name == field_name:
        return self._static_array_sizes(field.dimensions, field.ident.name, field.pos) if field.dimensions else None
    return None

  def _format_array(self, flat: list, shape: list[int]) -> str:
    if len(shape) == 1:
      return "{" + ", ".join(self._format_value(item, None) for item in flat) + "}"
    chunk = 1
    for size in shape[1:]:
      chunk *= size
    pieces = []
    for start in range(0, len(flat), chunk):
      pieces.append(self._format_array(flat[start:start + chunk], shape[1:]))
    return "{" + ", ".join(pieces) + "}"


class CellProxy(Cell):
  def __init__(
    self,
    array: list,
    index: int,
    kind: str = "int",
    shape: list[int] | None = None,
    int_type: IntType | None = None,
    writable: bool = True,
    is_char: bool = False,
    struct_name: str | None = None,
  ):
    self.array = array
    self.index = index
    self.kind = kind
    self.shape = shape
    self.int_type = int_type
    self.writable = writable
    self.is_char = is_char
    self.struct_name = struct_name
    self.elem_kind = None
    self.elem_int_type = None
    self.elem_is_char = False
    self.elem_struct_name = None

  @property
  def value(self):
    return self.array[self.index]

  @value.setter
  def value(self, new_value):
    self.array[self.index] = new_value


class StructFieldProxy(Cell):
  def __init__(
    self,
    struct_value: dict[str, object],
    field_name: str,
    kind: str = "int",
    shape: list[int] | None = None,
    int_type: IntType | None = None,
    writable: bool = True,
    is_char: bool = False,
    struct_name: str | None = None,
    elem_kind: str | None = None,
    elem_int_type: IntType | None = None,
    elem_is_char: bool = False,
    elem_struct_name: str | None = None,
  ):
    self.struct_value = struct_value
    self.field_name = field_name
    self.kind = kind
    self.shape = shape
    self.int_type = int_type
    self.writable = writable
    self.is_char = is_char
    self.struct_name = struct_name
    self.elem_kind = elem_kind
    self.elem_int_type = elem_int_type
    self.elem_is_char = elem_is_char
    self.elem_struct_name = elem_struct_name

  @property
  def value(self):
    return self.struct_value[self.field_name]

  @value.setter
  def value(self, new_value):
    self.struct_value[self.field_name] = new_value


class ArraySliceProxy(Cell):
  def __init__(
    self,
    array: list,
    offset: int,
    shape: list[int],
    writable: bool = True,
    elem_kind: str | None = None,
    elem_int_type: IntType | None = None,
    elem_is_char: bool = False,
    elem_struct_name: str | None = None,
  ):
    self.array = array
    self.offset = offset
    self.shape = shape
    self.kind = "array"
    self.int_type = elem_int_type
    self.writable = writable
    self.is_char = elem_is_char and len(shape) == 1
    self.struct_name = None
    self.elem_kind = elem_kind
    self.elem_int_type = elem_int_type
    self.elem_is_char = elem_is_char
    self.elem_struct_name = elem_struct_name

  @property
  def value(self):
    length = 1
    for dim in self.shape:
      length *= dim
    return self.array[self.offset:self.offset + length]

  @value.setter
  def value(self, new_value):
    length = 1
    for dim in self.shape:
      length *= dim
    self.array[self.offset:self.offset + length] = new_value


class ConstantParamProxy(Cell):
  """Read-only wrapper around a caller's Cell for constant parameters."""
  def __init__(self, inner: Cell):
    self._inner = inner
    self.writable = False
    self.kind = inner.kind
    self.shape = inner.shape
    self.int_type = inner.int_type
    self.is_char = inner.is_char
    self.struct_name = inner.struct_name
    self.elem_kind = getattr(inner, 'elem_kind', None)
    self.elem_int_type = getattr(inner, 'elem_int_type', None)
    self.elem_is_char = getattr(inner, 'elem_is_char', False)
    self.elem_struct_name = getattr(inner, 'elem_struct_name', None)

  @property
  def value(self):
    return self._inner.value

  @value.setter
  def value(self, new_value):
    self._inner.value = new_value
