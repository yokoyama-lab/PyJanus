"""Inverse interpreter for Jana: given a program and its final state, compute
the initial state that would produce it.

Since Jana programs are reversible, running the inverted program on the final
state yields the initial state.
"""
from __future__ import annotations

import copy
import itertools
from dataclasses import dataclass, replace

from .ast import ArrayExpr
from .ast import AssignStmt
from .ast import BareLocalStmt
from .ast import BinExpr
from .ast import BinOpKind
from .ast import DeclType
from .ast import FromStmt
from .ast import Ident
from .ast import IfStmt
from .ast import IntType
from .ast import IterateStmt
from .ast import LocalDecl
from .ast import LocalStmt
from .ast import Lval
from .ast import LvalExpr
from .ast import LvalField
from .ast import LvalIndex
from .ast import ModOp
from .ast import Number
from .ast import Proc
from .ast import ProcMain
from .ast import Program
from .ast import SourcePos
from .ast import Type
from .ast import Vdecl
from .invert import invert_stmts
from .invert import invert_program
from .parser_janus2026 import parse_program
from .runtime import Runtime
from .validate import validate_program


_DUMMY_POS = SourcePos("inverse", 0, 0)


@dataclass
class InverseResult:
  """Result of running the inverse interpreter."""
  initial_store: dict[str, object]
  success: bool
  error: str | None = None


def _extract_store(rt: Runtime) -> dict[str, object]:
  """Extract variable values from a completed Runtime."""
  assert rt._root_frame is not None
  store: dict[str, object] = {}
  for name, cell in rt._root_frame.vars.items():
    store[name] = copy.deepcopy(cell.value)
  return store


def _make_init_expr(value: object) -> "Number | ArrayExpr | None":
  """AST initializer for a value: a scalar int, or a (possibly nested) array."""
  if isinstance(value, bool):
    return Number(int(value), _DUMMY_POS)
  if isinstance(value, int):
    return Number(value, _DUMMY_POS)
  if isinstance(value, list):
    items = [_make_init_expr(v) for v in value]
    if any(it is None for it in items):
      return None
    return ArrayExpr(items, _DUMMY_POS)
  return None


def int_prod(xs: list[int]) -> int:
  p = 1
  for x in xs:
    p *= x
  return p


def _flatten_structs(value: object) -> list[dict]:
  """Row-major flatten of a (possibly nested) struct-array value to its leaf
  struct dicts.  The runtime store already holds multi-dim arrays flat, but a
  caller-supplied `--inverse` JSON may be nested, so accept both."""
  if isinstance(value, dict):
    return [value]
  out: list[dict] = []
  for sub in value:
    out.extend(_flatten_structs(sub))
  return out


def _flatten_ints(v: object) -> list[int]:
  """Row-major flatten of a (possibly nested or flat) array field value."""
  if isinstance(v, list):
    out: list[int] = []
    for x in v:
      out.extend(_flatten_ints(x))
    return out
  return [v]


def _unflatten(k: int, dims: list[int]) -> list[int]:
  """The row-major multi-index of flat position k for the given dimensions."""
  midx, rem = [], k
  for stride in [int_prod(dims[i + 1:]) for i in range(len(dims))]:
    midx.append(rem // stride)
    rem %= stride
  return midx


def _seed_struct_stmts(name: str, value: object, dims: list[int],
                       field_dims: dict[str, list[int]]) -> list["AssignStmt"]:
  """Reversible `+= v` statements driving a freshly-declared (all-zero) struct or
  struct-array variable to its final-store values.

  Structs take no declaration initializer in Janus, so the inverse interpreter
  cannot seed them through `_make_init_expr` the way it does scalars and arrays.
  Instead it prepends these field assignments before the inverted body: each
  struct field is driven from 0 to its final value, mirroring the "re-declare
  with the final store" step that scalars/arrays get for free.  `dims` are the
  variable's array dimensions (empty for a scalar struct); `field_dims` maps a
  field to its own array dimensions (a scalar field has []).  The store flattens
  multi-dim arrays row-major, so flat indices are unflattened back to `g[i][j]`
  (the struct array element) and `.v[a][b]` (an array field).
  """
  stmts: list[AssignStmt] = []

  def assign_field(base_sel: list, fld: str, v: object) -> None:
    fdims = field_dims.get(fld, [])
    if not fdims:                                # scalar field
      if v == 0:
        return                                   # `+= 0` is a no-op
      lval = Lval(Ident(name, _DUMMY_POS), base_sel + [LvalField(Ident(fld, _DUMMY_POS))])
      stmts.append(AssignStmt(ModOp.ADD_EQ, lval, Number(v, _DUMMY_POS), _DUMMY_POS))
    else:                                        # array field: flat row-major
      for k, elem in enumerate(_flatten_ints(v)):
        if elem == 0:
          continue
        idx_sel = [LvalIndex(Number(i, _DUMMY_POS)) for i in _unflatten(k, fdims)]
        lval = Lval(Ident(name, _DUMMY_POS),
                    base_sel + [LvalField(Ident(fld, _DUMMY_POS))] + idx_sel)
        stmts.append(AssignStmt(ModOp.ADD_EQ, lval, Number(elem, _DUMMY_POS), _DUMMY_POS))

  def seed_elem(base_sel: list, elem: dict) -> None:
    for fld, v in elem.items():
      assign_field(base_sel, fld, v)

  if not dims:                                   # scalar struct: value is a dict
    seed_elem([], value)
    return stmts

  for k, elem in enumerate(_flatten_structs(value)):   # struct array, row-major
    sel = [LvalIndex(Number(i, _DUMMY_POS)) for i in _unflatten(k, dims)]
    seed_elem(sel, elem)
  return stmts


def _struct_field_dims(struct_defs) -> dict[str, dict[str, list[int]]]:
  """struct name -> {field name -> its array dimensions ([] if scalar)}."""
  out: dict[str, dict[str, list[int]]] = {}
  for sd in struct_defs:
    out[sd.ident.name] = {
      fld.ident.name: [d.value for d in fld.dimensions if isinstance(d, Number)]
      for fld in sd.fields
    }
  return out


def _build_inverted_main(
  original_main: ProcMain,
  final_store: dict[str, int],
  sfdims: dict[str, dict[str, list[int]]],
) -> ProcMain:
  """Build a new main procedure for the inverted program.

  The inverted main:
  1. Declares the same variables but with init values from final_store
  2. Seeds structs (which have no declaration initializer) via prepended
     field assignments
  3. Runs the inverted statements of the original main
  """
  new_vdecls: list[Vdecl] = []
  struct_seeds: list[AssignStmt] = []
  for vdecl in original_main.vdecls:
    name = vdecl.ident.name
    value = final_store.get(name)
    # Structs (scalar or array) take no initializer; keep the (all-zero)
    # declaration and seed the fields with prepended `+= v` statements.
    if vdecl.typ.kind == "struct" and value is not None:
      new_vdecls.append(vdecl)
      dims = [d.value for d in vdecl.dimensions if isinstance(d, Number)]
      struct_seeds.extend(
        _seed_struct_stmts(name, value, dims, sfdims.get(vdecl.typ.name, {})))
      continue
    # Seed scalars, arrays and stacks from the final store.  A stack's store
    # value is its (top-first) contents list, and `stack s = {...}` sets exactly
    # that list, so the array initializer seeds it directly.
    seed = (vdecl.dimensions and isinstance(value, list)) or \
           (not vdecl.dimensions and isinstance(value, (int, bool))) or \
           (vdecl.typ.kind == "stack" and isinstance(value, list))
    init_expr = _make_init_expr(value) if seed else None
    if init_expr is not None:
      new_vdecls.append(Vdecl(
        decl_type=vdecl.decl_type,
        typ=vdecl.typ,
        ident=vdecl.ident,
        dimensions=vdecl.dimensions,
        init_expr=init_expr,
        pos=vdecl.pos,
      ))
    else:
      new_vdecls.append(vdecl)

  inverted_stmts = invert_stmts(original_main.stmts, global_mode=False)

  return ProcMain(new_vdecls, struct_seeds + inverted_stmts, original_main.pos)


def _references(expr, name: str) -> bool:
  """Whether `expr` reads the variable `name` (the cases a delocal init uses)."""
  if isinstance(expr, LvalExpr):
    return expr.lval.ident.name == name or any(_references(i, name) for i in expr.lval.indices)
  if isinstance(expr, BinExpr):
    return _references(expr.left, name) or _references(expr.right, name)
  return False


def _counter_step(var: str, stmts) -> "int | None":
  """The constant signed step of a top-level `var += c` / `var -= c` in stmts."""
  for s in stmts:
    if (isinstance(s, AssignStmt) and not s.lval.selectors
        and s.lval.ident.name == var and isinstance(s.expr, Number)):
      if s.mod_op == ModOp.ADD_EQ:
        return s.expr.value
      if s.mod_op == ModOp.SUB_EQ:
        return -s.expr.value
  return None


def _desugar_self_ref(stmts: list) -> list:
  """Rewrite the self-referential `delocal` counter idiom into a forward-
  equivalent form the standard inverter can handle.

  `local i=START; from i=START do {…; i += STEP} … until COND; delocal i = i`
  becomes `local i=START; <loop>; from COND do { i -= STEP } until i = START;
  delocal i = START`.  The reverse-count loop returns i to START (touching
  nothing else), so the delocal is no longer self-referential and inverts
  cleanly — PyJanus would otherwise invert `delocal i=i` to an invalid
  `local i=i` and fail to reverse such a procedure.  Identity on everything else.
  """
  out: list = []
  for s in stmts:
    if isinstance(s, LocalStmt):
      body = _desugar_self_ref(s.body)
      var = s.enter_decl.ident.name
      start = s.enter_decl.init_expr
      exit_init = s.exit_decl.init_expr
      step = ((_counter_step(var, body[0].do_part) or _counter_step(var, body[0].loop_part))
              if len(body) == 1 and isinstance(body[0], FromStmt) else None)
      if (exit_init is not None and _references(exit_init, var)
          and start is not None and not _references(start, var) and step):
        cond = body[0].exit_cond
        lv = Lval(Ident(var, _DUMMY_POS), [])
        dec = (AssignStmt(ModOp.SUB_EQ, lv, Number(step, _DUMMY_POS), _DUMMY_POS) if step > 0
               else AssignStmt(ModOp.ADD_EQ, lv, Number(-step, _DUMMY_POS), _DUMMY_POS))
        back = FromStmt(cond, [dec], [],
                        BinExpr(BinOpKind.EQ, LvalExpr(lv, _DUMMY_POS), start, _DUMMY_POS), _DUMMY_POS)
        new_exit = LocalDecl(s.exit_decl.decl_type, s.exit_decl.typ, s.exit_decl.ident,
                             s.exit_decl.dimensions, start, s.exit_decl.pos)
        out.append(LocalStmt(s.enter_decl, body + [back], new_exit, s.pos))
      else:
        out.append(LocalStmt(s.enter_decl, body, s.exit_decl, s.pos))
    elif isinstance(s, FromStmt):
      out.append(FromStmt(s.entry_cond, _desugar_self_ref(s.do_part),
                          _desugar_self_ref(s.loop_part), s.exit_cond, s.pos))
    elif isinstance(s, IfStmt):
      out.append(IfStmt(s.entry_cond, _desugar_self_ref(s.if_part),
                        _desugar_self_ref(s.else_part), s.exit_cond, s.pos))
    elif isinstance(s, IterateStmt):
      out.append(IterateStmt(s.typ, s.ident, s.start_expr, s.step_expr, s.end_expr,
                             _desugar_self_ref(s.body), s.pos))
    elif isinstance(s, BareLocalStmt):
      out.append(BareLocalStmt(s.decl, _desugar_self_ref(s.body), s.pos))
    else:
      out.append(s)
  return out


def run_inverse(
  program: Program,
  final_store: dict[str, int],
) -> InverseResult:
  """Given a program and desired final state, compute the initial state.

  Steps:
  1. Invert the procedures using invert_program()
  2. Create a new main with variables initialized to final_store values
     and with inverted statements (reversing the main body)
  3. Run the inverted program
  4. Return the resulting store as the initial state
  """
  if program.main is None:
    return InverseResult(
      initial_store={},
      success=False,
      error="No main procedure defined",
    )

  try:
    # Desugar self-referential `delocal` counter idioms first, so the (forward-
    # equivalent) main and procedures invert without producing an invalid
    # `local i=i`.  Identity on programs that do not use the construct.
    desugared_main = ProcMain(
      program.main.vdecls, _desugar_self_ref(program.main.stmts), program.main.pos)
    desugared_procs = [
      Proc(p.procname, p.params, _desugar_self_ref(p.body)) for p in program.procs]

    inv_main = _build_inverted_main(
      desugared_main, final_store, _struct_field_dims(program.struct_defs))

    # Use original (non-inverted) procedures: the inverted main swaps
    # call→uncall (global_mode=False), and the runtime's uncall handler
    # locally inverts each procedure body at execution time.
    inv_program = Program(inv_main, desugared_procs, program.struct_defs)

    rt = Runtime(inv_program)
    rt.run()

    initial_store = _extract_store(rt)

    return InverseResult(initial_store=initial_store, success=True)
  except Exception as exc:
    return InverseResult(
      initial_store={},
      success=False,
      error=str(exc),
    )


def run_inverse_from_source(
  source: str,
  final_values: dict[str, int],
) -> InverseResult:
  """Parse source, run inverse, return initial state."""
  try:
    program = parse_program("inverse_input.ja", source)
    validate_program(program)
  except Exception as exc:
    return InverseResult(
      initial_store={},
      success=False,
      error=f"Parse/validation error: {exc}",
    )
  return run_inverse(program, final_values)


def verify_inverse(
  program: Program,
  initial_store: dict[str, int],
  final_store: dict[str, int],
) -> bool:
  """Verify that running the program with initial_store produces final_store.

  Builds a program with variables initialized to initial_store values,
  runs it forward, and checks the result matches final_store.
  """
  if program.main is None:
    return False

  new_vdecls: list[Vdecl] = []
  for vdecl in program.main.vdecls:
    name = vdecl.ident.name
    if name in initial_store:
      init_expr = _make_init_expr(initial_store[name])
      new_vdecl = Vdecl(
        decl_type=vdecl.decl_type,
        typ=vdecl.typ,
        ident=vdecl.ident,
        dimensions=vdecl.dimensions,
        init_expr=init_expr,
        pos=vdecl.pos,
      )
      new_vdecls.append(new_vdecl)
    else:
      new_vdecls.append(vdecl)

  fwd_main = ProcMain(new_vdecls, program.main.stmts, program.main.pos)
  fwd_program = Program(fwd_main, program.procs, program.struct_defs)

  try:
    rt = Runtime(fwd_program)
    rt.run()
    result_store = _extract_store(rt)
  except Exception:
    return False

  for name, expected in final_store.items():
    if name not in result_store or result_store[name] != expected:
      return False
  return True


def find_input(
  program: Program,
  output_var: str,
  target_value: object,
  free_vars: list[str],
  search_range: range = range(0, 100),
) -> dict[str, object] | None:
  """Brute-force search for inputs that produce a desired output.

  Tries all combinations of free_vars values within search_range.
  Returns the first combination where the output_var equals target_value,
  or None if no solution is found.
  """
  if program.main is None:
    return None

  for combo in itertools.product(search_range, repeat=len(free_vars)):
    var_values = dict(zip(free_vars, combo))

    new_vdecls: list[Vdecl] = []
    for vdecl in program.main.vdecls:
      name = vdecl.ident.name
      if name in var_values:
        init_expr = Number(var_values[name], _DUMMY_POS)
        new_vdecl = Vdecl(
          decl_type=vdecl.decl_type,
          typ=vdecl.typ,
          ident=vdecl.ident,
          dimensions=vdecl.dimensions,
          init_expr=init_expr,
          pos=vdecl.pos,
        )
        new_vdecls.append(new_vdecl)
      else:
        new_vdecls.append(vdecl)

    fwd_main = ProcMain(new_vdecls, program.main.stmts, program.main.pos)
    fwd_program = Program(fwd_main, program.procs, program.struct_defs)

    try:
      rt = Runtime(fwd_program)
      rt.run()
      result_store = _extract_store(rt)
    except Exception:
      continue

    if output_var in result_store and result_store[output_var] == target_value:
      return var_values

  return None
