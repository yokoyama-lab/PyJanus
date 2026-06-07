"""Inverse interpreter for Jana: given a program and its final state, compute
the initial state that would produce it.

Since Jana programs are reversible, running the inverted program on the final
state yields the initial state.
"""
from __future__ import annotations

import copy
import itertools
from dataclasses import dataclass, replace

from .ast import DeclType
from .ast import Ident
from .ast import IntType
from .ast import Number
from .ast import ProcMain
from .ast import Program
from .ast import SourcePos
from .ast import Type
from .ast import Vdecl
from .invert import invert_stmts
from .invert import invert_program
from .parser_jana2014 import parse_program
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


def _make_init_expr(value: object) -> "Number | None":
  """Create an AST init expression for a scalar int value."""
  if isinstance(value, int):
    return Number(value, _DUMMY_POS)
  return None


def _build_inverted_main(
  original_main: ProcMain,
  final_store: dict[str, int],
) -> ProcMain:
  """Build a new main procedure for the inverted program.

  The inverted main:
  1. Declares the same variables but with init values from final_store
  2. Runs the inverted statements of the original main
  """
  new_vdecls: list[Vdecl] = []
  for vdecl in original_main.vdecls:
    name = vdecl.ident.name
    if name in final_store:
      init_expr = _make_init_expr(final_store[name])
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

  inverted_stmts = invert_stmts(original_main.stmts, global_mode=False)

  return ProcMain(new_vdecls, inverted_stmts, original_main.pos)


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
    inv_main = _build_inverted_main(program.main, final_store)

    # Use original (non-inverted) procedures: the inverted main swaps
    # call→uncall (global_mode=False), and the runtime's uncall handler
    # locally inverts each procedure body at execution time.
    inv_program = Program(inv_main, list(program.procs), program.struct_defs)

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
