"""Program equivalence checker for Jana programs.

Checks if two reversible programs compute the same function by
exhaustive testing on bounded inputs.
"""
from __future__ import annotations

import copy
import itertools
from dataclasses import dataclass, replace

from .ast import (
    DeclType,
    Number,
    ProcMain,
    Program,
    SourcePos,
    Vdecl,
)
from .invert import invert_stmts
from .runtime import Runtime


_DUMMY_POS = SourcePos("equiv", 0, 0)


@dataclass
class EquivResult:
    """Result of an equivalence check."""
    equivalent: bool
    tested: int
    counterexample: dict | None = None
    diff: tuple[dict, dict] | None = None


def _extract_store(program: Program) -> dict[str, object]:
    """Run a program and return the final variable store as {name: value}."""
    rt = Runtime(program)
    rt.run()
    assert rt._root_frame is not None
    return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


def _set_input_values(program: Program, values: dict[str, int]) -> Program:
    """Return a copy of the program with specified variable init values."""
    if program.main is None:
        return program
    new_vdecls: list[Vdecl] = []
    for vdecl in program.main.vdecls:
        if vdecl.ident.name in values:
            new_vdecl = replace(
                vdecl,
                init_expr=Number(values[vdecl.ident.name], _DUMMY_POS),
            )
            new_vdecls.append(new_vdecl)
        else:
            new_vdecls.append(vdecl)
    new_main = replace(program.main, vdecls=new_vdecls)
    return replace(program, main=new_main)


def check_equivalence(
    prog_a: Program,
    prog_b: Program,
    input_vars: list[str],
    input_range: range = range(-8, 9),
    max_combinations: int = 10000,
) -> EquivResult:
    """Check if two programs compute the same function.

    For each combination of values for input_vars (from input_range),
    sets those variables in both programs, runs them, and compares
    the final stores.

    Args:
        prog_a: First program.
        prog_b: Second program.
        input_vars: Variable names to vary across inputs.
        input_range: Range of values to try for each variable.
        max_combinations: Safety limit on total combinations tested.

    Returns:
        EquivResult with equivalence verdict and optional counterexample.
    """
    tested = 0
    for combo in itertools.islice(
        itertools.product(input_range, repeat=len(input_vars)),
        max_combinations,
    ):
        assignment = dict(zip(input_vars, combo))
        pa = _set_input_values(prog_a, assignment)
        pb = _set_input_values(prog_b, assignment)
        try:
            store_a = _extract_store(pa)
        except Exception:
            store_a = None
        try:
            store_b = _extract_store(pb)
        except Exception:
            store_b = None
        tested += 1
        if store_a != store_b:
            return EquivResult(
                equivalent=False,
                tested=tested,
                counterexample=assignment,
                diff=(store_a, store_b),
            )
    return EquivResult(equivalent=True, tested=tested)


def _make_identity_program(prog: Program) -> Program:
    """Return a program whose main body does nothing (identity)."""
    if prog.main is None:
        raise ValueError("Program has no main procedure")
    from .ast import SkipStmt
    new_main = replace(prog.main, stmts=[SkipStmt(_DUMMY_POS)])
    return replace(prog, main=new_main)


def _make_composed_program(
    prog: Program, extra_stmts: list,
) -> Program:
    """Return a program whose main body is prog's body followed by extra_stmts."""
    if prog.main is None:
        raise ValueError("Program has no main procedure")
    new_main = replace(
        prog.main,
        stmts=list(prog.main.stmts) + extra_stmts,
    )
    return replace(prog, main=new_main)


def check_inverse(
    prog: Program,
    input_vars: list[str],
    input_range: range = range(-8, 9),
    max_combinations: int = 10000,
) -> EquivResult:
    """Verify that prog; invert(prog) = identity for all tested inputs.

    Constructs a program that runs the main body forwards then backwards,
    and checks that all variables return to their initial values.

    Args:
        prog: Program to test.
        input_vars: Variable names to vary.
        input_range: Range of values for each variable.
        max_combinations: Safety limit.

    Returns:
        EquivResult indicating whether the round-trip is the identity.
    """
    if prog.main is None:
        raise ValueError("Program has no main procedure")

    inv_stmts = invert_stmts(prog.main.stmts, global_mode=False)
    composed = _make_composed_program(prog, inv_stmts)
    identity = _make_identity_program(prog)

    return check_equivalence(
        composed, identity, input_vars,
        input_range=input_range,
        max_combinations=max_combinations,
    )


def check_self_inverse(
    prog: Program,
    input_vars: list[str],
    input_range: range = range(-8, 9),
    max_combinations: int = 10000,
) -> EquivResult:
    """Verify that prog; prog = identity (program is its own inverse).

    Args:
        prog: Program to test.
        input_vars: Variable names to vary.
        input_range: Range of values for each variable.
        max_combinations: Safety limit.

    Returns:
        EquivResult indicating whether running the program twice
        is the identity.
    """
    if prog.main is None:
        raise ValueError("Program has no main procedure")

    doubled = _make_composed_program(prog, list(prog.main.stmts))
    identity = _make_identity_program(prog)

    return check_equivalence(
        doubled, identity, input_vars,
        input_range=input_range,
        max_combinations=max_combinations,
    )
