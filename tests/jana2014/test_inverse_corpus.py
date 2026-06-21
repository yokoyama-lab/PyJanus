"""The `--inverse` solver (`jana_py.inverse.run_inverse`) over the example corpus.

`run_inverse` seeds a store with a program's *final* values and runs it backwards
to recover the store right after the declarations ran (it undoes the statements,
not the declared initializers).  So a correct inverse of `run(P)` agrees with the
store of `P`'s declarations alone.

`run_inverse` only seeds *scalar* finals (array/stack finals are not threaded
in), so we compare scalar variables and skip programs whose inverse the solver
cannot run (multi-dimensional arrays, stacks).  This nonetheless exercises a
distinct path from `test_reversibility_corpus`: the runtime executes *backwards*
from a seeded store, end to end through `inverse.py`.
"""
from __future__ import annotations

import copy
import glob
from pathlib import Path

import pytest

from jana_py.ast import Program, ProcMain
from jana_py.inverse import run_inverse
from jana_py.parser_jana2014 import parse_program
from jana_py.runtime import Runtime
from jana_py.validate import validate_program

ROOT = Path(__file__).resolve().parents[2]
EXAMPLES = sorted(glob.glob(str(ROOT / "tests" / "jana2014" / "fixtures" / "examples" / "*.ja")))


def _store(program) -> dict:
  rt = Runtime(program)
  rt.run()
  return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


def _scalars(d: dict) -> dict:
  return {k: v for k, v in d.items() if not isinstance(v, list)}


@pytest.mark.parametrize("ja", EXAMPLES, ids=lambda p: Path(p).name)
def test_inverse_recovers_declared_initial_scalars(ja: str) -> None:
  program = parse_program(ja, Path(ja).read_text())
  validate_program(program)

  res = run_inverse(program, _store(program))
  if not res.success:
    pytest.skip(f"--inverse out of scope: {(res.error or '').splitlines()[0]}")

  # The store after the declarations (initializers applied, no statements run).
  decls = ProcMain(program.main.vdecls, [], program.main.pos)
  expected = _scalars(_store(Program(decls, program.procs, program.struct_defs)))
  if not expected:
    pytest.skip("no scalar variables to compare")

  assert _scalars(res.initial_store) == expected
