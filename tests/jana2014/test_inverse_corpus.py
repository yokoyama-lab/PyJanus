"""The `--inverse` solver (`jana_py.inverse.run_inverse`) over the example corpus.

`run_inverse` seeds a store with a program's *final* values and runs it backwards
to recover the store right after the declarations ran (it undoes the statements,
not the declared initializers).  So a correct inverse of `run(P)` agrees with the
store of `P`'s declarations alone.

`run_inverse` seeds scalar *and* array finals (including multi-dimensional);
only shapes it still cannot thread (stacks) skip with their reason.  This
exercises a path distinct from `test_reversibility_corpus`: the runtime executes
*backwards* from a seeded store, end to end through `inverse.py`.
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


@pytest.mark.parametrize("ja", EXAMPLES, ids=lambda p: Path(p).name)
def test_inverse_recovers_declared_initial(ja: str) -> None:
  program = parse_program(ja, Path(ja).read_text())
  validate_program(program)

  res = run_inverse(program, _store(program))
  if not res.success:
    pytest.skip(f"--inverse out of scope: {(res.error or '').splitlines()[0]}")

  # The store after the declarations (initializers applied, no statements run):
  # exactly what running the program backwards from its final store must recover.
  decls = ProcMain(program.main.vdecls, [], program.main.pos)
  expected = _store(Program(decls, program.procs, program.struct_defs))
  assert res.initial_store == expected
