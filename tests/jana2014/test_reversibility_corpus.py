"""Corpus-wide reversibility: running each example forward then inverted is the
identity on the store.

For every example program we run `main`'s body and then its *local* inverse
(`call`->`uncall`), executed by the interpreter, and check the store returns to
its initial value.  This exercises backward execution across the real programs
(recursion, arrays, local/delocal, stacks, iterate) -- the part of `runtime.py`
the unit tests touch least.

A program that is genuinely *not* reversible is expected to fail this and is
marked accordingly (e.g. `injective_iterate` uses `delocal i = i`, whose inverse
`local i = i` reads an undeclared variable).
"""
from __future__ import annotations

import copy
import glob
from pathlib import Path

import pytest

from jana_py.ast import Program, ProcMain
from jana_py.invert import invert_stmts
from jana_py.parser_jana2014 import parse_program
from jana_py.runtime import Runtime
from jana_py.validate import validate_program

ROOT = Path(__file__).resolve().parents[2]
EXAMPLES = sorted(glob.glob(str(ROOT / "tests" / "jana2014" / "fixtures" / "examples" / "*.ja")))

# Programs that legitimately are not reversible (so forward;inverse != identity).
NOT_REVERSIBLE = {"injective_iterate.ja"}  # delocal int i = i


def _store(program: Program) -> dict:
  rt = Runtime(program)
  rt.run()
  return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


@pytest.mark.parametrize("ja", EXAMPLES, ids=lambda p: Path(p).name)
def test_forward_then_inverse_is_identity(ja: str) -> None:
  program = parse_program(ja, Path(ja).read_text())
  validate_program(program)

  # Initial store: the declarations/initializers with no statements run.
  init = ProcMain(program.main.vdecls, [], program.main.pos)
  s_init = _store(Program(init, program.procs, program.struct_defs))

  # Roundtrip: the body followed by its local inverse (`call` -> `uncall`).
  body = list(program.main.stmts) + invert_stmts(program.main.stmts, global_mode=False)
  roundtrip = ProcMain(program.main.vdecls, body, program.main.pos)

  if Path(ja).name in NOT_REVERSIBLE:
    with pytest.raises(Exception):
      _store(Program(roundtrip, program.procs, program.struct_defs))
    return

  s_round = _store(Program(roundtrip, program.procs, program.struct_defs))
  assert s_round == s_init
