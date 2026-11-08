"""Independent finite-domain oracles and restoration checks for clean searches.

The expected answers use Python membership, list.count and bisect_left, not a
translation of the reversible control flow. Both the complete input array and
all output seeds must be restored by uncall. This is testing, not a proof of the
interpreter or of all possible integer inputs.
"""
from __future__ import annotations

from bisect import bisect_left
import contextlib
import copy
from functools import lru_cache
import io
import itertools
from pathlib import Path

import pytest

from jana_py.ast import Program, ProcMain
from jana_py.invert import invert_stmts
from jana_py.parser_jana2014 import parse_program
from jana_py.runtime import Runtime
from jana_py.validate import validate_program

EXAMPLES = Path(__file__).parent / "fixtures" / "examples"
# (sample, procedure, output kind, sorted prefix, sentinel contract)
CASES = [
  ("linear_search_c", "first_position", "position", False, None),
  ("linear_search_c", "flag_keep_position", "flag_position", False, None),
  ("linear_search_c", "flag_clean", "flag", False, None),
  ("linear_search_c", "count_matches", "count", False, None),
  ("linear_search_c", "flag_count_clean", "flag", False, None),
  ("sorted_linear_search_c", "sorted_lower_bound", "bound", True, None),
  ("sorted_linear_search_c", "sorted_flag_keep_bound", "flag_bound", True, None),
  ("sorted_linear_search_c", "sorted_flag_clean", "flag", True, None),
  ("sorted_linear_search_c", "sorted_first_position_clean", "first_xor", True, None),
  ("binary_lifting_search_c", "binary_lifting_bound", "bound", True, None),
  ("binary_lifting_search_c", "binary_lifting_flag_clean", "flag", True, None),
  ("binary_lifting_search_c", "binary_lifting_first_clean", "first_xor", True, None),
  ("binary_lifting_search_c", "binary_lifting_first_selective", "position", True, None),
  ("sentinel_search_c", "sentinel_position_ready", "position", False, "ready"),
  ("sentinel_search_c", "sentinel_position_zero", "position", False, "zero"),
  ("sentinel_search_c", "sentinel_position_saved", "position", False, "saved"),
  ("sentinel_search_c", "sentinel_flag_ready", "flag", False, "ready"),
  ("sentinel_search_c", "sentinel_flag_zero", "flag", False, "zero"),
  ("sentinel_search_c", "sentinel_flag_saved", "flag", False, "saved"),
  ("sentinel_search_c", "sentinel_flag_keep_zero", "flag_position", False, "zero"),
  ("sentinel_search_c", "sorted_sentinel_bound_ready", "bound", True, "threshold"),
  ("sentinel_search_c", "sorted_sentinel_flag_ready", "flag", True, "threshold"),
  ("sentinel_search_c", "sorted_sentinel_flag_zero", "flag", True, "zero"),
  ("sentinel_search_c", "sorted_sentinel_flag_saved", "flag", True, "saved"),
]


@lru_cache(maxsize=None)
def sample(stem):
  path = EXAMPLES / (stem + ".ja")
  program = parse_program(str(path), path.read_text())
  validate_program(program)
  return program


def run(program, stmts):
  main = ProcMain(program.main.vdecls, stmts, program.main.pos)
  p = Program(main, program.procs, program.struct_defs)
  with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
    runtime = Runtime(p, std="jana2014")
    runtime.run()
  return {name: copy.deepcopy(cell.value)
          for name, cell in runtime._root_frame.vars.items()}


def check_case(case, values, key, seed=0, old_slot=0):
  stem, procedure, kind, sorted_input, sentinel = case
  n = len(values)
  data = list(values) + ([old_slot] if sentinel else [])
  if not data:
    # PyJanus arrays have positive capacity; the unused cell is not input.
    data = [73]
  outputs = ["out", "p"] if kind.startswith("flag_") else ["out"]
  args = ["a", "key"]
  if procedure not in ("sentinel_position_ready", "sorted_sentinel_bound_ready"):
    args.append("n")
  args.extend(outputs)
  lines = ["procedure main()", f"  int a[{len(data)}]", "  int key", "  int n"]
  lines += [f"  int {name}" for name in outputs]
  lines += [f"  a[{i}] += {value}" for i, value in enumerate(data)]
  lines += [f"  key += {key}", f"  n += {n}", f"  out += {seed}",
            f"  call {procedure}({', '.join(args)})"]
  main = parse_program("<search-test>", "\n".join(lines) + "\n").main
  original = sample(stem)
  program = Program(main, original.procs, original.struct_defs)
  validate_program(program)
  setup = list(main.stmts[:-1])
  query = main.stmts[-1:]
  before = run(program, setup)
  after = run(program, list(main.stmts))
  back = run(program, list(main.stmts) + invert_stmts(query, global_mode=False))
  first = next((i for i, value in enumerate(values) if value == key), n)
  bound = bisect_left(values, key) if sorted_input else None
  if kind == "position":
    wanted = first
  elif kind == "bound":
    wanted = bound
  elif kind == "first_xor":
    wanted = seed ^ first
  elif kind == "count":
    wanted = seed + values.count(key)
  else:
    wanted = seed ^ int(key in values)
  context = (procedure, values, key, seed, old_slot)
  assert after["out"] == wanted, context
  if kind == "flag_position":
    assert after["p"] == first, context
  if kind == "flag_bound":
    assert after["p"] == bound, context
  assert {name: after[name] for name in ("a", "key", "n")} == {
    name: before[name] for name in ("a", "key", "n")}, context
  # Locals must have been removed, not merely hidden among final garbage.
  assert set(after) == set(before), context
  assert back == before, context


@pytest.mark.parametrize("case", CASES, ids=lambda case: case[1])
@pytest.mark.parametrize("n", range(5))
def test_exhaustive_small_prefixes(case, n):
  _, _, kind, sorted_input, sentinel = case
  arrays = (itertools.combinations_with_replacement((-1, 0, 1), n)
            if sorted_input else itertools.product((-1, 0, 1), repeat=n))
  for values in arrays:
    for key in (-2, -1, 0, 1, 2):
      seeds = (0,) if kind in ("position", "bound") else (0, 7)
      slots = ((key,) if sentinel == "ready" else
               (key, key + 5) if sentinel == "threshold" else
               (-3, 0, 11) if sentinel == "saved" else (0,))
      for seed in seeds:
        for old_slot in slots:
          check_case(case, list(values), key, seed, old_slot)


@pytest.mark.parametrize("n", (7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65))
def test_binary_lifting_power_boundaries(n):
  # Include the old fixed-width example's missing endpoint: key > max.
  values = [i // 3 - 10 for i in range(n)]
  for case in CASES:
    if case[0] != "binary_lifting_search_c":
      continue
    for key in (values[0] - 1, values[0], 0, values[-1], values[-1] + 1):
      for seed in ((0,) if case[2] in ("position", "bound") else (0, 7)):
        check_case(case, values, key, seed)
