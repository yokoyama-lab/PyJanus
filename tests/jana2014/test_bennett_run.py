"""Run the *actual* output of `bennett_embed` through the interpreter.

The existing Bennett tests check the generated AST shape and hand-write the
compute-copy-uncompute pattern by hand; none executes `bennett_embed`'s own
output.  These do, and pin the two properties of Bennett's construction (the
runnable counterpart of `coq/RevBennett.v`):
  * correctness + garbage-freeness: the output register gets f(input), the input
    is preserved, and the modified working variable is left untouched (its
    ancilla shadow is computed and uncomputed);
  * reversibility: running the embedded block then its inverse restores the store.
"""
from __future__ import annotations

import copy

from jana_py.ast import Program, ProcMain
from jana_py.bennett import bennett_embed
from jana_py.invert import invert_stmts
from jana_py.parser_jana2014 import parse_program
from jana_py.runtime import Runtime
from jana_py.validate import validate_program


def _run(program: Program) -> dict:
  validate_program(program)
  rt = Runtime(program)
  rt.run()
  return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


def _embed(src: str, output_map: dict[str, str]):
  """Parse `src`, Bennett-embed its main body, return (forward_prog, parsed)."""
  parsed = parse_program("b.ja", src)
  validate_program(parsed)
  embedded = bennett_embed(parsed.main.stmts, output_map)
  main = ProcMain(parsed.main.vdecls, embedded, parsed.main.pos)
  return Program(main, parsed.procs, parsed.struct_defs), parsed, embedded


DOUBLE = "procedure main()\n    int y = 5\n    int out\n    int x\n    x += y * 2\n"
MULTI = ("procedure main()\n    int y = 3\n    int z = 7\n    int out\n    int x\n"
         "    x += y\n    x += z\n")


def test_embed_computes_and_is_garbage_free():
  prog, _, _ = _embed(DOUBLE, {"x": "out"})
  s = _run(prog)
  assert s["out"] == 10          # f(y) = y*2
  assert s["y"] == 5             # input preserved
  assert s["x"] == 0             # working var untouched (computed via ancilla, uncomputed)


def test_embed_multistep():
  prog, _, _ = _embed(MULTI, {"x": "out"})
  s = _run(prog)
  assert s["out"] == 10 and s["y"] == 3 and s["z"] == 7 and s["x"] == 0


def test_embed_is_reversible():
  _, parsed, embedded = _embed(DOUBLE, {"x": "out"})
  roundtrip = list(embedded) + invert_stmts(embedded, global_mode=False)
  main = ProcMain(parsed.main.vdecls, roundtrip, parsed.main.pos)
  s = _run(Program(main, parsed.procs, parsed.struct_defs))
  assert s["out"] == 0 and s["y"] == 5 and s["x"] == 0   # forward; inverse = identity


# Computations whose body exercises the if / loop / swap renamers in bennett.py.
IF_COMP = ("procedure main()\n    int flag = 1\n    int out\n    int x\n"
           "    if flag = 1 then\n        x += 10\n    else\n        x += 20\n    fi flag = 1\n")
LOOP_COMP = ("procedure main()\n    int n = 3\n    int out\n    int x\n    int i\n"
             "    from i = 0 do\n        x += 2\n    loop\n        i += 1\n    until i = n\n")
SWAP_COMP = ("procedure main()\n    int a = 3\n    int b = 7\n    int out\n    int x\n    int w\n"
             "    x += a\n    w += b\n    x <=> w\n")


def _run_and_invert(src: str, output_map: dict[str, str]):
  prog, parsed, embedded = _embed(src, output_map)
  forward = _run(prog)
  roundtrip = list(embedded) + invert_stmts(embedded, global_mode=False)
  main = ProcMain(parsed.main.vdecls, roundtrip, parsed.main.pos)
  back = _run(Program(main, parsed.procs, parsed.struct_defs))
  return forward, back


def test_embed_if_branch():
  fwd, back = _run_and_invert(IF_COMP, {"x": "out"})
  assert fwd["out"] == 10 and fwd["flag"] == 1 and fwd["x"] == 0   # then-branch, garbage-free
  assert back["out"] == 0 and back["x"] == 0                       # reversible


def test_embed_loop():
  fwd, back = _run_and_invert(LOOP_COMP, {"x": "out"})
  assert fwd["out"] == 8 and fwd["n"] == 3 and fwd["x"] == 0 and fwd["i"] == 0
  assert back["out"] == 0


def test_embed_swap():
  fwd, back = _run_and_invert(SWAP_COMP, {"x": "out"})
  assert fwd["out"] == 7 and fwd["a"] == 3 and fwd["b"] == 7      # x<=>w gave x=b=7
  assert fwd["x"] == 0 and fwd["w"] == 0
  assert back["out"] == 0
