#!/usr/bin/env python3
"""How the corpus actually uses stacks — the input to "can we bound the depth?".

`docs/loop-queue.md` defers the stack encoding because a stack is unbounded
state, so the design question a human has to answer first is whether a *static*
depth bound exists.  That question is not answered by counting how many programs
declare a stack; it is answered by looking at where the pushes are.  A push in
straight-line code contributes a known amount.  A push inside a loop does not,
unless the loop's trip count is itself static.

So this reports, per program: how many stacks it declares, whether more than one
is live at a time, which operations it uses, and — the deciding column — whether
every push sits outside a loop.

    python3 tools/stack_usage.py            # table
    python3 tools/stack_usage.py --md       # markdown

It reads the AST only; it never compiles or runs anything, so it terminates on
the programs whose compilation does not (see `docs/totality-checking.md` §16.3).
"""
from __future__ import annotations

import argparse
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from jana_py import ast as A                       # noqa: E402
from jana_py import parser_jana2014, preprocess    # noqa: E402

CORPUS = "tests/jana2014/fixtures/examples/*.ja"
LOOPS = (A.FromStmt, A.IterateStmt)


def walk(node, in_loop: bool = False):
  """(statement, is it inside a loop) over a whole procedure body."""
  if isinstance(node, (list, tuple)):
    for x in node:
      yield from walk(x, in_loop)
    return
  if not isinstance(node, A.Stmt):
    return
  yield node, in_loop
  inner = in_loop or isinstance(node, LOOPS)
  for field in ("if_part", "else_part", "do_part", "loop_part", "body"):
    sub = getattr(node, field, None)
    if sub is not None:
      yield from walk(sub, inner)


def unbounded_procs(program) -> set[str]:
  """Procedures that can run an unbounded number of times.

  Two ways: the procedure is on a call cycle, or it is called from inside a
  loop.  Both propagate along calls — and that propagation is the whole point.
  `hanoi_c` pushes in `move`, which is neither recursive nor inside a loop; it
  is *called by* the recursion.  Judging by the pushing procedure alone called
  that program statically bounded, which is the opposite of true.
  """
  edges: dict[str, set[str]] = {}
  seeds: set[str] = set()
  units = ([program.main] if program.main else []) + list(program.procs)
  for unit in units:
    name = unit.procname.name if getattr(unit, "procname", None) else "<main>"
    callees = set()
    body = getattr(unit, "stmts", None) or getattr(unit, "body", None) or []
    for st, in_loop in walk(body):
      if isinstance(st, (A.CallStmt, A.UncallStmt)):
        callees.add(st.ident.name)
        if in_loop:
          seeds.add(st.ident.name)      # called from a loop
    edges[name] = callees

  # procedures on a call cycle
  colour: dict[str, int] = {}

  def visit(n, path):
    if n in path:
      seeds.update(path[path.index(n):])
      return
    if colour.get(n):
      return
    colour[n] = 1
    for m in edges.get(n, ()):
      visit(m, path + [n])

  for n in list(edges):
    visit(n, [])

  # everything reachable from a seed is equally unbounded
  out, work = set(seeds), list(seeds)
  while work:
    n = work.pop()
    for m in edges.get(n, ()):
      if m not in out:
        out.add(m)
        work.append(m)
  return out


def usage(path: pathlib.Path) -> dict | None:
  try:
    pt = preprocess.preprocess_text(str(path), path.read_text(encoding="utf-8"),
                                    None, "jana2014")
    program = parser_jana2014.parse_program(str(path), pt.text, pt.line_origins)
  except Exception:
    return None

  stacks, pushes, pops, pushes_in_loop, pops_in_loop = set(), 0, 0, 0, 0
  pushes_unbounded = 0
  unbounded = unbounded_procs(program)
  units = ([program.main] if program.main else []) + list(program.procs)
  for unit in units:
    uname = unit.procname.name if getattr(unit, "procname", None) else "<main>"
    in_unbounded = uname in unbounded
    decls = (getattr(unit, "vdecls", None) or getattr(unit, "params", None) or [])
    for decl in decls:
      if getattr(decl.typ, "kind", None) == "stack":
        stacks.add(decl.ident.name)
    body = getattr(unit, "stmts", None) or getattr(unit, "body", None) or []
    for stmt, in_loop in walk(body):
      if isinstance(stmt, A.PushStmt):
        pushes += 1
        pushes_in_loop += in_loop
        pushes_unbounded += in_unbounded
      elif isinstance(stmt, A.PopStmt):
        pops += 1
        pops_in_loop += in_loop
  if not stacks and not pushes and not pops:
    return None
  return {
      "name": path.name,
      "stacks": len(stacks),
      "push": pushes, "push_in_loop": pushes_in_loop,
      "push_unbounded": pushes_unbounded,
      "pop": pops, "pop_in_loop": pops_in_loop,
  }


def main(argv=None) -> int:
  ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
  ap.add_argument("--glob", default=CORPUS)
  ap.add_argument("--md", action="store_true")
  args = ap.parse_args(argv)

  rows = [u for p in sorted(ROOT.glob(args.glob)) if (u := usage(p))]
  bounded = [r for r in rows
             if r["push_in_loop"] == 0 and r["push_unbounded"] == 0]

  if args.md:
    print("| プログラム | stack 数 | push（うちループ内） | pop（うちループ内） | 深さの静的上界 |")
    print("|---|---:|---:|---:|---|")
    for r in rows:
      ok = ("**取れる**" if r in bounded else
            "取れない（再帰・ループから到達）" if r["push_unbounded"]
            else "取れない（ループ）")
      print(f"| `{r['name']}` | {r['stacks']} | {r['push']}（{r['push_in_loop']}） "
            f"| {r['pop']}（{r['pop_in_loop']}） | {ok} |")
  else:
    for r in rows:
      print(f"{r['name']:<30} stacks={r['stacks']} push={r['push']}"
            f"({r['push_in_loop']} in loop, {r['push_unbounded']} unbounded)"
            f" pop={r['pop']}({r['pop_in_loop']})")

  print(f"\nstack を使う: {len(rows)} 本")
  print(f"同時に2本以上の stack: {sum(1 for r in rows if r['stacks'] > 1)} 本")
  print(f"push がループ内: {sum(1 for r in rows if r['push_in_loop'])} 本 / "
        f"再帰・ループから到達する手続き内: {sum(1 for r in rows if r['push_unbounded'])} 本")
  print(f"**push がループにも「無限に呼ばれうる手続き」にも入らない＝深さの静的上界が取れる: {len(bounded)} 本**"
        + (f"  → {', '.join(r['name'] for r in bounded)}" if bounded else ""))
  return 0


if __name__ == "__main__":
  sys.exit(main())
