"""Static (syntactic) cost prediction for Jana programs.

This is the analyzer half of the RC-03 "resource atlas" work: from the AST
alone it predicts three facts about the dynamic resource vector measured by
``jana_py.pebble`` (``steps``, ``stack_peak``, ``call_depth_peak``,
``total_calls``, ...):

1. **Call depth.**  The call graph over procedures (``call``/``uncall``
   edges, starting from ``main``) is built and checked for cycles.  When it
   is acyclic, ``H`` = length of the longest path from ``main`` bounds the
   dynamic call depth: ``call_depth_peak <= H``.

2. **Stack-freeness.**  If no ``push``/``pop`` statement occurs in any
   procedure reachable from ``main`` then no Janus ``stack`` can ever be
   non-empty, so ``stack_peak = 0`` for every input.  (``uncall`` of a
   procedure turns its ``pop`` into ``push``, so both statement kinds are
   treated as "stack-using".)

3. **Call count.**  If the call graph is acyclic and no reachable procedure
   has a ``call``/``uncall`` inside a loop body (``from`` do/loop parts,
   ``iterate`` body, ``foreach`` body), then the number of call events is
   input-independent and bounded by the static count
   ``calls(P) = sum over call sites in P of (1 + calls(callee))``;
   ``total_calls <= calls(main)``.  A call inside a loop, or recursion,
   makes the bound infinite (``None``).

All three predictions are *sound* upper bounds / certificates: a
measurement that violates one is a bug either here or in the profiler
(see ``tests/resource_atlas/compare.py``).

Usage::

    from jana_py.costcheck import analyze
    pred = analyze(program)        # program: validated jana_py.ast.Program
    pred.depth_bound, pred.stack_free, pred.calls_bound

or ``python3 -m jana_py.cli --std jana2014 --costcheck prog.ja``.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Iterator

from .ast import (
    AncillaBlockStmt,
    BareLocalStmt,
    CallStmt,
    ForeachStmt,
    FromStmt,
    IfStmt,
    IterateStmt,
    LocalStmt,
    PopStmt,
    Program,
    PushStmt,
    SwitchStmt,
    UncallStmt,
)

MAIN = "main"


# ---------------------------------------------------------------------------
# AST walking
# ---------------------------------------------------------------------------

def iter_stmts(stmts: list, in_loop: bool = False) -> Iterator[tuple[Any, bool]]:
    """Yield every statement in `stmts` (recursively) with a flag telling
    whether it is lexically inside a loop body.

    Descends every block carrier: If, From (do_part and loop_part), Iterate,
    Local, BareLocal, Switch (cases and default), AncillaBlock, Foreach.
    """
    for stmt in stmts:
        yield stmt, in_loop
        if isinstance(stmt, IfStmt):
            yield from iter_stmts(stmt.if_part, in_loop)
            yield from iter_stmts(stmt.else_part, in_loop)
        elif isinstance(stmt, FromStmt):
            # The do_part runs once per iteration too (it is re-executed
            # after every loop_part), so both parts are loop bodies.
            yield from iter_stmts(stmt.do_part, True)
            yield from iter_stmts(stmt.loop_part, True)
        elif isinstance(stmt, IterateStmt):
            yield from iter_stmts(stmt.body, True)
        elif isinstance(stmt, ForeachStmt):
            yield from iter_stmts(stmt.body, True)
        elif isinstance(stmt, (LocalStmt, BareLocalStmt, AncillaBlockStmt)):
            yield from iter_stmts(stmt.body, in_loop)
        elif isinstance(stmt, SwitchStmt):
            for case in stmt.cases:
                yield from iter_stmts(case.body, in_loop)
            yield from iter_stmts(stmt.default_part, in_loop)


# ---------------------------------------------------------------------------
# Result types
# ---------------------------------------------------------------------------

@dataclass
class ProcSummary:
    """Syntactic facts about one procedure body."""
    name: str
    call_sites: list[str] = field(default_factory=list)   # callee names, with multiplicity
    calls_in_loop: int = 0        # call/uncall statements lexically inside a loop body
    stack_stmts: int = 0          # push/pop statements
    loops: int = 0                # from/iterate/foreach statements


@dataclass
class CostPrediction:
    """Static predictions about the RC-03 resource vector of a program."""
    procs: dict[str, ProcSummary]
    reachable: list[str]                  # procedures reachable from main (main first)
    call_graph: dict[str, list[str]]      # reachable proc -> distinct callees
    undefined_callees: list[str]          # called but not defined (e.g. external)
    acyclic: bool
    depth_bound: int | None               # H: call_depth_peak <= H (None if cyclic)
    stack_free: bool                      # certified stack_peak == 0
    stack_stmts: int                      # push/pop statements in reachable procs
    call_in_loop: bool                    # some reachable proc calls inside a loop
    calls_bound: int | None               # C: total_calls <= C (None if unbounded)
    loops_reachable: int                  # loop statements in reachable procs

    def to_dict(self) -> dict[str, Any]:
        return {
            "reachable": list(self.reachable),
            "call_graph": {k: list(v) for k, v in self.call_graph.items()},
            "undefined_callees": list(self.undefined_callees),
            "acyclic": self.acyclic,
            "depth_bound": self.depth_bound,
            "stack_free": self.stack_free,
            "stack_stmts": self.stack_stmts,
            "call_in_loop": self.call_in_loop,
            "calls_bound": self.calls_bound,
            "loops_reachable": self.loops_reachable,
        }


# ---------------------------------------------------------------------------
# Analysis
# ---------------------------------------------------------------------------

def summarize_body(name: str, stmts: list) -> ProcSummary:
    summary = ProcSummary(name)
    for stmt, in_loop in iter_stmts(stmts):
        if isinstance(stmt, (CallStmt, UncallStmt)):
            summary.call_sites.append(stmt.ident.name)
            if in_loop:
                summary.calls_in_loop += 1
        elif isinstance(stmt, (PushStmt, PopStmt)):
            summary.stack_stmts += 1
        elif isinstance(stmt, (FromStmt, IterateStmt, ForeachStmt)):
            summary.loops += 1
    return summary


def analyze(program: Program) -> CostPrediction:
    """Compute the static cost prediction for a (validated) program."""
    procs: dict[str, ProcSummary] = {}
    if program.main is not None:
        procs[MAIN] = summarize_body(MAIN, program.main.stmts)
    for proc in program.procs:
        procs[proc.procname.name] = summarize_body(proc.procname.name, proc.body)

    # Reachability from main (BFS, deterministic order).
    reachable: list[str] = []
    undefined: list[str] = []
    if MAIN in procs:
        queue = [MAIN]
        seen = {MAIN}
        while queue:
            name = queue.pop(0)
            reachable.append(name)
            for callee in procs[name].call_sites:
                if callee not in procs:
                    if callee not in undefined:
                        undefined.append(callee)
                    continue
                if callee not in seen:
                    seen.add(callee)
                    queue.append(callee)
    call_graph = {
        name: sorted({c for c in procs[name].call_sites if c in procs})
        for name in reachable
    }

    # Cycle detection (DFS colouring) over the reachable subgraph.
    WHITE, GREY, BLACK = 0, 1, 2
    colour = {name: WHITE for name in reachable}
    acyclic = True

    def dfs(name: str) -> None:
        nonlocal acyclic
        colour[name] = GREY
        for callee in call_graph[name]:
            if colour[callee] == GREY:
                acyclic = False
            elif colour[callee] == WHITE:
                dfs(callee)
        colour[name] = BLACK

    if MAIN in colour:
        dfs(MAIN)

    # Longest path (call depth bound) and static call count, on a DAG.
    depth_bound: int | None = None
    calls_bound: int | None = None
    call_in_loop = any(procs[n].calls_in_loop > 0 for n in reachable)
    if acyclic and MAIN in procs:
        height: dict[str, int] = {}
        count: dict[str, int | None] = {}

        def visit(name: str) -> None:
            if name in height:
                return
            h = 0
            c: int | None = 0
            for callee in procs[name].call_sites:
                if callee not in procs:
                    # Undefined callee: no body to descend into; count the event.
                    if c is not None:
                        c += 1
                    h = max(h, 1)
                    continue
                visit(callee)
                h = max(h, 1 + height[callee])
                sub = count[callee]
                if c is not None:
                    c = None if sub is None else c + 1 + sub
            if procs[name].calls_in_loop > 0:
                c = None
            height[name] = h
            count[name] = c

        visit(MAIN)
        depth_bound = height[MAIN]
        calls_bound = count[MAIN]

    stack_stmts = sum(procs[n].stack_stmts for n in reachable)
    loops_reachable = sum(procs[n].loops for n in reachable)
    return CostPrediction(
        procs=procs,
        reachable=reachable,
        call_graph=call_graph,
        undefined_callees=undefined,
        acyclic=acyclic,
        depth_bound=depth_bound,
        stack_free=(stack_stmts == 0),
        stack_stmts=stack_stmts,
        call_in_loop=call_in_loop,
        calls_bound=calls_bound,
        loops_reachable=loops_reachable,
    )


def format_prediction(pred: CostPrediction) -> str:
    """Human-readable rendering of a prediction (for ``--costcheck``)."""
    inf = "unbounded"
    lines = [
        "=== Static cost prediction ===",
        f"Reachable procedures: {', '.join(pred.reachable) if pred.reachable else '(none)'}",
        f"Call graph acyclic:   {'yes' if pred.acyclic else 'no (recursion)'}",
        f"call_depth_peak <=    {pred.depth_bound if pred.depth_bound is not None else inf}",
        f"stack_peak == 0:      {'certified (no push/pop reachable)' if pred.stack_free else f'not certified ({pred.stack_stmts} push/pop statement(s) reachable)'}",
        f"call inside a loop:   {'yes' if pred.call_in_loop else 'no'}",
        f"total_calls <=        {pred.calls_bound if pred.calls_bound is not None else inf}",
    ]
    if pred.undefined_callees:
        lines.append(f"Undefined callees:    {', '.join(pred.undefined_callees)}")
    if pred.call_graph:
        lines.append("Call graph:")
        for name in pred.reachable:
            callees = pred.call_graph.get(name, [])
            lines.append(f"  {name} -> {', '.join(callees) if callees else '-'}")
    return "\n".join(lines)
