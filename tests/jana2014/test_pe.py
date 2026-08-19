"""Tests for jana_py.pe (partial evaluator) on the jana2014 example fixtures.

The PE-vs-inversion property checked here: for a division of *preserved*
parameters, inv(spec(P)) and spec(inv P) compute the same partial injection
(always), and with the assertion-driven rules they are textually equal for the
example procedures where the plain PE differs.
"""
import json, os, random
from dataclasses import replace
import pytest
from jana_py import pe as PE
from jana_py.ast import (
    Program, ProcMain, Proc, LvalExpr, Lval, Vdecl, DeclType, Number, ArrayExpr, SourcePos, CallStmt,
    Ident, IfStmt, AssignStmt, ModOp, BinExpr, BinOpKind, AssertStmt, Type, IntType,
)
from jana_py.cli import parse_for_std
from jana_py.preprocess import preprocess_text
from jana_py.validate import validate_program
from jana_py.invert import invert_stmts, invert_proc_globally
from jana_py.runtime import Runtime
from jana_py.errors import JanaError
from jana_py.format import formatter_for_std

EX = os.path.join(os.path.dirname(__file__), "fixtures", "examples")
FMT = formatter_for_std("jana2014")
POS = SourcePos("test", 0, 0)

def load(name):
    path = os.path.join(EX, name)
    text = open(path).read()
    pre = preprocess_text(path, text, include_dirs=[], std="jana2014")
    prog = parse_for_std("jana2014", path, pre.text, pre.line_origins)
    validate_program(prog, require_main=True)
    return prog

def init_expr(v):
    return ArrayExpr([Number(x, POS) for x in v], POS) if isinstance(v, list) else Number(v, POS)

def run_proc(prog, procs, proc, state, K=6):
    """Run `call proc(params)` from `state`; return ('ok', store) or ('fail', None)."""
    vds, args = [], []
    for p in proc.params:
        dims = [Number(K, POS)] if p.dimensions else []
        vds.append(Vdecl(DeclType.VARIABLE, p.typ, p.ident, dims, init_expr(state[p.ident.name]), POS))
        args.append(LvalExpr(Lval(p.ident, []), POS))
    main = ProcMain(vds, [CallStmt(proc.procname, args, False, POS)], POS)
    rt = Runtime(Program(main, procs, prog.struct_defs), std="jana2014")
    try:
        rt.run()
    except (JanaError, RecursionError, ZeroDivisionError):
        return ("fail", None)
    return ("ok", json.dumps({k: c.value for k, c in rt._root_frame.vars.items()}, sort_keys=True))

def run_synth(proc, procs, state):
    """Like run_proc, but for procedures built directly from ast constructors
    (no fixture program / struct defs, scalar params only)."""
    vds, args = [], []
    for p in proc.params:
        vds.append(Vdecl(DeclType.VARIABLE, p.typ, p.ident, [], init_expr(state[p.ident.name]), POS))
        args.append(LvalExpr(Lval(p.ident, []), POS))
    main = ProcMain(vds, [CallStmt(proc.procname, args, False, POS)], POS)
    rt = Runtime(Program(main, procs, []), std="jana2014")
    try:
        rt.run()
    except (JanaError, RecursionError, ZeroDivisionError):
        return ("fail", None)
    return ("ok", json.dumps({k: c.value for k, c in rt._root_frame.vars.items()}, sort_keys=True))

CASES = [
    ("next_permutation_g.ja", "find_pivot", {"p": [3, 1, 2, 5, 4, 0], "n": 6}),
    ("edit_script_g.ja", "mincell", {"up": 2, "left": 3, "diag": 1, "c": 1}),
    ("adaptive_huffman_c.ja", "emit", {"v": 2, "w": 1}),
    ("ppm_lite_c.ja", "hufmax", {"cnt": [1, 2, 3, 0, 0, 0], "ctx": 0}),
    ("ppm_lite_c.ja", "ppm_dec", {"bits": [0, 1, 0, 0, 0, 0], "nbits": 3, "n": 2}),
]

def both(prog, P, sv, **rules):
    peP, _ = PE.specialize_with(P, sv, **rules)
    inv_peP = Proc(P.procname, P.params, invert_stmts(peP.body, True))
    pe_invP, _ = PE.specialize_with(invert_proc_globally(P), sv, **rules)
    return inv_peP, pe_invP

@pytest.mark.parametrize("fname,pname,sv", CASES)
def test_semantic_commutation(fname, pname, sv):
    prog = load(fname); P = next(p for p in prog.procs if p.procname.name == pname)
    inv_peP, pe_invP = both(prog, P, sv, cut_paths=True, global_cut=True, exit_seed=True)
    invP = invert_proc_globally(P)
    others = [invert_proc_globally(p) for p in prog.procs if p.procname.name != pname]
    rng = random.Random(0)
    for _ in range(15):
        st = {}
        for p in P.params:
            n = p.ident.name
            st[n] = sv[n] if n in sv else ([rng.randint(0, 6) for _ in range(6)] if p.dimensions else rng.randint(0, 6))
        outs = {run_proc(prog, others + [q], q, st) for q in (invP, inv_peP, pe_invP)}
        assert len(outs) == 1, (st, outs)

@pytest.mark.parametrize("fname,pname,sv", [c for c in CASES if c[1] in ("mincell", "emit", "hufmax", "ppm_dec")])
def test_if_asymmetry_closed_by_cutting_failing_paths(fname, pname, sv):
    prog = load(fname); P = next(p for p in prog.procs if p.procname.name == pname)
    plain = both(prog, P, sv, cut_paths=False, global_cut=False, exit_seed=False)
    assert FMT.format_proc(plain[0]) != FMT.format_proc(plain[1])          # plain PE: asymmetric
    full = both(prog, P, sv, cut_paths=True, global_cut=True, exit_seed=False)
    assert FMT.format_proc(full[0]) == FMT.format_proc(full[1])            # Mogensen sec.4 rules: textually equal

def test_exit_seed_removes_loop_asymmetry():
    from jana_py.ast import FromStmt
    prog = load("next_permutation_g.ja"); P = next(p for p in prog.procs if p.procname.name == "find_pivot")
    sv = CASES[0][2]
    def has_loop(stmts):
        return any(isinstance(s, FromStmt) or any(has_loop(getattr(s, n)) for n in ("body", "if_part", "else_part", "do_part", "loop_part") if hasattr(s, n)) for s in stmts)
    _, pe_invP_plain = both(prog, P, sv, cut_paths=False, global_cut=False, exit_seed=False)
    assert has_loop(pe_invP_plain.body)
    _, pe_invP_seed = both(prog, P, sv, cut_paths=False, global_cut=False, exit_seed=True)
    assert not has_loop(pe_invP_seed.body)

def test_global_cut_only_removes_failing_paths():
    # decreasekey: both branches survive globally, so the if must stay (soundness of rule iv)
    prog = load("binary_heap_g.ja"); P = next(p for p in prog.procs if p.procname.name == "decreasekey")
    from jana_py.ast import FromStmt
    peP, _ = PE.specialize_with(P, {"i": 2, "key": 3}, cut_paths=True, global_cut=True, exit_seed=True)
    txt = FMT.format_proc(peP)
    assert "from" in txt and "loop" in txt

def test_pe_is_not_identity():
    prog = load("ppm_lite_c.ja"); P = next(p for p in prog.procs if p.procname.name == "hufmax")
    peP, _ = PE.specialize_with(P, CASES[3][2])
    assert PE.count(peP.body) < PE.count(P.body)


# ---- Mogensen Part 2, sec. 4 end: combine adjacent dynamic assertions ----

def test_combine_asserts_merges_adjacent_dynamic_asserts():
    x = Ident("x", POS)
    def xv(): return LvalExpr(Lval(x, []), POS)
    def gt0(): return AssertStmt(BinExpr(BinOpKind.GT, xv(), Number(0, POS), POS), POS)
    def lt10(): return AssertStmt(BinExpr(BinOpKind.LT, xv(), Number(10, POS), POS), POS)
    def ne5(): return AssertStmt(BinExpr(BinOpKind.NEQ, xv(), Number(5, POS), POS), POS)

    stmts = [gt0(), lt10(), ne5()]
    merged = PE.combine_asserts(stmts)
    assert len(merged) == 1
    assert isinstance(merged[0], AssertStmt)
    assert isinstance(merged[0].expr, BinExpr) and merged[0].expr.op == BinOpKind.LAND

    # recurses into nested if/else bodies
    f = Ident("f", POS)
    cond = BinExpr(BinOpKind.EQ, LvalExpr(Lval(f, []), POS), Number(1, POS), POS)
    nested = [IfStmt(cond, [gt0(), lt10()], [ne5(), gt0()], cond, POS)]
    merged_nested = PE.combine_asserts(nested)
    assert len(merged_nested[0].if_part) == 1
    assert len(merged_nested[0].else_part) == 1

    # meaning is preserved: same ('ok'|'fail') outcome before/after merging, for every x
    xdecl = Vdecl(DeclType.VARIABLE, Type("int", POS, IntType.UNBOUND), x, [], None, POS)
    proc_before = Proc(Ident("chk", POS), [xdecl], stmts)
    proc_after = Proc(Ident("chk", POS), [xdecl], merged)
    for xval in range(-2, 12):
        before = run_synth(proc_before, [proc_before], {"x": xval})
        after = run_synth(proc_after, [proc_after], {"x": xval})
        assert before == after, (xval, before, after)


# ---- Mogensen Part 2, sec. 5.2: polyvariant specialisation of calls/uncalls ----

def _make_step_driver(n_calls):
    """Mirrors Mogensen's own illustrative example (Fig. 5 -> Fig. 6, sec. 5.3):
    `step(j, flag, x)` never reads `j`; `driver` calls it `n_calls` times with a
    different (unused) `j` each time but the same static `flag=1`, which lets the
    `if` collapse. Polyvariant specialisation should produce exactly ONE residual
    `step` (deduplicated on the *used* static arguments only), with a
    single-statement body (the `if` resolved away)."""
    j, flag, x = Ident("j", POS), Ident("flag", POS), Ident("x", POS)
    def vdecl(ident): return Vdecl(DeclType.VARIABLE, Type("int", POS, IntType.UNBOUND), ident, [], None, POS)
    def lv(ident): return LvalExpr(Lval(ident, []), POS)
    cond = BinExpr(BinOpKind.EQ, lv(flag), Number(1, POS), POS)
    step = Proc(Ident("step", POS), [vdecl(j), vdecl(flag), vdecl(x)], [
        IfStmt(cond,
               [AssignStmt(ModOp.ADD_EQ, Lval(x, []), Number(100, POS), POS)],
               [AssignStmt(ModOp.ADD_EQ, Lval(x, []), Number(1, POS), POS)],
               cond, POS),
    ])
    body = [CallStmt(Ident("step", POS), [Number(k, POS), Number(1, POS), lv(x)], False, POS) for k in range(n_calls)]
    driver = Proc(Ident("driver", POS), [vdecl(x)], body)
    return driver, step

def test_polyvariant_dedups_on_unused_static_argument():
    driver, step = _make_step_driver(5)
    procs = [driver, step]
    residual, callees, _S = PE.specialize_program(driver, {}, procs, polyvariant=True)
    assert len(callees) == 1, [c.procname.name for c in callees]     # 5 different j's, 1 residual step
    assert [p.ident.name for p in callees[0].params] == ["x"]        # j (unused) and flag (baked) both gone
    assert PE.count(callees[0].body) == 1                            # the if collapsed to one assignment
    assert all(isinstance(s, CallStmt) and s.ident.name == callees[0].procname.name for s in residual.body)

def test_polyvariant_reduces_residual_size():
    driver, step = _make_step_driver(5)
    procs = [driver, step]
    residual, callees, _S = PE.specialize_program(driver, {}, procs, polyvariant=True)
    residual0, callees0, _S0 = PE.specialize_program(driver, {}, procs, polyvariant=False)
    assert callees0 == []
    total_poly = PE.count(residual.body) + sum(PE.count(c.body) for c in callees)
    total_plain = PE.count(residual0.body) + PE.count(step.body)   # step is still required, unspecialised
    assert total_poly < total_plain, (total_poly, total_plain)

    # meaning is preserved for both polyvariant=True and polyvariant=False
    others = [q for q in procs if q.procname.name != "driver"]
    for xval in range(4):
        out_orig = run_synth(driver, procs, {"x": xval})
        out_poly = run_synth(residual, others + callees + [residual], {"x": xval})
        out_plain = run_synth(residual0, others + callees0 + [residual0], {"x": xval})
        assert out_orig == out_poly == out_plain, (xval, out_orig, out_poly, out_plain)

POLY_CASES = [
    ("ppm_lite_c.ja", "ppm_dec", {"bits": [0, 1, 0, 0, 0, 0], "nbits": 3, "n": 2}, 6),
    ("binary_heap_g.ja", "decreasekey", {"i": 3, "key": 5}, 8),
]

@pytest.mark.parametrize("fname,pname,sv,K", POLY_CASES)
def test_polyvariant_preserves_semantics(fname, pname, sv, K):
    """ppm_dec (calls/uncalls hufmax) and decreasekey (calls/uncalls parent):
    residual (body + any residual callees) must behave exactly like the
    original over random inputs, failures included -- and polyvariant=False
    must reproduce plain specialize_with() exactly (existing API unchanged)."""
    prog = load(fname)
    P = next(p for p in prog.procs if p.procname.name == pname)
    others = [q for q in prog.procs if q.procname.name != pname]

    residual, callees, _S = PE.specialize_program(P, sv, prog.procs, polyvariant=True)
    procs_poly = others + callees + [residual]

    residual0, callees0, _S0 = PE.specialize_program(P, sv, prog.procs, polyvariant=False, merge_asserts=False)
    assert callees0 == []
    residual_old, _S_old = PE.specialize_with(P, sv, cut_paths=True, global_cut=True, exit_seed=True)
    assert FMT.format_proc(residual0) == FMT.format_proc(residual_old)   # polyvariant=False == existing API

    rng = random.Random(0)
    for _ in range(15):
        st = {}
        for p in P.params:
            n = p.ident.name
            st[n] = sv[n] if n in sv else ([rng.randint(0, K - 1) for _ in range(K)] if p.dimensions else rng.randint(0, K - 1))
        out_orig = run_proc(prog, prog.procs, P, st, K=K)
        out_poly = run_proc(prog, procs_poly, residual, st, K=K)
        assert out_orig == out_poly, (st, out_orig, out_poly)


def test_feed_back_eliminates_the_block():
    """Rule (v): once the backward seeding has discovered the entry value of the
    block variable, the block disappears and the two residuals coincide."""
    from jana_py.ast import LocalStmt
    prog = load("next_permutation_g.ja")
    P = next(p for p in prog.procs if p.procname.name == "find_pivot")
    sv = CASES[0][2]
    rules = dict(cut_paths=True, global_cut=True, exit_seed=True)
    peP, _ = PE.specialize_with(P, sv, feed_back=True, **rules)
    inv_peP = Proc(P.procname, P.params, invert_stmts(peP.body, True))
    pe_invP, _ = PE.specialize_with(invert_proc_globally(P), sv, feed_back=True, **rules)
    assert not any(isinstance(s, LocalStmt) for s in pe_invP.body)
    assert FMT.format_proc(inv_peP) == FMT.format_proc(pe_invP)
    # without feed_back the block survives, so the test is not vacuous
    without, _ = PE.specialize_with(invert_proc_globally(P), sv, feed_back=False, **rules)
    assert any(isinstance(s, LocalStmt) for s in without.body)


def test_divergence_key_includes_the_decision_counter():
    """Cycle detection must not fire on a loop that terminates only because a
    speculative decision (rule (iv)) advances; the decision counter is part of
    the key.  `decreasekey` exercises the combination."""
    prog = load("binary_heap_g.ja")
    P = next(p for p in prog.procs if p.procname.name == "decreasekey")
    res, _ = PE.specialize_with(P, {"i": 2, "key": 3}, cut_paths=True, global_cut=True,
                                exit_seed=True, feed_back=True)
    assert PE.count(res.body) > 0
