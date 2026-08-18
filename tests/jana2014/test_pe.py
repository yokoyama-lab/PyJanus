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
from jana_py.ast import Program, ProcMain, Proc, LvalExpr, Lval, Vdecl, DeclType, Number, ArrayExpr, SourcePos, CallStmt
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
