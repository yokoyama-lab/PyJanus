"""Offline partial evaluator for Jana procedures (Mogensen-style), with the
assertion-driven rules studied in the PE-vs-inversion experiment:

  (i)/(iii)/(iv)  branch resolution by exit assertions, local and global
                  (Mogensen, PSI 2011, sec. 4: cutting away failing paths);
  (ii)            exit-seeded loop unrolling: unroll the *inverse* loop from the
                  static delocal value and invert the result back.

Public API:
  specialize(proc, static_vals, rules=Rules(...)) -> (residual Proc, static set)
  prune(stmts)     -- drop branches killed by a constant exit condition
  count(stmts)     -- statement count (size metric)
The division is a set of *preserved* parameters (never modified by the
procedure) with concrete values; a flow-insensitive, monovariant BTA (one
binding time per variable) is computed by fixpoint, as in Mogensen 2011.
"""
from __future__ import annotations
import copy
import hashlib
from dataclasses import replace, dataclass
from .ast import *
from .invert import invert_stmts

POS = SourcePos("pe", 0, 0)
class PEError(Exception): pass
DUAL = set()
RULE5 = False   # feed the discovered entry value back and re-specialise forwards
EXIT_SEED_GENERAL = False

class Diverges(PEError):
    """Unrolling a static loop revisited a static store.

    Sound because the exit condition of an unrolled loop reads static variables
    only: an identical static store yields an identical exit decision, so the
    loop can never terminate.  Complete whenever the static store takes finitely
    many values along the unrolling; the fuel is the fallback for the rest.
    """
    pass


class SeedEscaped(PEError):
    """A seeded (dual) variable would be updated under dynamic control, so the
    value carried in the static store would go stale."""
    pass


def T(v): return Boolean(True, POS)
def num(v): return Number(int(v), POS)

def _eq(a, b):
    """`a == b` with a constant on the right, so both directions of the
    specialiser build the same assertion text."""
    if isinstance(a, Number) and not isinstance(b, Number): a, b = b, a
    return BinExpr(BinOpKind.EQ, a, b, POS)

def vars_of(e, acc=None):
    """Variables read by an expression."""
    acc = set() if acc is None else acc
    if isinstance(e, LvalExpr):
        acc.add(e.lval.ident.name)
        for i in e.lval.indices: vars_of(i, acc)
    elif isinstance(e, BinExpr): vars_of(e.left, acc); vars_of(e.right, acc)
    elif isinstance(e, (UnaryExpr, TypeCastExpr)): vars_of(e.expr, acc)
    elif isinstance(e, TernaryExpr):
        for x in (e.cond, e.then_expr, e.else_expr): vars_of(x, acc)
    elif isinstance(e, (EmptyExpr, TopExpr, SizeExpr)): acc.add(e.ident.name)
    elif isinstance(e, ArrayExpr):
        for x in e.items: vars_of(x, acc)
    return acc

def _has_stack_expr(e):
    if isinstance(e, (NilExpr, EmptyExpr, TopExpr)): return True
    if isinstance(e, BinExpr): return _has_stack_expr(e.left) or _has_stack_expr(e.right)
    if isinstance(e, UnaryExpr): return _has_stack_expr(e.expr)
    return False

def is_static_expr(e, S):
    return vars_of(e) <= S and not _has_stack_expr(e)

def evalx(e, st):
    if isinstance(e, Number): return e.value
    if isinstance(e, Boolean): return int(e.value)
    if isinstance(e, LvalExpr):
        v = st[e.lval.ident.name]
        for i in e.lval.indices: v = v[evalx(i, st)]
        return v
    if isinstance(e, UnaryExpr):
        x = evalx(e.expr, st)
        return int(not x) if e.op == UnaryOpKind.NOT else ~x
    if isinstance(e, BinExpr):
        a, b = evalx(e.left, st), evalx(e.right, st)
        k = e.op
        if k == BinOpKind.ADD: return a + b
        if k == BinOpKind.SUB: return a - b
        if k == BinOpKind.MUL: return a * b
        if k == BinOpKind.DIV: return int(a / b)
        if k == BinOpKind.MOD: return a - int(a / b) * b
        if k == BinOpKind.AND: return a & b
        if k == BinOpKind.OR: return a | b
        if k == BinOpKind.XOR: return a ^ b
        if k == BinOpKind.SL: return a << b
        if k == BinOpKind.SR: return a >> b
        if k == BinOpKind.LAND: return int(bool(a) and bool(b))
        if k == BinOpKind.LOR: return int(bool(a) or bool(b))
        if k == BinOpKind.GT: return int(a > b)
        if k == BinOpKind.LT: return int(a < b)
        if k == BinOpKind.EQ: return int(a == b)
        if k == BinOpKind.NEQ: return int(a != b)
        if k == BinOpKind.GE: return int(a >= b)
        if k == BinOpKind.LE: return int(a <= b)
    raise PEError(f"cannot evaluate {type(e).__name__}")

def fold(e, S, st):
    """Residual expression: static sub-expressions replaced by their values."""
    if is_static_expr(e, S):
        try: return num(evalx(e, st))
        except PEError: return e
    if isinstance(e, BinExpr): return replace(e, left=fold(e.left, S, st), right=fold(e.right, S, st))
    if isinstance(e, UnaryExpr): return replace(e, expr=fold(e.expr, S, st))
    if isinstance(e, LvalExpr):
        return replace(e, lval=replace(e.lval, selectors=[LvalIndex(fold(s.expr, S, st)) if isinstance(s, LvalIndex) else s for s in e.lval.selectors]))
    return e

def fold_lval(lv, S, st):
    return replace(lv, selectors=[LvalIndex(fold(s.expr, S, st)) if isinstance(s, LvalIndex) else s for s in lv.selectors])

def assign(st, lv, f):
    name = lv.ident.name
    if not lv.indices: st[name] = f(st[name]); return
    ref = st[name]
    idx = [evalx(i, st) for i in lv.indices]
    for i in idx[:-1]: ref = ref[i]
    ref[idx[-1]] = f(ref[idx[-1]])

def assert_stmt(cond_expr, want_true, S, st):
    """Return [] if statically satisfied, residual assert if dynamic, raise if statically violated."""
    if is_static_expr(cond_expr, S):
        v = bool(evalx(cond_expr, st))
        if v != want_true: raise PEError("static assertion violated at PE time")
        return []
    e = fold(cond_expr, S, st)
    if not want_true: e = UnaryExpr(UnaryOpKind.NOT, e, POS)
    return [AssertStmt(e, POS)]

def pe(stmts, S, st, dctx=False, fuel=[10000]):
    out = []
    for s in stmts:
        fuel[0] -= 1
        if fuel[0] < 0: raise PEError("fuel exhausted (unbounded unrolling?)")
        if isinstance(s, AssignStmt):
            v = s.lval.ident.name
            if v in S and not dctx:
                x = evalx(s.expr, st)
                op = {ModOp.ADD_EQ: lambda a: a + x, ModOp.SUB_EQ: lambda a: a - x, ModOp.XOR_EQ: lambda a: a ^ x,
                      ModOp.MUL_EQ: lambda a: a * x, ModOp.DIV_EQ: lambda a: int(a / x)}[s.mod_op]
                assign(st, s.lval, op)
                if v in DUAL: out.append(replace(s, expr=num(x)))
            else:
                if v in DUAL: raise SeedEscaped(v)
                out.append(replace(s, lval=fold_lval(s.lval, S, st), expr=fold(s.expr, S, st)))
        elif isinstance(s, SwapStmt):
            l, r = s.left.ident.name, s.right.ident.name
            if l in S and r in S and not dctx:
                a = evalx(LvalExpr(s.left, POS), st); b = evalx(LvalExpr(s.right, POS), st)
                assign(st, s.left, lambda _: b); assign(st, s.right, lambda _: a)
            else:
                if l in DUAL or r in DUAL: raise SeedEscaped(l if l in DUAL else r)
                out.append(replace(s, left=fold_lval(s.left, S, st), right=fold_lval(s.right, S, st)))
        elif isinstance(s, IfStmt):
            if is_static_expr(s.entry_cond, S) and not dctx:
                if bool(evalx(s.entry_cond, st)):
                    out += pe(s.if_part, S, st, dctx, fuel); out += assert_stmt(s.exit_cond, True, S, st)
                else:
                    out += pe(s.else_part, S, st, dctx, fuel); out += assert_stmt(s.exit_cond, False, S, st)
            elif (s.pos.line, s.pos.column) in OPTIMISTIC and not dctx and is_static_expr(s.exit_cond, S):
                # rule (iii): resolve the branch by the (static) exit assertion, speculatively
                feas = []
                for want, part in ((True, s.if_part), (False, s.else_part)):
                    st2 = copy.deepcopy(st)
                    try:
                        res = pe(part, S, st2, False, fuel)
                        if bool(evalx(s.exit_cond, st2)) == want: feas.append((want, res, st2))
                    except PEError:
                        pass
                if len(feas) == 0: raise PEError("both branches statically infeasible")
                if len(feas) == 2:
                    if not RULE4: raise Unresolvable(f"if@{s.pos.line}")
                    k = CHOICE[0]; CHOICE[0] += 1
                    if k >= len(DECISIONS): raise Ambiguous(k, s.pos.line)
                    feas = [feas[0] if DECISIONS[k] else feas[1]]
                want, res, st2 = feas[0]
                st.clear(); st.update(st2)
                e = fold(s.entry_cond, S, st)
                out.append(AssertStmt(e if want else UnaryExpr(UnaryOpKind.NOT, e, POS), POS)); out += res
            else:
                out.append(IfStmt(fold(s.entry_cond, S, st), pe(s.if_part, S, st, True, fuel),
                                  pe(s.else_part, S, st, True, fuel), fold(s.exit_cond, S, st), s.pos))
        elif isinstance(s, FromStmt):
            if is_static_expr(s.exit_cond, S) and not dctx:
                first = True
                seen = set()
                while True:
                    key = _snapshot(S, st)
                    if key in seen: raise Diverges(f"loop@{s.pos.line}")
                    seen.add(key)
                    out += assert_stmt(s.entry_cond, first, S, st); first = False
                    out += pe(s.do_part, S, st, dctx, fuel)
                    if bool(evalx(s.exit_cond, st)): break
                    out += pe(s.loop_part, S, st, dctx, fuel)
            else:
                out.append(FromStmt(fold(s.entry_cond, S, st), pe(s.do_part, S, st, True, fuel),
                                    pe(s.loop_part, S, st, True, fuel), fold(s.exit_cond, S, st), s.pos))
        elif isinstance(s, LocalStmt):
            v = s.enter_decl.ident.name
            if v in S and not dctx and s.enter_decl.typ.kind != "stack":
                st[v] = evalx(s.enter_decl.init_expr, st)
                out += pe(s.body, S, st, dctx, fuel)
                if is_static_expr(s.exit_decl.init_expr, S):
                    if evalx(s.exit_decl.init_expr, st) != st[v]: raise PEError("static delocal mismatch")
                else:
                    out.append(AssertStmt(_eq(num(st[v]), fold(s.exit_decl.init_expr, S, st)), POS))
                del st[v]
            else:
                ed = replace(s.enter_decl, init_expr=fold(s.enter_decl.init_expr, S, st) if s.enter_decl.init_expr is not None else None)
                xd = replace(s.exit_decl, init_expr=fold(s.exit_decl.init_expr, S, st) if s.exit_decl.init_expr is not None else None)
                res = exit_seeded(s, S, st, dctx, fuel) if EXIT_SEED else None
                if res is not None and res[0] == "replace":
                    out += res[1]                      # rule (v): the block is gone
                else:
                    body = res[1] if res is not None else pe(s.body, S, st, dctx, fuel)
                    out.append(LocalStmt(ed, body, xd, s.pos))
        elif isinstance(s, IterateStmt):
            v = s.ident.name
            bounds_static = all(is_static_expr(e, S) for e in (s.start_expr, s.step_expr, s.end_expr))
            if bounds_static and not dctx and v in S:
                a, d, b = evalx(s.start_expr, st), evalx(s.step_expr, st), evalx(s.end_expr, st)
                if d == 0: raise PEError("zero step")
                if (a > b if d > 0 else a < b) if not s.exclusive else (a >= b if d > 0 else a <= b):
                    raise PEError("static iterate range empty (PyJanus fails on it)")
                if (a > b if d > 0 else a < b) if not s.exclusive else (a >= b if d > 0 else a <= b):
                    raise PEError("static iterate range empty (PyJanus fails on it)")
                cur = a
                while (cur < b if d > 0 else cur > b) if s.exclusive else (cur <= b if d > 0 else cur >= b):
                    st[v] = cur; out += pe(s.body, S, st, dctx, fuel); cur += d
                st.pop(v, None)
            else:
                out.append(replace(s, start_expr=fold(s.start_expr, S, st), step_expr=fold(s.step_expr, S, st),
                                   end_expr=fold(s.end_expr, S, st), body=pe(s.body, S, st, True, fuel)))
        elif isinstance(s, (CallStmt, UncallStmt)):
            if POLY is not None and s.ident.name in POLY.by_name:
                out.append(POLY.residualize(s, S, st))
            else:
                out.append(replace(s, args=[fold(a, S, st) for a in s.args]))
        elif isinstance(s, (PushStmt, PopStmt)):
            out.append(replace(s, expr=fold(s.expr, S, st)))
        elif isinstance(s, SkipStmt):
            pass
        elif isinstance(s, AssertStmt):
            out += assert_stmt(s.expr, True, S, st)
        else:
            raise PEError(f"unsupported {type(s).__name__}")
    return out

RULE3 = False
RULE4 = False          # global backtracking over ambiguous choice points (Mogensen Part 2 §4 style, exhaustive)
DECISIONS = []         # decisions taken so far for the current run (True = then-branch)
CHOICE = [0]           # counter of ambiguous choice points met in the current run
POLY = None             # active _PolyCtx (Mogensen §5.2 polyvariant call/uncall specialisation), or None
class Ambiguous(PEError): pass

def _all_ifs(stmts, acc):
    for s in stmts:
        if isinstance(s, IfStmt): acc.add((s.pos.line, s.pos.column))
        for name in ("body", "if_part", "else_part", "do_part", "loop_part"):
            if hasattr(s, name): _all_ifs(getattr(s, name), acc)
    return acc

def specialize(proc, static_vals):
    """Return residual Proc for the static division {name: value}.
    With RULE3, start optimistic (every if resolvable by its exit assertion) and
    drop the ifs that turn out unresolvable until the PE goes through."""
    global OPTIMISTIC
    OPTIMISTIC = _all_ifs(proc.body, set()) if RULE3 else set()
    global DECISIONS, CHOICE
    while True:
        S = static_set(proc, set(static_vals))
        try:
            if RULE4:
                body = _search(proc, S, static_vals)
            else:
                st = copy.deepcopy(static_vals); DECISIONS = []; CHOICE = [0]
                body = pe(proc.body, S, st, False, [10000])
            return Proc(proc.procname, proc.params, body), S
        except Unresolvable as e:
            line = int(str(e).split("@")[1])
            drop = {k for k in OPTIMISTIC if k[0] == line}
            if not drop: raise
            OPTIMISTIC = OPTIMISTIC - drop

OPTIMISTIC = set()   # ids (pos) of dynamic-entry ifs assumed resolvable by rule (iii)
class Unresolvable(PEError): pass

def static_set(proc, static0):
    """Flow-insensitive monovariant BTA (fixpoint): the set of static variables."""
    dyn = set(); static_all = [set(static0)]
    def is_static(e): return not (vars_of(e) & dyn) and vars_of(e) <= static_all[0] and not _has_stack_expr(e)
    def walk(stmts, dctx):
        for s in stmts:
            if isinstance(s, AssignStmt):
                v = s.lval.ident.name
                if dctx or not is_static(s.expr) or any(not is_static(i) for i in s.lval.indices) or v not in static_all[0]: dyn.add(v)
            elif isinstance(s, (CallStmt, UncallStmt)):
                if POLY is not None:
                    callee = POLY.by_name.get(s.ident.name)
                    if callee is None:
                        for a in s.args:
                            if isinstance(a, LvalExpr): dyn.add(a.lval.ident.name)
                    else:
                        callee_params = [v.ident.name for v in callee.params]
                        callee_mod = POLY.M.get(s.ident.name, set(callee_params))
                        for i in _call_dynamic_positions(s.args, callee_params, callee_mod):
                            a = s.args[i]
                            if isinstance(a, LvalExpr): dyn.add(a.lval.ident.name)
                            else: dyn.update(vars_of(a))
                else:
                    for a in s.args:
                        if isinstance(a, LvalExpr): dyn.add(a.lval.ident.name)
            elif isinstance(s, (PushStmt, PopStmt)): dyn.add(s.ident.name); dyn.update(vars_of(s.expr))
            elif isinstance(s, SwapStmt):
                l, r = s.left.ident.name, s.right.ident.name
                if dctx or l not in static_all[0] or r not in static_all[0] or any(not is_static(i) for i in s.left.indices + s.right.indices): dyn.add(l); dyn.add(r)
            elif isinstance(s, IfStmt):
                d = dctx or not (is_static(s.entry_cond) or ((s.pos.line, s.pos.column) in OPTIMISTIC and is_static(s.exit_cond)))
                walk(s.if_part, d); walk(s.else_part, d)
            elif isinstance(s, FromStmt):
                d = dctx or not is_static(s.exit_cond); walk(s.do_part, d); walk(s.loop_part, d)
            elif isinstance(s, IterateStmt):
                d = dctx or not (is_static(s.start_expr) and is_static(s.end_expr) and is_static(s.step_expr))
                if d: dyn.add(s.ident.name)
                else: static_all[0].add(s.ident.name)
                walk(s.body, d)
            elif isinstance(s, LocalStmt):
                v = s.enter_decl.ident.name
                if dctx or s.enter_decl.typ.kind == "stack" or s.enter_decl.init_expr is None or not is_static(s.enter_decl.init_expr): dyn.add(v)
                else: static_all[0].add(v)
                walk(s.body, dctx)
            else:
                for name in ("body", "if_part", "else_part", "do_part", "loop_part"):
                    if hasattr(s, name): walk(getattr(s, name), True)
                if hasattr(s, "ident") and not isinstance(s, (CallStmt, UncallStmt)): dyn.add(s.ident.name)
    prev = None
    while prev != (len(dyn), len(static_all[0])):
        prev = (len(dyn), len(static_all[0])); walk(proc.body, False); static_all[0] -= dyn
    return static_all[0]

def count(stmts):
    n = 0
    for s in stmts:
        n += 1
        for name in ("body", "if_part", "else_part", "do_part", "loop_part"):
            if hasattr(s, name): n += count(getattr(s, name))
    return n

# ---- post-pass: prune branches killed by a constant exit assertion ----
def _const(e):
    if isinstance(e, Number): return bool(e.value)
    if isinstance(e, Boolean): return e.value
    return None

def prune(stmts):
    out = []
    for s in stmts:
        if isinstance(s, IfStmt):
            c = _const(s.exit_cond)
            if c is True:   # else-branch would need exit false: dead
                out.append(AssertStmt(s.entry_cond, POS)); out += prune(s.if_part)
            elif c is False:
                out.append(AssertStmt(UnaryExpr(UnaryOpKind.NOT, s.entry_cond, POS), POS)); out += prune(s.else_part)
            else:
                out.append(replace(s, if_part=prune(s.if_part), else_part=prune(s.else_part)))
        elif isinstance(s, FromStmt):
            out.append(replace(s, do_part=prune(s.do_part), loop_part=prune(s.loop_part)))
        elif isinstance(s, (LocalStmt, IterateStmt)):
            out.append(replace(s, body=prune(s.body)))
        else:
            out.append(s)
    return out


# ---- rule (ii): exit-seeded loop unrolling = the other projection applied to one loop ----
EXIT_SEED = False

def exit_seeded(s, S, st, dctx, fuel):
    """Rule (ii): the first inversion projection applied inside one block.

    For `local v = <dyn> BODY delocal v = <static e>` whose BODY contains a loop
    that cannot be unrolled forwards, seed v with the delocal value e and
    specialise the *inverse* of the relevant code from that seed, then invert the
    residual back.  v is dual: its value drives specialisation and its updates are
    still emitted, so the residual moves v from its entry value to e.  An
    assertion pins the entry value.

    Two forms:
      narrow  (default) --- the loop is the last statement of the block; the
              prefix is specialised forwards first and only the loop is seeded;
      general (EXIT_SEED_GENERAL) --- the whole block body is inverted and
              specialised from the seed, so a prefix, a suffix and several loops
              are all covered.

    Soundness conditions.  The seed is the store at the exit of the seeded region,
    so that region must not modify any *other* static variable (its entry value
    would be used where the exit value is meant).  And a seeded variable must
    never be updated under dynamic control (`SeedEscaped`), because a residualised
    construct leaves the carried value stale.

    Returns the new body, or None when the pattern does not apply or when the
    backward route removes no loop (so the rule never makes a residual worse).
    """
    if dctx or not s.body: return None
    v = s.enter_decl.ident.name
    if s.exit_decl.init_expr is None or not is_static_expr(s.exit_decl.init_expr, S): return None
    if not _has_unrollable_gap(s.body, S): return None       # forward already does the job
    Sx = S | {v}
    global DUAL
    saved = DUAL

    if EXIT_SEED_GENERAL:
        if _assigned(s.body, set()) & S: return None
        st_seed, prefix, region = copy.deepcopy(st), [], s.body
    else:
        if not isinstance(s.body[-1], FromStmt): return None
        loop = s.body[-1]
        if not is_static_expr(loop.entry_cond, Sx): return None   # the inverse loop must unroll
        if _assigned([loop], set()) & S: return None
        st_work = copy.deepcopy(st)
        try:
            prefix = pe(s.body[:-1], S, st_work, dctx, fuel)      # prefix first: it moves the store
        except PEError:
            return None
        st_seed, region = st_work, [loop]

    try:
        st_seed[v] = evalx(s.exit_decl.init_expr, st) if EXIT_SEED_GENERAL else evalx(s.exit_decl.init_expr, st_seed)
    except PEError:
        return None
    DUAL = DUAL | {v}
    try:
        residual_inv = pe(invert_stmts(region, global_mode=False), Sx, st_seed, False, [4000])
    except PEError:
        return None
    finally:
        DUAL = saved
    seeded = prefix + invert_stmts(residual_inv, global_mode=False)
    try:
        plain = pe(s.body, S, copy.deepcopy(st), dctx, [4000])
    except PEError:
        plain = None
    if plain is not None and _residual_loops(seeded) >= _residual_loops(plain):
        return None
    entry_val = st_seed[v]
    lv = LvalExpr(Lval(Ident(v, POS), []), POS)

    # Rule (v): the backward pass has *discovered* the entry value of v.  Feed it
    # back as a binding time and specialise the block forwards in the ordinary
    # way; the block then disappears, and the residual has the same shape the
    # forward direction produces.  The guard states the discovered value in terms
    # of the block's initialiser, so v does not occur in the result.
    if RULE5 and not (_assigned(s.body, set()) & S) and s.enter_decl.init_expr is not None:
        st2 = copy.deepcopy(st); st2[v] = entry_val
        try:
            fwd = pe(s.body, S | {v}, st2, dctx, [4000])
            if evalx(s.exit_decl.init_expr, st2) != st2[v]:
                raise PEError("delocal mismatch after re-forward specialisation")
        except PEError:
            fwd = None
        if fwd is not None and not _mentions(fwd, v):
            try:
                guard5 = assert_stmt(_eq(s.enter_decl.init_expr, num(entry_val)), True, S, st)
            except PEError:
                guard5 = None
            if guard5 is not None:
                return ("replace", guard5 + fwd)

    seeded = invert_stmts(residual_inv, global_mode=False)

    # Rule (v), seeded case: the unrolling knew v at every point, so v survives in
    # the residual only as its own updates.  If nothing reads it, drop those
    # updates and the block; the wrapper was only there to carry the counter.
    if RULE5 and not prefix and not _reads(seeded, v):
        stripped = _drop_updates(seeded, v)
        if stripped is not None and s.enter_decl.init_expr is not None:
            try:
                guard5 = assert_stmt(_eq(s.enter_decl.init_expr, num(entry_val)), True, S, st)
            except PEError:
                guard5 = None                      # the seed contradicts a static initialiser
            if guard5 is not None:
                return ("replace", guard5 + stripped)

    guard = [AssertStmt(_eq(lv, num(entry_val)), POS)]
    return ("body", (prefix + guard + seeded) if not EXIT_SEED_GENERAL else (guard + seeded))


def _search(proc, S, static_vals, prefix=(), depth=0):
    """DFS over ambiguous choice points: return the residual body of the first
    globally consistent decision sequence; raise PEError if none."""
    global DECISIONS, CHOICE
    if depth > 64: raise PEError("choice depth")
    DECISIONS = list(prefix); CHOICE = [0]
    st = copy.deepcopy(static_vals)
    try:
        return pe(proc.body, S, st, False, [10000])
    except Ambiguous as a:
        k, line = a.args
        results = []
        for d in (True, False):
            try:
                results.append(_search(proc, S, static_vals, tuple(prefix) + (d,), depth + 1))
            except Unresolvable:
                raise
            except PEError:
                continue
        if len(results) == 1: return results[0]        # only one globally consistent path: cut the other (Mogensen §4)
        if len(results) == 2: raise Unresolvable(f"if@{line}")   # both survive: must stay a dynamic if (no path is failing)
        raise PEError("no consistent decision sequence")


def specialize_with(proc, static_vals, *, cut_paths=True, global_cut=True, exit_seed=True,
                    feed_back=False, seed_whole_block=False):
    """Convenience wrapper: set the rule flags for one call and restore them."""
    global RULE3, RULE4, RULE5, EXIT_SEED, EXIT_SEED_GENERAL
    saved = (RULE3, RULE4, RULE5, EXIT_SEED, EXIT_SEED_GENERAL)
    RULE3, RULE4, RULE5, EXIT_SEED, EXIT_SEED_GENERAL = \
        cut_paths, global_cut, feed_back, exit_seed, seed_whole_block
    try:
        return specialize(proc, static_vals)
    finally:
        RULE3, RULE4, RULE5, EXIT_SEED, EXIT_SEED_GENERAL = saved


# ---- Mogensen Part 2, sec. 4 (end): merge adjacent dynamic assertions ----
# "assert c1; assert c2" is rewritten to "assert c1 && c2". Recurses into
# nested bodies; a run of 3+ consecutive asserts collapses left-associatively.
def combine_asserts(stmts):
    out = []
    for s in stmts:
        for name in ("if_part", "else_part", "do_part", "loop_part", "body"):
            if hasattr(s, name):
                s = replace(s, **{name: combine_asserts(getattr(s, name))})
        if out and isinstance(out[-1], AssertStmt) and isinstance(s, AssertStmt):
            out[-1] = replace(out[-1], expr=BinExpr(BinOpKind.LAND, out[-1].expr, s.expr, POS))
        else:
            out.append(s)
    return out


# ---- Mogensen Part 2, sec. 5.2: polyvariant specialisation of procedure calls ----

def _call_dynamic_positions(args, callee_params, callee_mod):
    """Positions of `args` that MUST stay dynamic: bound to a formal that the
    callee (transitively) modifies, a non-l-value argument bound to such a
    formal (conservative: no single caller variable to attribute the write
    to), or an l-value argument whose base variable is aliased (passed more
    than once) in this same call (conservative: aliasing is not analysed)."""
    base = [a.lval.ident.name if isinstance(a, LvalExpr) else None for a in args]
    dup = {nm for nm in base if nm is not None and base.count(nm) > 1}
    out = set()
    for i, a in enumerate(args):
        fname = callee_params[i] if i < len(callee_params) else None
        modified = fname is None or fname in callee_mod
        if isinstance(a, LvalExpr):
            if modified or a.lval.ident.name in dup: out.add(i)
        elif modified:
            out.add(i)
    return out


def _modified_params(procs):
    """Fixpoint: for each proc, the subset of its own formal parameters that
    are modified (directly, or transitively through a call/uncall to another
    procedure that modifies the corresponding formal). Mirrors the language's
    own restriction that any variable a procedure call can modify is dynamic
    (Mogensen §5.2 / §3.1's output-variable rule, generalised to procedures)."""
    by_name = {p.procname.name: p for p in procs}
    M = {p.procname.name: set() for p in procs}
    changed = True
    while changed:
        changed = False
        for p in procs:
            name = p.procname.name
            own_params = {v.ident.name for v in p.params}
            mod = set(M[name])
            def walk(stmts):
                for s in stmts:
                    if isinstance(s, AssignStmt):
                        if s.lval.ident.name in own_params: mod.add(s.lval.ident.name)
                    elif isinstance(s, SwapStmt):
                        if s.left.ident.name in own_params: mod.add(s.left.ident.name)
                        if s.right.ident.name in own_params: mod.add(s.right.ident.name)
                    elif isinstance(s, (PushStmt, PopStmt)):
                        if s.ident.name in own_params: mod.add(s.ident.name)
                    elif isinstance(s, IfStmt):
                        walk(s.if_part); walk(s.else_part)
                    elif isinstance(s, FromStmt):
                        walk(s.do_part); walk(s.loop_part)
                    elif isinstance(s, (LocalStmt, IterateStmt)):
                        walk(s.body)
                    elif isinstance(s, (CallStmt, UncallStmt)):
                        callee = by_name.get(s.ident.name)
                        if callee is None:
                            for a in s.args:
                                if isinstance(a, LvalExpr) and a.lval.ident.name in own_params:
                                    mod.add(a.lval.ident.name)
                            continue
                        callee_params = [v.ident.name for v in callee.params]
                        callee_mod = M[callee.procname.name]
                        for i in _call_dynamic_positions(s.args, callee_params, callee_mod):
                            a = s.args[i]
                            if isinstance(a, LvalExpr):
                                if a.lval.ident.name in own_params: mod.add(a.lval.ident.name)
                            else:
                                mod.update(vars_of(a) & own_params)
            walk(p.body)
            if mod != M[name]:
                M[name] = mod; changed = True
    return M


def _mark_used(stmts, own_params, acc):
    """Add to `acc` every own_params variable that is *read* anywhere in
    `stmts` (directly; call/uncall argument propagation is handled by
    `_used_params`'s fixpoint driver, not here)."""
    for s in stmts:
        if isinstance(s, AssignStmt):
            acc.update(vars_of(s.expr) & own_params)
            for idx in s.lval.indices: acc.update(vars_of(idx) & own_params)
        elif isinstance(s, SwapStmt):
            for idx in s.left.indices: acc.update(vars_of(idx) & own_params)
            for idx in s.right.indices: acc.update(vars_of(idx) & own_params)
        elif isinstance(s, IfStmt):
            acc.update(vars_of(s.entry_cond) & own_params); acc.update(vars_of(s.exit_cond) & own_params)
            _mark_used(s.if_part, own_params, acc); _mark_used(s.else_part, own_params, acc)
        elif isinstance(s, FromStmt):
            acc.update(vars_of(s.entry_cond) & own_params); acc.update(vars_of(s.exit_cond) & own_params)
            _mark_used(s.do_part, own_params, acc); _mark_used(s.loop_part, own_params, acc)
        elif isinstance(s, LocalStmt):
            if s.enter_decl.init_expr is not None: acc.update(vars_of(s.enter_decl.init_expr) & own_params)
            if s.exit_decl.init_expr is not None: acc.update(vars_of(s.exit_decl.init_expr) & own_params)
            _mark_used(s.body, own_params, acc)
        elif isinstance(s, IterateStmt):
            for e in (s.start_expr, s.step_expr, s.end_expr): acc.update(vars_of(e) & own_params)
            _mark_used(s.body, own_params, acc)
        elif isinstance(s, (PushStmt, PopStmt)):
            acc.update(vars_of(s.expr) & own_params)
        elif isinstance(s, AssertStmt):
            acc.update(vars_of(s.expr) & own_params)
        # CallStmt/UncallStmt args: propagated by _used_params's fixpoint driver.
        # SkipStmt: nothing to read.


def _used_params(procs, M):
    """Fixpoint: for each proc, the subset of its own formal parameters whose
    *value* can affect the residual code -- referenced directly in the body,
    or passed on (unchanged, i.e. not itself in M) to a callee position that
    is itself used. Mogensen §5.2 "Avoiding code duplication": only these
    variables should key a procedure's specialisation."""
    by_name = {p.procname.name: p for p in procs}
    used = {p.procname.name: set() for p in procs}
    changed = True
    while changed:
        changed = False
        for p in procs:
            name = p.procname.name
            own_params = {v.ident.name for v in p.params}
            acc = set(used[name])
            _mark_used(p.body, own_params, acc)
            def scan_calls(stmts):
                for s in stmts:
                    if isinstance(s, (CallStmt, UncallStmt)):
                        callee = by_name.get(s.ident.name)
                        if callee is None:
                            for a in s.args:
                                if isinstance(a, LvalExpr): acc.update(vars_of(a) & own_params)
                            continue
                        callee_params = [v.ident.name for v in callee.params]
                        callee_used = used[callee.procname.name]
                        for i, a in enumerate(s.args):
                            if i < len(callee_params) and callee_params[i] in callee_used:
                                acc.update(vars_of(a) & own_params)
                    for attr in ("body", "if_part", "else_part", "do_part", "loop_part"):
                        if hasattr(s, attr): scan_calls(getattr(s, attr))
            scan_calls(p.body)
            if acc != used[name]:
                used[name] = acc; changed = True
    return used


def _freeze(v):
    return tuple(_freeze(x) for x in v) if isinstance(v, list) else v


def _residual_name(procname, key):
    if not key:
        return f"{procname}_0"
    payload = repr(sorted((k, _freeze(v)) for k, v in key.items()))
    h = int(hashlib.sha1(payload.encode()).hexdigest(), 16) % 10**8
    return f"{procname}_{h}"


class _PolyCtx:
    """Residualises call/uncall statements to specialised (polyvariant)
    procedures: a call whose actual argument for an unmodified formal is
    static is replaced by a call to a procedure specialised to that value;
    only the (transitively) modified or dynamic arguments remain in the
    residual call. Same (procname, static key) -> same residual procedure,
    memoised eagerly (before its body is specialised) so mutually recursive
    procedures terminate. `finish()` drains the queue and returns the made
    procedures; specialising one may enqueue more."""

    def __init__(self, by_name, M, USED):
        self.by_name = by_name
        self.M = M
        self.USED = USED
        self.memo = {}
        self.name_taken = set()
        self.queue = []

    def residualize(self, stmt, S, st):
        callee = self.by_name.get(stmt.ident.name)
        if callee is None:
            return replace(stmt, args=[fold(a, S, st) for a in stmt.args])
        procname = stmt.ident.name
        params = [p.ident.name for p in callee.params]
        mod = self.M.get(procname, set(params))
        dyn_pos = _call_dynamic_positions(stmt.args, params, mod)
        key, dyn_args = {}, []
        for i, a in enumerate(stmt.args):
            fname = params[i] if i < len(params) else None
            if i not in dyn_pos and fname is not None and is_static_expr(a, S):
                key[fname] = evalx(a, st)
            else:
                dyn_args.append(fold(a, S, st))
        if not key:
            # Nothing to specialise this call to: avoid creating a pointless
            # duplicate and just call the original procedure unchanged.
            return replace(stmt, args=dyn_args)
        residual_name = self._get_or_queue(procname, callee, key)
        Ctor = UncallStmt if isinstance(stmt, UncallStmt) else CallStmt
        return Ctor(Ident(residual_name, stmt.pos), dyn_args, stmt.external, stmt.pos)

    def _get_or_queue(self, procname, callee, key):
        used = self.USED.get(procname, {p.ident.name for p in callee.params})
        memo_key = (procname, tuple(sorted((k, _freeze(v)) for k, v in key.items() if k in used)))
        if memo_key in self.memo:
            return self.memo[memo_key]
        base_name = name = _residual_name(procname, key)
        n = 1
        while name in self.name_taken:
            name = f"{base_name}_{n}"; n += 1
        self.name_taken.add(name)
        self.memo[memo_key] = name
        self.queue.append((name, procname, callee, dict(key)))
        return name

    def finish(self):
        made = []
        while self.queue:
            name, procname, callee, key = self.queue.pop(0)
            residual, _S = specialize(callee, key)
            keep = [p for p in callee.params if p.ident.name not in key]
            made.append(Proc(Ident(name, POS), keep, residual.body))
        return made


def specialize_program(proc, static_vals, procs, *, cut_paths=True, global_cut=True,
                        exit_seed=True, polyvariant=True, merge_asserts=True):
    """Specialise `proc` for `static_vals`, with `procs` as the set of
    procedures that may be (transitively) called. Returns
    (residual_proc, residual_callees, static_set). With polyvariant=True
    (Mogensen §5.2), calls/uncalls with static arguments to unmodified
    formals are residualised to specialised procedures (memoised per
    (procname, static key), keyed only on the variables actually used --
    §5.2 "Avoiding code duplication"); with polyvariant=False, calls are
    left as in plain `specialize` (all arguments dynamic, no new procedures).
    With merge_asserts=True (§4 end), adjacent dynamic assertions in the
    residual bodies are combined. specialize()/specialize_with() are
    untouched by this function -- their behaviour is exactly the
    polyvariant=False, merge_asserts=False case."""
    global RULE3, RULE4, EXIT_SEED, POLY
    saved_rules = (RULE3, RULE4, EXIT_SEED)
    saved_poly = POLY
    RULE3, RULE4, EXIT_SEED = cut_paths, global_cut, exit_seed
    try:
        if polyvariant:
            by_name = {p.procname.name: p for p in procs}
            M = _modified_params(procs)
            USED = _used_params(procs, M)
            POLY = _PolyCtx(by_name, M, USED)
        else:
            POLY = None
        residual, S = specialize(proc, static_vals)
        residual_procs = POLY.finish() if POLY is not None else []
    finally:
        RULE3, RULE4, EXIT_SEED = saved_rules
        POLY = saved_poly
    if merge_asserts:
        residual = Proc(residual.procname, residual.params, combine_asserts(residual.body))
        residual_procs = [Proc(p.procname, p.params, combine_asserts(p.body)) for p in residual_procs]
    return residual, residual_procs, S


def _snapshot(S, st):
    """Hashable image of what drives specialisation: the static part of the store
    together with the speculative-decision counter of rule (iv).  Leaving the
    counter out makes the divergence test unsound in the presence of rule (iv):
    two iterations with the same static store may take different branches."""
    def h(v):
        return tuple(h(x) for x in v) if isinstance(v, list) else v
    return (CHOICE[0],) + tuple(sorted((k, h(st[k])) for k in S if k in st))

DUAL = set()   # variables treated as static for evaluation whose updates are also emitted (rule ii)

def _assigned(stmts, acc):
    """Variables that these statements can modify."""
    for x in stmts:
        if isinstance(x, AssignStmt): acc.add(x.lval.ident.name)
        elif isinstance(x, SwapStmt): acc.add(x.left.ident.name); acc.add(x.right.ident.name)
        elif isinstance(x, (CallStmt, UncallStmt)):
            for a in x.args:
                if isinstance(a, LvalExpr): acc.add(a.lval.ident.name)
        elif isinstance(x, (PushStmt, PopStmt)): acc.add(x.ident.name)
        elif isinstance(x, IterateStmt): acc.add(x.ident.name)
        for name in ("body", "if_part", "else_part", "do_part", "loop_part"):
            if hasattr(x, name): _assigned(getattr(x, name), acc)
    return acc

def _mentions(stmts, name):
    """Whether these statements read or write the variable `name`."""
    for x in stmts:
        for attr in ("expr", "entry_cond", "exit_cond", "start_expr", "step_expr", "end_expr"):
            e = getattr(x, attr, None)
            if e is not None and not isinstance(e, list) and name in vars_of(e): return True
        for attr in ("lval", "left", "right"):
            lv = getattr(x, attr, None)
            if lv is not None and getattr(lv, "ident", None) is not None and lv.ident.name == name: return True
        for attr in ("ident",):
            idt = getattr(x, attr, None)
            if idt is not None and getattr(idt, "name", None) == name: return True
        for a in getattr(x, "args", []) or []:
            if name in vars_of(a): return True
        for d in ("enter_decl", "exit_decl", "decl"):
            dd = getattr(x, d, None)
            if dd is not None:
                if dd.ident.name == name: return True
                if dd.init_expr is not None and name in vars_of(dd.init_expr): return True
        for nm in ("body", "if_part", "else_part", "do_part", "loop_part"):
            if hasattr(x, nm) and _mentions(getattr(x, nm), name): return True
    return False

def _reads(stmts, name):
    """Whether these statements *read* `name` (as opposed to only assigning it)."""
    for x in stmts:
        for attr in ("expr", "entry_cond", "exit_cond", "start_expr", "step_expr", "end_expr"):
            e = getattr(x, attr, None)
            if e is not None and not isinstance(e, list) and name in vars_of(e): return True
        for attr in ("lval", "left", "right"):
            lv = getattr(x, attr, None)
            if lv is not None and getattr(lv, "ident", None) is not None:
                if any(name in vars_of(i) for i in lv.indices): return True
        for a in getattr(x, "args", []) or []:
            if name in vars_of(a): return True
        for d in ("enter_decl", "exit_decl", "decl"):
            dd = getattr(x, d, None)
            if dd is not None and dd.init_expr is not None and name in vars_of(dd.init_expr): return True
        for nm in ("body", "if_part", "else_part", "do_part", "loop_part"):
            if hasattr(x, nm) and _reads(getattr(x, nm), name): return True
    return False

def _drop_updates(stmts, name):
    """Remove assignments to `name`.  Sound only where every such assignment sits
    at an unrolled (statically controlled) position, which `SeedEscaped`
    guarantees for a seeded variable."""
    out = []
    for x in stmts:
        if isinstance(x, AssignStmt) and not x.lval.selectors and x.lval.ident.name == name: continue
        if isinstance(x, SwapStmt) and name in (x.left.ident.name, x.right.ident.name): return None
        new = x
        for nm in ("body", "if_part", "else_part", "do_part", "loop_part"):
            if hasattr(x, nm):
                sub = _drop_updates(getattr(x, nm), name)
                if sub is None: return None
                new = replace(new, **{nm: sub})
        out.append(new)
    return out

def _residual_loops(stmts):
    """Number of `from` loops left in a residual."""
    n = 0
    for x in stmts:
        if isinstance(x, FromStmt): n += 1
        for name in ("body", "if_part", "else_part", "do_part", "loop_part"):
            if hasattr(x, name): n += _residual_loops(getattr(x, name))
    return n

def _has_unrollable_gap(stmts, S):
    """Some loop in these statements cannot be unrolled forwards."""
    for x in stmts:
        if isinstance(x, FromStmt) and not is_static_expr(x.exit_cond, S): return True
        for name in ("body", "if_part", "else_part", "do_part", "loop_part"):
            if hasattr(x, name) and _has_unrollable_gap(getattr(x, name), S): return True
    return False
