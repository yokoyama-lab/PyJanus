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
from dataclasses import replace, dataclass
from .ast import *
from .invert import invert_stmts

POS = SourcePos("pe", 0, 0)
class PEError(Exception): pass
DUAL = set()

def T(v): return Boolean(True, POS)
def num(v): return Number(int(v), POS)

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
                out.append(replace(s, lval=fold_lval(s.lval, S, st), expr=fold(s.expr, S, st)))
        elif isinstance(s, SwapStmt):
            l, r = s.left.ident.name, s.right.ident.name
            if l in S and r in S and not dctx:
                a = evalx(LvalExpr(s.left, POS), st); b = evalx(LvalExpr(s.right, POS), st)
                assign(st, s.left, lambda _: b); assign(st, s.right, lambda _: a)
            else:
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
                while True:
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
                    out.append(AssertStmt(BinExpr(BinOpKind.EQ, num(st[v]), fold(s.exit_decl.init_expr, S, st), POS), POS))
                del st[v]
            else:
                ed = replace(s.enter_decl, init_expr=fold(s.enter_decl.init_expr, S, st) if s.enter_decl.init_expr is not None else None)
                xd = replace(s.exit_decl, init_expr=fold(s.exit_decl.init_expr, S, st) if s.exit_decl.init_expr is not None else None)
                body = exit_seeded(s, S, st, dctx, fuel) if EXIT_SEED else None
                if body is None: body = pe(s.body, S, st, dctx, fuel)
                out.append(LocalStmt(ed, body, xd, s.pos))
        elif isinstance(s, IterateStmt):
            v = s.ident.name
            bounds_static = all(is_static_expr(e, S) for e in (s.start_expr, s.step_expr, s.end_expr))
            if bounds_static and not dctx and v in S:
                a, d, b = evalx(s.start_expr, st), evalx(s.step_expr, st), evalx(s.end_expr, st)
                if d == 0: raise PEError("zero step")
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
    """`local v = <dyn> ; ...; from c1 do A loop B until c2 ; delocal v = <static e>`
    where the loop is the last statement of the local body and it is not unrollable
    forward: seed v := e at the exit, unroll the *inverse* loop from that seed
    (it is now static), and invert the unrolled code back.  Returns the new body
    or None when the pattern does not apply."""
    if dctx or not s.body or not isinstance(s.body[-1], FromStmt): return None
    loop = s.body[-1]; v = s.enter_decl.ident.name
    if s.exit_decl.init_expr is None or not is_static_expr(s.exit_decl.init_expr, S): return None
    if is_static_expr(loop.exit_cond, S): return None            # forward already unrolls it
    Sx = S | {v}
    if not is_static_expr(loop.entry_cond, Sx): return None      # inverse loop must be unrollable with v static
    stx = copy.deepcopy(st); seed = stx[v] = evalx(s.exit_decl.init_expr, st)
    inv_loop = invert_stmts([loop], global_mode=False)
    global DUAL
    saved = DUAL; DUAL = DUAL | {v}
    try:
        unrolled = pe(inv_loop, Sx, stx, False, [2000])   # own fuel: a bad seed must not kill the outer PE
    except PEError:
        return None
    finally:
        DUAL = saved
    entry_val = stx[v]                       # value of v at the entry of the original loop
    prefix = pe(s.body[:-1], S, st, dctx, fuel)
    lv = LvalExpr(Lval(Ident(v, POS), []), POS)
    return prefix + [AssertStmt(BinExpr(BinOpKind.EQ, lv, num(entry_val), POS), POS)] + invert_stmts(unrolled, global_mode=False)


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


def specialize_with(proc, static_vals, *, cut_paths=True, global_cut=True, exit_seed=True):
    """Convenience wrapper: set the rule flags for one call and restore them."""
    global RULE3, RULE4, EXIT_SEED
    saved = (RULE3, RULE4, EXIT_SEED)
    RULE3, RULE4, EXIT_SEED = cut_paths, global_cut, exit_seed
    try:
        return specialize(proc, static_vals)
    finally:
        RULE3, RULE4, EXIT_SEED = saved
