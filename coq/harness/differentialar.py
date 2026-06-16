#!/usr/bin/env python3
"""Differential test (arrays): verified `Janus_arr.run` vs. PyJanus.

Extends the parameterized harness with arrays: array reads `A[e]`, array-cell
assignments `A[e] op= ...`, and array parameters.  Scalars and arrays share the
verified store's location space (`LS x` vs. `LA a i`), so one global-slot map
serves both.  The driver is given a *report list* (built from PyJanus's `-s`
output: main's scalars and every declared array cell) and prints those
locations; we compare positionally.

Skipped: multi-dim arrays, array-element swap, `local`/`delocal`, `for`, stacks,
`/`, `>=`/`<=`, and programs PyJanus rejects at run time (e.g. out-of-bounds).

Usage:  differentialar.py <driver-binary> <file.ja> [file.ja ...]
"""
import ast, itertools, json, re, subprocess, sys

STD = "jana2014"
CLI = ["python3", "-m", "jana_py.cli", "--std", STD]


class Unsupported(Exception):
    pass


def cli(args, ja):
    return subprocess.run(CLI + args + [ja], capture_output=True, text=True)


ARR_RE = re.compile(r"^(\w+)(?:\[\d+\])+\s*=\s*(\{.*\})\s*$")     # possibly nested
STK_RE = re.compile(r"^(\w+)\s*=\s*<(.*)\]\s*$")                  # stack: <top, …, bottom]
SCA_RE = re.compile(r"^(\w+)\s*=\s*(-?\d+)\s*$")


def parse_store(res):
    if res.returncode != 0:
        raise Unsupported("pyjanus runtime error")
    scal, arr, stk = {}, {}, {}
    for line in res.stdout.splitlines():
        line = line.strip()
        m = ARR_RE.match(line)
        if m:
            arr[m.group(1)] = ast.literal_eval(m.group(2).replace("{", "[").replace("}", "]"))
            continue
        m = STK_RE.match(line)
        if m:
            stk[m.group(1)] = [int(x) for x in m.group(2).split(",") if x.strip()]
            continue
        m = SCA_RE.match(line)
        if m and not line.startswith(("Warning", "PyJanus")):
            scal[m.group(1)] = int(m.group(2))
    return scal, arr, stk


def _any(o, pred):
    if pred(o):
        return True
    if isinstance(o, dict):
        return any(_any(v, pred) for v in o.values())
    if isinstance(o, list):
        return any(_any(x, pred) for x in o)
    return False


def recursive_with_locals(proc):
    # flat-gid model has no call stack for locals: a self-recursive procedure
    # that declares locals would reuse the same slots across frames.
    name = proc["procname"]["name"]
    body = proc["body"]
    calls_self = _any(body, lambda o: isinstance(o, dict)
                      and o.get("ident", {}).get("name") == name and "args" in o)
    has_local = _any(body, lambda o: isinstance(o, dict) and "enter_decl" in o)
    return calls_self and has_local


def nested_get(v, combo):                                        # v[i0][i1]…, 0 if absent
    for i in combo:
        if not isinstance(v, list) or i >= len(v):
            return 0
        v = v[i]
    return v if isinstance(v, int) else 0


class T:
    def __init__(self, src):
        self.src = src
        self.idx = {}
        self.procmap = {}
        self.tmpn = 0
        self.stacks = set()                                  # (scope, name) that are stacks

    def stack_ids(self, sc, name):                           # a stack = array + top counter
        self.stacks.add((sc, name))
        return self.gid(sc, name + "#arr"), self.gid(sc, name + "#top")

    def is_stack(self, sc, name):
        return (sc, name) in self.stacks

    def kw_at(self, pos, *kws):
        line = self.src[pos["line"] - 1][pos["column"] - 1:]
        return next((k for k in kws if line.startswith(k)), kws[-1])

    def fresh(self, sc):                                     # fresh caller-side temp slot
        self.tmpn += 1
        return self.gid(sc, f"__t{self.tmpn}")

    def gid(self, sc, name):
        k = (sc, name)
        if k not in self.idx:
            self.idx[k] = len(self.idx)
        return self.idx[k]

    def kind_at(self, pos):
        return "uncall" if self.src[pos["line"] - 1][pos["column"] - 1:].startswith("uncall") else "call"

    def _reads(self, e, name):                               # does expr read scalar `name`?
        if isinstance(e, dict):
            lv = e.get("lval")
            if lv and lv.get("ident", {}).get("name") == name and not lv.get("selectors"):
                return True
            return any(self._reads(v, name) for v in e.values())
        if isinstance(e, list):
            return any(self._reads(x, name) for x in e)
        return False

    def expr(self, sc, e):
        if "op" in e and "expr" in e:                        # unary: !e (logical not)
            if e["op"] != "!":
                raise Unsupported(f"unary {e['op']}")
            return f"(b eq {self.expr(sc, e['expr'])} (c 0))"
        if "op" in e:
            op, l, r = e["op"], self.expr(sc, e["left"]), self.expr(sc, e["right"])
            # arithmetic
            r2 = {"+": f"(b add {l} {r})", "-": f"(b sub {l} {r})", "*": f"(b mul {l} {r})",
                  "/": f"(b div {l} {r})", "%": f"(b mod {l} {r})"}.get(op)
            if r2:
                return r2
            # comparisons / logicals appear only in conditions: encode by truthiness
            r2 = {
                "==": f"(b eq {l} {r})", "<": f"(b lt {l} {r})", ">": f"(b lt {r} {l})",
                ">=": f"(b sub (c 1) (b lt {l} {r}))",      # not (a < b)
                "<=": f"(b sub (c 1) (b lt {r} {l}))",      # not (b < a)
                "!=": f"(b sub (c 1) (b eq {l} {r}))",      # not (a == b)
                "&&": f"(b mul {l} {r})",                   # nonzero iff both nonzero
                "||": f"(b add (b mul {l} {l}) (b mul {r} {r}))",  # nonzero iff either nonzero
            }.get(op)
            if r2 is None:
                raise Unsupported(f"operator {op}")
            return r2
        if "value" in e:
            return f"(c {int(e['value'])})"
        if "lval" in e:
            return self.read(sc, e["lval"])
        if "ident" in e:                                     # bare ident in a value context
            nm = e["ident"]["name"]
            if self.is_stack(sc, nm):                         # stack truthiness/size = its depth
                return f"(v {self.stack_ids(sc, nm)[1]})"
            raise Unsupported("size() / array length")
        raise Unsupported(f"expr {sorted(e)}")

    # Multi-dimensional indices are folded to one via an injective Cantor
    # pairing (translator-only; the verified store stays 1-D).  Exact, since
    # (i+j)(i+j+1) is even.
    def cantor_expr(self, idxs):
        acc = idxs[0]
        for j in idxs[1:]:
            sm = f"(b add {acc} {j})"
            acc = f"(b add (b div (b mul {sm} (b add {sm} (c 1))) (c 2)) {j})"
        return acc

    @staticmethod
    def cantor_val(idxs):
        acc = idxs[0]
        for j in idxs[1:]:
            sm = acc + j
            acc = sm * (sm + 1) // 2 + j
        return acc

    def _index(self, sc, sel):
        return self.cantor_expr([self.expr(sc, s["expr"]) for s in sel])

    def read(self, sc, lv):
        sel = lv.get("selectors", [])
        g = self.gid(sc, lv["ident"]["name"])
        return f"(v {g})" if not sel else f"(ar {g} {self._index(sc, sel)})"

    def target(self, sc, lv):
        sel = lv.get("selectors", [])
        g = self.gid(sc, lv["ident"]["name"])
        return f"(ls {g})" if not sel else f"(la {g} {self._index(sc, sel)})"

    def stmt(self, sc, s):
        if not s or set(s) <= {"pos"}:
            return "(skip)"
        if "prints" in s:
            return "(skip)"
        if "mod_op" in s:
            op = {"+=": "add", "-=": "sub", "^=": "xor"}.get(s["mod_op"])
            if op is None:
                raise Unsupported(s["mod_op"])
            return f"(asgn {self.target(sc, s['lval'])} {op} {self.expr(sc, s['expr'])})"
        if "if_part" in s:
            return (f"(if {self.expr(sc, s['entry_cond'])} {self.seq(sc, s['if_part'])} "
                    f"{self.seq(sc, s['else_part'])} {self.expr(sc, s['exit_cond'])})")
        if "do_part" in s:
            return (f"(loop {self.expr(sc, s['entry_cond'])} {self.seq(sc, s['do_part'])} "
                    f"{self.seq(sc, s['loop_part'])} {self.expr(sc, s['exit_cond'])})")
        if "enter_decl" in s:                                # local … / delocal …
            ed, xd = s["enter_decl"], s["exit_decl"]
            if ed["typ"]["kind"] == "stack":                 # local stack ss = nil  (track its counter)
                _, top = self.stack_ids(sc, ed["ident"]["name"])
                return f"(seq (enter {top} (c 0)) (seq {self.seq(sc, s['body'])} (exit {top} (c 0))))"
            if ed.get("dimensions") or xd.get("dimensions"):
                raise Unsupported("local array")
            xname = ed["ident"]["name"]
            # dead-cell Exit needs the exit expr independent of x (known final value);
            # `delocal x = x`-style self-references need a whole-block argument.
            if self._reads(ed["init_expr"], xname) or self._reads(xd["init_expr"], xname):
                raise Unsupported("self-referential local/delocal")
            x = self.gid(sc, ed["ident"]["name"])
            e0 = self.expr(sc, ed["init_expr"])
            e1 = self.expr(sc, xd["init_expr"])
            return f"(seq (enter {x} {e0}) (seq {self.seq(sc, s['body'])} (exit {x} {e1})))"
        if "start_expr" in s and "step_expr" in s:          # iterate int i = start to end [step]
            i = self.gid(sc, s["ident"]["name"])
            start = self.expr(sc, s["start_expr"])
            step = self.expr(sc, s["step_expr"])
            end = self.expr(sc, s["end_expr"])
            stop = end if s.get("exclusive") else f"(b add {end} {step})"
            body = self.seq(sc, s["body"])
            istart = f"(b eq (v {i}) {start})"
            istop = f"(b eq (v {i}) {stop})"
            incr = f"(asgn (ls {i}) add {step})"
            return (f"(seq (enter {i} {start}) "
                    f"(seq (loop {istart} (skip) (seq {body} {incr}) {istop}) "
                    f"(exit {i} {stop})))")
        if "ident" in s and "args" in s:
            if s.get("external"):
                raise Unsupported("external procedure")
            name = s["ident"]["name"]
            if name not in self.procmap:
                raise Unsupported(f"unknown procedure {name}")
            # Argument passing, all reduced to scalar reference + existing constructs:
            #   bare l-value x        -> reference (its slot)
            #   array element A[i]    -> A[i] <=> t; f(...,t); A[i] <=> t   (swap into temp)
            #   constant/expression e -> local t=e; f(...,t); delocal t=e   (value argument)
            actuals, swaps, valwraps = [], [], []
            for a in s["args"]:
                if "lval" in a:
                    lv = a["lval"]
                    if lv.get("selectors"):                  # array cell by reference
                        t = self.fresh(sc)
                        swaps.append((self.target(sc, lv), t))
                        actuals.append(t)
                    elif self.is_stack(sc, lv["ident"]["name"]):   # stack = (array, top) by reference
                        actuals.extend(self.stack_ids(sc, lv["ident"]["name"]))
                    else:
                        actuals.append(self.gid(sc, lv["ident"]["name"]))
                else:                                        # value argument
                    t = self.fresh(sc)
                    actuals.append(t)
                    valwraps.append((t, self.expr(sc, a)))
            call = (f"({self.kind_at(s['pos'])} {self.procmap[name]} {len(actuals)} "
                    + " ".join(map(str, actuals)) + ")")
            for t, e in reversed(valwraps):
                call = f"(seq (enter {t} {e}) (seq {call} (exit {t} {e})))"
            for cell, t in reversed(swaps):
                call = f"(seq (swap {cell} (ls {t})) (seq {call} (swap {cell} (ls {t}))))"
            return call
        if "left" in s and "right" in s and "op" not in s:   # swap (scalar or array cell)
            return f"(swap {self.target(sc, s['left'])} {self.target(sc, s['right'])})"
        if "ident" in s and "expr" in s and "args" not in s and "mod_op" not in s:   # push/pop(x, s)
            arr, top = self.stack_ids(sc, s["ident"]["name"])
            xt = self.target(sc, s["expr"]["lval"])
            swap = f"(swap (la {arr} (v {top})) {xt})"
            inc = f"(asgn (ls {top}) add (c 1))"
            dec = f"(asgn (ls {top}) sub (c 1))"
            if self.kw_at(s["pos"], "pop", "push") == "pop":
                return f"(seq {dec} {swap})"
            return f"(seq {swap} {inc})"
        raise Unsupported(f"stmt {sorted(s)}")

    def seq(self, sc, stmts):
        ss = [self.stmt(sc, x) for x in stmts]
        if not ss:
            return "(skip)"
        acc = ss[-1]
        for x in reversed(ss[:-1]):
            acc = f"(seq {x} {acc})"
        return acc


def translate(ja):
    r = cli(["-a"], ja)
    if r.returncode != 0:
        raise Unsupported("parse failed")
    ast = json.loads(r.stdout)
    if ast.get("struct_defs"):
        raise Unsupported("uses structs")
    if "main" not in ast:
        raise Unsupported("no main")
    with open(ja) as f:
        p = T(f.read().splitlines())
    procs = ast.get("procs", [])
    for i, proc in enumerate(procs):
        p.procmap[proc["procname"]["name"]] = i
    proc_out = []
    for proc in procs:
        if recursive_with_locals(proc):
            raise Unsupported("self-recursion with local variables (no frame stack)")
        name = proc["procname"]["name"]
        formals = []
        for par in proc["params"]:                           # a stack param = (array, top)
            if par["typ"]["kind"] == "stack":
                formals.extend(p.stack_ids(name, par["ident"]["name"]))
            else:
                formals.append(p.gid(name, par["ident"]["name"]))
        body = p.seq(name, proc["body"])
        proc_out.append((formals, body))
    main = ast["main"]
    scalars, arrays, stks, inits = [], [], [], []

    def emit_init(g, item, prefix):                          # nested initializer -> asgn stmts
        if isinstance(item, dict) and "items" in item:
            for k, sub in enumerate(item["items"]):
                emit_init(g, sub, prefix + [k])
        else:
            flat = T.cantor_val(prefix)
            inits.append(f"(asgn (la {g} (c {flat})) add {p.expr('main', item)})")

    for vd in main.get("vdecls", []):
        nm = vd["ident"]["name"]
        if vd["typ"]["kind"] == "stack":                     # stack: array + top counter
            arr, top = p.stack_ids("main", nm)
            stks.append((nm, arr, top))
            ie = vd.get("init_expr")
            if ie is not None and "items" in ie:             # stack literal {bottom, …, top}
                for k, item in enumerate(ie["items"]):
                    inits.append(f"(asgn (la {arr} (c {k})) add {p.expr('main', item)})")
                inits.append(f"(asgn (ls {top}) add (c {len(ie['items'])}))")
            continue
        g = p.gid("main", nm)
        dims = vd.get("dimensions", [])
        ie = vd.get("init_expr")
        if dims:
            arrays.append((nm, g, [int(d["value"]) for d in dims]))
            if ie is not None:                               # int A[..] = {..} (possibly nested)
                if "items" not in ie:
                    raise Unsupported("array initializer form")
                emit_init(g, ie, [])
        else:
            scalars.append((nm, g))
            if ie is not None:                               # int x = e
                inits.append(f"(asgn (ls {g}) add {p.expr('main', ie)})")
    mainbody = p.seq("main", main["stmts"])
    for s0 in reversed(inits):                               # run initializers first
        mainbody = f"(seq {s0} {mainbody})"
    parts = [str(len(p.idx)), str(len(proc_out))]
    for formals, body in proc_out:
        parts.append(str(len(formals)))
        parts += [str(f) for f in formals]
        parts.append(body)
    parts.append(mainbody)
    return " ".join(parts), scalars, arrays, stks


def check(driver, ja):
    sexpr, scalars, arrays, stks = translate(ja)
    py_s, py_a, py_stk = parse_store(cli(["-s"], ja))
    reports, expected, labels = [], [], []
    for name, g in scalars:
        reports.append(f"(rs {g})"); expected.append(py_s.get(name, 0)); labels.append(name)
    for name, g, dims in arrays:
        nested = py_a.get(name)
        for combo in itertools.product(*[range(d) for d in dims]):
            reports.append(f"(ra {g} {T.cantor_val(list(combo))})")
            expected.append(nested_get(nested, combo))
            labels.append(f"{name}{list(combo)}")
    KMAX, stack_q = 64, []                                    # query top + cells, reconstruct
    for name, arr, top in stks:
        tp = len(reports); reports.append(f"(rs {top})")
        cs = len(reports)
        reports += [f"(ra {arr} {i})" for i in range(KMAX)]
        stack_q.append((name, tp, cs))
    full = sexpr + " " + str(len(reports)) + " " + " ".join(reports)
    out = subprocess.run([driver], input=full, capture_output=True, text=True).stdout
    if out.strip() == "NONE":
        raise Unsupported("interpreter returned NONE (out of fuel?)")
    got = [int(x) for x in out.split()]
    diffs = []
    for i, (lab, e) in enumerate(zip(labels, expected)):
        if got[i] != e:
            diffs.append((lab, got[i], e))
    for name, tp, cs in stack_q:
        my = [got[cs + k] for k in range(got[tp])][::-1]     # top first
        if my != py_stk.get(name, []):
            diffs.append((name, my, py_stk.get(name, [])))
    return diffs


def main():
    driver, files = sys.argv[1], sys.argv[2:]
    fails = skips = passes = 0
    for ja in files:
        try:
            diffs = check(driver, ja)
        except (Unsupported, KeyError) as e:
            print(f"SKIP {ja}: {e}"); skips += 1; continue
        except Exception as e:                                # noqa
            print(f"ERROR {ja}: {type(e).__name__}: {e}"); fails += 1; continue
        if diffs:
            print(f"FAIL {ja}: " + ", ".join(f"{n}: verified={a} pyjanus={b}" for n, a, b in diffs))
            fails += 1
        else:
            print(f"PASS {ja}"); passes += 1
    print(f"\n{passes} passed, {fails} failed, {skips} skipped")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
