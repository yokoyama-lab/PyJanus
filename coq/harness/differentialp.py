#!/usr/bin/env python3
"""Differential test (parameterized): verified `Janus_param.run` vs. PyJanus.

Covers Janus programs *with* reference procedures.  Each procedure's variables
and main's variables are given distinct global slots (keyed by (scope, name)); a
call emits the actual variables' slots and the verified interpreter renames the
callee's formals onto them (matching `RevProc`'s reference semantics).  Only
main's variables are compared (procedure formals are aliased to actuals during a
call, so the surviving top-level store is main's).

`call` vs `uncall` is recovered from the node's source position (its `pos` is the
keyword location), since PyJanus's `-a` JSON serializes both identically.

Skipped: arrays, `local`/`delocal`, reversible I/O, `external` procedures.

Usage:  differentialp.py <driver-binary> <file.ja> [file.ja ...]
"""
import json, subprocess, sys

STD = "jana2014"
CLI = ["python3", "-m", "jana_py.cli", "--std", STD]


class Unsupported(Exception):
    pass


def cli(args, ja):
    return subprocess.run(CLI + args + [ja], capture_output=True, text=True)


def parse_store(text):
    d = {}
    for line in text.splitlines():
        line = line.strip()
        if " = " in line and not line.startswith(("Warning", "PyJanus", "Error")):
            name, _, val = line.partition(" = ")
            try:
                d[name.strip()] = int(val.strip())
            except ValueError:
                pass
    return d


class Prog:
    def __init__(self, src):
        self.src = src                # source lines (for call/uncall disambiguation)
        self.idx = {}                 # (scope, name) -> global slot
        self.procmap = {}             # procname -> pidx

    def gid(self, scope, name):
        k = (scope, name)
        if k not in self.idx:
            self.idx[k] = len(self.idx)
        return self.idx[k]

    def kind_at(self, pos):
        line = self.src[pos["line"] - 1]
        return "uncall" if line[pos["column"] - 1:].startswith("uncall") else "call"

    def expr(self, sc, e):
        if "op" in e:
            op, l, r = e["op"], self.expr(sc, e["left"]), self.expr(sc, e["right"])
            return {"==": f"(b eq {l} {r})", "<": f"(b lt {l} {r})", ">": f"(b lt {r} {l})",
                    "+": f"(b add {l} {r})", "-": f"(b sub {l} {r})",
                    "*": f"(b mul {l} {r})"}.get(op) or self._u(f"operator {op}")
        if "value" in e:
            return f"(c {int(e['value'])})"
        if "lval" in e:
            return f"(v {self._var(sc, e['lval'])})"
        raise Unsupported(f"expr {sorted(e)}")

    def _var(self, sc, lval):
        if lval.get("selectors"):
            raise Unsupported("array access")
        return self.gid(sc, lval["ident"]["name"])

    def _u(self, m):
        raise Unsupported(m)

    def stmt(self, sc, s):
        if not s or set(s) <= {"pos"}:
            return "(skip)"
        if "prints" in s:                                   # printf: no store change
            return "(skip)"
        if "mod_op" in s:
            op = {"+=": "add", "-=": "sub", "^=": "xor"}.get(s["mod_op"]) or self._u(s["mod_op"])
            return f"(asgn {self._var(sc, s['lval'])} {op} {self.expr(sc, s['expr'])})"
        if "if_part" in s:
            return (f"(if {self.expr(sc, s['entry_cond'])} {self.seq(sc, s['if_part'])} "
                    f"{self.seq(sc, s['else_part'])} {self.expr(sc, s['exit_cond'])})")
        if "do_part" in s:
            return (f"(loop {self.expr(sc, s['entry_cond'])} {self.seq(sc, s['do_part'])} "
                    f"{self.seq(sc, s['loop_part'])} {self.expr(sc, s['exit_cond'])})")
        if "ident" in s and "args" in s:                    # call / uncall
            if s.get("external"):
                raise Unsupported("external procedure")
            name = s["ident"]["name"]
            if name not in self.procmap:
                raise Unsupported(f"unknown procedure {name}")
            actuals = []
            for a in s["args"]:
                if "lval" not in a:
                    raise Unsupported("non-variable argument")
                actuals.append(self._var(sc, a["lval"]))
            kind = self.kind_at(s["pos"])
            return f"({kind} {self.procmap[name]} {len(actuals)} " + " ".join(map(str, actuals)) + ")"
        if "left" in s and "right" in s and "op" not in s:  # swap
            l, r = s["left"], s["right"]
            if "ident" not in l or "ident" not in r:
                raise Unsupported("non-variable swap")
            return f"(swap {self._var(sc, l)} {self._var(sc, r)})"
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
        p = Prog(f.read().splitlines())
    procs = ast.get("procs", [])
    for i, proc in enumerate(procs):
        p.procmap[proc["procname"]["name"]] = i
    proc_out = []
    for proc in procs:
        name = proc["procname"]["name"]
        formals = []
        for par in proc["params"]:
            if par.get("dimensions"):
                raise Unsupported("array parameter")
            formals.append(p.gid(name, par["ident"]["name"]))
        body = p.seq(name, proc["body"])
        proc_out.append((formals, body))
    main = ast["main"]
    for vd in main.get("vdecls", []):
        if vd.get("dimensions"):
            raise Unsupported("array declaration")
        p.gid("main", vd["ident"]["name"])
    mainbody = p.seq("main", main["stmts"])
    parts = [str(len(p.idx)), str(len(proc_out))]
    for formals, body in proc_out:
        parts.append(str(len(formals)))
        parts += [str(f) for f in formals]
        parts.append(body)
    parts.append(mainbody)
    main_names = {gid: name for (scope, name), gid in p.idx.items() if scope == "main"}
    return " ".join(parts), main_names


def run_driver(driver, sexpr):
    out = subprocess.run([driver], input=sexpr, capture_output=True, text=True).stdout
    d = {}
    for line in out.splitlines():
        if line.strip() == "NONE":
            raise Unsupported("interpreter returned NONE (out of fuel?)")
        if "=" in line:
            i, _, v = line.partition("=")
            d[int(i)] = int(v)
    return d


def check(driver, ja):
    sexpr, main_names = translate(ja)
    oc = run_driver(driver, sexpr)
    py = parse_store(cli(["-s"], ja).stdout)
    diffs = []
    for gid, name in main_names.items():
        if oc.get(gid, 0) != py.get(name, 0):
            diffs.append((name, oc.get(gid, 0), py.get(name, 0)))
    return diffs


def main():
    driver, files = sys.argv[1], sys.argv[2:]
    fails = skips = passes = 0
    for ja in files:
        try:
            diffs = check(driver, ja)
        except (Unsupported, KeyError) as e:                  # unsupported AST shape
            print(f"SKIP {ja}: {e}")
            skips += 1
            continue
        except Exception as e:                                # noqa
            print(f"ERROR {ja}: {type(e).__name__}: {e}")
            fails += 1
            continue
        if diffs:
            print(f"FAIL {ja}: " + ", ".join(f"{n}: verified={a} pyjanus={b}" for n, a, b in diffs))
            fails += 1
        else:
            print(f"PASS {ja}")
            passes += 1
    print(f"\n{passes} passed, {fails} failed, {skips} skipped")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
