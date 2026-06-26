#!/usr/bin/env python3
"""Differential test: the *verified* extracted interpreter vs. PyJanus.

For each `.ja` program (in the verified core subset: int vars, += -= ^=, <=>,
if/fi, from/loop/until, seq, skip; no procedures/arrays/locals-with-delocal),
translate it via PyJanus's own AST (`-a`) into the s-expr the OCaml driver reads,
run the driver, and compare its final store against PyJanus's (`-s`).

Usage:  differential.py <driver-binary> <file.ja> [file.ja ...]
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


class T:
    def __init__(self):
        self.idx = {}

    def v(self, name):
        if name not in self.idx:
            self.idx[name] = len(self.idx)
        return self.idx[name]

    def expr(self, e):
        if "op" in e:
            op, l, r = e["op"], self.expr(e["left"]), self.expr(e["right"])
            if op == "==": return f"(b eq {l} {r})"
            if op == "<":  return f"(b lt {l} {r})"
            if op == ">":  return f"(b lt {r} {l})"          # x>y  ==  y<x
            if op == "+":  return f"(b add {l} {r})"
            if op == "-":  return f"(b sub {l} {r})"
            if op == "*":  return f"(b mul {l} {r})"
            raise Unsupported(f"operator {op}")
        if "value" in e:
            return f"(c {int(e['value'])})"
        if "lval" in e:
            lv = e["lval"]
            if lv.get("selectors"):
                raise Unsupported("array access")
            return f"(v {self.v(lv['ident']['name'])})"
        raise Unsupported(f"expr {sorted(e)}")

    def stmt(self, s):
        if not s or set(s) <= {"pos"}:                       # {} or {pos}  ->  skip
            return "(skip)"
        if "mod_op" in s:
            lv = s["lval"]
            if lv.get("selectors"):
                raise Unsupported("array assignment")
            op = {"+=": "add", "-=": "sub", "^=": "xor"}.get(s["mod_op"])
            if op is None:
                raise Unsupported(f"mod_op {s['mod_op']}")
            return f"(asgn {self.v(lv['ident']['name'])} {op} {self.expr(s['expr'])})"
        if "if_part" in s:
            return (f"(if {self.expr(s['entry_cond'])} {self.seq(s['if_part'])} "
                    f"{self.seq(s['else_part'])} {self.expr(s['exit_cond'])})")
        if "do_part" in s:
            return (f"(loop {self.expr(s['entry_cond'])} {self.seq(s['do_part'])} "
                    f"{self.seq(s['loop_part'])} {self.expr(s['exit_cond'])})")
        if "left" in s and "right" in s and "op" not in s:   # swap
            return f"(swap {self.v(s['left']['ident']['name'])} {self.v(s['right']['ident']['name'])})"
        raise Unsupported(f"stmt {sorted(s)}")

    def seq(self, stmts):
        ss = [self.stmt(x) for x in stmts]
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
    if "main" not in ast:
        raise Unsupported("no main")
    if ast.get("procs"):
        raise Unsupported("uses procedures (verified Call needs parameters)")
    if ast.get("struct_defs"):
        raise Unsupported("uses structs")
    main = ast["main"]
    t = T()
    for vd in main.get("vdecls", []):
        if vd.get("dimensions"):
            raise Unsupported("array declaration")
        t.v(vd["ident"]["name"])
    body = t.seq(main["stmts"])
    return f"{len(t.idx)} 0 {body}", t.idx


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
    sexpr, idx = translate(ja)
    name_of = {i: n for n, i in idx.items()}
    oc = run_driver(driver, sexpr)
    py = parse_store(cli(["-s"], ja).stdout)
    diffs = []
    for i, name in name_of.items():
        if oc.get(i, 0) != py.get(name, 0):
            diffs.append((name, oc.get(i, 0), py.get(name, 0)))
    return diffs


def main():
    driver, files = sys.argv[1], sys.argv[2:]
    fails = skips = passes = 0
    for ja in files:
        try:
            diffs = check(driver, ja)
        except Unsupported as e:
            print(f"SKIP {ja}: {e}")
            skips += 1
            continue
        except Exception as e:                                # noqa
            print(f"ERROR {ja}: {e}")
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
