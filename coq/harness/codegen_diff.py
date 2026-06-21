#!/usr/bin/env python3
"""Differential test of PyJanus's two back-ends: interpreter (-s) vs C++ codegen.

For each .ja program we run the interpreter to get the final store, generate C++,
inject prints of main's scalars and array cells, compile at -O0 (so uninitialized
reads show), run, and compare.  Reports WRONG (runs but disagrees) / CFAIL
(compile error) / CGERR (codegen raised) / SKIP / PASS.
"""
from __future__ import annotations

import copy
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py.parser_jana2014 import parse_program
from jana_py.validate import validate_program
from jana_py.runtime import Runtime
from jana_py.c_codegen import format_program


def interp(program):
    rt = Runtime(program)
    rt.run()
    return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


def check(ja: str):
    src = Path(ja).read_text()
    program = parse_program(ja, src)
    validate_program(program)
    try:
        store = interp(program)
    except Exception as e:                       # interpreter rejects/raises
        return ("SKIP", f"interp: {type(e).__name__}")

    scal = [vd.ident.name for vd in program.main.vdecls if not vd.dimensions]
    arrs = {vd.ident.name: [int(d.value) for d in vd.dimensions]
            for vd in program.main.vdecls if vd.dimensions}
    # only 1-D arrays are straightforward to print
    arrs1 = {n: d[0] for n, d in arrs.items() if len(d) == 1}
    if any(len(d) != 1 for d in arrs.values()):
        return ("SKIP", "multi-dim array (cannot flatten print)")

    try:
        cpp = format_program(None, program)
    except Exception as e:
        return ("CGERR", f"{type(e).__name__}: {e}")

    # Lead with a newline: a `show(...)` left over in the program may print
    # without a trailing newline, which would merge with the first marker line.
    prints = 'std::cout << "\\n";'
    prints += "".join(f'std::cout << "@{n}=" << {n} << "\\n";' for n in scal)
    prints += "".join(f'std::cout << "@{n}[{i}]=" << {n}[{i}] << "\\n";'
                      for n, d in arrs1.items() for i in range(d))
    cpp2 = cpp.replace("return 1;", prints + "return 0;")
    if "return 1;" not in cpp:
        return ("SKIP", "no main return marker")

    comp = subprocess.run(["g++", "-std=c++17", "-O0", "-x", "c++", "-", "-o", "/tmp/_cgd"],
                          input=cpp2, capture_output=True, text=True)
    if comp.returncode != 0:
        return ("CFAIL", comp.stderr.strip().splitlines()[-1] if comp.stderr else "compile error")
    run = subprocess.run(["/tmp/_cgd"], capture_output=True, text=True, timeout=10)
    got = {}
    for line in run.stdout.splitlines():
        if line.startswith("@") and "=" in line:
            k, v = line[1:].split("=", 1)
            got[k] = int(v)

    diffs = []
    for n in scal:
        if got.get(n) != int(store.get(n, 0)):
            diffs.append(f"{n}: cpp={got.get(n)} interp={store.get(n,0)}")
    for n, d in arrs1.items():
        cells = store.get(n, [])
        for i in range(d):
            ev = int(cells[i]) if i < len(cells) else 0
            if got.get(f"{n}[{i}]") != ev:
                diffs.append(f"{n}[{i}]: cpp={got.get(f'{n}[{i}]')} interp={ev}")
    if diffs:
        return ("WRONG", "; ".join(diffs[:4]))
    return ("PASS", "")


def main():
    tally = {}
    for ja in sys.argv[1:]:
        try:
            tag, msg = check(ja)
        except Exception as e:                   # noqa
            tag, msg = "ERROR", f"{type(e).__name__}: {e}"
        tally[tag] = tally.get(tag, 0) + 1
        if tag != "PASS":
            print(f"{tag:6} {Path(ja).name}: {msg}")
        else:
            print(f"{tag:6} {Path(ja).name}")
    print("\n" + ", ".join(f"{k}={v}" for k, v in sorted(tally.items())))


if __name__ == "__main__":
    main()
