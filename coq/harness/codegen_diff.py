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
from jana_py.errors import JanaError
from jana_py.runtime import Runtime
from jana_py import c_codegen
from jana_py.c_codegen import format_program


def interp(program):
    rt = Runtime(program)
    rt.run()
    return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


class _Ragged(Exception):
    """A declaration whose leaf cells cannot be enumerated statically."""


def _dims_of(decl):
    out = []
    for d in (decl.dimensions or []):
        if d is None or not hasattr(d, "value"):
            raise _Ragged("array with a non-constant dimension")
        out.append(int(d.value))
    return out


def _leaves(vdecls, sdefs, esc):
    """Enumerate every scalar cell of main's store.

    Returns (label, C++ expression, accessor path).  The C++ side goes through
    `esc`, the code generator's identifier escaper, so a variable or field whose
    Janus name is a C++ keyword is still addressable; the path walks the
    interpreter's value under the *Janus* names (list index for `[i]`, dict key
    for `.f`).  Covers scalars, arrays of any rank, structs, arrays of structs
    and struct array fields -- the comparison is not limited to 1-D int arrays."""
    out = []

    def cells(cpre, path, typ, dims):
        idxs = [[]]
        for n in dims:
            idxs = [t + [k] for t in idxs for k in range(n)]
        for t in idxs:
            sub = "".join(f"[{k}]" for k in t)
            c = cpre + sub
            # The interpreter stores a multi-dimensional array as one flat
            # row-major list, so a whole index group is a single step.
            flat = 0
            for k, n in zip(t, dims):
                flat = flat * n + k
            q = path + ([flat] if dims else [])
            if typ.kind == "struct":
                fields = sdefs.get(typ.name)
                if fields is None:
                    raise _Ragged(f"unknown struct type {typ.name}")
                for f in fields:
                    cells(f"{c}.{esc(f.ident.name)}", q + [f.ident.name], f.typ, _dims_of(f))
            else:
                out.append((c, c, q))

    for vd in vdecls:
        if vd.typ.kind == "stack":
            continue
        cells(esc(vd.ident.name), [vd.ident.name], vd.typ, _dims_of(vd))
    return out


def _dig(value, path):
    """Read the interpreter's store along a leaf path; missing cells read 0."""
    cur = value
    for step in path:
        if isinstance(step, int):
            if not isinstance(cur, list) or step >= len(cur):
                return 0
            cur = cur[step]
        else:
            if not isinstance(cur, dict) or step not in cur:
                return 0
            cur = cur[step]
    return 0 if cur is None else cur


def check(ja: str):
    src = Path(ja).read_text()
    program = parse_program(ja, src)
    try:
        validate_program(program)
    except JanaError as e:
        # The program is not valid Janus, so there is nothing to say about the
        # back-end.  Report it under its own tag: letting it escape as a bare
        # exception made `main()` print ERROR, which reads like a harness crash.
        return ("INVALID", str(e).splitlines()[1].strip() if "\n" in str(e) else str(e))
    try:
        store = interp(program)
    except Exception as e:                       # interpreter rejects/raises
        return ("SKIP", f"interp: {type(e).__name__}")

    stacks = [vd.ident.name for vd in program.main.vdecls if vd.typ.kind == "stack"]
    sdefs = {sd.ident.name: sd.fields for sd in program.struct_defs}

    try:
        cpp = format_program(None, program)          # also fixes the escaper's map
    except Exception as e:
        return ("CGERR", f"{type(e).__name__}: {e}")
    try:
        leaves = _leaves(program.main.vdecls, sdefs, c_codegen._esc)
    except _Ragged as e:
        return ("SKIP", str(e))

    # Lead with a newline: a `show(...)` left over in the program may print
    # without a trailing newline, which would merge with the first marker line.
    prints = 'std::cout << "\\n";'
    prints += "".join(f'std::cout << "@{lab}=" << {cexpr} << "\\n";'
                      for lab, cexpr, _ in leaves)
    prints += "".join(f'std::cout << "@@{n}=";for(auto _v:{n})std::cout<<_v<<",";std::cout<<"\\n";'
                      for n in stacks)
    cpp2 = cpp.replace("return 1;", prints + "return 0;")
    if "return 1;" not in cpp:
        return ("SKIP", "no main return marker")

    comp = subprocess.run(["g++", "-std=c++17", "-O0", "-x", "c++", "-", "-o", "/tmp/_cgd"],
                          input=cpp2, capture_output=True, text=True)
    if comp.returncode != 0:
        return ("CFAIL", comp.stderr.strip().splitlines()[-1] if comp.stderr else "compile error")
    run = subprocess.run(["/tmp/_cgd"], capture_output=True, text=True, timeout=10)
    got = {}
    got_stacks = {}
    for line in run.stdout.splitlines():
        if line.startswith("@@"):                 # a stack dump: @@name=v0,v1,...
            k, v = line[2:].split("=", 1)
            got_stacks[k] = [int(x) for x in v.split(",") if x.strip()]
        elif line.startswith("@") and "=" in line:
            k, v = line[1:].split("=", 1)
            got[k] = int(v)

    diffs = []
    for lab, _, path in leaves:
        ev = int(_dig(store, path))
        if got.get(lab) != ev:
            diffs.append(f"{lab}: cpp={got.get(lab)} interp={ev}")
    for n in stacks:
        # the C++ vector is bottom..top (push_back); the interpreter lists top..bottom.
        cpp_stack = list(reversed(got_stacks.get(n, [])))
        if cpp_stack != list(store.get(n, [])):
            diffs.append(f"{n}: cpp={cpp_stack} interp={store.get(n, [])}")
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
