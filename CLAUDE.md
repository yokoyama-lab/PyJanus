# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

PyJanus is a dependency-free (Python 3.10+) interpreter for **Janus**, the
reversible programming language. Beyond running programs forwards and backwards,
it provides a debugger, a C++ code generator, an inverse interpreter, and a set
of reversible-computing research tools (Bennett embedding, circuit synthesis,
equivalence checking, pebble-game space profiling).

## Commands

```bash
# Run a program (default standard: janus2026)
python3 -m jana_py.cli --std jana2014 tests/jana2014/fixtures/examples/fib.ja
python3 -m jana_py.cli --std janus1982 prog.ja   # select language dialect

# Common modes (all via the single CLI entry point)
python3 -m jana_py.cli -i prog.ja        # invert: print inverted source
python3 -m jana_py.cli -a prog.ja        # print AST as JSON
python3 -m jana_py.cli -c prog.ja        # emit C++ code
python3 -m jana_py.cli -d prog.ja        # step-debugger output
python3 -m jana_py.cli --circuit prog.ja --profile prog.ja
python3 -m jana_py.cli --inverse '{"x": 10}' prog.ja   # final store -> initial store
python3 -m jana_py.cli -I mylib prog.ja   # add an #include search dir (repeatable)

# Tests (unittest-based, but run under pytest; organized per dialect under tests/<std>/)
python3 -m pytest tests/ -q
python3 -m pytest tests/jana2014/test_reversibility.py -q          # single file
python3 -m pytest tests/jana2014/test_reversibility.py::ReversibilityTests::test_swap   # single test
python3 tests/jana2014/test_reversibility.py                # unittest-style files also run directly
```

### Standard library

A bundled, all-reversible standard library lives in `jana_py/lib/std/` (it ships
with the package). `#include "std/array.ja"` resolves through the preprocessor's
search path — relative to the including file first, then any `-I DIR`, then the
**dialect-specific** stdlib (`jana_py/lib/<std>/`, e.g. `lib/jana2014/`), then the
canonical janus2026 stdlib (`jana_py/lib/std`). `preprocess.STDLIB_DIR` points at
`jana_py/lib`; the dialect is threaded via `preprocess_text(..., std=args.std)`.
Modules:

| module           | procedures |
|------------------|------------|
| `std/array.ja`   | reverse, rotate_left, xor_into, add_into, cswap |
| `std/bits.ja`    | flip_bit, swap_bits, bit_reverse, rotate_bits_left |
| `std/math.ja`    | mul_acc, divmod, gcd (reversible Euclid w/ quotient stack) |
| `std/stack.ja`   | copy_top, move_all |
| `std/reduce.ja`  | sum_into, dot_into, count_into (clean accumulators); min_into, max_into (need history) |
| `std/sort.ja`    | sort (reversible bubble sort recording swap decisions in flags[]) |

Every library procedure must be reversible (`uncall` undoes `call` exactly) and
have a forward-AND-backward test (`tests/janus2026/test_stdlib_*.py`). Two
recurring reversibility patterns the library encodes: (1) **ancilla flags** — a
value-only comparator (`cswap`/`sort` with `fi (x < y)`) breaks its reversibility
assertion on an already-ordered pair, so it records the swap decision in an extra
flag bit instead; (2) **history** — operations that discard information (`gcd`,
`sort`, `min_into`/`max_into`) are made reversible by keeping just enough history
(a quotient stack, a flag array, a stack of deltas) for `uncall` to replay them
backwards. Clean accumulators (`sum_into` etc.) need neither: they preserve their
input, so `uncall` simply subtracts.

The library is authored **once** in janus2026; copies for other dialects are
*generated* by re-emitting the parsed AST with that dialect's formatter
(`jana_py/_gen_stdlib.py` → `jana_py/lib/jana2014/std/*.ja`). Edit only the
janus2026 source, then run `python -m jana_py._gen_stdlib`;
`tests/janus2026/test_stdlib_dialects.py` asserts the copies are current AND that
each computes the same store as the janus2026 original — it is the correctness
check for the AST→dialect-source formatters.

There is no lint step; the package is pure Python (`pyproject.toml` defines
the `pyjanus` console script → `jana_py.cli:main`). CI
(`.github/workflows/test.yml`) runs the pytest suite on every push/PR
against Python 3.10/3.12/3.14 — install locally with `pip install -e ".[dev]"`.

## Architecture

The interpreter is a linear pipeline, all wired together in `jana_py/cli.py:main`:

```
source text
  → preprocess.preprocess_text   (#define/#include/#ifdef; tracks line_origins for error maps)
  → parser_<dialect>.parse_program  (dialect chosen by --std; all emit the SAME ast.py types)
  → validate.validate_program    (static checks: unique bindings, struct defs, main proc, ...)
  → consumer:
      runtime.Runtime.run        (forward/backward execution + debugger)
      invert.invert_program      (AST→AST: swap call/uncall, reverse statement order)
      format.formatter_for_std   (AST→Janus source; CFormatter = C-style, with
                                  ProcedureFormatter / Janus1982Formatter
                                  subclasses overriding dialect-specific syntax)
      c_codegen.format_program   (AST→C++)
      circuit / pebble / inverse / bennett / equiv  (research tools)
```

**Key design point — multiple dialect parsers, one shared AST.** The original
`parser.py` was split into per-standard modules, all exposing the same
`parse_program(filename, text, line_origins)` signature and producing the same
`jana_py/ast.py` node types. The dialect is selected by `--std`:

| `--std` value   | parser module               |
|-----------------|-----------------------------|
| `janus2026`     | `parser_janus2026.py` (default, C-style) |
| `jana2014`      | `parser_jana2014.py`        |
| `jana2014basic` | `parser_jana2014basic.py` (subclasses the jana2014 parser; 1982-flavored hybrid grammar) |
| `jana2014_in_out` | `parser_jana2014_in_out.py` (subclasses the jana2014 parser; adds reversible `read`/`write` I/O) |
| `janus1982`     | `parser_janus1982.py` (strict original) |
| `janus1982ext`  | `parser_janus1982ext.py` (re-exports `parser_jana2014basic`) |

Because every consumer (runtime, invert, format, codegen, all analysis tools)
operates on the shared AST, **changes to `ast.py` ripple across all of them** —
when adding or changing a node type, update the parser(s), the runtime, `format.py`,
`c_codegen.py`, and `invert.py` together. `invert.py` is the conceptual heart of
reversibility: each statement type must define its own inverse.

**`runtime.py` is large (~2500 lines)** and central. `Runtime` holds the store of
`Cell`s; lvalue aliasing/indexing is handled through proxy cells (`CellProxy`,
`StructFieldProxy`, `ArraySliceProxy`, `ConstantParamProxy`). It also implements
modular arithmetic (`-m` bits / `-p` prime), the debugger, and backward execution.

### Tests

Tests live in per-dialect directories mirroring the `--std` values
(`tests/jana2014/`, `tests/jana2014_in_out/`, `tests/janus2026/`, ...). Most are
`unittest.TestCase` classes (runnable under pytest), but a few files are
pytest-style (fixtures like `capsys`) and silently run nothing under plain
`python3 file.py` — use pytest to run the full suite. Most tests invoke the CLI
via `subprocess` against `python3 -m jana_py.cli`, with `.ja` fixtures in
`tests/<std>/fixtures/` (valid programs) and `tests/<std>/fixtures_errors/`
(programs expected to fail, e.g. aliasing violations, assertion failures, parse
errors). `tests/jana2014_in_out/programs/` holds `.ja` programs with embedded
`// case:/in:/out:` specs that `test_programs.py` runs forward AND backward.
When adding a language feature, add a fixture and assert both forward result and
reversibility.

Note: library helpers `encode.py` and `inverse.py` hardcode the `janus2026`
parser; `parser.py` is only a backwards-compat shim re-exporting
`parser_jana2014.parse_program` for old external callers.

## Formal mechanization (`coq/`)

`coq/` is a Rocq/Coq 9.1 development that machine-checks Janus's reversibility,
**independent of the Python interpreter**. The core abstraction is the module
type `REV_PRIM` + functor `RevLang` (`RevCore.v`): supply the atomic primitives
and three local laws (`pinv_invol`, `pstep_det`, `pstep_rev`) and the functor
proves the headline results once for all instances — `exec_rev`, `exec_iff`,
`exec_det`, and `exec_injective` (reversibility: a final store determines the
initial store). Other `.v` files are instances/extensions (denotational
semantics, dagger-category structure, Bennett embedding, an extracted fuel
interpreter).

- Build: `cd coq && rocq makefile -f _CoqProject -o Makefile && make` (whole dev
  ≈ 6 s). `.vo` files are build products (gitignored), so build with whatever
  single `rocq` is on PATH — currently opam 9.1.1; a `.vo` left over from a
  *different* install fails with "inconsistent assumptions over library
  Corelib.Init.Prelude", fixed by `make clean && make`. If `make` asks for a
  `rocqworker` under a path that no longer exists, the stale dep file is to
  blame: `rm -f coq/.Makefile.d` and regenerate the Makefile.
- `coq/audit.sh` builds the dev and asserts every headline theorem depends on at
  most `functional_extensionality` — no extra axioms, no `Admitted`. CI runs it
  (`.github/workflows/coq.yml`).
- How this development compares to the other machine-checked Janus (Paolini,
  Piccolo & Roversi's Matita formalization, TYPES 2015) — and which of its
  results are still worth importing — is tracked in
  `docs/janus-formalizations.md`.
- **Before claiming anything in the categorical layer is new, read
  `docs/reversible-categorical-semantics.md`.** Glück & Kaarsgaard already give
  the categorical semantics of Janus-class languages (join inverse categories,
  LMCS 2018), and the trace-as-loop, `test†` conditional, join-based recursion
  and rig structure all appear there first. That doc is the theorem-by-theorem
  correspondence and says what is left as genuinely new.

### Differential testing (`coq/harness/`)

The verified development is the oracle for the Python implementation:

- `differentialar.py` / `differential.py` — run the **verified** interpreter
  (`run`, extracted to OCaml from `RevExtract.v` and proved sound) against
  `pyjanus -s` on the same `.ja` program and compare final stores. The two
  interpreters are completely independent (extracted Coq vs hand-written Python).
- `codegen_diff.py` — run PyJanus's interpreter against its **C++ codegen**
  output (compile at `-O0`, run, compare stores). This is what caught the
  codegen wrong-output bugs; it is folded into pytest. When touching `runtime.py`
  or `c_codegen.py`, run these to catch divergence.
  The contract is two-sided and **a compile failure is a test failure, not a
  skip**: what the generator emits must compile *and* must agree with the
  interpreter. A construct the back-end cannot translate must raise out of
  `format_program` (reported `CGERR`, skipped) rather than be emitted as broken
  C++. All 97 examples pass, including structs, rank-*n* arrays and keyword-named
  identifiers. Because C++ resolves every name, this test is also the static
  checker the interpreter lacks — it caught a call to an undefined procedure and
  a body using an undeclared variable, both in unreachable code.
