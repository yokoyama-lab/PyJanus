# Differential testing: verified interpreter vs. PyJanus

This harness runs the **verified** interpreter — `run`, extracted to OCaml from
`RevExtract.v` and proved sound against the big-step semantics (`run_sound`) —
on `.ja` programs and checks its final store against the **PyJanus**
implementation (`pyjanus -s`).

```
./run.sh                       # build + test all fixtures/*.ja
```

`run.sh` (1) extracts `janus_verified.ml` (via `rocq compile RevExtract.v`),
(2) compiles `driver.ml` against it, (3) runs `differential.py` over the
fixtures.

## How it works

- `differential.py` parses each program with PyJanus's own front end
  (`pyjanus --std jana2014 -a`, the JSON AST), translates it into the small
  s-expression the driver reads, runs the driver, and runs `pyjanus -s` on the
  same file; it then compares the two final stores.
- `driver.ml` reads the s-expr, builds the extracted `stmt`/`expr` values, runs
  `Janus_verified.run`, and prints the final store.

The two interpreters are completely independent (one is extracted Coq, the other
hand-written Python), so agreement on e.g. `x ^= y` giving `7 XOR 4 = 3` is a
genuine cross-check.

## Three interpreters

- **core** (`differential.py` + `driver.ml`, from `RevExtract.v`): `int` vars,
  `+= -= ^=`, `<=>`, `if/fi`, `from/loop/until`, seq, `skip`.
- **parameterized** (`differentialp.py` + `driverp.ml`, from `RevExtractP.v`):
  the above **plus reference procedures** (`call`/`uncall` with arguments).
- **array+procedure** (`differentialar.py` + `driverar.ml`, from
  `RevExtractAr.v`, *most capable*): the above **plus arrays** — reads `A[e]`,
  cell assignments `A[e] op= …`, and arrays passed by reference. This is the one
  `run.sh` runs over the real fixtures.

A call's actuals are emitted as variable slots and the verified interpreter
renames the callee's formals onto them (matching `RevProc`/`RevArr` reference
semantics). `call` vs `uncall` is recovered from the node's source position,
since PyJanus's `-a` serializes both identically. Scalars and arrays share the
verified store's location space (`LS x` vs. `LA a i`), so one global-slot map
serves both. Only `main`'s declared variables/array cells are compared (via a
*report list* built from PyJanus's `-s` output). Passes e.g. `fib.ja` (recursive
reference procedures) and array-by-reference programs.

Supported beyond the core: reference procedures, arrays (incl. by reference,
array-element swap `A[i] <=> B[j]`, initializers `int A[3] = {…}`, and **array
cells passed by reference** `f(A[i])`, realized as `A[i] <=> t; f(…,t); A[i] <=> t`),
**`local`/`delocal`** blocks (verified `Enter`/`Exit`), **`iterate`/`for`**
counting loops (desugared to a local counter + `from/loop/until`), **value
arguments** (`f(…,e)` → `local t=e; f(…,t); delocal t=e`), the operators `/ %`
(matching Python floor-division/modulo) and `>= <= != && ||` (encoded by
truthiness, since they occur only in conditions). Every argument-passing mode
thus reduces to scalar reference + the verified constructs — no special calling
convention in the kernel.

**Multi-dimensional** arrays are supported by folding indices with an injective
Cantor pairing into the 1-D verified store (translator-only); the verified
`wf_assign` is a *runtime* cell-aliasing test, so `A[j][i] += … A[j][k]` is
accepted exactly when the cells differ. **Stacks** are a fresh array + a top
counter: `push(x,s)` = `s#arr[s#top] <=> x; s#top += 1`, `pop` its inverse;
`empty(s)`/`size(s)` read the counter; a `stack` argument passes both ids by
reference.

## Scope

Skipped automatically (each needs a deeper model extension): a procedure that is
**self-recursive and declares locals** (the flat-slot model has no per-frame
stack for locals — recursion with only reference parameters, e.g. `fib`, is
fine), a *self-referential* `delocal` (`delocal x = x`, needing a whole-block
argument), and `size(A)` for arrays (runtime array length). Also skipped:
programs PyJanus rejects at run time (out-of-bounds, division by zero).

## Files

- `driver.ml` / `driverp.ml` / `driverar.ml` — OCaml front ends.
- `differential.py` / `differentialp.py` / `differentialar.py` — translators.
- `run.sh` — build & run.
- `fixtures/*.ja` — in-subset Janus programs.
