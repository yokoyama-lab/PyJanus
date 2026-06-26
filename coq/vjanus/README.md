# vjanus — a standalone verified Janus interpreter

`vjanus` runs **jana2014** programs through the **machine-checked** evaluation
core extracted from Coq (`run` in `coq/RevExtractFrame.v`, proved sound against
the big-step semantics of `RevFrame.v`, which is itself proved reversible).
Unlike the differential test harness, it has **no Python dependency at runtime**:
its own OCaml lexer/parser reads jana2014 source and lowers it to the verified
AST.

```
prog.ja → lexer + parser (own AST) → lower → extracted run → final store
```

The core is **frame-stacked**: locals live in depth-indexed frames (`L d x`), so
a procedure that recurses while declaring a `local` gets fresh storage per
activation. That is what lets `vjanus` run programs the earlier flat-store core
could not (e.g. `stack-operations.ja`'s recursive `reverse`).

## Build & run

```bash
bash coq/vjanus/build.sh                 # extracts (rocq) + compiles (ocamlc)
coq/vjanus/vjanus -s prog.ja             # run, print the final store
coq/vjanus/vjanus -inverse '<JSON>' prog.ja   # inverse: final store -> initial store
```

Requires the Rocq prover (for the one-time extraction) and `ocamlc`. The store is
printed in PyJanus's `-s` format, so results compare directly:

```bash
coq/vjanus/vjanus -s ../../tests/jana2014/fixtures/examples/fib.ja
```

`build.sh` also builds and runs `frame_smoke`, a direct end-to-end check of the
extracted core on the recursion-with-locals aliasing case.

### Verified inverse (`-inverse`)

`-inverse '<final-store JSON>'` reconstructs the **initial** store from a final
one, using the Coq-extracted `invert` (`RevExtractFrame.v`, proved to satisfy
`RevFrame.exec_iff`): it inverts main's body and runs it from the seeded final
store. It is **output-compatible with PyJanus `--inverse`** — same input JSON,
same output JSON — so the two inverters compare directly. Following PyJanus, the
declaration initializers are *not* inverted: the reconstructed store is the state
at the start of main's body (its declared initial values), and the seed stands
in for re-declaring with the final store.

```bash
coq/vjanus/vjanus -inverse '{"x": 3, "y": 8}' prog.ja              # -> {"x": 0, "y": 0}
coq/vjanus/vjanus -inverse '{"a": {"x": 4, "y": 4}}' prog.ja       # scalar struct
```

Scope is main scalars, integer arrays (any rank), scalar structs (`{field:
value}`), struct arrays (a row-major list of `{field: value}`), structs with
**array fields** (`{v: [..], ..}`) and **stacks** (a top-first contents list);
multi-dim arrays, struct arrays and array fields are flattened row-major to match
PyJanus, and the seed accepts either flat or nested input.
`tests/jana2014/test_vjanus_inverse.py` is the differential check (verified
inverse vs PyJanus, over the whole corpus) — it matches on every program, with no
skips.  (The self-referential `delocal` is invertible on both sides: vjanus via
its loop-aware lowering, and PyJanus via a matching reverse-count desugaring in
`jana_py/inverse.py`, added so it no longer inverts `delocal i=i` to an invalid
`local i=i`.)

## Compatibility & scope

"jana2014-compatible" means it accepts the language of `jana_py/parser_jana2014.py`.
This is verified, not asserted: `tests/jana2014/test_vjanus_corpus.py` runs the
whole corpus through both `vjanus` and PyJanus and asserts identical stores —
every main scalar, array, stack and struct, forward and via in-program
`call`/`uncall` (including nested struct-by-reference, the reverse of a
stack-building procedure, and structs with array fields).  The whole corpus
matches: **52 match, 0 skip**.

### Variable scope

jana2014 has three variable classes, and each has a distinct scope:

| class | introduced by | scope | frame ref |
|-------|---------------|-------|-----------|
| **global** | `procedure main()` declaration block | entire `main` body | `RG n` |
| **formal** | procedure parameter list | entire procedure body | `RF i` (positional index), substituted to the caller's ref at each call site |
| **local** | `local x = e` | `body` in `local x = e; body; delocal x = e'` | `RL d n` (frame depth `d`) |

Two scoping rules enforced by `check_program` (static error, exit 1):

1. **`local x = e` — `x` is NOT yet in scope at `e`.**  The initialiser `e`
   runs before `x` is allocated.  `local i = i + 1` is rejected: there is no
   `i` at that point.

2. **`delocal x = e'` — `x` IS still in scope at `e'`, but self-reference is
   forbidden.**  When `e'` reads `x`, the freed value references the dying
   cell; the inverse `Enter` would try to read a dead (zero) cell instead.
   Any self-referential delocal is a static error — see the section below.

These rules are not enforced by PyJanus (which only runs forward), so a program
that passes PyJanus may still be rejected by vjanus if it violates them.

### Self-referential `delocal` — static error

Any `delocal x = e` where `e` reads `x` is a **static error** (exit 1):
`check_program` walks the AST before lowering and rejects it with a clear
message.  The reason is fundamental: freeing a non-zero local reversibly requires
the delocal expression to give the cell's current value without reading the cell
itself — otherwise the inverse `Enter` would try to read a dead (zero) cell.

The canonical rewrite for a loop counter is to keep the final value in a separate
non-self-referential expression.  For example, instead of:

```janus
local int i = 0
    from i = 0 do { body; i += 1 } until i = n
delocal int i = i               // ERROR: reads i
```

use `iterate` or a helper variable whose delocal expression does not mention itself:

```janus
iterate int i = 0 to n - 1     // no local/delocal needed at all
    body
end
```

or, when `n / 2` iterations are needed:

```janus
local int pairs = n / 2         // delocal reads n, not pairs
    iterate int i = 0 to pairs - 1
        arr[i * 2] <=> arr[i * 2 + 1]
    end
delocal int pairs = n / 2
```

The lowering
classifies each variable into the frame core's refs — a `main` global (`RG`), a
depth-`d` local (`RL`), or a positional formal (`RF`, resolved to the actual's
absolute name at the call site) — and encodes:

- arrays as flat cells with an injective Cantor pairing for multi-dim indices;
- stacks as an (array, top-counter) pair (two globals / two formals / two
  locals); `push`/`pop` as the counter bump plus an XOR swap (the core has no
  Swap primitive);
- structs as a compile-time grouping of slots: a field access resolves to one
  slot (scalar struct) or an array cell at `elem*size + offset` (struct array).
  A *scalar* struct (no array fields) passes by reference as one ref per field
  and a struct-valued `local` uses one `Enter`/`Exit` per field.  A struct
  with **array fields** (`lstructs_flat` / `fstructs_flat` / `gstructs_flat`)
  is laid flat in a single array slot — each array field reserves enough cells
  for its Cantor-folded indices (`a.v[i]` = `base + offset(v) + Cantor(i)`) —
  and passes as a **single base ref** (RG/RL/RF) so that `ARd(base, foff)` in
  the callee resolves correctly after `argsubst`; a flat-struct `local` uses
  `AAsn(OAdd/OSub)` per statically-enumerated cell instead of `Enter`/`Exit`;
- by-value call args via `Enter`/`Exit` on a fresh local; array-cell args via a
  swap-temp (XOR) around the call.

## Files

| file | role |
|------|------|
| `glue.ml`   | int ↔ Coq numeral conversions; runners over `Janus_frame.run` (forward, and seeded for `invert`) |
| `ast.ml`    | vjanus's own jana2014 AST |
| `lexer.ml`  | jana2014 tokenizer |
| `parser.ml` | recursive-descent parser → AST |
| `lower.ml`  | AST → verified frame `stmt`/`expr` + ref classification, arrays, stacks |
| `main.ml`   | CLI (`-s` run + store dump; `-inverse` verified inverse + JSON I/O) |
| `frame_smoke.ml` | end-to-end check of the extracted core on recursion-with-locals |
| `build.sh`  | extract + compile |
