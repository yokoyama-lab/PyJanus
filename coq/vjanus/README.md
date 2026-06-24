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
value}`), struct arrays (a row-major list of `{field: value}`) and structs with
**array fields** (`{v: [..], ..}`); multi-dim arrays, struct arrays and array
fields are flattened row-major to match PyJanus, and the seed accepts either flat
or nested input. A **stack** in main makes it exit 3 ("unsupported"): PyJanus
`--inverse` can't seed a stack, so there is no oracle to match there.
`tests/jana2014/test_vjanus_inverse.py` is the differential check (verified
inverse vs PyJanus, over the whole corpus).

## Compatibility & scope

"jana2014-compatible" means it accepts the language of `jana_py/parser_jana2014.py`.
This is verified, not asserted: `tests/jana2014/test_vjanus_corpus.py` runs the
whole corpus through both `vjanus` and PyJanus and asserts identical stores —
every main scalar, array, stack and struct, forward and via in-program
`call`/`uncall` (including nested struct-by-reference, the reverse of a
stack-building procedure, and structs with array fields).  Currently
**47 match, 1 skips**.

One jana2014 construct makes `vjanus` exit with a clean "unsupported" (exit code
3), not a crash — and it is a **principled boundary**, not just unfinished work:

- self-referential `delocal x = e(x)` — in practice `delocal i = i`, used to free
  a loop counter at its *dynamic* final value (e.g. `local i = 0; from i = 0 …
  until i+1 >= n; delocal i = i`).

  This is fundamentally outside a *statement-reversible* interpreter. `vjanus`'s
  core proves every statement reversible (`exec_rev`), and freeing a non-zero
  local back to a dead cell is not reversible in isolation: the inverse cannot
  recover the discarded value. The two escapes both fail here — recording the
  value as history makes the final store carry garbage (so it no longer matches
  PyJanus), and uncomputing the loop to bring `i` back to its initial value is
  non-local (it would also undo the loop's real effects). PyJanus accepts the
  construct only because it runs forward and may discard a local outright;
  `vjanus`, being verified-reversible, may not. Supporting it would require
  recognising the whole `local … loop … delocal i=i` idiom as one reversible
  unit (a loop-aware, non-local lowering) rather than per-statement Enter/Exit.

The lowering
classifies each variable into the frame core's refs — a `main` global (`RG`), a
depth-`d` local (`RL`), or a positional formal (`RF`, resolved to the actual's
absolute name at the call site) — and encodes:

- arrays as flat cells with an injective Cantor pairing for multi-dim indices;
- stacks as an (array, top-counter) pair (two globals / two formals / two
  locals); `push`/`pop` as the counter bump plus an XOR swap (the core has no
  Swap primitive);
- structs as a compile-time grouping of slots: a field access resolves to one
  slot (scalar struct) or an array cell at `elem*size + offset` (struct array);
  a struct passes by reference as one ref per field, an array of structs as a
  single base ref; a struct-valued `local` is one `Enter`/`Exit` per field. A
  struct with **array fields** is laid out flat in a single array slot — each
  array field reserves enough cells for its Cantor-folded indices, so `a.v[i]`
  is `base + offset(v) + Cantor(i)` (such structs are GA-addressed, hence not
  passed by reference);
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
