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
```

Requires the Rocq prover (for the one-time extraction) and `ocamlc`. The store is
printed in PyJanus's `-s` format, so results compare directly:

```bash
coq/vjanus/vjanus -s ../../tests/jana2014/fixtures/examples/fib.ja
```

`build.sh` also builds and runs `frame_smoke`, a direct end-to-end check of the
extracted core on the recursion-with-locals aliasing case.

## Compatibility & scope

"jana2014-compatible" means it accepts the language of `jana_py/parser_jana2014.py`.
This is verified, not asserted: `tests/jana2014/test_vjanus_corpus.py` runs the
whole corpus through both `vjanus` and PyJanus and asserts identical stores —
every main scalar, array and stack, forward and via in-program `call`/`uncall`.
Currently **37 match, 1 skips**.

One jana2014 feature is **not yet** in the verified core and makes `vjanus` exit
with a clean "unsupported" (exit code 3), not a crash:

- self-referential `local x = … delocal x = e(x)` (the delocal value reads the
  variable being removed).

This is the subject of Phase 2b (extending the formalization). Structs are a
later phase. The lowering classifies each variable into the frame core's refs —
a `main` global (`RG`), a depth-`d` local (`RL`), or a positional formal (`RF`,
resolved to the actual's absolute name at the call site) — and encodes:

- arrays as flat cells with an injective Cantor pairing for multi-dim indices;
- stacks as an (array, top-counter) pair (two globals / two formals / two
  locals); `push`/`pop` as the counter bump plus an XOR swap (the core has no
  Swap primitive);
- by-value call args via `Enter`/`Exit` on a fresh local; array-cell args via a
  swap-temp (XOR) around the call.

## Files

| file | role |
|------|------|
| `glue.ml`   | int ↔ Coq numeral conversions; thin runner over `Janus_frame.run` |
| `ast.ml`    | vjanus's own jana2014 AST |
| `lexer.ml`  | jana2014 tokenizer |
| `parser.ml` | recursive-descent parser → AST |
| `lower.ml`  | AST → verified frame `stmt`/`expr` + ref classification, arrays, stacks |
| `main.ml`   | CLI (`-s` run + store dump) |
| `frame_smoke.ml` | end-to-end check of the extracted core on recursion-with-locals |
| `build.sh`  | extract + compile |
