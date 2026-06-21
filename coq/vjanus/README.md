# vjanus — a standalone verified Janus interpreter

`vjanus` runs **jana2014** programs through the **machine-checked** evaluation
core extracted from Coq (`run` in `coq/RevExtractAr.v`, proved sound & complete
against the big-step semantics of `RevArr.v`, which is itself proved reversible).
Unlike the differential test harness, it has **no Python dependency at runtime**:
its own OCaml lexer/parser reads jana2014 source and lowers it to the verified
AST.

```
prog.ja → lexer + parser (own AST) → lower → extracted run → final store
```

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

## Compatibility & scope

"jana2014-compatible" means it accepts the language of `jana_py/parser_jana2014.py`.
This is verified, not asserted: `tests/jana2014/test_vjanus_corpus.py` runs the
whole corpus through both `vjanus` and PyJanus and asserts identical stores
(36 match, forward and via in-program `call`/`uncall`).

Three jana2014 features are **not yet** in the verified core and make `vjanus`
exit with a clean "unsupported" (exit code 3), not a crash:

- self-recursive procedures that declare a `local` (no activation-record frame
  stack — the flat store would alias locals across frames);
- self-referential `local x = … delocal x = e(x)`;
- structs.

These are the subject of Phase 2 (extending the formalization). The lowering
mirrors `coq/harness/differentialar.py` (stacks → array+top counter; `local`
→ `Enter`/`Exit`; call args by reference / swap-temp / value-wrap; multi-dim
indices via an injective Cantor pairing).

## Files

| file | role |
|------|------|
| `glue.ml`   | int ↔ Coq numeral conversions; thin runner over `Janus_arr.run` |
| `ast.ml`    | vjanus's own jana2014 AST |
| `lexer.ml`  | jana2014 tokenizer |
| `parser.ml` | recursive-descent parser → AST |
| `lower.ml`  | AST → verified `stmt`/`expr` + slot/proc/array-length tables |
| `main.ml`   | CLI (`-s` run + store dump) |
| `build.sh`  | extract + compile |
