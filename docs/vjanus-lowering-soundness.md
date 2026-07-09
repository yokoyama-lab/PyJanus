# vjanus lowering soundness — status and roadmap

`vjanus` (`coq/vjanus/`) reads jana2014 source, **lowers** it (`lower.ml`,
OCaml, ~660 lines) to the machine-checked frame core (`coq/RevFrame.v`, extracted
via `coq/RevExtractFrame.v`), and runs it. The evaluation *core* is proved
reversible and sound in Coq. The open question is the **lowering** itself: does
`lower.ml` preserve the intended jana2014 semantics? This note records what is
verified today and what a full proof would require.

## What guarantees the lowering today

1. **Differential testing against the oracle.** `tests/jana2014/test_vjanus_corpus.py`
   runs the whole corpus through both `vjanus` and PyJanus and asserts identical
   final stores (forward and via in-program `call`/`uncall`);
   `test_vjanus_inverse.py` does the same for the verified `-inverse`. Every
   program in the verified subset matches. This is strong empirical evidence, not
   a proof.

2. **Rule-level correctness for the two nontrivial encodings** (`coq/RevLowering.v`,
   machine-checked, no axioms beyond `functional_extensionality`). Most lowering
   rules map one source construct to one core primitive, so they are correct by
   construction. Exactly two rules *encode* a construct with no core counterpart,
   and those are where a translator can silently go wrong:

   - **Swap → XOR triple.** The frame core has no `Swap` primitive, so `x <=> y`
     becomes `x ^= y; y ^= x; x ^= y`. `RevLowering.xor3_swaps` proves the triple
     computes the swap; `xor3_selfinverse` proves it is its own inverse (so
     `uncall` of a swap is correct). `xor3_alias_zero` proves that if the two
     operands alias the *same* cell the triple collapses it to 0 — the reason an
     aliased `a[i] <=> a[i]` is rejected statically.
   - **Clean local-array bracket.** `local int a[n]` is lowered by bracketing the
     body with per-cell `a[c] += 0` / `a[c] -= 0`. `add_zero_noop` / `sub_zero_noop`
     prove each bracket is the identity on the store.

## What a full soundness proof would require

End-to-end soundness is the theorem: *for every jana2014 program `P`, the store
computed by `run (lower P)` equals the store defined by a reference jana2014
semantics of `P`.* Reaching it is a distinct, larger undertaking:

1. **A Coq reference semantics for jana2014** — big-step over the source AST
   (scalars, arrays with Cantor-folded multi-dim indices, stacks, structs,
   `local`/`delocal`, `call`/`uncall`, all guards and expressions). Today the
   *reference* is the PyJanus interpreter, in Python.
2. **A Gallina model of `lower.ml`** — the ref-classification (`RG`/`RF`/`RL`),
   array/stack/struct flattening, the by-value/`Enter`-`Exit` and swap-temp
   calling idioms, the XOR encodings — re-expressed as a Coq function.
3. **A simulation/commutation proof** relating source `exec` to core `exec`
   through the lowering, per construct, discharged with the rule-level lemmas
   above as leaves.
4. **A parser-adequacy argument** (or a shared AST) so the OCaml parser in
   `coq/vjanus/parser.ml` and the Coq source AST agree.

Steps 1–3 are comparable to a small verified-compiler pass and are the natural
next research increment; step 4 is an engineering boundary (the parser is trusted
today, as in most verified pipelines).

## Suggested increments (small → large)

1. Grow `RevLowering.v` to cover more rules in isolation (by-value call via
   `Enter`/`Exit`; the stack `push`/`pop` XOR-swap-plus-counter; struct-field
   addressing `elem*size + offset`).
2. Formalize the jana2014 **expression** semantics in Coq and prove the
   expression-lowering (`expr` in `lower.ml`) preserves values — the smallest
   self-contained slice of full soundness.
3. Tackle a single statement form end-to-end (e.g. `Assign`) against a Coq source
   semantics, establishing the simulation skeleton the other forms slot into.
