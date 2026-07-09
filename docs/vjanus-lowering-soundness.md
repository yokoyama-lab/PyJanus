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

2. **Rule-level correctness for the encodings that carry proof obligations**
   (`coq/RevLowering.v`, machine-checked, no axioms beyond
   `functional_extensionality`; the arithmetic-addressing lemmas need none).
   Most lowering rules map one source construct to one core primitive, so they
   are correct by construction. The rules that *encode* a construct with no
   direct core counterpart — where a translator can silently go wrong — are each
   verified in isolation:

   - **Swap → XOR triple.** The frame core has no `Swap` primitive, so `x <=> y`
     becomes `x ^= y; y ^= x; x ^= y`. `xor3_swaps` proves the triple computes
     the swap; `xor3_selfinverse` proves it is its own inverse (so `uncall` of a
     swap is correct). `xor3_alias_zero` proves that if the two operands alias
     the *same* cell the triple collapses it to 0 — the reason an aliased
     `a[i] <=> a[i]` is rejected statically.
   - **Stack `push`/`pop` → XOR-swap + counter.** `push(x,s)` lowers to an XOR
     swap of the top cell and `x` followed by `top += 1` (and `pop` the reverse).
     `pop_push` proves `pop` undoes `push`; `push_clean` proves that with a clean
     top cell it is the intended stack move (value onto the stack, `x` consumed
     to 0).
   - **Clean local-array bracket.** `local int a[n]` is lowered by bracketing the
     body with per-cell `a[c] += 0` / `a[c] -= 0`. `add_zero_noop` / `sub_zero_noop`
     prove each bracket is the identity on the store.
   - **Array cell addressing is injective (no aliasing).** Struct-array element
     fields address `elem*n + off` (`off < n`): `addr_injective` proves distinct
     (element, field) pairs never collide. Multi-dimensional array indices fold
     via the Cantor pairing `(a+b)*(a+b+1)/2 + b`: `cantor2_injective` proves
     distinct index pairs never collide (`tri_closed` ties the fixpoint
     triangular number to `vjanus`'s closed-form `cantor_val`).

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

1. **(done)** Rule-in-isolation lemmas in `RevLowering.v`: the swap XOR triple,
   the stack `push`/`pop` XOR-swap-plus-counter, the clean local-array bracket,
   and injectivity of both struct-array addressing and the Cantor index fold.
   The one remaining rule of this kind is the by-value call idiom (`Enter`/`Exit`
   on a fresh local around the call), which needs the frame core's `Enter`/`Exit`
   and so is best proved against `RevFrame.v` rather than in isolation.
2. Formalize the jana2014 **expression** semantics in Coq and prove the
   expression-lowering (`expr` in `lower.ml`) preserves values — the smallest
   self-contained slice of full soundness. (Note: this would also pin down the
   boolean-coercion rules — e.g. `||` is lowered to `l*l + r*r`, valid only when
   its result is consumed as a truth value; formalizing expressions makes that
   side condition explicit.)
3. Tackle a single statement form end-to-end (e.g. `Assign`) against a Coq source
   semantics, establishing the simulation skeleton the other forms slot into.
