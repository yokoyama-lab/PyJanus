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
2. **(done, `coq/RevLowerExpr.v`)** The jana2014 **expression** semantics in
   Coq, the Gallina model of `lower.ml`'s `expr`, and value preservation:

   ```
   lower_expr_sound : seval g e = Some v -> eval 0 (enc g) (lower e) = v
   ```

   The source semantics is read off PyJanus's `_eval_bin` / `_check_bin_operands`
   and is *partial*: `/` and `%` have no value at a zero divisor, and `&&`, `||`,
   `!` have none unless their operands are booleans — which is exactly what
   licenses the arithmetic encodings. `and_encoding` / `or_encoding` prove
   `&& = l*r` and `|| = l + r - l*r` correct on 0/1 operands, and
   `or_squares_wrong` refutes the `|| = l*l + r*r` this file used to have
   (it yields 2 at `l = r = 1`) — the bug the comment below records as
   "caught by hand", now mechanized.

   **The slice found a live soundness bug — since fixed.** `seval` is partial
   where the core's `bden` is total, and the two really did diverge:

   | expression | PyJanus | vjanus |
   |---|---|---|
   | `x / 0` | raises `Division by zero` | quietly yields `0` |
   | `x % 0` | raises `Division by zero` | quietly yields `x` (`Z.modulo a 0 = a`) |

   Confirmed against both implementations, not just on paper
   (`RevLowerExpr.div_zero_diverges` / `mod_zero_diverges`, plus
   `test_division_by_zero_is_refused` in `tests/jana2014/test_vjanus_features.py`,
   which now passes). The corpus differential test never caught it because no
   example divides by zero, and a program PyJanus rejects at run time is skipped
   by the harness rather than compared — a structural blind spot of differential
   testing that a semantics model does not share.

   **Fixed** by making expression evaluation *guarded* in `RevFrame.v`, in the
   shape `aok` already uses for `*=`/`/=`: a decidable `safe d s e` (no division
   or modulus by a zero divisor anywhere in `e`), threaded into every premise
   that evaluates an expression — `wf_asn`/`wf_aasn`, both `If` rules, `E_Loop`,
   `L_one`/`L_more`, `O_cons`, `E_Enter`/`E_Exit` — with `safe_ncell` (safety
   survives an update the expression does not read) as the stability lemma that
   lets the reversal rebuild the inverted statement's guard, exactly as
   `reads_cell_stable` does for aliasing. `run`/`runloop` check it too, so
   `run_sound` and `run_complete` still hold. vjanus now refuses `x / 0` instead
   of computing 0.

   That the guard is not *over*-restrictive is itself proved: `lower_expr_safe`
   says a source expression that has a value lowers to a safe one, so no program
   PyJanus accepts is newly rejected (`lower_expr_ok` bundles safety with value
   preservation). Making `eval` itself `option`-valued would have been more
   faithful but ripples through every use, including extraction.

   **A second live bug, same shape.** The first model wrote the boolean
   restriction as a *value-level* condition (operands in `{0,1}`), which is
   **more permissive than PyJanus** — the unsafe direction. PyJanus checks
   `isinstance(v, bool)`, so the rule is **syntactic**: only a comparison, `!`,
   `&&`, `||` or `empty` produces a Python `bool`, and a variable holding `1` is
   an `int` and is rejected. vjanus had no such check, so:

   | expression | PyJanus | vjanus (before) |
   |---|---|---|
   | `2 && 3` | type error | `6` (it lowers to `2 * 3`) |
   | `b \|\| c`, `b`,`c` vars holding 1 | type error | `1` |
   | `!x`, `x` an int | type error | `x == 0` |

   The encodings `&& = l*r` and `|| = l + r - l*r` are correct *only* on 0/1, so
   without the check the lowering is unsound — `and_needs_wf` states exactly
   that: `wf (2 && 3) = false`, the source value is 1, the lowered value is 6.
   Fixed by giving `lower.ml` the same syntactic check (`is_bool_expr`,
   rejecting with a type error as PyJanus does), and by replacing the model's
   value-level condition with `isbool`/`wf`, which `lower_expr_sound` and
   `lower_expr_safe` now require. `bool_check_is_syntactic` pins that a variable
   holding 1 does not qualify.

   Not covered by this slice (each needs the ref-classification model): array and
   struct l-values, stacks, `size`/`top`/`empty`, and the Cantor index fold —
   whose injectivity is already in `RevLowering.v`.
3. **(done, `coq/RevLowerStmt.v`)** The statement forms of the scalar fragment,
   end to end against a Coq reference semantics, establishing the simulation
   skeleton:

   ```
   lower_stmt_sound   : sexec s g h -> exec Γ 0 (lower_stmt s) (enc g) (enc h)
   lower_stmt_correct : sexec s g h -> exec Γ 0 (lower_stmt s) (enc g) t -> t = enc h
   ```

   The first is the forward simulation; the second is what vjanus actually needs
   — with the core's `exec_det`, if the reference semantics says the answer is
   `h` then the translation cannot produce anything else. `lower_stmt_reversible`
   comes free from `exec_rev`.

   Covered: `skip`, `x op= e`, `x <=> y`, sequencing, `if/fi`, `from/loop/until`.
   The guards follow PyJanus (`Runtime` applies `bool(value)`, so *any* nonzero
   is true — no boolean requirement, unlike `&&`/`||`), and an assignment carries
   the occurrence check, the expression's definedness and `aok`.

   The case that carries the content is `x <=> y`, the one rule here that is not
   one-to-one: `swap_lowering` discharges the XOR triple against `RevFrame.exec`
   itself rather than on an abstract store, and in doing so **forces the side
   condition into the statement** — the triple zeroes the cell when `x = y`, so
   the source semantics may only admit `x <> y` (`self_swap_has_no_step` pins the
   failure mode). Both implementations already agreed on that; the proof now
   records *why* it is needed instead of leaving it to the aliasing checker.
   `reads_lower` is the other bridge: the core's runtime aliasing test on a
   lowered expression is exactly the source's occurrence check.

   **Both directions are now proved on this fragment.** `lower_stmt_complete`
   is the converse — a core run implies a source run — and `lower_stmt_iff`
   bundles them:

   ```
   lower_stmt_complete : wfs s = true ->
       exec Γ 0 (lower_stmt s) (enc g) t -> exists h, t = enc h /\ sexec s g h
   lower_stmt_iff      : wfs s = true ->
       (sexec s g h <-> exec Γ 0 (lower_stmt s) (enc g) (enc h))
   ```

   The converse is what rules out vjanus *accepting* a program the reference
   semantics rejects, and getting it to go through is precisely what exposed the
   two lowering bugs above:

   - a zero divisor is recovered from `RevFrame.safe` — which the core carries
     only because of the first fix; before it, `BDiv` was total and the core
     simply ran where the source errored;
   - the boolean restriction on `&&`/`||`/`!` is **not recoverable at all**,
     because the lowering erases it (`&&` becomes `BMul`). It has to be a
     hypothesis, `wfs s` — and that is exactly the check `lower.ml` now performs
     statically, which is the second fix.

   So the hypothesis of the theorem and the check in the translator are the same
   condition, which is the useful outcome: the proof says what the translator
   must verify, and the translator verifies it.

   `seval_defined` is the bridge in the other direction: the core's safety guard
   is the source's definedness, so an expression the core will evaluate is one
   the source gives a value to.

4. **(started)** The **ref classification** — `lower.ml`'s `ref_of`, which sends
   a `main` variable to `RG n` (cell `G n`) and a local to `RL x` (cell `L d x`).
   `RevLowerExpr`/`RevLowerStmt` now carry a scope `lv : nat -> bool` through
   `lower`, `lower_stmt` and `enc`, so a source name lands in a global or a local
   slot according to it, and:

   - `loceqb_sloc` — **distinct source names never alias**, whatever their kinds:
     a global slot and a local slot are always different cells, and two of the
     same kind differ by name. This is the invariant that makes the flattening
     safe, and it is what the aliasing side conditions rest on;
   - `reads_lower` now relates the core's runtime aliasing test to the source's
     occurrence check **across both slot kinds**, not just globals.

   What is *not* done is `local`/`delocal` itself. Designing it turned up two
   requirements worth recording, because they are not obvious until the proof
   demands them:

   - **the source semantics has to be scope-indexed** (`sexec lv`), not because
     `seval` depends on the scope — it does not, the source store is one
     namespace — but because the body of a `local` is lowered at `sc_set lv x`
     while the surrounding statement is at `lv`, so the induction hypothesis has
     to be available at the *inner* scope;
   - **a deadness invariant has to be threaded**: `enc` sends an unbound name to
     0, so `Enter`'s dead-cell premise `s (L d x) = 0` is *automatic* in the
     forward direction but carries **no information back** — the backward
     direction cannot recover `g x = 0` from it. It has to be an invariant on the
     source store ("every name not currently bound holds 0"), preserved by every
     rule, rather than a premise of the `local` rule.

   Neither is hard, but together they change the shape of `sexec` and of both
   simulation theorems, so they are their own increment rather than a case to
   add.

5. Then the rest: arrays and the Cantor index fold, structs, stacks, and
   `call`/`uncall` with the frame depth — the point at which `RevLowering.v`'s
   isolation lemmas become leaves of a simulation rather than free-standing
   facts.
