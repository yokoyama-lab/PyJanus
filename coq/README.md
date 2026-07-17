# Mechanized reversibility of Janus (Rocq/Coq)

A machine-checked proof, in the [Rocq Prover](https://rocq-prover.org/) (Coq
successor, tested with **Rocq 9.1**), that **Janus** — the reversible imperative
language — is reversible, packaged as a **reusable framework** that applies to a
*class* of reversible structured languages rather than to Janus alone.

## What is proved

For every program `s` and procedure environment `Γ`, the big-step semantics
`exec` satisfies:

| Theorem | Statement |
|---|---|
| `exec_rev` | `exec s a b → exec (invert s) b a` — the inverted program runs backwards |
| `exec_iff` | `exec s a b ↔ exec (invert s) b a` |
| `exec_det` | forward determinism |
| `exec_injective` | `exec s a b → exec s a' b → a = a'` — **reversibility**: a final store determines the initial store (the program denotes an *injective* partial function) |

These follow the big-step operational semantics whose reversibility is the
reference property of the small-step paper *“A Small-Step Semantics for Janus”*,
RC 2024 ([hal-04610285](https://inria.hal.science/hal-04610285)).

## The framework (contribution ④)

The reversibility argument is **language-independent**. `RevCore.v` isolates it
behind a module type `REV_PRIM` whose obligations are *local* laws on the atomic
primitives only:

```
pinv_invol : pinv (pinv p) = p
pstep_det  : pstep p a b → pstep p a b' → b = b'
pstep_rev  : pstep p a b → pstep (pinv p) b a
```

The functor `RevLang (P : REV_PRIM)` builds the structured control flow
(sequencing, **assertion-guarded** conditionals and loops, procedure
call/uncall), the inverter `invert`, the semantics `exec`, and proves the four
theorems above **once and for all**. The slogan:

> *A structured language is reversible exactly when its atoms are locally
> invertible.* The control-flow skeleton is shared; only the atoms differ.

### Combinator-level independence: the relational algebra (`RevAlgebra.v`)

`RevLang` fixes the *control-flow constructors*. `RevAlgebra.v` lifts the
abstraction one level further: a program denotes a **relation** on an abstract
`state`, a relation is `reversible` when it is a partial injection
(`det R /\ det (conv R)` — deterministic forwards *and* backwards), and each
control-flow construct is a **relational combinator** whose reversibility is a
*closure theorem*:

| combinator | meaning | closure lemma |
|---|---|---|
| `idR` | skip | `rev_id` |
| `compR` | sequencing | `rev_comp` |
| `conv` | uncall (converse) | `rev_conv` |
| `ifR` | assertion-guarded choice | `rev_if` |
| `loopR` | `from/do/loop/until` | `rev_loop` |
| `iterR` | **bounded repetition** (not in `RevLang`!) | `rev_iter` |

The inverse of a combinator is the same combinator on the converses, with
assertions swapped (`conv_comp`, `conv_if`, `conv_loop`). The class is **open**:
`iterR` is a combinator *absent from `RevLang`'s syntax*, shown reversible in
three lines from `rev_id`/`rev_comp` — a new combinator needs only its own
closure lemma, no fixed syntax to edit. Finally `Connect` exhibits the `RevLang`
constructors as exactly these combinators (`exec_Seq` = `compR`, `exec_If` =
`ifR`, `exec_Loop` = `loopR`, `reversible_prim`), so the fixed syntax is just one
selection from the open class.

### The laws are tight (`RevNecessity.v`)

The three `REV_PRIM` laws are not just *sufficient* but *necessary*:

- `prim_injective` — the laws **force** every primitive to be injective
  (`pstep p a b → pstep p a' b → a = a'`).
- `reset_inadmissible` — a "reset to 0" atom is forward-*deterministic* yet
  non-injective, and provably has **no** deterministic reversing completion, so
  it can satisfy neither `pstep_rev`/`pstep_det` nor host any `REV_PRIM`.

Sufficiency (`RevCore`) + necessity (`RevNecessity`) together: **a primitive is
admissible to the framework iff it is injective** — forward determinism alone is
not enough.

### Instances

| File | State | Primitives | Reversibility |
|---|---|---|---|
| `RevJanus.v` | `store = var → Z` | `x op= e` (with `¬ occurs x e`), `x <=> y` | `janus_reversible` |
| `RevToy.v` | `Z` (a counter) | `Inc`, `Dec` | `toy_reversible` |
| `RevExt.v` | `loc → Z` (scalars + array cells + local cells) | array/scalar `l op= e`, `l1 <=> l2`, `local`/`delocal` enter/exit | `ext_reversible` |
| `RevIO.v` | `(nat → Z) × list Z × list Z` (store + input + output streams) | `read`/`write` and their stream duals `unread`/`unwrite` | `io_reversible` |
| `RevMul.v` | `Z` (a register) | `x *= k`, `x /= k` (relational; nonzero-factor guard, `/=` partial) | `mul_reversible` |
| `RevMod.v` | `Z` held canonical in `[0, M)` | modular `x += k`, `x -= k` (wrapping, `mod M`) | `mod_reversible` |
| `RevExtMod.v` | modular store `loc → Z` (scalars + array cells + local cells, each canonical in `[0, M)`) | modular `l op= e`, `l1 <=> l2`, `local`/`delocal` (values wrap `mod M`); expressions unbounded | `extmod_reversible` |
| `RevSMod.v` | `Z` held canonical in the signed window `[-2^(b-1), 2^(b-1))` | signed-modular `x += k`, `x -= k` (the `-m bits` register) | `smod_reversible` |
| `RevExtSMod.v` | signed-modular store `loc → Z` (scalars + array cells + local cells, each canonical in the signed window) | signed-modular `l op= e`, `l1 <=> l2`, `local`/`delocal`; **every expression result wraps too** (the `-m bits` mode) | `extsmod_reversible` |

`RevIO.v` gives the `jana2014_in_out` I/O dialect a *verified* reversible
semantics (read consumes the input, its inverse pushes it back; write emits to
output, its inverse pops it) — the reversibility that `vjanus` can otherwise only
refuse.  `RevMul.v` accounts for Janus's multiplicative updates `*=` / `/=`,
which the *total* frame-core `aop` (`OAdd/OSub/OXor`) cannot host: as a
`REV_PRIM` **relation** they fit exactly — `*=` is injective iff the factor is
nonzero, and `/=` is the corresponding *partial* inverse (it relates a value to
another only when the factor divides it).

`RevMod.v` is the basis for Janus's **sized integer types** (`i8`/`i16`/`i32`/…,
and the global `-m bits` mode): each register has a modulus `M = 2^bits`, so every
update wraps.  Wrapping a plain `Z` cell is not reversible (it is injective only
*within* one residue window), so — with the register held canonical in `[0, M)` —
the modular updates `x += k` / `x -= k` are proved mutually inverse bijections.
This is why `vjanus` (a pure `Z` machine) declines sized-int programs (exit 3):
running them faithfully needs a modular core, and `RevMod.v` is its verified
target.

`RevExtMod.v` is that **modular core**, built the same way as `RevExt.v` (a
`RevCore` instance with a store over scalars, array cells and local cells) but
with every register held canonical in `[0, M)` and every assignment wrapping
`mod M` — while expression intermediates stay unbounded, exactly matching
PyJanus (a binary-op result is `UNBOUND`; only a store wraps).  The canonical
guard `0 <= a l < M` baked into an update's `pstep` is what a `Z/M` cell type
would enforce structurally; each update yields `_ mod M`, so it is preserved.
`extmod_reversible` / `extmod_iff` come for free from the functor, giving
reversibility of bounded-int array/local programs (the `i8` example wraps
`250 += 10` to `4`, reversibly, in an array cell).

`RevExtractMod.v` makes that core **runnable**: a fuel-bounded interpreter [run]
for the modular language, proved sound (`run_sound : run fuel Γ s a = Some b →
exec Γ s a b`, hence `run_injective`) and extracted to OCaml (`janus_modular.ml`,
at `M = 256`).  The `Prim` step goes through a functional `pstep_fn` that refines
the relation `pstep` — the modular update's canonicity guard `0 ≤ a l < M` becomes
a runtime test.

Janus's **global** `-m bits` mode is semantically distinct from the per-variable
sized types above: it wraps *every* value — expression intermediates included —
into the **signed** window `[-2^(b-1), 2^(b-1))` (PyJanus's `_normalize_int`
falls through to the `mod_bits` branch on every binary-operator result, not just
at assignment).  `RevSMod.v` verifies the signed wrap `norm` itself (lands in the
window, is a ring map onto it, and its wrapping updates are mutually inverse
bijections — checked against PyJanus's `-m 8` output directly: `100 += 50`
wraps to `-106` in both).  `RevExtSMod.v` threads that wrap through `eval`
itself (so `(100 + 50) - 90` wraps mid-computation to `60`, again checked against
`-m 8`), giving `extsmod_reversible` for a genuinely `-m`-faithful store core.
`RevExtractSMod.v` extracts its runnable, sound interpreter to OCaml
(`janus_smod.ml`, at `bits = 8`) the same way as `RevExtractMod.v`.

What remains to make `vjanus` *run* sized ints or `-m` is now only the glue:
lowering jana2014 to the relevant core's `stmt`/`expr` and threading the modulus
(per-variable for `i8`/…, or global for `-m bits`) — as `vjanus`'s `lower.ml` +
`glue.ml` already do for the unbounded `RevFrame` core.

`RevLowering.v` verifies the `vjanus` translation rules that do **not** map a
source construct to a single core primitive (and so carry real proof
obligations): the swap `x <=> y`, lowered to the XOR triple
`x ^= y; y ^= x; x ^= y` — proved to compute the swap and to be its own inverse
(and to collapse an *aliased* `a[i] <=> a[i]` to 0, which is why it is rejected);
the stack `push`/`pop`, lowered to an XOR-swap of the top cell plus a counter
bump — proved that `pop` undoes `push`; the clean local-array bracket
`a[c] += 0 … a[c] -= 0`, proved to be the identity on the store; and injectivity
of both struct-array cell addressing (`elem*n + off`) and the Cantor fold of
multi-dimensional indices — no two distinct indices alias.  Whole-translator
soundness (a Coq model of all of `lower.ml` proved to commute with the source
semantics) remains future work — see `docs/vjanus-lowering-soundness.md`.

All reversibility theorems are obtained purely as instances of the generic
`exec_injective` — no per-language reversibility proof is repeated. The Janus
instance reuses the algebraic lemmas in `Janus.v` to discharge its three laws.

### Withstanding extension: arrays and `local`/`delocal` (`RevExt.v`)

`RevExt.v` demonstrates that features usually thought of as *language
extensions* are absorbed by the framework **without touching `RevCore.v`**:

- **Arrays are just more locations.** The store is indexed by a location type
  `loc` covering scalars, array cells `Cell a i`, and local cells. Array-cell
  update/swap are *literally the same atoms* as scalar update/swap.
- **`local`/`delocal` needs no new combinator.** It is two reversible atoms —
  `PEnter` (initialize a dead cell) and `PExit` (assert-and-clear it) — wrapped
  around the body with `Seq`. Because they are genuine inverses, the generic
  `invert` automatically rewrites `local x=e; S; delocal x=e'` to
  `local x=e'; invert S; delocal x=e` (`invert_LocalBlock`, by computation),
  and `exec_injective` gives reversibility of array/local programs for free.

## Verified clean-reversible construction (contribution ⑤)

A separate layer turns the framework into a **constructive methodology**:

> given a non-reversible spec `f` *proven injective* (a left inverse `g` with
> `g ∘ f = id`), build a **clean (garbage-free) reversible Janus program** that
> is *proven correct on the formal semantics* — and get its reversibility **for
> free** from `exec_iff`.

The pattern (each coder is `spec + injectivity proof ⟹ Janus program +
`exec`-correctness, reversibility free):

| file | coder | reversibility shape |
|---|---|---|
| `RevPipeline.v` | 2-var delta / Fibonacci-step / XOR | in-place affine & self-inverse atoms |
| `RevPipelineArr.v` | multi-cell delta (Seq **and** a Janus `Loop`, n=3) | array l-values + a real loop |
| `RevGolomb.v` | Golomb/Rice `n ↦ (n/d, n mod d)` | **divmod consume** (uses `ODiv`/`OMod`) |
| `RevVarint.v` | LEB128/varint (iterated divmod, fixed 3 digits) | two divmod-consume stages |
| `RevZigzag.v` | ZigZag `ℤ ↔ ℕ` | a reversible **`If`** (parity exit predicate) |
| `RevDeltaN.v` | **general length `N`** backward delta | a Janus `Loop` proved by **loop-invariant induction** (`opn`) |

The injectivity proof is reused verbatim as the cleanliness/reversibility
certificate; `denote`'s `ODiv`/`OMod` are read-only (never inverted), so adding
them keeps `exec_iff` intact. Every theorem here is axiom-audited (`audit.sh`).

## Files

- `Janus.v` — standalone, self-contained core-Janus development (concrete
  stores/expressions; the original reference proof). `binop` includes read-only
  `ODiv`/`OMod` (total; used by the construction-pipeline coders).
- `RevCore.v` — the generic `REV_PRIM` / `RevLang` framework.
- `RevJanus.v` — Janus as an instance of `RevLang`.
- `RevToy.v` — a reversible counter over `Z`, a second unrelated instance.
- `RevExt.v` — Janus extended with arrays and `local`/`delocal`, showing the
  framework withstands extension along the atom/state layer (core unchanged).
- `RevProc.v` — Janus with **parameterized (reference) procedures**: a call
  binds formals→actuals as a variable renaming of the body. Reversibility holds
  via `rename_invert` (renaming commutes with `invert`); aliasing is captured by
  the `occurs` side condition (`alias_blocks`), not an extra hypothesis.
- `RevCoreP.v` — the **generic framework with parameterized procedures**:
  `REV_PRIM_P` adds an abstract renaming (`ren`/`rprim`/`rguard`) with the single
  law `pinv (rprim r p) = rprim r (pinv p)`; the `RevLangP` functor proves
  reversibility for `Call p r` generically. Instantiated (`JanusP`) to recover
  reference procedures from the functor.
- `RevExtract.v` — a **verified executable interpreter**: a fuel-bounded
  computable `run` proved sound vs. `exec` (`run_sound`), extracted to OCaml
  (`janus_verified.ml`) as a reference interpreter for differential testing
  against PyJanus. `run_reversible` ties a real run to `exec_injective`.
- `RevExtractP.v` — the same, for `RevProc`'s language **with parameterized
  reference procedures** (`run_sound` vs. `RevProc.exec`), extracted to
  `janus_param.ml`.
- `RevArr.v` — Janus with **arrays** (dynamic-index reads `A[e]`, cell
  assignments `A[e] op= …`, and l-value **swap** `A[i] <=> B[j]`),
  **`local`/`delocal`** blocks (`Enter`/`Exit`, dead-cell model), and `/`,`%`
  operators, on top of reference procedures; reversibility (`exec_injective`).
  The array-assignment side condition `wf_assign` is the **runtime** aliasing
  test (the written *cell* is not read by the rhs — `reads_cell`), faithful to
  Janus and admitting `A[j][i] += … A[j][k]` (`i≠k`) which a static name-based
  check would reject.
- `RevExtractAr.v` — the verified computable interpreter for `RevArr`
  (`run_sound` vs. `RevArr.exec`), extracted to `janus_arr.ml`.
- `RevFrame.v` — Janus with **frame-stacked locals**: locals live in
  depth-indexed frames (`L d x`), so a procedure that **recurses while
  declaring a `local`** gets fresh storage per activation (the flat `RevArr`
  model aliases them). By-reference calls resolve each actual to an absolute
  name at the caller's depth and run the body one frame deeper; formals are
  positional (`RF i`). Same headline results as the rest
  (`exec_rev`/`exec_iff`/`exec_det`/`exec_injective`, `run_sound`), and the same
  index-precise `reads_cell` array discipline as `RevArr`.
- `RevExtractFrame.v` — the verified computable interpreter for `RevFrame`,
  extracts both `run` and `invert` to `janus_frame.ml`; it backs the standalone
  **`vjanus`** interpreter (`coq/vjanus/`, own jana2014 lexer/parser +
  frame-aware lowering), which matches PyJanus on the whole corpus (48 pass /
  0 skip — the self-referential `delocal` counter idiom is handled by a
  loop-aware lowering) with no Python at runtime,
  including arrays, stacks and structs (all lowered to frame slots). `vjanus
  -inverse` additionally runs the verified `invert` (final store → initial
  store), output-compatible with PyJanus `--inverse` and differentially tested
  against it (`tests/jana2014/test_vjanus_inverse.py`). See `coq/vjanus/README.md`.
- `harness/` — a **differential-testing driver**: runs the extracted verified
  interpreters on `.ja` programs and diffs the final store against PyJanus
  (`./harness/run.sh`). The array+procedure interpreter agrees with PyJanus on
  the real fixtures it covers — recursive reference procedures (`fib.ja`),
  arrays, and arrays passed by reference; `local`/`delocal`, `for`-loops, value
  arguments, stacks, `/` and `>=` are skipped.
- `RevAlgebra.v` — reversibility as an open algebra of relational combinators
  (Seq/If/Loop become closure theorems); the syntax is one instance.
- `RevNecessity.v` — the three `REV_PRIM` laws are necessary (tight): they force
  primitive injectivity, and a non-injective atom is inadmissible.
- `RevSmallStep.v` — a small-step (structural operational) semantics for the
  framework, **proved equivalent** to the big-step `exec`
  (`exec Γ s a b ↔ multistep Γ (embed s) a RSkip b`).
- `RevPipeline.v`, `RevPipelineArr.v`, `RevGolomb.v`, `RevVarint.v`,
  `RevZigzag.v`, `RevDeltaN.v` — the **verified clean-reversible construction
  pipeline** (see the section above): proven-injective specs compiled to
  clean-reversible Janus programs proved correct on `exec`, with reversibility
  free from `exec_iff`. Covers in-place affine/XOR atoms, array l-values, divmod
  consume (`ODiv`/`OMod`), a reversible `If`, and a general-`N` `Loop` proved by
  loop-invariant induction.

## Building

```bash
# whole development
rocq makefile -f _CoqProject -o Makefile && make

# or a single file
rocq compile RevCore.v

# build + assert every headline theorem is axiom-clean (this is what CI runs)
./audit.sh
```

The build is light (whole development ≈ 3 s, < 0.5 GB RAM). `audit.sh` builds the
development and runs `Print Assumptions` on every headline theorem, failing on any
axiom beyond `functional_extensionality` or any `Admitted`; it is wired into CI
(`.github/workflows/coq.yml`), alongside the Python test workflow.

## Trust / axioms

```coq
Require Import RevJanus RevToy.
Print Assumptions janus_reversible.   (* functional_extensionality only *)
Print Assumptions toy_reversible.     (* closed under the global context — no axioms *)
```

`janus_reversible` uses only `functional_extensionality` (unavoidable because
stores are functions `var → Z`); `toy_reversible` uses no axioms at all. No
`Admitted`, no extra axioms — the results are fully machine-checked.

## Small-step semantics (`RevSmallStep.v`)

Mechanizing the heart of *"A Small-Step Semantics for Janus"* (hal-04610285) for
the framework. Runtime configurations `(rs, state)` extend source statements with
markers that make control flow single-step: `RAssert g v` realizes the exit
assertions of `if`; `RLoopE`/`RTest`/`RCont` are the three phases of one loop
turn (run `s1`; test `g2`: exit / run `s2`; assert `¬g1`; repeat). The relation
`step` and its closure `multistep` are defined, and proved **equivalent** to the
big-step semantics:

- `complete : exec Γ s a b → multistep Γ (embed s) a RSkip b` — every big-step
  run is realized step-by-step.
- `sound : multistep Γ (embed s) a RSkip b → exec Γ s a b` — via a
  big-step-on-runtime relation `bexec`, a reverse simulation (`sim`: each `step`
  preserves `bexec` backward), and a decoding of `bexec (embed s)` to `exec`
  (the loop phases `RLoopE`/`RTest`/`RCont` decode to `lp`).
- `equiv : exec Γ s a b ↔ multistep Γ (embed s) a RSkip b` — **done, axiom-free**.

Combined with `exec_rev`/`exec_injective` (RevCore), reversibility transfers to
the small-step semantics for free.

## Further results (claims-to-theorem map)

Built on top of the framework; `audit.sh` checks every one of these (with the
core results) on each build.

| Result | Rocq name | File | Axioms |
|---|---|---|---|
| Stack-machine instance (state = `list Z`) | `stack_reversible` | `RevStack.v` | none |
| 2nd-order cellular-automaton instance | `ca_reversible` | `RevCA.v` | funext |
| Executable invert correctness (extracted `run`) | `run_invert_iff` | `RevInvert.v` | funext |
| Denotational adequacy (`denote = exec`) | `adequacy` | `RevDenote.v` | none |
| Full abstraction | `full_abstraction` | `RevDenote.v` | none |
| Inverter = relational converse, denotationally | `denote_invert` | `RevDenote.v` | none |
| Inverse-monoid / dagger structure | `inv_law1` | `RevInverse.v` | none |
| Multi-object dagger restriction category (PInj) | `pinj_inverse_law` | `RevCat.v` | none |
| Bennett reversibilization (compute–copy–uncompute) | `bennett_correct` | `RevBennett.v` | none |

The stack machine and the cellular automaton share **no state space and no
primitives** with Janus, yet inherit reversibility verbatim from the functor.

## Scope and next steps

This covers **core Janus** (integer variables, reversible updates
`+= / -= / ^=`, swap, `if/fi`, `from/loop/until`, `call`/`uncall`, sequencing,
`skip`) plus **arrays and `local`/`delocal`** (`RevExt.v`) and **parameterized
reference procedures** — both as a concrete instance (`RevProc.v`) and in the
**generic framework** (`RevCoreP.v`). A **verified interpreter** is extracted to
OCaml (`RevExtract*.v`) and **differentially tested against PyJanus** end-to-end
(`harness/`, wired into the Python test suite as
`tests/jana2014/test_verified_corpus.py`): the two agree on every in-subset
program of the example corpus. The development also includes a denotational
semantics with full abstraction, the inverse-category (dagger) structure, and a
machine-checked Bennett reversibilization (see *Further results* above).
