# Clean reversible search examples

These `jana2014` samples separate the *answer* from temporary information needed
for reversibility. All preserve the input array, key and logical length. They
are educational implementations with executable tests, not a claim of new
asymptotic search bounds or an end-to-end mechanized verification of PyJanus.

## Run and test

```bash
python3 -m jana_py.cli --std jana2014 -s tests/jana2014/fixtures/examples/linear_search_c.ja
python3 -m jana_py.cli --std jana2014 -s tests/jana2014/fixtures/examples/sorted_linear_search_c.ja
python3 -m jana_py.cli --std jana2014 -s tests/jana2014/fixtures/examples/sentinel_search_c.ja
python3 -m jana_py.cli --std jana2014 -s tests/jana2014/fixtures/examples/binary_lifting_search_c.ja
python3 -m pytest tests/jana2014/test_clean_search_examples.py -q
```

The last command checks every array of lengths 0 through 4 over `{-1,0,1}`
(sorted arrays for sorted procedures), each key in `{-2,-1,0,1,2}`, and both
zero and nonzero accumulator seeds. Sentinel-save variants also use old sentinel
values `-3`, `0`, and `11`. Binary tests include lengths just below, at and just
above powers of two through 64. The oracles are independently expressed with
Python membership, `list.count`, first-match enumeration and `bisect_left`.
Every case checks the result, full input preservation, removal of local scratch,
and exact restoration by `uncall`. The usual corpus tests additionally check
the executable sample mains, metadata, independent reference modules,
forward/inverse execution, formatting and C++ code generation where supported.

These finite tests do not prove correctness for all arrays. The preconditions
below are part of each procedure's contract, not automatically checked guards.
Invalid inputs, aliasing or insufficient capacity are outside the contract.

## Shared contracts

- `n >= 0` is the logical prefix length, not necessarily physical capacity.
- Arguments are nonaliasing: scalar outputs do not alias the array, `key`, `n`,
  each other or any other input. The array and inputs stay unchanged on return.
- Non-sentinel procedures need capacity at least `max(1,n)`. An empty logical
  prefix uses one unused backing cell because PyJanus arrays have positive size.
- Sentinel procedures need **at least `n+1` physical cells**. Cell `a[n]` is
  outside the searched prefix. Save/restore wrappers may modify it temporarily.
- Sorted procedures require only the real prefix `a[0:n]` to be nondecreasing.
  Duplicates, negative values, empty input and keys outside the range are allowed.
- Position/lower-bound outputs must begin at zero. They are partial reversible
  interfaces: do not interpret them as arbitrary-seed XOR oracles.
- Flag and `*_first_clean` wrappers use XOR accumulation. With output seed `s`,
  they return `s XOR membership` or `s XOR first_match_or_n`. Seed zero returns
  the ordinary answer. `count_matches` adds the number of matches to its seed.
- Run with ordinary mathematical integers. No fixed-width overflow guarantee,
  physical-bit memory bound, bit-complexity bound or energy claim is made.

## General linear search

`linear_search_c.ja` contains:

- `first_position`: the least matching index, or `n` if absent.
- `flag_clean`: a membership XOR oracle that uncomputes its temporary position.
- `flag_keep_position`: returns both membership and position. If the requested
  answer is *only* a flag, that retained position is garbage; if position is also
  an intended output, it is not garbage.
- `count_matches`: an additive count, a different problem from Boolean search.
- `flag_count_clean`: a duplicate-safe full-scan membership baseline, using
  compute/copy/uncompute of a count.

The loop tests its exit condition before incrementing. Thus a head hit and an
empty prefix need zero increments; `p = n || a[p] = key` depends on short-circuit
Boolean evaluation to avoid reading outside the logical prefix. First-match
position is a useful answer, so retaining it does not itself violate cleanliness.
The clean membership wrapper scans back to erase it.

## Sorted linear search

`sorted_linear_search_c.ja` returns the lower bound (insertion position) with
`sorted_lower_bound`. A lower bound is not necessarily a hit. The membership
wrappers therefore also test equality. `sorted_first_position_clean` returns
first-match-or-`n` by XOR accumulation and uncomputes the insertion position.
The retained-bound variant exposes that position as an additional result.

## Sentinels

`sentinel_search_c.ja` offers three explicit contracts:

- `*_ready`: the caller supplies the sentinel. The equality kernel needs
  `a[n] == key`, not merely `a[n] >= key`. The sorted threshold kernel needs
  `a[n] >= key`; the augmented array need not itself be sorted.
- `*_zero`: `a[n]` initially equals zero. XOR writes the sentinel and restores
  the slot afterward. There is no hidden discarded original slot value.
- `*_saved`: an arbitrary original `a[n]` is swapped into a local scalar,
  restored afterward, and that scalar is deallocated at zero.

The flag wrappers uncompute the position while the sentinel is still present,
then restore the slot. The extra sentinel cell and save scalar are real storage
costs even though no scratch survives. A sentinel removes the per-probe bounds
check; it does not change the linear worst-case search bound.

## Binary lifting and prior art

`binary_lifting_search_c.ja` adapts the output-bit branch-recovery idea from
Masuda and Yokoyama, **Analyzing Trade-offs in Reversible Linear and Binary
Search Algorithms** (2019), [section 2.2 and Figure 6](https://arxiv.org/abs/1910.10406).
That paper already gives logarithmic-time reversible binary search with constant
extra words and no garbage. This example's contribution is the explicit
lower-bound/duplicates/empty-prefix interface and reproducible tests, **not**
a new asymptotic result.

`binary_lifting_bound` chooses a power of two greater than `n`, then halves the
stride and conditionally adds it to `p`. Before a probe, `p` is a multiple of
`2*stride`; afterwards `p % (2*stride) == stride` recovers whether the update
was taken. Consequently no separate per-probe history bit is required.
`p + stride <= n && a[p + stride - 1] < key` safely handles partial final blocks
and returns `n` for a key above every element. For `n=0`, both loops exit
without indexing the array.

- `binary_lifting_bound`: lower bound, zero-initialized position output.
- `binary_lifting_flag_clean`: arbitrary-seed membership XOR oracle.
- `binary_lifting_first_clean`: arbitrary-seed first-match-or-`n` XOR oracle.
- `binary_lifting_first_selective`: zero-initialized position output; preserve a
  successful bound directly, or uncompute a miss and return `n`. Its output
  contract differs from the XOR wrapper even when both start at zero.

In a unit-cost word model, the lifting family uses `O(log(n+1))` search work and
a constant number of auxiliary scalar words, with no final scratch. Wrapper
uncomputation changes constants, not these asymptotics. The position/stride
words themselves require enough bits to represent the index and the power of
two strictly greater than `n`. Bounds on Python interpreter allocations,
expression-evaluation time or hardware energy do not follow from the number
of Janus scalar variables.

## Verification scope

The checked-in `.ja` sources, independent Python references and regression tests
are the reproducible software deliverable. Separate research models of linear
search and binary branch recovery do not establish a semantic refinement from
these files through the PyJanus parser/runtime. No such end-to-end theorem is
claimed here. Existing Coq-extracted-interpreter corpus tests may support only a
language fragment or may be skipped when their toolchain is unavailable; report
those skips separately rather than treating them as successful proofs.
