# Reference implementations for the example corpus

One Python module per program in `tests/jana2014/fixtures/examples/`, named after
it (`gcd_g.ja` → `gcd_g.py`). Each defines

```python
def expected() -> dict[str, object]:
    ...
```

returning the values the Janus program's final store must hold, keyed by
variable name, and

```python
GARBAGE = ["log", "blog"]
```

naming the variables that are history rather than answer.
`tests/jana2014/test_reference_impls.py` runs the program, parses its store, and

1. compares every key `expected()` names,
2. checks that nothing non-trivial survives that is in *neither* list -- a value
   nobody claims is a question, not a detail,
3. requires the filename to end in `_g` when some declared garbage actually
   survives the run, and `_c` when none does.

(3) is why the split matters: **32 of the 97 leave garbage (`_g`), 65 are clean
(`_c`)**. Whether a variable is garbage is decided from the algorithm; whether
any of it survives is decided by running the program. Naming *every* file one
way or the other, rather than marking only the dirty ones, means a file nobody
has classified cannot pass as clean.

## Why these exist

Everything else that checks this corpus runs *the same Janus source* a second
way — backwards, through the C++ back-end, through an extracted Coq
interpreter. Those catch a back-end that disagrees; none of them can catch a
program that computes the wrong thing, because there is nothing to disagree
with. These modules are the missing second opinion.

## Rules

1. **Implement the algorithm, do not transliterate the Janus.** A line-by-line
   port shares the original's bugs and proves nothing. Write what the algorithm
   *is* — `math.gcd`, `sorted`, a two-line recurrence — and let the shapes
   differ.
2. **Do not import `jana_py`, and do not read the `.ja` file.** The only thing
   copied across is the input, which the Janus `main` hardcodes; put it in a
   module-level constant so the transcription is visible in one place.
3. **Assert only what the algorithm determines.** Garbage (a decision log, a
   quotient stack, an ancilla flag array) is an artefact of *this* reversible
   encoding, not of the function being computed, so leave it out — `@keep` in
   the program's own header is the list that belongs here. Partial is fine: a
   module that pins one array is worth more than none.
4. Store values arrive as plain Python — `int`, `list` (arrays of any rank, and
   stacks top-first), `dict` (structs).

## Coverage

All 97 examples have one, and all 97 agree.

Five predict less than the whole answer and declare a `PARTIAL` string saying
what they leave out; `test_the_partial_references_are_the_declared_ones` pins
that list so it cannot grow quietly.

| module | not predicted |
|---|---|
| `adaptive_huffman` | the emitted bits — which losing symbol gets `10` is the encoder's convention |
| `ppm_lite` | the emitted bits, for the same reason |
| `matrixmult` | the product in `A` — how `multLD` and `multU` split the factorisation |
| `matrixmult_v1` | the product in `B`, for the same reason |
| `binary_heap` | the final array layout, which follows this encoding's sift order |

Leaving *garbage* unasserted is not a gap and is not listed: a quotient stack or
a decision log is an artefact of the reversible encoding, not of the function.

## Adding one

```bash
python3 tools/check_corpus_meta.py store tests/jana2014/fixtures/examples/X.ja
$EDITOR tests/jana2014/reference/X.py
python3 -m pytest tests/jana2014/test_reference_impls.py -q -k X
```

A mismatch is not automatically your bug. It means the reference and the Janus
program disagree about the answer, and which one is wrong is the question worth
asking — that is what this directory is for.
