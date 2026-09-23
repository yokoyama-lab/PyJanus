# Output / garbage annotations for the 101-program fixture corpus

`out_annotations.json` is a **hand-written** sidecar that says, for every
program in the four fixture corpora, which main-level variables are the
program's intended outputs, which are inputs, and which are garbage.  Janus
itself has no such notion (the whole final store is "the output"), so the
RC-03 headline "65% of written arrays are never cleared" mixes legitimate
results with garbage.  These annotations let `../recount.py` split that
figure.  Design and classification algorithm: `docs/output-annotation.md`;
loader and classifier: `jana_py/outannot.py`.

Corpus covered (101 programs):

| directory | programs |
|---|---|
| `tests/jana2014/fixtures/examples/` | 85 |
| `tests/jana2014_in_out/fixtures/examples/` | 10 |
| `tests/janus2026/fixtures/examples/` | 4 |
| `tests/jana2014basic/fixtures/examples/` | 2 |

## Fields

Top level: `_schema`, `roles` (the role vocabulary, for humans) and
`programs`, a list with one entry per fixture:

| field | meaning |
|---|---|
| `file` | repository-relative path of the fixture (the join key) |
| `std` | dialect directory (`jana2014`, `jana2014_in_out`, `janus2026`, `jana2014basic`) |
| `arrays` | `{name: role}` for **every** array declared in `main`; role is `output` / `input` / `garbage` / `scratch` |
| `scalars_out` | scalars (and whole structs) that are intended outputs; all other scalars are inputs or garbage |
| `stacks` | `{name: role}` for every stack declared in `main`; role is `garbage`, `garbage (reversibility log)`, `output` or `scratch` (the loader keeps only the first word) |
| `rationale` | one line, quoting the fixture's header comment where it states the forward mapping |
| `confidence` | `high` / `medium` / `low` |

Roles:

- `output` -- intended result; expected non-zero at termination.  Arrays
  transformed **in place** (`gray_code` `bits`, `heap_sort` `a`, the CA
  state slots) are `output`, not `input`.
- `input` -- input data; expected unchanged from its value after main's
  initialisation (read-only, or modified and restored by an `uncall`).
- `garbage` -- not an intended result but left non-zero: branch/overwrite
  logs, retained DP intermediates (`lis` `L`, `kmp` `f`), all-1 `visited`
  flags, AVL node arrays of a *sort*.
- `scratch` -- intended to end all-zero / empty: uncomputed ancillas
  (`injective_bwt_inverse`), consumed inputs (`run-length-enc` `text`), or
  declared-but-never-written arrays (`heap_sort` `ord`, `selection_sort` `p`).

Struct-typed variables: a struct *array* (`Pair v[3]`, `node pool[5]`) is
listed under `arrays` by its own name; an array **field** of a scalar struct
is listed with a dotted name (`a.v`, `a.grid`, `d.entries`).  If the profiler
names these differently the recount reports them as unmatched rather than
guessing.

Conventions applied when the header was silent or ambiguous:

- A stack that only holds the branch history (`gb`, `log`, `blog`, `dlog`,
  ...) is `garbage (reversibility log)` unless the header calls it an
  output (`convex_hull` `hseq` "doubles as the hull sequence").
- A whole DP table whose single cell is the answer (`knapsack` `K`,
  `lcs` `L`, `edit_distance` `D`, `matrix_apsp` `m_arr`) is `output` with
  `confidence: medium` ("table-as-output" caveat: cell-level classification
  is future work).
- `visited`/`intree` arrays that are all 1 at termination are `garbage`
  even where the header lists them among the outputs (`dijkstra`,
  `topological_sort`, `kosaraju_scc`, `prim_mst`), confidence `medium`.

## Counts (101 programs)

- arrays: 175 = output 72, input 56, garbage 27, scratch 20
- stacks: 42 = garbage 31, output 6, scratch 5
- scalars_out: 74
- confidence: high 75, medium 22, low 4

Low-confidence entries (4) -- feature tests with no algorithmic contract:

- `tests/jana2014/fixtures/examples/test2.ja`
- `tests/jana2014_in_out/fixtures/examples/test2.ja`
- `tests/jana2014basic/fixtures/examples/test2.ja`
- `tests/janus2026/fixtures/examples/build-dict.ja`

Medium-confidence entries (22): `dijkstra`, `edit_distance`, `fall`,
`fib_variants`, `injective_bits`, `injective_partition`,
`injective_sort_network`, `kmp`, `knapsack`, `kosaraju_scc`, `lcs`, `lis`,
`matrix_apsp`, `matrixmult` (x2), `matrixmult_v1.0` (x2), `prim_mst`,
`sqrt` (x2), `topological_sort`, `tree_sort`.

## Regenerating / checking

The file was produced from a hand table and cross-checked so that every
array and stack declared in each fixture's `main` has exactly one role and
no annotated name is undeclared.  `tests/jana2014/test_outannot.py`
re-checks the invariants (101 entries, unique files, valid roles, every
file exists).
