# RC-03 array figure, recomputed with output/garbage annotations

- arrays CSV: `tests/resource_atlas/data/corpus_arrays.csv`
- annotations: `tests/resource_atlas/annotations/out_annotations.json`
- programs in CSV: 71; arrays: 168; written arrays: 146
- programs in the sidecar: 101; sidecar programs without a CSV row: 30 (no arrays declared, or only struct-field arrays -- see 'Annotated arrays absent from the CSV')

## Headline (written arrays)

RC-03 (unannotated): "of the written arrays, N never take a cell back to 0, M end empty".

| quantity | count | % of written | % of never-take |
|---|---:|---:|---:|
| written arrays | 146 | 100% | - |
| never take (takes = 0) | 95 | 65.1% | 100% |
| ... of which **output** | 39 | 26.7% | 41.1% |
| ... of which **input-preserved** | 34 | 23.3% | 35.8% |
| ... of which **garbage** | 22 | 15.1% | 23.2% |
| ... of which clean (never take yet all-zero: never written non-zero) | 0 | 0.0% | 0.0% |
| end empty / clean (ends_empty) | 17 | 11.6% | - |

Reading: the RC-03 "never cleared" share is the *never take* row; the three rows
below it split it into legitimate outputs, untouched inputs, and garbage proper.
Garbage among never-take arrays as a share of never-take: 23.2%; as a share of written arrays: 15.1%.

## Per class (written arrays)

| class | count | % of written |
|---|---:|---:|
| output | 62 | 42.5% |
| input-preserved | 40 | 27.4% |
| garbage | 27 | 18.5% |
| clean | 17 | 11.6% |

Unannotated written arrays (counted as garbage): 0

Annotation / measurement mismatches (classification unchanged; listed for review):
- `tests/jana2014/fixtures/examples/gray_code_roundtrip.ja`: `bits`: input array had takes (modified and restored?)
- `tests/jana2014/fixtures/examples/injective_arith_coding.ja`: `m`: input array had takes (modified and restored?)
- `tests/jana2014/fixtures/examples/injective_ca_rule90.ja`: `b`: input array had takes (modified and restored?)
- `tests/jana2014/fixtures/examples/injective_lehmer.ja`: `perm`: input array had takes (modified and restored?)
- `tests/jana2014/fixtures/examples/permutation_rank.ja`: `b`: input array had takes (modified and restored?)
- `tests/janus2026/fixtures/examples/caesar.ja`: `msg`: input array had takes (modified and restored?)

## Annotated arrays absent from the CSV

7 annotated arrays in 6 programs have no CSV row, so they are neither in the RC-03 count nor in the split above:

| program | array | annotated role; reason |
|---|---|---|
| `tests/jana2014/fixtures/examples/structs_array_field.ja` | `a.v` | output; struct field: profiler does not report array fields of structs |
| `tests/jana2014/fixtures/examples/structs_array_field.ja` | `a.grid` | output; struct field: profiler does not report array fields of structs |
| `tests/jana2014/fixtures/examples/structs_flat_param.ja` | `a.v` | input; struct field: profiler does not report array fields of structs |
| `tests/jana2014/fixtures/examples/structs_flat_repass.ja` | `a.v` | input; struct field: profiler does not report array fields of structs |
| `tests/jana2014/fixtures/examples/structs_local_arr.ja` | `a.v` | input; struct field: profiler does not report array fields of structs |
| `tests/jana2014/fixtures/examples/structs_local_arr2d.ja` | `a.grid` | input; struct field: profiler does not report array fields of structs |
| `tests/janus2026/fixtures/examples/build-dict.ja` | `d.entries` | output; struct field: profiler does not report array fields of structs |

Programs with annotated arrays but no CSV row at all: `tests/jana2014/fixtures/examples/structs_array_field.ja`, `tests/jana2014/fixtures/examples/structs_flat_param.ja`, `tests/jana2014/fixtures/examples/structs_flat_repass.ja`, `tests/jana2014/fixtures/examples/structs_local_arr.ja`, `tests/jana2014/fixtures/examples/structs_local_arr2d.ja`

## Stacks

The arrays CSV has **no stack rows** (the profiler reports stacks only as the aggregate `stack_peak` in `corpus_atlas.csv`), so a measured output / input / garbage split for stacks is not possible.  Annotation-side counts from the sidecar (roles of the stacks declared in `main`):

| stack role | count | % of stacks |
|---|---:|---:|
| stacks annotated | 42 | 100% |
| output | 6 | 14.3% |
| garbage | 31 | 73.8% |
| scratch | 5 | 11.9% |

Garbage stacks per program (reversibility logs): `avl_delete.ja`: alog, hlog, rlog, dlog; `avl_insert.ja`: alog, hlog, rlog; `bellman_ford.ja`: dlog, plog, rlog; `bfs.ja`: blog; `depth_first_search.ja`: blog; `dijkstra.ja`: dlog, blog; `dynamic_array.ja`: dbit; `ext_gcd.ja`: qlog; `floyd_warshall.ja`: dlog, blog; `gcd.ja`: log; `heap_sort.ja`: gb; `kmp.ja`: gq, gb; `kosaraju_scc.ja`: blog; `modexp.ja`: g; `next_permutation.ja`: glog; `prim_mst.ja`: dlog, blog; `topological_sort.ja`: blog; `tree_sort.ja`: alog, hlog, rlog

## Garbage arrays per program

| program | confidence | garbage arrays (puts/takes) | output | input | clean |
|---|---|---|---|---|---|
| `tests/jana2014/fixtures/examples/avl_delete.ja` | high | - | key, left, right, ht | - | - |
| `tests/jana2014/fixtures/examples/avl_insert.ja` | high | - | key, left, right, ht | - | - |
| `tests/jana2014/fixtures/examples/avl_search.ja` | high | - | - | key, left, right | - |
| `tests/jana2014/fixtures/examples/base_convert.ja` | high | - | d | - | - |
| `tests/jana2014/fixtures/examples/bellman_ford.ja` | high | - | dist, pred | eu, ev, ew | - |
| `tests/jana2014/fixtures/examples/bfs.ja` | high | - | dist, visited, queue | adj | - |
| `tests/jana2014/fixtures/examples/binary_heap.ja` | high | heapgarbage (3/0), heapgarbage1 (2/0), heapgarbage2 (3/0), heapgarbage3 (2/0), heapgarbage4 (1/0), heapgarbage5 (1/0), insertgarbage (3/0), insertgarbage1 (3/0), insertgarbage2 (3/0), insertgarbage3 (3/0), insertgarbage4 (4/0) | A | - | - |
| `tests/jana2014/fixtures/examples/bubble_sort.ja` | high | - | a, ord | - | - |
| `tests/jana2014/fixtures/examples/closest_pair.ja` | high | - | - | x, y | - |
| `tests/jana2014/fixtures/examples/convex_hull.ja` | high | - | hull | x, y | - |
| `tests/jana2014/fixtures/examples/counting_sort.ja` | high | c (6/1) | b | a | - |
| `tests/jana2014/fixtures/examples/depth_first_search.ja` | high | - | visited, order | adj | - |
| `tests/jana2014/fixtures/examples/dijkstra.ja` | medium | visited (5/0) | dist | w | - |
| `tests/jana2014/fixtures/examples/dup_insertion_sort.ja` | high | - | b | a | - |
| `tests/jana2014/fixtures/examples/dynamic_array.ja` | high | - | data | - | - |
| `tests/jana2014/fixtures/examples/edit_distance.ja` | medium | - | D | x, y | - |
| `tests/jana2014/fixtures/examples/factor.ja` | high | - | fact | - | - |
| `tests/jana2014/fixtures/examples/floyd_warshall.ja` | high | - | path | - | - |
| `tests/jana2014/fixtures/examples/gray_code.ja` | high | - | bits | - | - |
| `tests/jana2014/fixtures/examples/gray_code_roundtrip.ja` | high | - | - | bits | - |
| `tests/jana2014/fixtures/examples/heap_sort.ja` | high | - | a | - | ord |
| `tests/jana2014/fixtures/examples/injective_arith_coding.ja` | high | - | - | m | - |
| `tests/jana2014/fixtures/examples/injective_arithmetic.ja` | high | - | - | coeffs | - |
| `tests/jana2014/fixtures/examples/injective_bwt_inverse.ja` | high | - | - | L | cnt, C, occ, T, path, s |
| `tests/jana2014/fixtures/examples/injective_ca_rule90.ja` | high | - | - | b | a |
| `tests/jana2014/fixtures/examples/injective_cipher_sbox.ja` | high | - | - | sbox, inv_sbox | rk |
| `tests/jana2014/fixtures/examples/injective_gcd.ja` | high | - | - | - | log |
| `tests/jana2014/fixtures/examples/injective_iterate.ja` | high | - | b, c | a | - |
| `tests/jana2014/fixtures/examples/injective_lehmer.ja` | high | - | - | perm | - |
| `tests/jana2014/fixtures/examples/injective_mini_cipher.ja` | high | - | - | - | logs |
| `tests/jana2014/fixtures/examples/injective_partition.ja` | medium | flags_b (3/0) | b | a | flags |
| `tests/jana2014/fixtures/examples/injective_sort_network.ja` | medium | - | b | a | log, log_b |
| `tests/jana2014/fixtures/examples/injective_vm.ja` | high | - | - | ops, args | - |
| `tests/jana2014/fixtures/examples/kmp.ja` | medium | f (1/0) | - | p, t | - |
| `tests/jana2014/fixtures/examples/knapsack.ja` | medium | - | K | wt, val | - |
| `tests/jana2014/fixtures/examples/kosaraju_scc.ja` | medium | visited (5/0), order (4/0) | comp | adj, adjt | - |
| `tests/jana2014/fixtures/examples/lcs.ja` | medium | - | L | x, y | - |
| `tests/jana2014/fixtures/examples/lis.ja` | medium | L (8/0) | - | a | - |
| `tests/jana2014/fixtures/examples/matrix_apsp.ja` | medium | - | m_arr | - | - |
| `tests/jana2014/fixtures/examples/matrixmult.ja` | medium | - | A | B | - |
| `tests/jana2014/fixtures/examples/matrixmult_v1.0.ja` | medium | - | B | A | LDU |
| `tests/jana2014/fixtures/examples/merge_sort.ja` | high | - | a, ord | - | - |
| `tests/jana2014/fixtures/examples/next_permutation.ja` | high | - | d | - | - |
| `tests/jana2014/fixtures/examples/perm-to-code.ja` | high | - | x | - | - |
| `tests/jana2014/fixtures/examples/permutation_rank.ja` | high | - | - | b | - |
| `tests/jana2014/fixtures/examples/prim_mst.ja` | medium | key (8/4), intree (5/0) | parent | w | - |
| `tests/jana2014/fixtures/examples/quick_sort.ja` | high | - | a, ord | - | - |
| `tests/jana2014/fixtures/examples/reversible_ca_ring.ja` | high | - | a, b | - | - |
| `tests/jana2014/fixtures/examples/reversible_ca_rule90.ja` | high | - | a, b | - | - |
| `tests/jana2014/fixtures/examples/reversible_gates.ja` | high | - | ctrl, p, q | - | - |
| `tests/jana2014/fixtures/examples/run-length-enc.ja` | high | - | arc | - | text |
| `tests/jana2014/fixtures/examples/selection_sort.ja` | high | ftab (3/0) | a | - | p |
| `tests/jana2014/fixtures/examples/structs_array.ja` | high | - | v | - | - |
| `tests/jana2014/fixtures/examples/structs_array_field_arr.ja` | high | - | g | - | - |
| `tests/jana2014/fixtures/examples/structs_array_param.ja` | high | - | data | - | - |
| `tests/jana2014/fixtures/examples/structs_grid.ja` | high | - | grid | - | - |
| `tests/jana2014/fixtures/examples/structs_local.ja` | high | - | - | out | - |
| `tests/jana2014/fixtures/examples/test2.ja` | low | - | test_array | - | - |
| `tests/jana2014/fixtures/examples/topological_sort.ja` | medium | visited (5/0) | order | adj | - |
| `tests/jana2014/fixtures/examples/tree_sort.ja` | medium | key (3/0), left (5/4), right (4/3), ht (13/10), cnt (3/0) | b | a | - |
| `tests/jana2014_in_out/fixtures/examples/factor.ja` | high | - | fact | - | - |
| `tests/jana2014_in_out/fixtures/examples/matrixmult.ja` | medium | - | A | B | - |
| `tests/jana2014_in_out/fixtures/examples/matrixmult_v1.0.ja` | medium | - | B | A | LDU |
| `tests/jana2014_in_out/fixtures/examples/perm-to-code.ja` | high | - | x | - | - |
| `tests/jana2014_in_out/fixtures/examples/run-length-enc.ja` | high | - | arc | - | text |
| `tests/jana2014_in_out/fixtures/examples/test2.ja` | low | - | test_array | - | - |
| `tests/janus2026/fixtures/examples/build-dict.ja` | low | - | - | out | - |
| `tests/janus2026/fixtures/examples/caesar.ja` | high | - | - | msg | - |
| `tests/janus2026/fixtures/examples/linked-list.ja` | high | - | - | vals | pool |
| `tests/janus2026/fixtures/examples/sort-network.ja` | high | - | - | arr | - |
| `tests/jana2014basic/fixtures/examples/test2.ja` | low | - | test_array | - | - |

`*` = unannotated array (garbage by default).  puts/takes are the profiler's 0->non-0 and non-0->0 counts.
