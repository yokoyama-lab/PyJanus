# Corpus atlas summary

Programs: 101 total, 101 measured, 0 failed to run (kept as rows with an `error` column in corpus_atlas.csv).

| quantity | value |
|---|---|
| steps median / max | 62 / 2171 (permutation_rank.ja) |
| stack_peak median / max | 0 / 79 (avl_delete.ja) |
| call_depth_peak median / max | 1 / 7 (avl_delete.ja) |
| final_live_bits median / max | 23 / 343 (matrix_apsp.ja) |
| programs with stack_peak > 0 | 33/101 = 32.7% |
| programs ending with all state zero | 0/101 = 0.0% |
| erasures | 0 in all 101 programs (by construction) |
| arrays seen / written (puts > 0) | 168 / 146 |
| written arrays that never take (takes = 0) | 95/146 = 65.1% |
| written arrays that end empty (all cells 0) | 17/146 = 11.6% |

rc03 (111-program corpus at c6c1656, tex:149-150): 122/189 = 65% written arrays never take,
25/189 = 13% end empty; 36/111 = 32% use a stack; steps median 74; stack_peak median 0.
rc03 on the renamed 101 fixtures (tex:179-181): 121/177 = 68% never take, 23/177 = 13% end empty.

## Top stack users

| file | stack_peak | steps |
|---|---:|---:|
| tests/jana2014/fixtures/examples/avl_delete.ja | 79 | 810 |
| tests/jana2014/fixtures/examples/floyd_warshall.ja | 67 | 412 |
| tests/jana2014/fixtures/examples/avl_insert.ja | 65 | 691 |
| tests/jana2014/fixtures/examples/kosaraju_scc.ja | 60 | 311 |
| tests/jana2014/fixtures/examples/bellman_ford.ja | 54 | 327 |
| tests/jana2014/fixtures/examples/prim_mst.ja | 38 | 462 |
| tests/jana2014/fixtures/examples/dijkstra.ja | 37 | 451 |
| tests/jana2014/fixtures/examples/kmp.ja | 37 | 168 |
| tests/jana2014/fixtures/examples/bfs.ja | 36 | 206 |
| tests/jana2014/fixtures/examples/heap_sort.ja | 35 | 396 |

## Programs per dialect

| std | programs | measured |
|---|---:|---:|
| jana2014 | 85 | 85 |
| jana2014_in_out | 10 | 10 |
| jana2014basic | 2 | 2 |
| janus2026 | 4 | 4 |
