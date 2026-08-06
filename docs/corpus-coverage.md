# 検証被覆マトリクス（`tests/jana2014/fixtures/examples/`）

*`tools/corpus_coverage.py` が pytest の `--junitxml` から生成する。手で編集しない。*

```bash
# 表の列になるテストだけでよい（全体を回す必要はない・約9分）
python3 -m pytest -q -p no:randomly --junitxml=/tmp/coverage.xml \
  tests/jana2014/test_reversibility_corpus.py tests/jana2014/test_inverse_corpus.py \
  tests/jana2014/test_format_roundtrip.py tests/jana2014/test_codegen_corpus.py \
  tests/jana2014/test_verified_corpus.py tests/jana2014/test_verified_cores_corpus.py \
  tests/jana2014/test_vjanus_corpus.py tests/jana2014/test_vjanus_inverse.py \
  tests/jana2014/test_reference_impls.py tests/jana2014/test_corpus_metadata.py \
  tests/janus2026/test_step1_golden.py
python3 tools/corpus_coverage.py /tmp/coverage.xml > docs/corpus-coverage.md
```

## 1. 何を見ている表か

8本のテストが97本を全数 glob するが、**そのうち何本かは渡された大半を skip する**。
抽出された Coq コアが扱えるのは Janus の断片で、手続き・配列・構造体を使う
プログラムはその外に出るためである。skip は理由つきで数えられているが、
pytest の要約は総数しか出さないので、**どのプログラムがどのコアで検証されて
いないか**はこれまでどこにも書かれていなかった。

| 列 | 何を確かめるか |
|---|---|
| `reversibility` | forward then inverse restores the store |
| `inverse` | the inverse interpreter recovers the initial store |
| `format` | AST to source to AST is stable |
| `codegen` | the C++ back-end agrees with the interpreter |
| `flat core` | the extracted flat core agrees |
| `both cores` | both extracted cores agree |
| `vjanus` | the extracted frame core agrees |
| `vjanus inv` | the frame core agrees running backwards |
| `step1` | the small-step semantics matches its golden |
| `reference` | an independent Python implementation agrees |
| `metadata` | the header's @expect and @oracle hold |

## 2. 列ごとの被覆率

| 検査 | 検査済み | skip | 被覆率 |
|---|---:|---:|---:|
| `reversibility` | 101 | 0 | 100% |
| `inverse` | 101 | 0 | 100% |
| `format` | 101 | 0 | 100% |
| `codegen` | 101 | 0 | 100% |
| `flat core` | 80 | 21 | 79% |
| `both cores` | 1 | 100 | 0% |
| `vjanus` | 101 | 0 | 100% |
| `vjanus inv` | 101 | 0 | 100% |
| `step1` | 0 | 101 | 0% |
| `reference` | 101 | 0 | 100% |
| `metadata` | 101 | 0 | 100% |

## 3. skip の理由

| 検査 | 理由 | 本数 |
|---|---|---:|
| `step1` | requires the Haskell reference impleme | 101 |
| `both cores` | array parameter | 58 |
| `both cores` | unsupported statement | 16 |
| `flat core` | self-recursion + locals | 13 |
| `both cores` | structs | 13 |
| `flat core` | *= | 4 |
| `both cores` | operator / | 3 |
| `both cores` | array declaration | 2 |
| `both cores` | unsupported expression | 2 |
| `both cores` | operator % | 2 |
| `flat core` | /= | 1 |
| `flat core` | array of structs w/ array field | 1 |
| `flat core` | out of fuel | 1 |
| `flat core` | local struct from non-variable | 1 |
| `both cores` | operator & | 1 |
| `both cores` | operator >= | 1 |
| `both cores` | 'left' | 1 |
| `both cores` | *= | 1 |

## 4. プログラム別

`o` = 検査済み、空欄 = そのテストの対象外、それ以外は skip の理由。

| プログラム | `reversibility` | `inverse` | `format` | `codegen` | `flat core` | `both cores` | `vjanus` | `vjanus inv` | `step1` | `reference` | `metadata` |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `ackermann_c.ja` | o | o | o | o | self-recursion + locals | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `adaptive_huffman_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `arith_coding_c.ja` | o | o | o | o | o | operator / | o | o | requires the Haskell reference impleme | o | o |
| `arith_roundtrip_c.ja` | o | o | o | o | o | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `array_element_arg_c.ja` | o | o | o | o | o | array declaration | o | o | requires the Haskell reference impleme | o | o |
| `avl_delete_g.ja` | o | o | o | o | self-recursion + locals | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `avl_insert_g.ja` | o | o | o | o | self-recursion + locals | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `avl_search_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `base_convert_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `bellman_ford_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `bennett_divmod_c.ja` | o | o | o | o | o | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `bfs_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `binary_heap_g.ja` | o | o | o | o | self-recursion + locals | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `binary_search_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `bit_bijections_c.ja` | o | o | o | o | o | operator / | o | o | requires the Haskell reference impleme | o | o |
| `bitwise_ops_c.ja` | o | o | o | o | o | operator & | o | o | requires the Haskell reference impleme | o | o |
| `bubble_sort_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `bwt_inverse_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `bwt_plain_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `ca_rule90_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `cantor_pair_c.ja` | o | o | o | o | o | operator / | o | o | requires the Haskell reference impleme | o | o |
| `cipher_sbox_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `closest_pair_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `combination_c.ja` | o | o | o | o | o | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `convex_hull_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `counting_sort_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `cuckoo_insert_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `cycle_lemma_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `depth_first_search_g.ja` | o | o | o | o | self-recursion + locals | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `dijkstra_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `dup_insertion_sort_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `dynamic_array_g.ja` | o | o | o | o | *= | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `edit_distance_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `edit_script_g.ja` | o | o | o | o | o | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `ext_gcd_g.ja` | o | o | o | o | o | unsupported expression | o | o | requires the Haskell reference impleme | o | o |
| `factor_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `factorial_c.ja` | o | o | o | o | self-recursion + locals | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `fall_c.ja` | o | o | o | o | o | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `fib_c.ja` | o | o | o | o | o | o | o | o | requires the Haskell reference impleme | o | o |
| `fib_variants_c.ja` | o | o | o | o | o | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `floyd_warshall_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `gcd_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `gcd_g.ja` | o | o | o | o | o | unsupported expression | o | o | requires the Haskell reference impleme | o | o |
| `glaisher_c.ja` | o | o | o | o | *= | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `gray_code_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `gray_code_roundtrip_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `hamming_c.ja` | o | o | o | o | o | operator % | o | o | requires the Haskell reference impleme | o | o |
| `hanoi_c.ja` | o | o | o | o | o | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `hash_chain_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `heap_sort_g.ja` | o | o | o | o | self-recursion + locals | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `int_bijections_c.ja` | o | o | o | o | o | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `iterate_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `kmp_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `knapsack_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `kosaraju_scc_g.ja` | o | o | o | o | self-recursion + locals | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `landauer_interp_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `lcs_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `lehmer_code_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `lis_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `lomuto_partition_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `matrix_apsp_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `matrixmult_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `matrixmult_v1_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `merge_sort_g.ja` | o | o | o | o | self-recursion + locals | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `mini_cipher_c.ja` | o | o | o | o | o | operator >= | o | o | requires the Haskell reference impleme | o | o |
| `modexp_g.ja` | o | o | o | o | *= | operator % | o | o | requires the Haskell reference impleme | o | o |
| `next_permutation_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `perm_to_code_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `permutation_rank_c.ja` | o | o | o | o | o | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `ppm_lite_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `prim_mst_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `quick_sort_g.ja` | o | o | o | o | self-recursion + locals | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `rans_encode_c.ja` | o | o | o | o | /= | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `reversible_ca_ring_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `reversible_ca_rule90_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `reversible_gates_c.ja` | o | o | o | o | o | array declaration | o | o | requires the Haskell reference impleme | o | o |
| `run_length_enc_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `run_length_enc_stack_c.ja` | o | o | o | o | o | 'left' | o | o | requires the Haskell reference impleme | o | o |
| `selection_sort_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `sort_network_c.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `sort_rank_g.ja` | o | o | o | o | o | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `sqrt_g.ja` | o | o | o | o | o | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `stack_operations_c.ja` | o | o | o | o | self-recursion + locals | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `stack_uncall_c.ja` | o | o | o | o | o | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `stack_vm_c.ja` | o | o | o | o | o | unsupported statement | o | o | requires the Haskell reference impleme | o | o |
| `structs_array_c.ja` | o | o | o | o | o | structs | o | o | requires the Haskell reference impleme | o | o |
| `structs_array_field_arr_c.ja` | o | o | o | o | array of structs w/ array field | structs | o | o | requires the Haskell reference impleme | o | o |
| `structs_array_field_c.ja` | o | o | o | o | out of fuel | structs | o | o | requires the Haskell reference impleme | o | o |
| `structs_array_param_c.ja` | o | o | o | o | o | structs | o | o | requires the Haskell reference impleme | o | o |
| `structs_flat_param_c.ja` | o | o | o | o | o | structs | o | o | requires the Haskell reference impleme | o | o |
| `structs_flat_repass_c.ja` | o | o | o | o | o | structs | o | o | requires the Haskell reference impleme | o | o |
| `structs_grid_c.ja` | o | o | o | o | o | structs | o | o | requires the Haskell reference impleme | o | o |
| `structs_local_arr2d_c.ja` | o | o | o | o | o | structs | o | o | requires the Haskell reference impleme | o | o |
| `structs_local_arr_c.ja` | o | o | o | o | o | structs | o | o | requires the Haskell reference impleme | o | o |
| `structs_local_c.ja` | o | o | o | o | local struct from non-variable | structs | o | o | requires the Haskell reference impleme | o | o |
| `structs_nested_c.ja` | o | o | o | o | o | structs | o | o | requires the Haskell reference impleme | o | o |
| `structs_param_c.ja` | o | o | o | o | o | structs | o | o | requires the Haskell reference impleme | o | o |
| `structs_scalar_c.ja` | o | o | o | o | o | structs | o | o | requires the Haskell reference impleme | o | o |
| `topological_sort_g.ja` | o | o | o | o | self-recursion + locals | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `tree_sort_g.ja` | o | o | o | o | self-recursion + locals | array parameter | o | o | requires the Haskell reference impleme | o | o |
| `zagier_c.ja` | o | o | o | o | *= | *= | o | o | requires the Haskell reference impleme | o | o |

## 5. 一度も走らない検査

**1本も検査していない列**。テストは存在するが、条件が揃わず全数 skip される。

| 検査 | 全数 skip の理由 |
|---|---|
| `step1` | requires the Haskell reference impleme |

## 6. 生きている検査で一度も skip されないプログラム

**1/101 本**が、実際に走る 10 列すべてで検査されている。

`fib_c.ja`

