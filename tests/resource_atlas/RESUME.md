# 再開メモ（janus-cost-atlas ブランチ）

## 今日やったこと
- 計測器: `jana_py/pebble.py` に RC-03 の資源ベクトル（stack_peak, total_calls, final_live_bits, 配列ごとの puts/takes, erasures=0）を追加．CLI `--profile-json` / `--costcheck`．
- 20 点表: `tests/resource_atlas/{gen_inputs,measure}.py`，変種 130 本（`generated/`），`data/scaling.*`, `data/corpus_*`．gcd_fib と bubble_sort は 20/20 で予測則に一致．
- costcheck: `jana_py/costcheck.py` 静的予測器（深さ上界 H，スタック不使用証明，total_calls 上界 C）．`data/prediction_vs_measurement.*` で 101+130 本，違反 0．
- Rocq 法則: `coq/JanusCost.v`（exec_det, exec_cost_rev, exec_injective, exec_peak_lo, GCD.gcd_stack_eq_divisions, BSORT.bsort_stack_eq_comparisons, no_push_stack_zero, acyclic_depth_bound, no_call_in_loop_bounded_calls）．`_CoqProject`, `audit.sh`, `coq/README.md` も更新．
- out 注釈: `docs/output-annotation.md`, `jana_py/outannot.py`, `annotations/out_annotations.json`（101 本）．
- 再集計: `recount.py` -> `data/recount.md`．takes=0 の配列 95 = output 39 / input 34 / garbage 22，終端空 17．

## 未解決
- (a) `JanusCost.v` は手元では Coq 8.12.2 でしか検査していない．CI（`.github/workflows/coq.yml`，Rocq 9.1）の green を確認すること．
- (b) cutrod と [Yoko17] の可逆メモ化 7 本は PyJanus に無い．Tetsuo さんに提供を依頼し，rc03 の cutrod stack/steps ≈ 0.104–0.112 の観察を再現・証明する．
- (c) 計測器が構造体フィールドの配列（`a.v`, `a.grid`, `d.entries`，注釈済み 7 本）を報告しない．
- (d) rc03 の DP 入力列は未公開なので knapsack / lcs / edit_distance の steps は最小サイズ以外で一致しない．
- (e) `out` キーワードはコメント/サイドカーの下書きのみ．パーサ変更はしていない．
- (f) 論文投稿先は情処 PRO / TOPRO．案: 1 導入（RC-03 の観察）→ 2 コスト意味論と資源ベクトル → 3 計測（20 点表・全数）→ 4 静的予測器と実測照合 → 5 Rocq による法則の証明 → 6 出力/ゴミ再集計と out 注釈 → 7 関連研究・今後（cutrod, 構造体, パーサ）．

## コマンド
```bash
python3 -m tests.resource_atlas.gen_inputs   # generated/*.ja を書き直す
python3 -m tests.resource_atlas.measure      # data/scaling.*, data/corpus_* を書き直す（約 1 分）
python3 -m tests.resource_atlas.compare      # data/prediction_vs_measurement.* を書き直す
python3 tests/resource_atlas/recount.py      # data/recount.md を書き直す
python3 -m pytest tests/ -q                  # 1246 passed, 440 skipped が期待値
bash coq/audit.sh                            # Rocq 9.1 でのビルドと Print Assumptions 監査（CI と同じ）
```
