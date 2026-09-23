# Resource atlas (RC-03 資源アトラスの再計測と静的予測)

セミナー資料 RC-03「可逆プログラムは何を払っているか（Janus 系コーパス 111 本の資源アトラス）」
（`tetsuo-jp/rc-lecture-notes`, `src/rc03_resource_atlas.tex`; 以下 rc03）の観察を，
このリポジトリの中で **(1) 計測器**，**(2) 規模を振った生データ**，**(3) 構文的な静的予測器**
の 3 点として再現・拡張したもの．

## 1. 計測器 — `jana_py/pebble.py`（`--profile` / `--profile-json`）

`profile_space(program, std=...)` が返す `SpaceProfile` に rc03 の資源ベクトル
（rc03.tex:97-117, 表 tab:metrics）を追加した．既存フィールドと値は変えていない．

| 量 | 定義（rc03.tex 行） | 実装 |
|---|---|---|
| `steps` | 実行した文の数（:109） | 既存 `total_steps`（複合文 if/from/local も 1 文として数える） |
| `stack_peak` | 全フレームの退避値の総深さのピーク（:110） | 1 文実行後ごとに生存フレームの `stack` 変数を走査し要素数を合計．記憶域は **同一性** (`id()`) で識別し，参照渡しされたスタックを重複して数えない（:120, :125-127 の 75,802 対 310 の誤り） |
| `call_depth_peak` | 呼び出しの深さのピーク（:111） | 既存 `call_depth_max` の別名 |
| `total_calls` | — | call + uncall の回数 |
| `final_live_bits` | 終端で 0 でない状態のビット数（:112） | main 終了時の生存フレーム（root）の全セルの `bit_length` 和（可変オブジェクトは同一性で重複排除） |
| `puts` / `takes` | 配列セルの 0→非0 と逆向きの回数，配列ごと（:113） | 1 文ごとに各配列の各セルの零/非零を前回と比較．配列は記憶域の同一性で識別し，最初に見たフレームでの名前で報告 |
| `erasures` | 不可逆な消去の回数（恒等的に 0，:114） | 常に 0 として記録 |

CLI: `python3 -m jana_py.cli --std jana2014 --profile-json tests/jana2014/fixtures/examples/gcd.ja`
（`--profile` は方言 `std` を渡すようになった）．

注: 旧来の `max_live_vars` / `max_live_bits` は歴史的な「一度でも実行したフレーム全部」の
集計（返却済みフレームと参照渡しセルを重複計上する）のまま残してある．新しい量はすべて
`_bind_args`/`_call_proc` で保守する正しい生存フレームスタックから計算する．

## 2. 規模を振った再計測 — `gen_inputs.py`, `measure.py`, `generated/`, `data/`

rc03 §規模を振った計測（:201-234）は 9 族 × 6 サイズ．ここでは本リポジトリにある族について
約 20 サイズずつ測り直した．**原本のフィクスチャは改変せず**（:205），手続き部を逐語コピーし
`main` の初期化だけを書き換えた変種を `generated/` に置く（130 本）．

| 族 | パラメータ | 予測 stack_peak | 6 点との照合 |
|---|---|---|---|
| `gcd_fib` | a=F(k+2), b=F(k+1), k=1..20 | k（減算回数 = 除算回数） | steps 20,28,36,44,52,60（k=4..14）が **完全一致** |
| `gcd_pair` | 非フィボナッチ 6 対 | (ユークリッド商の和) − 1 | — |
| `bubble_sort` | n=2..21，降順入力，原本どおり call+uncall | n(n−1)/2 | steps は rc03 の (2×+1)/2… 下記 |
| `bubble_sort_fwd` | 同上，forward `call bsort` のみ | n(n−1)/2 | steps 68,148,260,404,580,788（n=4..14）が **完全一致** |
| `bubble_sort_perm` | 決定的擬似乱数順列 n=5,8,13,21 | n(n−1)/2（入力順序に無依存） | — |
| `knapsack` | n=1..20, cap=n+2（原本は n=3,cap=5） | 0 | n=2 で 50 一致，以降 −3..−21 |
| `lcs` | m=n=s, s=1..20 | 0 | s=2 で 29 一致，以降 +2..+12 |
| `edit_distance` | m=n=s, s=1..20 | 0 | −6..−33 |

結果（`data/scaling.csv`, `data/scaling.md`）: **130/130 点で stack_peak が予測則に一致**．
`steps` の rc03 との差の説明:

* bubble_sort: rc03 の 6 点は原本の後半（`ord` 初期化と `uncall bsort`）を含まない forward
  のみの計測と一致する（`bubble_sort_fwd` が 6 点すべて一致）．原本フィクスチャは c6c1656 と
  HEAD で同一なので，rc03 側の生成器が forward だけの main を作っていたと判断できる．
* DP 3 族: 内側ループの if の分岐で実行文数が変わる（一致/不一致，`wt[i] > w` の真偽）ため
  `steps` は入力の内容に依存する．rc03 の入力列（`scripts/gen_atlas_tables.py`）は公開
  されておらず，本リポジトリの決定的な入力列とは中身が異なる．規模の同定（先頭点の一致）と
  2 次の成長は合う．なお knapsack のサイズ 3 は原本と同じ (n=3,cap=5) だが rc03 は 86，
  当計測器（と原本）は 83 なので，rc03 の knapsack の刻みは cap=n+2 ではない．
* `steps` の定義自体は gcd_fib・bubble_sort_fwd の 12 点完全一致で同一と確認できる．

**cutrod について**: rc03 の 9 族のうち `cutrod_linear`（および対のメモ化 `fib_pairs`，
`fib_iter`, `factorial` の rc03 版入力）は [Yoko17] の可逆メモ化実装 7 本に属し，
本リポジトリには存在しない（HEAD にも c6c1656 にも無い）．捏造はせず，
上向き DP 3 族（knapsack, lcs, edit_distance）を「スタックを使わない族」の代表として測った．

### 全数計測 — `data/corpus_atlas.csv`, `data/corpus_arrays.csv`, `data/corpus_summary.md`

101 本（jana2014 85 + jana2014_in_out 10 + janus2026 4 + jana2014basic 2，各ディレクトリの
テストと同じ `--std`）をすべて実行できた（失敗 0；失敗した場合も `error` 列付きで行を残す）．

| 量 | 本リポジトリ 101 本 | rc03 111 本（:137-159） | rc03 改名後 101 本（:179-181） |
|---|---|---|---|
| stack_peak > 0 | 33/101 = 32.7% | 36/111 = 32% | — |
| 書き込みのあった配列で takes = 0 | 95/146 = 65.1% | 122/189 = 65% | 121/177 = 68% |
| 終端で空になる配列 | 17/146 = 11.6% | 25/189 = 13% | 23/177 = 13% |
| 終端で全状態が 0 の本数 | 0 | 0 | 0 |
| stack_peak 上位 | avl_delete 79, floyd_warshall 67, avl_insert 65, kosaraju_scc 60, bellman_ford 54 | AVL 削除 79, APSP 67, AVL 挿入 65, SCC 60, SSSP 54 | — |
| final_live_bits 最大 | 343 (matrix_apsp) | 343 (APSP) | — |
| steps 中央値 | 62 | 74 | — |

上位 5 本の stack_peak と final_live_bits の最大値が rc03 と一致しており，計測器の定義が
揃っていることの照合になっている．配列本数（146 対 177）の差は，配列の同定法
（ここでは記憶域の同一性で 1 本，ローカル配列の再確保は同名 1 本に合算）の違いと考えられる．

## 3. 構文的予測器 — `jana_py/costcheck.py`（`--costcheck`）, `compare.py`

AST だけから次を予測する（`analyze(program) -> CostPrediction`）:

1. main から到達可能な手続きの call/uncall グラフが非循環なら，最長路 H について
   `call_depth_peak ≤ H`．
2. 到達可能な手続きに push/pop が 1 つも無ければ `stack_peak = 0`
   （uncall で pop は push になるので両方を「スタック使用」と見る）．
3. 非循環かつ到達可能な手続きのループ本体（from の do/loop 部，iterate，foreach）に
   call/uncall が無ければ `total_calls ≤ C`，C = Σ_呼び出し点 (1 + calls(呼び先))．
   このとき total_calls は入力に無依存．

`data/prediction_vs_measurement.{csv,md}`（101 本 + 変種 130 本）:

| 予測 | 適用できた本数（コーパス） | 成立 | 違反 | 等号成立 |
|---|---|---|---|---|
| call_depth_peak ≤ H | 84/101（17 本は再帰） | 84 | **0** | 84/84 |
| stack_peak = 0 の保証 | 68/101 | 68（実測 0） | **0** | 保証されない 33 本はすべて実測 > 0 |
| total_calls ≤ C | 63/101（27 本はループ内 call，17 本は再帰） | 63 | **0** | 63/63 |

変種 130 本も同様に違反 0，等号成立 130/130．

## 再生成

```bash
python3 -m tests.resource_atlas.gen_inputs   # generated/*.ja を書き直す
python3 -m tests.resource_atlas.measure      # data/scaling.*, data/corpus_* を書き直す（約 1 分）
python3 -m tests.resource_atlas.compare      # data/prediction_vs_measurement.* を書き直す
python3 -m pytest tests/resource_atlas -q    # 生成物と CSV の整合を検査する回帰テスト
```

乱数は使わない（順列は `random.Random(n)` の固定シード）．同じ入力から同じ表が再生成される．
