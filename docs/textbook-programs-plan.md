# 教科書的可逆プログラムを増やす計画（PyJanus）

*作成: 2026-07-06 / このファイルは PyJanus 内で起動した Claude セッションが「可逆プログラムを次々に追加する」ための実行手順・規約・バックログ。*

## 0. この文書の位置づけ

- **目的**: 教科書的な可逆 (Janus) プログラムを継続的に追加していくための **playbook**（作り方・置き場・検証・バックログ）。
- **これはゼロからではない**: PyJanus には既に **約100本規模**の可逆プログラムが実装済み。本計画は「既存規約に乗せて抜けを埋め、次々に追加する」もの。**新規作成の前に必ず既存 corpus を確認して重複を避ける**こと。
- **関係文書（先に読む）**:
  - `docs/reversible-pearls.md` — 題材カタログ本体。Bird *PFAD* / JFP Functional Pearls から抽出した可逆アルゴリズムの Tier 別ロードマップ・実装済み一覧・出典。**本書はこれを実行に移す手順書**であり、題材選定はこのカタログを正とする。
  - `docs/DIALECTS.md` — Janus 方言仕様（janus1982 / jana2014 / janus2026 等）。
  - `CLAUDE.md` — リポジトリ全体の規約・CLI コマンド。

## 1. 置き場（二形態・既存規約を踏襲）

新規プログラムは既存と同じ**二形態**で追加する:

| 形態 | ディレクトリ | 用途・検証 |
|---|---|---|
| I/O なし | `tests/jana2014/fixtures/examples/<name>.ja` | 2つの Coq 抽出コアで機械検証（差分一致） |
| I/O あり | `tests/jana2014_in_out/programs/<name>.ja` | I/O ハーネスで前進＋後退を確認 |

- 拡張子 `.ja`、既定方言 **`janus2026`**（最新・stdlib 正本）。古典題を旧方言で見せたい時のみ `--std jana2014` 等。
- 標準ライブラリ `jana_py/lib/std/*.ja`（`array` / `bits` / `math`(gcd, divmod, mul_acc) / `stack` / `sort` / `reduce`）を `#include "std/…"` で再利用し重複を避ける。

## 2. 実行と検証（test-first が原則）

```bash
# 実行 / 逆実行 / 逆写像 / C++ 生成 / デバッガ
python3 -m jana_py.cli prog.ja
python3 -m jana_py.cli -i prog.ja                 # 反転ソースを表示
python3 -m jana_py.cli --inverse '{"x": 10}' prog.ja
python3 -m jana_py.cli -c prog.ja
python3 -m jana_py.cli -d prog.ja

# テスト（push 毎に CI が 3.10/3.12/3.14 で実行）
python3 -m pytest tests/ -q
```

- **可逆性の不変条件**: 「`call f` の後に `uncall f` で全変数が元に戻る」。既存の流儀は `tests/jana2014/test_reversibility.py`（前進ストア＝call+uncall 後ストアを assert）。
- **2コア差分検証**: Coq から抽出し健全性証明済みの**2つの独立インタプリタ**（`vjanus`＝frame コア / `driverar`＝flat コア）と PyJanus の結果一致を確認する。ハーネスは `coq/harness/`（`differential.py` / `differentialar.py`、`coq/harness/README.md`）。`fixtures/examples/` に置いたものは I/O ハーネスのフィクスチャテスト（`tests/jana2014_in_out/test_in_out_example_fixtures.py` ほか）が拾う。**正確な起動法は起動時に `coq/harness/README.md` と当該テストを読んで確認**すること。

## 3. 可逆化の技法（＋検証コアの重要制約）

> **制約（必読）**: 検証コアの可逆代入演算子は `+= / -= / ^=` のみ。**`*= / /=` は無い**。
> したがって「`N /= b` で N を破壊する divmod ループ」は両コアで検証**不可**（`vjanus` は exit 3 でスキップ）。
> **回避策＝純式での桁抽出**: `d[i] += (n / b^i) % b`。式中の `/ %`（二項演算 `BDiv/BMod`）は使えるので `+=` だけで可逆になり両コアで検証できる。`base_convert` / `injective_arith_coding` がこの方式。

プログラム冒頭コメントに「何を計算するか／単射の構造／どの技法か」を明記すると教材価値が上がる。技法は概ね4分類:

1. **クリーン蓄積** — 入力を保存し `uncall` は減算で戻す。例: 加算・乗算(`mul_acc`)・内積・フィボナッチ・線形探索。
2. **アンシラフラグ** — 捨てると非可逆になる判定を 1bit に記録。例: `cswap`・可逆バブルソート・可逆 Lomuto partition・二分探索。
3. **履歴スタック** — 破棄する情報を退避し `uncall` で再生。例: 可逆ユークリッド `gcd`・RLE・順列⇄Lehmer 符号・整数平方根。
4. **Bennett uncompute** — 補助を計算→使用→逆計算で消去し結果のみ残す。例: 逆BWT。

## 4. 新規プログラムを1本追加する手順（チェックリスト）

1. **題材選定**: 下記バックログ or `reversible-pearls.md` の Tier から選ぶ。
2. **重複確認**: `ls tests/jana2014/fixtures/examples/ tests/jana2014_in_out/programs/` と `grep -ri <キーワード>` で既存を確認。
3. **技法決定**: §3 の 1–4 から選び、検証コア制約（`*= /=` 回避）を満たす設計にする。
4. **test-first**: 期待入出力と「逆でのラウンドトリップ」を先に固定。
5. `tests/jana2014/fixtures/examples/<name>.ja`（I/O なし）を作成。冒頭コメントに計算内容／単射構造／技法を記載。
6. 必要なら `tests/jana2014_in_out/programs/<name>.ja`（I/O 版）も追加。
7. 実行＆逆実行で手動確認 → 2コア差分ハーネス → `pytest tests/ -q` が緑。
8. `docs/reversible-pearls.md` の表に 1 行追記（将来候補→実装済みへ）。
9. safe-push（コミット前 gitleaks）＋ Notion 作業ログ 1 行。

## 5. バックログ（次に作るもの）

### A. Pearls ロードマップの残課題（`reversible-pearls.md` 由来・研究価値高）
- **逆BWT のインプレース版** — `s` が `L` の置換である性質を使い `L` を消費する版。
- **⑥ 双射BWT (BBWT)** — index 不要（Lyndon 分解＋LF-mapping）。arXiv:2004.12590。

### B. 教科書「基礎」トラック（候補・**追加前に既存との重複を必ず確認**）
古典的可逆計算の定番で、未実装または簡潔な教材版が欲しいもの:
- ハノイの塔（可逆・手数カウント）
- Ackermann（可逆・履歴スタック）
- 二分探索（アンシラフラグ）
- 拡張ユークリッド / モジュラべき乗（履歴）
- ビット計数・パリティ（`injective_bits.ja` と重複確認）
- 配列 / 連結リストの反転（`write_reversed.ja` と重複確認）

> 注: 既存 corpus には既に fib・factor(階乗)・`injective_gcd`・`sqrt`・sort(`injective_sort_network`/`sort_n3`)・
> `run_length_enc`・`gray_code`・`lehmer_code`/`perm_to_code`・`cantor_pair`・`base_convert`・
> 算術符号化・逆BWT・CA(Rule90)・Toffoli/Fredkin・行列積・LZ ファミリ（lz77/78/w/…）などが揃っている。
> 「基礎」トラックは**これらと重複しない**教材簡潔版・未カバー題を狙う。

## 6. 出典・参照
- `docs/reversible-pearls.md`（題材カタログ）／`docs/DIALECTS.md`（方言）
- R. Bird. *Pearls of Functional Algorithm Design*. Cambridge, 2010.
- R. S. Bird, S.-C. Mu. Inverting the Burrows–Wheeler transform (Functional Pearl). *JFP* 14(6), 2004.
- D. Köppl et al. In-Place Bijective Burrows–Wheeler Transforms. arXiv:2004.12590.
