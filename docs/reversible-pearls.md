# 可逆 Pearl カタログ — Bird / JFP の calculation を可逆 Janus へ

「クリーン可逆シミュレーション」として PyJanus に追加できる**単射・全単射**な
アルゴリズムを，Richard Bird *Pearls of Functional Algorithm Design*（PFAD, 全30章）
と JFP の Functional Pearls から抽出して整理した設計ノート。実装済みのものと将来候補を
一覧化し，実装の優先順位を与える。

## なぜ Bird/Pearl 系か

Bird らの calculation（等式変形によるアルゴリズム導出）の伝統には，「ある関数の**逆**を
導く」Pearl が複数ある。可逆言語 Janus では順方向手続き `call f` の逆が
**自動的に `uncall f`** になるため，「逆を別途導出する」という Pearl の主題そのものを
言語が体現する。さらに我々は **2つの独立な検証済み抽出インタプリタ**（vjanus = frame
コア，driverar = flat コア，どちらも Coq から抽出し健全性証明済み）で逆の正しさを
機械検証できる。

## 既存の可逆シミュレーション（実装済み）

`tests/jana2014/fixtures/examples/`（I/O なし・両コアで検証）と
`tests/jana2014_in_out/programs/`（I/O ハーネスで前方＋後方）に二形態で配置。

| 名前 | 単射の構造 | 機構 |
|------|-----------|------|
| `reversible_ca_rule90` / `_ring` | 二次的可逆セルオートマトン（Rule 90R） | `new = (左 XOR 右) XOR prev`，XOR が自己逆 |
| `gray_code` / `gray_code_roundtrip` | 反射 Gray 符号（全単射） | `g[i] ^= b[i+1]`，`uncall` で復号 |
| `reversible_gates` / `toffoli_gate` | 普遍可逆ゲート Toffoli・Fredkin | 制御保存ゲート（各自己逆） |
| `bitwise_ops` | 式中ビット演算 `& | ^` | 検証コア `BAnd/BOr/BXor`（`Z.land/lor/lxor`） |
| `injective_*`（既存） | 単射算術・Lehmer・iterate 等 | — |

## 将来候補（Bird/JFP 由来）

研究価値 × 実装容易性で 3 Tier に分類。

| # | 候補 | 出典 | 全単射の構造 | 逆の機構 | 難度 | 価値 |
|---|------|------|------------|----------|:---:|:---:|
| 1 | 基数変換（Horner） | Bird–Meertens / Horner則 | 整数 ⇄ 桁列 | divmod の逆＝Horner評価 | 低 | 中 |
| 2 | Cantor / boustrophedon ペアリング | 数え上げ Pearl | ℕ×ℕ ⇄ ℕ | 三角数の逆 | 低 | 中（lower.ml 内で既使用） |
| 3 | 順列のランク付け（Lehmer / 階乗進法） | PFAD ch.12 *Ranking suffixes* | 順列 ⇄ ランク | unranking | 低〜中 | 中（既存 `injective_lehmer` の発展） |
| 4 | 整数算術符号化 | PFAD ch.24–25 *Arithmetic coding* | メッセージ ⇄ 整数区間 | 区間の逆細分 | 中〜高 | 高（可逆圧縮テーマ） |
| 5 | **Burrows–Wheeler 変換 + 逆** | **PFAD ch.13 + Bird&Mu JFP 2004** | 文字列 ⇄ (BWT, index) | **LF-mapping**（last-to-first） | 高 | 最高 |
| 6 | 双射BWT (BBWT) | arXiv 2004.12590 | 文字列 ⇄ BWT（index 不要） | Lyndon 分解＋LF | 高 | 高 |

対象外（非単射のため可逆化できない）: smallest free number（PFAD ch.1），
Boyer–Moore / KMP（ch.16–17），maximum segment sum 系。

## 推奨シーケンス

- **Tier 1（低コスト・すぐ効く）**: ① 基数変換（Horner）→ ③ Lehmer rank/unrank（既存を
  I/O＋両コア化）→ ② Cantor ペアリング
- **Tier 2（中）**: ④ 整数算術符号化（可逆 divmod を丁寧に）
- **Tier 3（目玉）**: ⑤ **BWT + 逆**（Bird&Mu の calculational な逆導出が `uncall` に対応；
  固定長文字列でまず）→ ⑥ 双射BWT はその発展

各候補は既存と同じ二形態（`fixtures/examples/` の I/O なし版＋`jana2014_in_out/programs/`
の I/O 版）で追加し，両検証コアで PyJanus と差分一致を確認する（test-first）。

## 出典

- R. Bird. *Pearls of Functional Algorithm Design*. Cambridge University Press, 2010.
  <https://www.cambridge.org/core/books/pearls-of-functional-algorithm-design/B0CF0AC5A205AF9491298684113B088F>
- R. S. Bird and S.-C. Mu. Inverting the Burrows–Wheeler transform (Functional Pearl).
  *JFP* 14(6):603–612, 2004.
  <https://www.cs.ox.ac.uk/people/richard.bird/online/BirdMu2004Inverting.pdf>
- D. Köppl et al. In-Place Bijective Burrows–Wheeler Transforms. arXiv:2004.12590.
  <https://arxiv.org/pdf/2004.12590>
- 参考実装（Haskell）: <https://github.com/kirchnergo/pfad>
