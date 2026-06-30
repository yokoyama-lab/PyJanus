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
| `base_convert` | 基数変換（Horner 桁抽出）整数 → 桁列 | `d[i] += (n / b^i) % b`（純式・`+=` のみ，`uncall` で減算） |
| `lehmer_code`（I/O）/ `injective_lehmer`（両コア） | 順列 ⇄ Lehmer符号 ⇄ 整数（PFAD ch.12） | インプレース左ランク変換＋階乗進法（local コピー乗算） |
| `cantor_pair` | Cantor ペアリング ℕ×ℕ → ℕ | `z += (x+y)(x+y+1)/2 + y`（純式・`+=` のみ） |
| `injective_partition`（両コア）/ `partition`（I/O） | 可逆 Lomuto partition（quicksort の心臓部） | 走査位置ごとの分岐ビットを `flags[]` に記録（sort_network と同型）；恒等swap は内側 `if j > lo+p` で抑止 |
| `injective_arith_coding`（両コア）/ `arith_coding`（I/O） | 整数算術符号化＝双射 rANS（PFAD ch.24–25） | 状態写像 `x ↦ (x/f)·M + C + x%f` を値保存 divmod の鏡像で実現（`/=`/`*=` なし・純式 `/ % *` のみ）；`if` は slot 判定 `x%M < f0` で閉じ `uncall` が復号器 |
| `injective_bwt_inverse`（両コア）/ `bwt_inverse`（I/O） | **逆BWT＝LF-mapping**（PFAD ch.13 + Bird&Mu JFP2004） | 計数→累積C→`T[i]=C[L[i]]+rank`→`path`巡回→`s[n-1-k]=L[path[k]]`；入れ子添字でポインタ追跡，ancilla は Bennett 流に uncompute し s のみ残す；`uncall` が前方BWT（固定長・sentinel 付き） |
| `injective_*`（既存） | 単射算術・iterate 等 | — |

## 将来候補（Bird/JFP 由来）

研究価値 × 実装容易性で 3 Tier に分類。

| # | 候補 | 出典 | 全単射の構造 | 逆の機構 | 難度 | 価値 |
|---|------|------|------------|----------|:---:|:---:|
| 4 | ✅ 整数算術符号化（実装済み: 双射 rANS） | PFAD ch.24–25 *Arithmetic coding* | メッセージ ⇄ 整数状態 | rANS 状態写像の逆＝`uncall` | 中〜高 | 高（可逆圧縮テーマ） |
| 5 | ✅ **Burrows–Wheeler 変換 + 逆**（実装済み: 逆BWT＝LF, 固定長n=5・sentinel） | **PFAD ch.13 + Bird&Mu JFP 2004** | 文字列 ⇄ (BWT, index) | **LF-mapping**（last-to-first）；`uncall`＝前方BWT | 高 | 最高 |
| 6 | 双射BWT (BBWT) | arXiv 2004.12590 | 文字列 ⇄ BWT（index 不要） | Lyndon 分解＋LF | 高 | 高 |

対象外（非単射のため可逆化できない）: smallest free number（PFAD ch.1），
Boyer–Moore / KMP（ch.16–17），maximum segment sum 系。

## 検証コアの制約メモ（重要）

検証コア（RevArr/RevFrame）の可逆代入演算子は `+= / -= / ^=`（`AAdd/ASub/AXor`）のみ。
**`*=` / `/=` は持たない**（その可逆性は除算可能性の前提を伴い，ビット演算のような総関数
追加では済まず可逆性の再証明が要る）。したがって `N /= b` を使う「N を破壊する divmod
ループ」は両コアで検証できない（vjanus は exit 3 でスキップ）。

回避策＝**純式での桁抽出**: `d[i] += (n / b^i) % b`。`/` `%` は式中の二項演算
（`BDiv/BMod`）なので `/=` 不要，`+=` だけで可逆になり両コアで検証可能。`base_convert`
はこの方式。算術符号化（④）も同様に「破壊的除算を避ける」設計が鍵。

## 推奨シーケンス

- **Tier 1（完了）**: ✅ ① 基数変換（`base_convert`）・✅ ③ Lehmer rank/unrank
  （`lehmer_code` I/O ＋ `injective_lehmer` 両コア）・✅ ② Cantor ペアリング（`cantor_pair`）
- **Tier 2（中）**: ✅ 可逆 Lomuto partition（`injective_partition` 両コア ＋ `partition` I/O；
  swap 決定を `flags[]` に記録し `uncall` が逆スキャッタ）・✅ ④ 整数算術符号化＝双射 rANS
  （`injective_arith_coding` 両コア ＋ `arith_coding` I/O；状態 divmod を値保存分解で `+=/-=` 化，
  `uncall` が復号器）
- **Tier 3（目玉）**: ✅ ⑤ **逆BWT＝LF-mapping**（`injective_bwt_inverse` 両コア ＋ `bwt_inverse`
  I/O；固定長 n=5・sentinel 付きで `uncall` が前方BWT，ancilla は Bennett 流に uncompute）。
  残課題: L を消費する**インプレース版**（s が L の置換である点を使う）と可変長・⑥ 双射BWT への発展

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
