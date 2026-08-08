# Lanese–Vidal 2026 と `coq/RevLoopLemma.v` の逐条対応

*I. Lanese, G. Vidal. **A Reversible Semantics for Janus.** arXiv:2602.16913, 2026.*
*対応先: `coq/RevLoopLemma.v`（2026-08-08）／比較対象: `coq/RevSmallStep.v`*

論文は**機械検証していない**。この文書は、どの主張を形式化し、どれを形式化せず、
**どこで設計が分岐したか**を1件ずつ突き合わせたものである。

---

## 0. まず全体の対応

論文には**意味論が2つ**ある。

| | 論文 | 配置 | 目的 |
|---|---|---|---|
| A | §3 の小ステップ意味論 | `⟨σ, s, π⟩` — ストア・現在文・**継続スタック π** | 大ステップとの同値（Theorem 1） |
| B | §5 の CFG／ラベル意味論 | `⟨σ, ℓ₁, ℓ₂, π⟩` — ストア・**2つのラベル**・スタック | **Loop Lemma**（Lemma 5） |

`RevLoopLemma.v` は**この2つを1つにまとめている**。配置は
`mk (cctl : list rs) (cst : state) (chist : list ev)` で、

- `cctl` が **A の π に対応**（論文は「現在文 + スタック」、こちらは全部をスタックに載せる。
  `⟨σ, s, π⟩` ↔ `mk (s :: π) σ h` で同型）
- `chist` が **B のラベル対の役割を果たす**。論文はプログラムカウンタを2ラベルで持ち、
  「どの辺を通ってきたか」を CFG から読む。こちらは通った規則が捨てた情報を
  イベントとして直接積む

**この差が §3 の結論をすべて動かす**ので、先に述べておく。

---

## 1. §3 — 継続スタック付き小ステップ意味論

| 論文 | `RevLoopLemma.v` | 状態 |
|---|---|---|
| 配置 `⟨σ, s, π⟩` | `mk (s :: k) a h`（`cctl` が `s :: π`） | **対応あり** |
| 前進簡約 `→` | `fstep` | **対応あり**（13規則） |
| **Lemma 1**（大ステップの証明から簡約列を作る） | `complete_pc` の相互帰納（`L.exec_mut`、`P0` が `L.lp` 側） | **形式化済み** |
| **Definition 1**（balanced derivation） | `fbaln G k n c c'`（`fbal` はその段数を隠したもの） | **形式化済み** |
| **Definition 2**（loop derivation） | `sound_bal_n` の第2成分 | **形式化済み**（独立した定義ではなく、相互再帰の片側として。下記 §5） |
| **Definition 3**（trace ＝ 適用した規則の列） | `chist : list ev` | **強めたもの**（下記 §4） |
| **Lemma 2**（`⟨σ,s,π₁⟩ →* ⟨σ′,skip,π₂⟩` の分解） | `fbaln_cut` / `fbaln_cut1` | **形式化済み** |
| **Theorem 1** `ϵ ⊢ s ⇓ σ` **iff** `⟨ϵ,s,[]⟩ →* ⟨σ,skip,[]⟩` | `exec_iff_pc` | **形式化済み・両方向** |

論文の Theorem 1 の証明は「only if は Lemma 1、if は Lemma 2 と
『この形の簡約列は balanced である』」という構成で、**こちらも同じ道を通った**
（2026-08-08）。最後の「この形の簡約列は balanced である」に当たるのが
`fmulti_nil_fbaln`——**最上位ではスタックが空で行き詰まるので、balanced 性は
無料で付いてくる**。加えて `complete_pc_bal` で「Lemma 1 が作る簡約列は
どの段でも balanced」を示したので、同値は最上位に限らず**任意の `k` で成り立つ**
（`exec_iff_fbal`）。

---

## 2. §5 — CFG／ラベル意味論と Loop Lemma

| 論文 | `RevLoopLemma.v` | 状態 |
|---|---|---|
| Fig. 7 の拡張構文（`[·]ℓ` によるラベル付け、`start` / `stop`） | — | **作っていない**（§3 の設計判断） |
| CFG（`entry`, `block`, `flow`） | — | 同上 |
| **Lemma 3**（`entry(s) −→ ℓ` の性質） | — | CFG 固有につき対象外 |
| **Lemma 4** `flow⁻¹(s) = flow(I⟦s⟧)` | — | CFG 固有につき対象外 |
| 後進簡約 `↽` | `bstep` | **対応あり**（13規則） |
| **Definition 4**（reachable configuration） | — | **不要になった**（§3） |
| **Lemma 5（Loop Lemma）** reachable な `⟨σ,ℓ₁,ℓ₂,π⟩` について `⇀ iff ↽` | `loop_lemma : fstep G c c' <-> bstep G c' c` | **形式化済み・仮定が弱い**（§3） |
| Example 1 / Example 2（具体的な簡約列） | `seq_collapse_separated` / `exit_assertion_separated` | **別の具体例**（§4） |

---

## 3. 設計が分岐した1点 — ラベル対 vs 履歴

**論文**は制御を CFG 上の**2ラベル** `⟨ℓ₁, ℓ₂⟩` で持つ。逆行するとき「直前がどこだったか」は
CFG の辺を逆に辿って求める。この方式には代償がある。

> **Definition 4 (reachable configuration).** …
> *This rules out, e.g., the case of configurations `⟨σ, ℓ, ℓ′, π⟩` where `ℓ` and `ℓ′`
> are not the two ends of an edge of the CFG.*

つまり **Loop Lemma は「到達可能な配置」でしか主張できない**。ラベルの対は勝手に作れて
しまい、CFG の辺に対応しない対からは逆行できないからである。

**`RevLoopLemma.v`** は捨てた情報そのものを `chist` に積む。イベントは

```coq
| EIf (g1 : guard) (s1 s2 : rs) (g2 : guard) (br : bool)
| EAssert (g : guard) (v : bool)
```

のように**その規則が消したものを全部持つ**ので、逆行に外部の構造（CFG）が要らない。
結果として

```coq
Theorem loop_lemma : forall G c c', fstep G c c' <-> bstep G c' c.
```

は**到達可能性の仮定なしで**成り立つ。**論文の Lemma 5 より仮定が弱い。**

代わりに失うものもある。論文のラベルは**有限**で実装に落ちるが、こちらの履歴は
**実行の長さに比例して伸びる**。可逆計算では履歴が伸びること自体が主題（この repo の
`_g` / `_c` 分類がまさにそれ）なので、意味論としては誠実な選択だと考えるが、
**「PC を持つ」という論文の主張をそのまま機械化したのではない**ことは明記しておく。

---

## 4. 強めた点・弱めた点

### 強めた

| | |
|---|---|
| **Loop Lemma の仮定** | 到達可能性が不要（§3） |
| **trace** | 論文の Definition 3 は「適用した規則の列」。規則名だけでは逆行に足りないので論文は CFG へ移る。`chist` は規則が消した**値**まで持つので、それ自体で逆行が閉じる |
| **決定性** | 論文は Loop Lemma までで、両方向の決定性を別立てで述べていない。`fstep_det` / `bstep_det` と、そこから出る `fstep_backward_det` を証明した |
| **機械検証** | 論文は無し。`loop_lemma` / `loop_lemma_multi` / `fstep_det` / `bstep_det` / `fstep_backward_det` / `complete_pc` / `run_is_reversible` はいずれも **`Closed under the global context`**（`functional_extensionality` すら不要）。`coq/audit.sh` が検査する |
| **反例の分離** | 論文は `if e1 then skip else s2 fi e2` が `skip` へ潰れる例を挙げるだけ。`RevSmallStep.exit_assertion_collapses` でその潰れを**定理として**述べ、`RevLoopLemma.exit_assertion_separated` で新しい意味論では潰れないことを**定理として**述べた。差が注釈でなく命題になっている |

| **同値の成立範囲** | 論文の Theorem 1 は最上位（空の継続スタック）の主張。`exec_iff_fbal` は**任意の制御スタック `k`** で同値を述べる。`k` を残したまま `s` を回し切る balanced derivation が `L.exec G s a b` と1対1に対応する |

### 弱い・未着手

| | |
|---|---|
| **CFG 版意味論（§5 の Fig. 7・Lemma 3・Lemma 4）** | 作っていない。§3 の設計判断による |
| **言語の範囲** | 論文は Janus の具体構文（`x⊕= e`、`x[e]⊕= e`、`start`/`stop`）を扱う。こちらは `REV_PRIM` の抽象 `prim` なので、代入の具体形は抽象化されている。**逆に言えば `RevJanus` / `RevExt` / `RevStack` / `RevCA` / `RevToy` の5実例すべてに一度に効く** |
| **Example 1 / 2** | 論文の具体的な簡約列を再現していない |

---

## 5. balanced derivation — 論文どおりに埋めた（2026-08-08）

Theorem 1 の "if" 方向が唯一の本質的な欠落だった。**論文の道筋をそのまま通した。**

### 定義（論文の Definition 1）

```coq
Inductive fbaln (G : L.pname -> L.stmt) (k : ctrl) : nat -> conf -> conf -> Prop :=
| fbn_done : forall a h, fbaln G k 0 (mk k a h) (mk k a h)
| fbn_step : forall n c c' c'',
    fstep G c c' -> length k < length (cctl c) ->
    fbaln G k n c' c'' -> fbaln G k (S n) c c''.
```

「制御スタックが `k` まで縮んだ配置からは**もう踏まない**」という条件で、
`k` の上に積んだものを回し切って `k` が現れた瞬間に止まる列を切り出す。

**なぜ `fmulti` のままでは駄目か**: `fmulti G (mk (s :: k) a h) (mk k b h')` は
「途中で `k` より短くなってから積み直した」実行を排除しない。`F_Drop` が
スタックを縮めるので、各中間配置を `k` の上に留めないと分解が成立しない。
これが論文が Definition 1 を置く理由でもある。

**段数を添字に持たせた**のは、分解が1本の列を2本に切って**両方**に再帰するため。
`fbaln` の導出そのものに構造帰納法をかけても、切った断片は見えない。

### 骨格

| 補題 | 役割 | 実際の分量 |
|---|---|---|
| `fstep_suffix` | 1ステップはスタックの先頭しか書き換えない → その下は残る | 13規則を一度に潰す1行（`repeat apply suffix_cons`） |
| **`fbaln_cut`（＝論文の Lemma 2）** | `k` で balanced な列が中間の段 `k0` の上から始まるなら、**必ず `k0` ちょうどを通る**。そこで切ると段数が分かれる | 20行。想定した「切断補題」は `suffix` の保存＋長さの三分律に解けた |
| `fbaln_cut1` | 使う形はいつも「1文を `k0` の上に積んだ」だけ、という特殊化 | 5行 |
| `sound_bal_n` | 段数に関する強帰納法。文の側とループ本体（Definition 2）の**2本立て** | 60行 |
| `complete_pc_bal` | `complete_pc` の結論を `fmulti` から `fbaln` へ強める | `fmulti_trans` を `fbaln_app` に置き換えるだけ |
| `fmulti_nil_fbaln` | 最上位では balanced 性は無料（空スタックは行き詰まりなので下へ抜けられない） | 8行 |

**見込みは外した**。着手前は `fbaln_cut` の `F_Seq` の場合に専用の切断補題が要ると
書いていたが、実際には**文ごとの場合分けは不要**だった。「`suffix k0` はステップで
保存される」＋「`suffix k0` で長さが等しければ `= k0`」の2つだけで、どの規則で
切れるかを問わずに切断できる。**`F_Seq` は特別ではなかった。**

### 得られたもの

```coq
Theorem exec_iff_fbal : forall G k s a b h,
  L.exec G s a b <-> exists h', fbal G k (mk (embed s :: k) a h) (mk k b h').

Theorem exec_iff_pc : forall G s a b,
  L.exec G s a b <-> exists h, fmulti G (mk (embed s :: nil) a nil) (mk nil b h).
```

後者が**論文の Theorem 1 そのもの**（論文の `skip` ＋空スタックが、こちらの
空の制御スタック）。前者はそれより強く、**最上位に限らず任意の `k`** で同値を言う。

すべて **`Closed under the global context`**（`functional_extensionality` すら不要）。
`coq/audit.sh` が `fbaln_cut` / `sound_pc` / `complete_pc_bal` / `exec_iff_fbal` /
`exec_iff_pc` を検査する。

### 併せて残した検算

`fbal_seq_skip` は `Seq Skip Skip` の3段の balanced derivation を手で組んだもの
（`F_Seq` → `F_Drop` → `F_Drop`、履歴は `[EDrop; EDrop; ESeq]`）。
`sound_seq_skip` はそれを `sound_pc` に食わせて `L.exec G (Seq Skip Skip) a a` を
取り出す。定義が空回りしていないことの計算チェックである。

### 使わなかったもう1つの道

決定性からの `machine_agrees`（2026-08-08 に先に実施）は
`L.exec G s a b -> fmulti G (mk [embed s] a []) (mk nil b' h) -> b = b'` で、
Theorem 1 より弱い（機械が停止することを言わない）。**`exec_iff_pc` はこれを含む**
ので冗長になったが、道具立てが独立なので両方残してある。

## 6. まとめ

**Loop Lemma と大ステップとの同値、どちらも形式化した。**

- Loop Lemma は**論文より仮定が弱い**（到達可能性が要らない。§3）
- 大ステップとの同値は**両方向**。論文と同じ balanced derivation を通り、
  さらに**最上位に限らず任意の制御スタックで**成り立つ（§5）
- CFG 版の意味論は作らず、履歴で同じ問題を解いた——これは論文の再現ではなく
  **別解**であり、Definition 4 が不要になったのはその副産物である

残っているのは §5 の CFG／ラベル意味論（Fig. 7・Lemma 3・Lemma 4）と
Example 1 / 2 の再現で、いずれも§3の設計判断から外れる部分である。
