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
| **Definition 1**（balanced derivation） | — | **未形式化** |
| **Definition 2**（loop derivation） | — | **未形式化** |
| **Definition 3**（trace ＝ 適用した規則の列） | `chist : list ev` | **強めたもの**（下記 §4） |
| **Lemma 2**（`⟨σ,s,π₁⟩ →* ⟨σ′,skip,π₂⟩` の分解） | — | **未形式化** |
| **Theorem 1** `ϵ ⊢ s ⇓ σ` **iff** `⟨ϵ,s,[]⟩ →* ⟨σ,skip,[]⟩` | `complete_pc` / `complete_pc_top` | **半分**（→ のみ。§5 参照） |

論文の Theorem 1 の証明は「only if は Lemma 1、if は Lemma 2 と
『この形の簡約列は balanced である』」という構成である。**こちらは Lemma 1 側だけを
持っている**。

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

### 弱い・未着手

| | |
|---|---|
| **Theorem 1 の "if" 方向** | `fmulti G (mk [embed s] a []) (mk [] b h) -> L.exec G s a b` が**未証明**。論文は Lemma 2（balanced derivation）を経由する。**残る唯一の本質的な穴**。ただし下の `machine_agrees` で実用上の帰結は押さえた |
| **Definition 1 / 2 / Lemma 2** | balanced derivation・loop derivation を形式化していない |
| **CFG 版意味論（§5 の Fig. 7・Lemma 3・Lemma 4）** | 作っていない。§3 の設計判断による |
| **言語の範囲** | 論文は Janus の具体構文（`x⊕= e`、`x[e]⊕= e`、`start`/`stop`）を扱う。こちらは `REV_PRIM` の抽象 `prim` なので、代入の具体形は抽象化されている。**逆に言えば `RevJanus` / `RevExt` / `RevStack` / `RevCA` / `RevToy` の5実例すべてに一度に効く** |
| **Example 1 / 2** | 論文の具体的な簡約列を再現していない |

---

## 5. 次に埋めるべき穴

**Theorem 1 の "if" 方向**が唯一の本質的な欠落である。道筋は2つ。

1. **論文どおり** — balanced derivation（Definition 1）を形式化し、Lemma 2 を経由する。
   **着手前の設計（2026-08-08 に確定）**:

   ```coq
   (* Definition 1: 制御スタックが k を接尾辞として保ち、最後に k ちょうどへ戻る *)
   Definition suffix (k c : ctrl) : Prop := exists j, c = j ++ k.

   Inductive fbal (G : L.pname -> L.stmt) (k : ctrl) : conf -> conf -> Prop :=
   | fb_refl : forall c, suffix k (cctl c) -> fbal G k c c
   | fb_step : forall c c' c'',
       fstep G c c' -> suffix k (cctl c') -> fbal G k c' c'' -> fbal G k c c''.
   ```

   要る補題は3つ。
   - **`complete_pc_balanced`** — `complete_pc` の結論を `fmulti` から `fbal` へ強める。
     証明は同じ相互帰納で、各ステップに `suffix` の証明義務が増えるだけ
   - **`fbal_inv`（＝ 論文の Lemma 2）** — `fbal G k (mk (s :: k) a h) (mk k b h')` を
     `s` の構造で分解する。`F_Seq` の場合に「前半が `s2 :: k` へ balanced に到達する
     地点で切る」ための**切断補題**がここに要る。**ここが分量の山**
   - **`sound_pc`** — `fbal_inv` から `L.exec G s a b` を組む

   **なぜ `fmulti` のままでは駄目か**: `fmulti G (mk (s :: k) a h) (mk k b h')` は
   「途中で `k` より短くなってから積み直した」実行を排除しない。`F_Drop` が
   スタックを縮めるので、`suffix` を各中間配置に課さないと分解が成立しない。
   これが論文が Definition 1 を置く理由でもある。
2. ~~**決定性から**~~ — **2026-08-08 に実施済み**。`nil_stuck`（`mk nil _ _` は行き詰まり）と
   `fmulti_det_stuck`（行き詰まりまでの実行は一意）から
   **`machine_agrees : L.exec G s a b -> fmulti G (mk [embed s] a []) (mk nil b' h) -> b = b'`**
   を得た。Theorem 1 そのものより弱い（機械が停止することは言わない）が、
   **「大ステップが答えを持つとき、機械が別の答えを出すことはない」**は押さえている

`RevSmallStep.v` が同じ穴を `bexec` という補助関係で埋めているので、そちらの手口も使える。

---

## 6. まとめ

**Loop Lemma は形式化した。しかも論文より仮定が弱い。** 大ステップとの同値は
**半分＋α**——大ステップ → 機械（`complete_pc`）に加え、逆向きの実用的な帰結
（`machine_agrees`：機械が別の答えを出すことはない）まで。完全な逆向き
（balanced derivation 経由）が残っている。CFG 版の意味論は作らず、
履歴で同じ問題を解いた——これは論文の再現ではなく**別解**であり、
Definition 4 が不要になったのはその副産物である。
