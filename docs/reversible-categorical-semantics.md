# 可逆計算の圏論的意味論 — 先行研究と `coq/` の対応

*作成: 2026-07-29 / 対象: `coq/` の圏論層（`RevCat` / `RevTrace` / `RevSMC` / `RevTraced` /
`RevCtrl` / `RevFix` / `RevDenote`）が、Kaarsgaard らの既存研究のどれに当たるかを
明示し、機械検証として何が新しいかを切り分けるための文書。*

> **この文書の信頼度**: 書誌情報は dblp / DOI / arXiv で裏取り済み。内容は
> **abstract と ar5iv 抽出の本文断片を読んだ範囲**であり、LMCS 論文の全文精読は
> していない。「対応する」と書いた箇所は、**定義の形が一致していることを確認できた
> ものだけ**に限り、推測は「要確認」と明記した。

## 0. なぜこの文書が要るか

`coq/` の圏論層は、Paolini–Piccolo–Roversi の Matita 形式化（→
`docs/janus-formalizations.md`）を参照して作った。そちらは確かに先行の**機械検証**だが、
**紙の上の先行研究はもう一系統あり、そちらの方が我々のやっていることに近い**。

Robin Kaarsgaard と Robert Glück の一連の仕事がそれで、**Janus を含む
structured reversible flowchart languages の圏論的意味論**を確立している。
これを踏まえずに書くと、既知の結果を新規のように提示してしまう。実際、
本開発のいくつかのファイルは当初そうなっていた（本文書と同時に訂正した）。

## 1. 対応表

| `coq/` の定理 | 先行研究の対応物 | 一致の度合い |
|---|---|---|
| `RevTrace.traceH` の実行公式<br>`R₁₁ ∨ ∃n. R₁₂ ; fb^n ; R₂₁` | Glück–Kaarsgaard 2018, Prop. 2<br>`Tr^U_{A,B}(f) = f₁₁ ∨ ⋁_{n∈ω} f₂₁ f₂₂ⁿ f₁₂` | **同一**（我々の `∃n` が彼らの ω-join） |
| `RevCtrl.if_is_test_sum`<br>`ifR g₁ R S g₂ = testH g₁ ; (R+S) ; (testH g₂)†` | Glück–Kaarsgaard 2018<br>`⟦if p then c₁ else c₂ fi q⟧ = ⟦q⟧† (⟦c₁⟧ ⊕ ⟦c₂⟧) ⟦p⟧` | **同一**。彼らの extensivity / decision が我々の `testH` |
| `RevTrace.loop_is_trace`（ループ＝trace） | 同上（ループを trace で定義） | 彼らは**定義**、我々は帰納的意味論からの**導出**。方向が逆 |
| `RevDenote.adequacy` / `full_abstraction` | Glück–Kaarsgaard 2018 の soundness / adequacy / equational full abstraction | 射程が同じ（要確認: 彼らの full abstraction は「certain conditions」付き） |
| `RevCat` の PInj（dagger restriction category, inverse law） | 同上。**PInj は彼らの canonical example**（`Inv(Pfn) ≅ PInj`） | 既知 |
| `RevSMC`（余積・積の対称モノイダル＋分配） | Kaarsgaard–Rennela 2021 の **rig 構造** | rig ＝ 2つのモノイダル構造＋分配。我々が証明したのはこれに相当 |
| `RevTraced`（trace 公理） | join inverse category が **dagger trace** を持つことは既知（Kaarsgaard 2019 が一般化） | 既知。しかも我々の「plain traced」より強い |
| `RevFix.Dfix`（環境汎関数の Kleene 鎖の合併＝最小不動点） | Axelsen–Kaarsgaard 2016 / Kaarsgaard–Axelsen–Glück 2017（**join から不動点**） | **同じ構成**。我々が「完備束だから領域理論不要」と説明したものは、join inverse category の join 構造そのもの |
| `RevSmallStep`（小ステップ ↔ 大ステップ同値） | Lanese–Vidal 2026 が「従来の小ステップ意味論は情報を捨てるため可逆でない」と指摘し、可逆な小ステップを与えている | **要確認**。我々が機械検証したのは RC 2024 版との同値であって、小ステップ自体の可逆性ではない |

## 2. 語彙 — 標準名は「join inverse rig category」

`RevSMC.v` / `RevTraced.v` は "distributive traced symmetric monoidal category" を
目標に組んだが、**この分野の標準語彙はそれではない**。

Kaarsgaard–Rennela 2021 の **join inverse rig category** が対応する概念で、
著者らはこれを「可逆計算の圏論的モデル」と位置づけ、Rfun・Theseus・reversible
flowcharts を統一的に扱っている。構成要素は:

- **inverse category**（＝ dagger + restriction、部分単射の抽象）
- **join**（両立する射の結び。ここから不動点と反復が出る）
- **rig**（2つのモノイダル構造＋分配性）

そして **trace は join から導かれる**（join inverse category は mild な条件下で
dagger trace を持つ、Kaarsgaard 2019）。

**この事実は今後の作業方針を変える**: `RevTraced.v` に残した vanishing-II と
dinaturality を経路手術で直接証明するより、**join 経由で導出する方が文献の筋に乗る**。
現状の `traceH` は「経路の存在」で定義しており、join としての性質（可算結び）を
まだ取り出していない。

## 3. 何が新しいか（切り分け）

**新しくないもの** — 以下はすべて 2016–2021 に紙で出ている:
PInj の圏論的構造（inverse / rig / dagger trace）、ループ＝trace、`if` の dagger 定式化、
flowchart 言語の soundness・adequacy・full abstraction、join からの可逆再帰。

**機械検証として新しい可能性があるもの**（いずれも「今回の探索で対応物が見つからなかった」
という限定付き。網羅的な否定ではない）:

1. **上記が機械検証されていること。** Kaarsgaard 系の成果に proof assistant による
   形式化は今回の探索では出てこなかった。Janus の *certified* な仕事として見つかるのは
   Paolini–Piccolo–Roversi の Matita 版（TYPES 2015）で、そちらは**圏論的意味論を
   `Pinj` 上で構築しているが、join inverse category の語彙は使っていない**。
2. **再帰を含む Janus。** Glück–Kaarsgaard 2018 は明示的に「Janus **without**
   recursion」。再帰は別系統（2016/2017）で扱われている。本開発は
   `RevFix` / `RevProc` / `RevCoreP` / `RevFrame` で再帰を含めて一つの検証済み開発に
   収めており、その組み合わせは増分かもしれない。
3. **法則の必要性**（`RevNecessity.v`）。「3法則は十分かつ必要」「非単射な原子は許容されない」
   に当たる議論は、先行研究側に対応物が見当たらなかった。
4. **抽出インタプリタと差分試験**（`RevExtract*` / `vjanus` / `harness`）。圏論側の
   仕事ではないが、意味論と実装を突き合わせる層は先行研究の射程外。
5. **形式化が実装のバグを検出したこと**（0除算の乖離、`&&`/`||` の bool 検査欠落。
   → `docs/vjanus-lowering-soundness.md`）。これも圏論の話ではない。

## 4. 注意 — 主張を書くときに

- 「PInj は traced である」は**既知**。書くなら「機械検証した」と限定する。
- 「出口表明は入口テストの dagger である」も**既知**（Glück–Kaarsgaard の定義そのもの）。
  我々の増分は、**帰納的な `exec` から導出した**こと（彼らは定義として置く）。
- 「ループは trace である」も同様に、**導出であること**が増分。
- `docs/janus-formalizations.md` の「先方（Matita）に無いもの」リストは、
  **「Kaarsgaard 系にも無いか」を別途確認しないと使えない**。Matita 版との比較だけで
  「我々が広い」と書くと、この系統を見落とす。

## 5. 文献

すべて dblp / DOI で裏取り済み。

**Janus を含む flowchart 言語の圏論的意味論**
- R. Glück, R. Kaarsgaard. *A categorical foundation for structured reversible flowchart
  languages: Soundness and adequacy.* Logical Methods in Computer Science **14**(3:16), 2018.
  [doi:10.23638/LMCS-14(3:16)2018](https://doi.org/10.23638/LMCS-14(3:16)2018) /
  [arXiv:1710.03666](https://arxiv.org/abs/1710.03666)
  （会議版: MFPS 2018）

**可逆再帰と join**
- H. B. Axelsen, R. Kaarsgaard. *Join Inverse Categories as Models of Reversible Recursion.*
  FoSSaCS 2016. [doi:10.1007/978-3-662-49630-5_5](https://doi.org/10.1007/978-3-662-49630-5_5)
- R. Kaarsgaard, H. B. Axelsen, R. Glück. *Join inverse categories and reversible recursion.*
  J. Log. Algebraic Methods Program. **87**, 2017.
  [doi:10.1016/j.jlamp.2016.08.003](https://doi.org/10.1016/j.jlamp.2016.08.003)

**rig 構造 / dagger trace**
- R. Kaarsgaard, M. Rennela. *Join Inverse Rig Categories for Reversible Functional
  Programming, and Beyond.* MFPS 2021, EPTCS 351, 152–167.
  [arXiv:2105.09929](https://arxiv.org/abs/2105.09929)
- R. Kaarsgaard. *Inversion, Iteration, and the Art of Dual Wielding.* RC 2019.
  [doi:10.1007/978-3-030-21500-2_3](https://doi.org/10.1007/978-3-030-21500-2_3) /
  [arXiv:1904.01679](https://arxiv.org/abs/1904.01679)

**当研究室が共著の系列**
- R. Glück, R. Kaarsgaard, T. Yokoyama. *Reversible Programs Have Reversible Semantics.*
  FM Workshops 2019. [doi:10.1007/978-3-030-54997-8_26](https://doi.org/10.1007/978-3-030-54997-8_26)
- R. Glück, R. Kaarsgaard, T. Yokoyama. *From reversible programming languages to
  reversible metalanguages.* Theor. Comput. Sci. **920**, 2022.
  [doi:10.1016/j.tcs.2022.02.024](https://doi.org/10.1016/j.tcs.2022.02.024)

**Janus の小ステップ意味論**
- I. Lanese, G. Vidal. *A Reversible Semantics for Janus.* 2026.
  [arXiv:2602.16913](https://arxiv.org/abs/2602.16913)
  — 従来の小ステップ意味論が前進計算で情報を捨てるため可逆でないことを指摘し、
  Loop Lemma を満たす小ステップを与える。`RevSmallStep.v` の位置づけに影響しうる。

**機械検証（Janus）**
- L. Paolini, M. Piccolo, L. Roversi. *A Certified Study of a Reversible Programming
  Language.* TYPES 2015, LIPIcs 69, 7:1–7:21.
  [doi:10.4230/LIPIcs.TYPES.2015.7](https://doi.org/10.4230/LIPIcs.TYPES.2015.7)
  → 詳細は `docs/janus-formalizations.md`
