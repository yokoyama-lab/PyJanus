# Janus の他の機械検証との比較（Paolini–Piccolo–Roversi, Matita）

*作成: 2026-07-27 / 対象: `coq/` の Rocq 開発を、Janus の先行機械検証と突き合わせ、
取り込むべき差分を管理するための文書。*

## 0. 比較対象

> Luca Paolini, Mauro Piccolo, Luca Roversi.
> *A Certified Study of a Reversible Programming Language.*
> TYPES 2015, LIPIcs vol. 69, pp. 7:1–7:21, 2018.
> [doi:10.4230/LIPIcs.TYPES.2015.7](https://doi.org/10.4230/LIPIcs.TYPES.2015.7)

Matita 0.99 の成果物（26 個の `.ma`, 約 6000 行）。論文記載の入手先は 404 で、
第一著者ページの `janus.zip` のみ生存。取得済みミラー:
**`yokoyama-lab/janus-matita-paolini`（private, third-party mirror）**。
以下の行番号・名前はそのミラーの `janus/` 配下を指す。

**先方の構成**（`README.md` の Layout に対応）:

| 層 | ファイル | 内容 |
|---|---|---|
| 構文・操作的意味論 | `janus.ma` (589行) | パラメトリック構文 + **燃料付き関数型**の前進/後退意味論。頂点定理 `op_sem_reversibility` |
| 具体インスタンス | `concrjanus.ma` | `ℕ` 上の `+=`/`-=` と `* / % ≤ ≠ =` |
| 表示的意味論の圏 | `category.ma`, `monoidal_category.ma`, `dagger_category.ma`, `rel*.ma`, `pinj.ma`, `domain.ma` | `Pinj`（部分単射の圏）を **積・余積の対称モノイダル、分配、dagger、trace、CPO** として構築 |
| 解釈 | `rel_interpretation.ma` | `den_eval_stm`（文→`Pinj` 射）、`den_program` = **Knaster–Tarski 最小不動点** |
| 完全抽象 | `correctness.ma`, `completeness.ma`, `compl_thm.ma` | `den_stm_correct`（操作的 ⊆ 表示的）/ `den_stm_complete`（表示的 ⊆ 操作的、燃料を構成） |

## 1. 突き合わせ（2026-07-27 時点）

| 論点 | Paolini et al. (Matita) | PyJanus `coq/` (Rocq) |
|---|---|---|
| 可逆性の頂点定理 | `op_sem_reversibility`（fwd↔bwd） | `exec_rev` / `exec_iff` / `exec_injective` |
| 抽象化の単位 | `params` + `sem_params`（意味論側の義務は **`reverse_eval_rev` 1本**） | `REV_PRIM`（`pinv_invol` / `pstep_det` / `pstep_rev` の3法則）+ 関手 `RevLang`。**先方の2記録から3法則を導けることを `RevPPR.v` で証明済み（2026-07-28）** |
| 法則の必要性 | 議論なし | **`RevNecessity.v`**（3法則は十分かつ必要）— 先方にない |
| 意味論の形 | 燃料付き**関数**（`option state`） | 帰納的**関係** `exec` + 別途 `RevExtract.v` の燃料付き `run`（`run_sound` / `run_complete`） |
| 状態 | `list value`（変数は添字）→ **funext 不要** | `var → Z`（関数）→ `RevJanus` は funext を使用。**`RevPPR.v` の list 版 `janus_list_reversible` は公理ゼロ（2026-07-28）** |
| 演算の全域性 | `option` 値（部分的） | `Janus.v` の `eval` は全域。**`RevPPR.v` の `JanusZ` は `option` 値で 0 除算に値なし（2026-07-28）** |
| 手続き | 環境＝文のリスト、**最小不動点**で意味付け | `Γ : pname → stmt` + 帰納的 `exec`。表示的側は **`RevFix.v` で最小不動点化（2026-07-27 追加）** |
| 表示的意味論 | `Pinj` 射（圏論的） | `RevDenote.v`（関係の組合せ子）+ `RevCat.v`（dagger restriction category） |
| 完全抽象 | correctness + completeness | `adequacy` + `full_abstraction` + `denote_cong` |
| 余積・**trace** | あり（`Pinj_Traced` ほか） | **`RevTrace.v` で追加（2026-07-28）**。積・分配・coherence は未 |
| 配列・`local`/`delocal`・スタック | なし | `RevExt.v` / `RevArr.v` / `RevFrame.v` |
| 有界整数・`-m bits` | なし | `RevMod.v` / `RevSMod.v` / `RevExtMod.v` / `RevExtSMod.v` |
| I/O・`*=`/`/=` | なし | `RevIO.v` / `RevMul.v` |
| 抽出インタプリタ・差分試験 | なし | `RevExtract*.v` → OCaml、`vjanus`、`coq/harness/` |
| 小ステップ意味論 | なし | `RevSmallStep.v`（大ステップと同値） |
| 公理監査 | Matita に `Print Assumptions` が**無い**。`utils.ma` は矛盾公理 `IMPOSSIBLE`（daemon）を宣言（他ファイルからの参照はテキスト検索の範囲で無し） | `audit.sh` が全頂点定理を毎ビルド検査（funext 以外・`Admitted` を許さない）。CI 済み |

要約: **可逆性・拡張・実行可能性・監査は PyJanus が広く、圏論的な意味論の構造は先方が深い。**

## 2. 取り込み済み

### `coq/RevFix.v` — 手続きの意味を最小不動点に（2026-07-27）

`RevDenote.v` は自身の冒頭で「表示は環境へ再帰できないので手続きの意味は
パラメータ」と断っており、`adequacy` は `D := Dexec`（＝各手続きの**操作的**意味）
で述べられていた。つまり表示的意味論が再帰を `exec` から借りていた。

先方はそこを `den_program` = 環境汎関数の Knaster–Tarski 最小不動点（`Pinj` 射の
CPO 上）で閉じている。`RevFix.v` は同じことを、**関係の包含が完備束**である事実だけで
行う（領域理論は不要）:

- `step E p := denote E (Γ p)`、`approx` はその Kleene 鎖、`Dfix := ⋃ₙ approx n`
- `Dfix_fixed` / `Dfix_least` — 最小不動点であること
- `fix_adequacy : denote Dfix s a b <-> exec Γ s a b` — **`exec` を含まない**表示に対する
  adequacy。2方向はそれぞれ先方の `den_stm_correct`（操作的な実行は有限近似で実現される。
  先方の燃料が、こちらでは近似の添字）と `den_stm_complete` に対応
- `exec_is_lfp` — ゆえに `exec Γ` 自身がその最小不動点
- `denote_fix_reversible` — **再帰手続きの可逆性を純表示的に**証明（各近似が部分単射、
  鎖が増加 ⇒ 合併も部分単射。先方が `Pinj` の CPO 構造から得ているもの）
- `fix_diverges` — 自己呼出しだけの手続きは空関係（最小不動点であることの健全性検査）

全て公理なし（Janus インスタンスのみ funext）。`audit.sh` に追加済み。

### `coq/RevTrace.v` — 余積と trace、ループ＝trace（2026-07-28）

先方の `Pinj` は余積で traced で、ループは `trace(loop_fun …)` として解釈される
（`rel_interpretation.ma:229` の `loop_fun`, `rel_trace.ma` 678行）。PyJanus 側には
モノイダル構造も trace も**一切なかった**。追加したもの:

- 余積 `sumH`・入射・関手性・dagger 整合（`convH_sumH`）
- **trace** `traceH R = R₁₁ ∪ (R₁₂ ; fb* ; R₂₁)`（実行公式）と
  **`pinj_traceH`＝trace は部分単射を保つ**（先方の `good_rel_trace_inj`）
- `trace_conv`（trace と dagger の可換）、`trace_yanking` / `trace_vanishing` /
  `trace_natural_l`（yanking・vanishing-I・左自然性）
- **`loop_is_trace`**: `from g1 do R₁ loop R₂ until g2` ＝ `traceH turn`。
  `pinj_turn` が示すのは「継続ターンは `g1` が偽の状態に着地し、進入は `g1` が真の
  状態に着地する」という排他性こそが `turn` を部分単射にしている、ということ。
  よって `rev_loop_via_trace` は `RevAlgebra.rev_loop` を trace 閉包の一例として再導出する。

未了: vanishing-II と superposing（余積の結合・対称の coherence が要る）、積の
モノイダル構造と分配性。

### `coq/RevPPR.v` — 先方の言語は我々の枠組みの一インスタンス（2026-07-28）

先方の2記録を module type `PPR_PARAMS` に写し、`REV_PRIM` の3法則を**導出**した
（`pinv_invol`←演算子の対合、`pstep_det`←評価の関数性、`pstep_rev`←`reverse_eval_rop`
＋非出現側条件 `evalE_upd`＝先方の `ev_expr_irrelevant_from_non_present_variable`）。
よって**先方の言語は `exec_injective` を無償で継承する**（`ppr_reversible`）。

同時に旧 (C)(D) も解消:
- 状態が `list const`＋添字なので **`janus_list_reversible` は公理ゼロ**
  （`RevJanus.janus_reversible` は funext を要する）。
- 演算が `option` 値。同梱の `JanusZ` は `/` `%` が 0 で値を持たない（実装に忠実）。

## 3. 先方成果物のビルド確認（2026-07-28・完了）

ミラーの README は「テキスト検査のみ、Matita は動かしていない」と明記していたが、
**26ファイル全部がビルドできることを確認した**。手順:

```bash
# 本機の opam switch `matita`（Matita 0.99.5）
export PATH=/home/a/.local/share/opam/matita/bin:$PATH
cd <mirror>/janus
printf 'baseuri=cic:/matita/janus\nlibrary=false\n' > root   # 唯一の追加ファイル
matitac compl_thm.ma      # OK  74m21s（コールド。24ファイル＝この依存閉包）
matitac correctness.ma    # OK（閉包外の残り2本）
matitac concrjanus.ma     # OK
```

- `.ma` ソースは**一切改変不要**（`git status` はミラーで clean、追加は `root` のみ）。
  再インポート時の diff はきれいなまま。
- コンパイル済みオブジェクトは `~/.matita/matita/janus/*.ng` に 26/26 揃う。
- `compl_thm.ma` の依存閉包は 24 ファイル。**`correctness.ma` と `concrjanus.ma` は
  閉包外**なので、完全性だけ確認して満足しないこと（correctness＝操作的⊆表示的は
  別に走らせる必要がある）。

**ただし公理の話は強くならない**: Matita に `Print Assumptions` は無いので、
`utils.ma` の矛盾公理 `IMPOSSIBLE`（daemon）が他ファイルから使われていないという
観察は依然テキスト検索どまり。ビルド成功が保証するのは「証明スクリプトが完結して
型検査を通る」ことまでで、`audit.sh` に相当するものは先方には存在しない。

## 4. 残っている差分（優先度順）

### (A) 抽出インタプリタの完全性を横展開
`run_complete`（`exec` から燃料の存在）は `RevExtract.v` の `run` にのみある。
`RevExtractAr` / `RevExtractFrame` / `RevExtractMod` / `RevExtractSMod` は
`run_sound` のみ。`vjanus` が「動くはずのプログラムを取りこぼさない」保証になる。

### (B) trace 構造の残り
vanishing-II と superposing（余積の結合・対称の coherence）、積の対称モノイダル
構造と分配性 `δ`。先方は `rel_prod.ma` / `rel_distr.ma` / `monoidal_category.ma`
で持っている。`loop_is_trace` が済んだので優先度は下がった。

## 5. 参照
- ミラー: `yokoyama-lab/janus-matita-paolini`（private, `janus/` が展開済みアーカイブ）
- 本リポジトリ: `coq/README.md`（定理→ファイル対応表）、`coq/audit.sh`（公理監査）
- 関連: `docs/vjanus-lowering-soundness.md`（未証明の翻訳健全性）
