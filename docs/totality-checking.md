# 可逆プログラムの全域性検査 — 表明破れの到達不能性を IC3 で証明する

Janus の可逆性は**構文的**に保証される。しかし `fi` の出口条件、`from` の入口条件、
`delocal`、`assert`、`*=` / `/=` の可除性条件は**実行時**に破れうる。

> **表明が破れない ⟺ そのプログラムは仮定した定義域上で全域な単射**

破れうるプログラムは部分単射でしかない。この文書は、その「破れない」を機械証明する
仕組み（`jana_py/smv.py` + `jana_py/nuxmv.py` + `tools/verify_corpus.py`）の設計と、
コーパス上の実測をまとめる。

関連: 圏論側の対応は `docs/reversible-categorical-semantics.md`、Rocq 側の全体像は
`coq/README.md`。式の整形式性（`wf`）の形式化は `coq/RevLowerExpr.v`。

## 1. なぜ検査でなく証明が要るか

PyJanus には既に `jana_py/equiv.py` があり、`P; Q⁻¹` を組んで恒等と比較する
——**還元の形は正しい**——が、後段は**有界全数検査**である（docstring 明記）。
入力の範囲を切って全部試すので、

- 整数が有界でしか扱えない
- 「破れない」ことの根拠が「試した範囲では破れなかった」でしかない

`~/dev/CLAUDE.md` の原則どおり、**上界（反例）は未成熟な道具でよいが、下界（存在しない
こと）には成熟した道具が要る**。ここでは nuXmv 2.2.0 の IC3（無限状態・SMT エンジン）で
帰納的不変量を自動構成し、**整数の範囲を切らずに**証明する。

## 2. 符号化

プログラムをプログラムカウンタ `pc` と整数変数からなる遷移系にし、あらゆる実行時表明を
専用のエラー位置 `pc = 0`（ERR）への分岐にする。性質は `INVARSPEC pc != 0` の一本。

| Janus | 符号化 |
|---|---|
| `x += e` / `-=` / `*=` / `/=` | `next(x) = x ± e` 等。`*=` は `e ≠ 0`、`/=` は `e ≠ 0 ∧ x mod e = 0` を守れないと ERR |
| `x <=> y` | 並行代入 |
| `if e1 then S1 else S2 fi e2` | `e1` で分岐、合流時に「取った枝と `e2` が一致」しなければ ERR |
| `from e1 do S1 loop S2 until e2` | `assert e1; S1; while ¬e2 { S2; assert ¬e1; S1 }` を CFG の後退辺で表現 |
| `local x = e … delocal x = e'` | 入口で `next(x) = e`、出口で `x = e'` でなければ ERR |
| `assert(e)` | `e` でなければ ERR |
| `call` / `uncall` | **インライン展開**（`uncall` は `invert.py` の反転を展開）。深さ上限を超えたら BOUND 位置へ |
| `printf` | 無視（ストアを触らない）|

`--smv-init zero` は PyJanus が実際に走る零ストア、`--smv-init any` は**全入力**での
全域性を問う。後者が本命だが、多くのプログラムは定義域が限られるので
`--smv-assume "n >= 0"` のような**事前条件**が要る。「どの定義域上で全域か」を明示
させられるのは、この検査の副産物として有用である。

```bash
python3 -m jana_py.cli --std jana2014 --smv prog.ja                    # モデルを出力
python3 -m jana_py.cli --std jana2014 --smv --smv-init any prog.ja
python3 tools/verify_corpus.py --init zero --timeout 120               # コーパス一括
```

## 3. 素朴な翻訳が不健全になる3点

実装中に実際に踏んだ罠。いずれも**証明を嘘にする**種類の誤りである。

### 3.1 整数除算の丸め方向が違う

**nuXmv の整数 `/` は 0 方向切り捨て、Janus（＝Python）は床除算。**
さらに **nuXmv の `mod` は SMT エンジンでは整数に使えない**（word 型のみ）。

```
-7 / 2  →  nuXmv: -3   /  Janus: -4
```

素朴に `/` を写すと、負の被除数で**実際には失敗するプログラムを安全と証明してしまう**。
`jana_py/smv.py` の `_div_defines` は切り捨て商から床商への補正を SMV の `case` で書き、
`mod` は床商から導く。4つの符号の組み合わせすべてで Python と一致することを確認済み
（`tests/verify/test_smv.py` および nuXmv 上の直接検証）。

### 3.2 ソートの混同

Janus の比較は整数を返すので `x += (y > 0)` は合法である。翻訳を**二ソート**にし、
混ざった式は**推測せず拒否**する。これは `coq/RevLowerExpr.v` が `wf` として形式化した
規律と同じもので、以前 PyJanus 本体で非 boolean オペランドのバグを見つけたのと同根。

### 3.3 別名検査は静的でなく実行時

これが最も危なかった。`x += x` は非単射だが、**PyJanus はこれを静的にではなく実行時に
弾く**（`validate_program` を通ってしまう）。素朴に写すと `next(x) = x + x` となり、
**可逆でないプログラムを安全と証明する**。しかも手続き境界をまたぐ:

```janus
procedure bar(int a, int b)   // a と b が同じ変数に束縛されると非単射
    a += b
procedure main()
    int x
    call bar(x, x)            // ← PyJanus は実行時に "aliases" エラー
```

インライン展開後に環境を解決すると別名は**構文的に判定できる**ので、該当文に到達する
こと自体をエラーとして ERR への無条件辺にした。到達しない経路上の別名違反はエラーで
ないという PyJanus の挙動とも一致する。`local`/`delocal` の名前不一致も同様に実行時
検査なので同じ扱いにした。

**この3点はいずれもコーパス実験が炙り出した。** 単体テストだけでは 3.3 は出なかった。

## 4. 断片とその被覆率（実測）

対象は**スカラー断片**（int 変数のみ、配列・スタック・構造体なし）。
`tests/jana2014/fixtures/examples/` の97本を分類すると:

| 条件 | 本数 |
|---|---|
| スカラーのみ | 4 / 97 |
| ＋ printf を無視 | 12 / 97 |
| ＋ 具体長の配列を展開（要実装） | 13 / 97 |
| 残りの主な阻害要因 | `int a[]`（長さ未指定の配列引数）65、stack 31、struct 13 |

**配列が本質的である**ことがはっきりした（74本が添字を使う）。スカラー断片だけでは
ベンチマークとして小さい。次節の課題を参照。

## 5. 結果

`tools/verify_corpus.py --init zero --timeout 120`（nuXmv 2.2.0 / IC3、`check_invar_ic3`）。
対象は `tests/jana2014/fixtures/examples/` 97本 ＋ `tests/jana2014/fixtures_errors/` 52本
= 149本。

| 判定 | 本数 | 意味 |
|---|---:|---|
| `refuted` | 12 | 表明破れへ到達する初期ストアを提示 |
| `proved` | 7 | 帰納的不変量で到達不能を証明 |
| `unknown` | 6 | 120秒でタイムアウト |
| `unsupported` | 110 | 断片外（うち100本が配列・スタック・構造体） |
| `parse-error` | 7 | 構文エラー（error fixture として想定内） |
| `static-error` | 7 | `validate_program` が弾く（模型検査の対象外） |

### 5.1 検出側 — 12/12、誤検出 0

**断片内にある実行時エラー fixture 12本を全て検出した。**

| fixture | 反例 |
|---|---|
| `assert.ja` | — |
| `assertion-fail-if-fwd/bwd.ja`, `assertion-fail-from-fwd/bwd.ja` | `x=0` |
| `delocal-wrong-value.ja` | `x=2` |
| `delocal-wrong-name.ja` | — |
| `division-by-zero.ja` | `x=0` |
| `alias-1.ja`, `var-modified-on-rhs.ja` | `x=0` |
| `vjanus-delocal-self-ref.ja` | `t=1, x=0` |
| `infinite-recursion.ja` | `[bound]`（表明破れではなくインライン上限への到達として正しく区別） |

**examples の97本からは1本も `refuted` が出ていない＝誤検出ゼロ。**
最後の3本（`alias-1` / `var-modified-on-rhs` / `delocal-wrong-name`）は §3.3 の修正で
初めて検出できるようになったもので、修正前は逆に「安全」と**誤って証明**していた。

### 5.2 証明側 — 2/8、ここが本当の課題（が、§5.3 で見方が変わる）

examples 97本のうち断片内は12本。うち4本は `^=` / `&`（ビット演算）で拒否。
残る**8本を nuXmv にかけて、証明できたのは2本**（`cantor_pair.ja`, `zagier.ja`)、
**6本がタイムアウト**（`fall.ja`, `fib.ja`, `fib_variants.ja`, `injective_basics.ja`,
`injective_bennett.ja`, `sqrt.ja`）。

タイムアウトの内訳を1本追跡した（`fall.ja`、モデルは78行と小さい）。`--smv-init zero`
では初期ストアが完全に具体的なので実行は決定的な有限列であり、IC3 が探すべき帰納的
不変量は実質その実行列そのものになる。BMC（`msat_check_invar_bmc -a een-sorensson`）へ
切り替えても280秒で bound 44 まで進んで結論が出なかった。

> **示唆**: 具象初期ストアに対しては解釈器を走らせる方が速く正しい。模型検査が価値を
> 生むのは `--smv-init any`（記号的初期ストア）の側である。「安全である」ことの証明が
> 欲しいのは、そもそも全入力についてであって特定の1入力についてではない。

### 5.3 記号的初期ストアの方が**易しい** — 直観と逆

上の示唆を検証するため、同じ8本を `--init any` で走らせた。

| プログラム | `--init zero` | `--init any` | `any` の反例 |
|---|---|---|---|
| `cantor_pair.ja` | proved | proved | — |
| `zagier.ja` | proved | **refuted** | `x=-5, y=-2, z=-6` |
| `fall.ja` | timeout (120s) | **refuted** | `t_end=-3` ほか |
| `fib.ja` | timeout (120s) | **refuted** | `x2=-1` |
| `fib_variants.ja` | timeout (120s) | **refuted** | `x2=-1` ほか |
| `sqrt.ja` | timeout (120s) | **refuted** | `num=-66, root=-2` |
| `injective_basics.ja` | timeout | timeout | — |
| `injective_bennett.ja` | timeout | timeout | — |

合計すると `--init zero` は 2 proved / 6 timeout、`--init any` は 1 proved / 5 refuted /
2 timeout。**具象ストアでタイムアウトした6本のうち4本が、記号的ストアでは数秒で反例に
落ちた。** IC3 は「この1本の実行列」より「全入力に共通する不変量」を探す方が得意なので、
問題を**弱める**（入力を固定する）と却って難しくなる。

`zagier.ja` の挙動が2つの問いの違いを端的に示す: **零ストアでは安全と証明でき、
全入力では反例が出る**。前者は「PyJanus が実際に走らせる1本の実行は落ちない」、
後者は「全域単射である」であって、別の主張である。

さらに重要なのは**反例の中身**である。`fib.ja` の反例は `x2 = -1` — `fib` の出口表明
`fi x1 = x2` は `x1` と `x2` が両方 0 から始まらないと破れる。`fall.ja` の反例は
`t_end = -3` — ループ `until t = t_end` が `t` を増やす以上、`t_end` は非負でなければ
ならない。つまり:

> **反例は「欠けている事前条件」そのもの**である。この検査器は「安全か」に答えるだけで
> なく、**そのプログラムが全域単射である定義域を教える**。

`sqrt.ja` の `num = -66` も同様で、`root` 手続きは非負の被平方数を前提にしている。
`--smv-assume` でその事前条件を与え直せば証明に転じる（`tests/verify/test_smv_nuxmv.py`
の `test_a_precondition_recovers_the_proof` がこの往復を回帰テストにしている）。

`^=` の4本はビットベクタ後端（`word[N]`）を用意すれば扱える。整数と語のどちらで
符号化するかは、プログラムがビット演算を使うかで自動的に決まる。

## 6. 限界（正直に）

- **配列・スタック・構造体は未対応。** 断片の被覆率が低い最大の原因。
- **手続きはインライン展開**なので再帰は深さ上限まで。上限に到達した場合はモデルが
  BOUND 位置でそれを申告し、証明はその深さまでの主張にとどまる。
- **printf の引数エラーは対象外。** ストア意味論だけを見ているので、`printf` の型不一致で
  PyJanus が落ちるプログラムを「安全」と報告する。これは対象外であって誤りではないが、
  「proved」の意味を狭く読む必要がある。
- **非停止は表明破れではない。** ループが止まらないプログラムは ERR に到達しないので
  「proved」になりうる。全域性は「表明が破れない」であって「停止する」ではない。
  停止性は別テーマ（`~/dev/CLAUDE.md` の TRS ツール群、KoAT2/AProVE/CeTA）。
- **モデルと解釈器の一致は差分テストで担保**している（`tests/verify/test_smv_nuxmv.py`）が、
  翻訳の健全性そのものは機械証明されていない。`coq/RevLowerExpr.v` / `RevLowerStmt.v` が
  vjanus の lowering についてやったことを、この翻訳についてもやるのが筋。

## 7. 次の一手

1. **具体長の配列をスカラーへ展開**する（C++ codegen と回路合成が既にやっている変換）。
   長さ未指定の引数は `N` を与えて具体化し、「長さ N まで、値は無限領域で」証明する。
   **値の有界性を外す**のが既存の `equiv.py` に対する増分なので、長さの有界性は残ってよい。
2. **等価性検証へ拡張**（本命）。可逆性により `P ≡ Q ⟺ P;Q† ⊑ id ∧ dom P = dom Q` で、
   `Q†` は `invert.py` で構文的に得られる。自己合成／積プログラムが要らないので状態空間が
   半分で済む。`dom P = dom Q` の部分が本文書の全域性検査そのものであり、両者は
   ひとつの体系をなす。対象は `PyJanus2PISA` の peephole と regalloc の translation validation。
3. **BMC への退避**。IC3 がタイムアウトした場合に `check_invar_bmc` で「深さ k までは
   破れない」を得る。SAT 側の証明ログ（DRAT）まで取れば下界側の主張が認証つきになる。
