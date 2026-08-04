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

**文ごとに位置を作らない（large-block 符号化）。** 直線部分は「変数 → ブロック入口の値で
書いた式」という pending 写像と経路条件へ**記号実行**し、制御が実際に分岐・合流する所でだけ
位置を切る。`v += g; h -= v; h += halfg; t += 1` は4遷移ではなく**1遷移**になり、`h` の更新は
`((h - (v + g)) + halfg)` である。式の翻訳が pending 写像を*読む*ので、逐次合成は式を組み立てる
過程で起き、生成済みテキストへの置換処理は一切要らない。§5.4 のとおり、これが決定率を
左右した唯一の要因だった。

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

出力形式は2つある。`style="assign"`（既定）は変数ごとに次状態関数を1つ書き、`TRUE` の既定枝が
フレーム条件をすべて吸収する。`style="trans"` は辺の巨大な選言で、遷移ごとに未変更変数の
`next(v) = v` を並べる。`fall.ja` で前者は後者の約7分の1の大きさだが、**判定結果は完全に同一**
だった（§5.4）。

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

**さらに 3.3 には取りこぼしが2つ残っていた**（§10 の機械検証で発覚）。どちらも
コーパスには現れない形だったので、実験でも見つからなかった。

- **`x <=> x` に別名検査が無かった。** 代入には付けたが swap には付けていなかった。
  swap の記号実行は pending 写像の2項を同時交換するだけなので、両辺が同じ変数に解決
  されると**恒等写像**になる。モデルに ERR 辺が1本も立たず、nuXmv は
  `INVARSPEC pc != ERR` を**証明してしまう**——PyJanus は "Identifiers `x' and `x' are
  aliases" で落ちるのに。3.3 と同じ不健全性が swap に残っていた。
- **仮引数の二重束縛それ自体をエラーにしていた。** 呼び出し時に「2つの仮引数が同じ
  変数に解決される」だけで ERR にしていたが、PyJanus は**文単位**で検査するので、
  本体がその2つを同じ文に持ち込まなければ普通に走る。健全side だが誤検出になる。

いずれも「検査は文ごと、対象は代入と swap の2つ」に揃えて修正した。`_call` の一括
拒否は削除し、swap に代入と同じ無条件 ERR 辺を追加した。

## 4. 断片とその被覆率（実測）

対象は**スカラー断片に配列を加えたもの**（int 変数と int 配列。スタック・構造体なし）。
配列は宣言を要素ごとの SMV 変数へ展開し、添字は定数・変数のどちらも扱う（§12）。

`tests/jana2014/fixtures/examples/` の97本のうち **`compile_to_smv` が受理するのは
17本**（2026-08-04 実測。配列対応前は8本）。残る80本の**最初にぶつかる**阻害要因:

| 阻害要因 | 本数 |
|---|---:|
| 非スカラ宣言（stack 31 / struct 13 が主） | 38 |
| 引数が単なる変数でない（`f(a[0])` 等） | 10 |
| `^=`（ビット演算の代入） | 9 |
| 断片外の文（`for` / `push` / `pop` 等） | 9 |
| ビット演算子 `&` `\|` | 6 |
| 非スカラの `local` | 3 |
| スカラとセルの swap | 2 |
| 多次元配列 | 2 |
| 断片外の式 | 1 |

**配列はもはや阻害要因ではない**——97本中66本が配列を宣言に持つが、それだけで弾かれる
ものは無くなった。次の壁は **stack（31本）と struct（13本）** で、これは別種の作業になる
（可変長の状態と、フィールドを持つ複合型）。**多次元配列は射程外**（`matrixmult.ja` /
`matrixmult_v1.0.ja` の2本のみ。`coq/RevLowering.v` に Cantor fold の単射性があるので
入口はある）。

## 5. 結果

`tools/verify_corpus.py --init zero --timeout 120`（nuXmv 2.2.0 / IC3、`check_invar_ic3`）。
対象は `tests/jana2014/fixtures/examples/` 97本 ＋ `tests/jana2014/fixtures_errors/` 52本
= 149本。

| 判定 | 本数 | 意味 |
|---|---:|---|
| `refuted` | 12 | 表明破れへ到達する初期ストアを提示 |
| `proved` | 10 | 帰納的不変量で到達不能を証明 |
| `unknown` | 3 | 120秒でタイムアウト、または IC3 が断念 |
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

### 5.2 証明側 — 5/8

examples 97本のうち断片内は12本。うち4本は `^=` / `&`（ビット演算）で拒否。
残る**8本を nuXmv にかけて、5本を証明**（`cantor_pair`, `fall`, `fib`, `injective_basics`,
`zagier`）、3本が未決（`fib_variants` と `injective_bennett` はタイムアウト、`sqrt` は
IC3 が断念）。`fib.ja` は不変量が2本＝ERR だけでなく **BOUND も証明**しており、
インライン深さ16で再帰が尽きることまで示せている。

ここに至るまでの経緯は §5.4 に分けて書いた。**最初の符号化（文ごとに1位置）では 2/8
しか証明できなかった**。

### 5.3 具象ストアと記号ストアは別の問い

同じ8本を `--init any` でも走らせた。

| プログラム | `--init zero` | `--init any` | `any` の反例 |
|---|---|---|---|
| `cantor_pair.ja` | proved | proved | — |
| `zagier.ja` | proved | **refuted** | `x=-11` ほか |
| `fall.ja` | proved | **refuted** | `t_end=-3` ほか |
| `fib.ja` | proved（＋BOUND） | **refuted** | `x2=-1` |
| `injective_basics.ja` | proved | **refuted** | `a=-4` ほか |
| `fib_variants.ja` | timeout | **refuted** | `an=2` ほか |
| `sqrt.ja` | gave up | **refuted** | `bit=3` ほか |
| `injective_bennett.ja` | timeout | timeout | — |

`--init zero` は 5 proved / 3 unknown、`--init any` は 1 proved / 6 refuted / 1 timeout。
**8本中7本が決着**する。

`zagier.ja` などの挙動が2つの問いの違いを端的に示す: **零ストアでは安全と証明でき、
全入力では反例が出る**。前者は「PyJanus が実際に走らせる1本の実行は落ちない」、
後者は「全域単射である」であって、別の主張である。前者だけなら解釈器を走らせれば
足りるので、模型検査が本当に効くのは後者である。

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

### 5.4 何が効いたか — 符号化であって道具ではなかった

最初の符号化は**文ごとに1位置**を作る素朴なもので、`--init zero` で 2/8、`--init any` で
6/8 しか決着しなかった。`fall.ja`（モデル78行）ですら IC3 も BMC も結論を出せない。
そこで2つの改良を**別々に**測った。

| 変更 | `fall.ja` のモデル | `--init zero` | `--init any` |
|---|---|---|---|
| 素朴（文ごとに1位置、TRANS 形式） | 36辺 / 36位置 / `next` 等式 432個 | 2/8 proved | 6/8 決着 |
| ＋ ASSIGN 形式（変数ごとの次状態関数） | case 枝 62個（約1/7） | **2/8（変化なし）** | **6/8（変化なし）** |
| ＋ large-block（直線部を1遷移に） | 21辺 / 8位置 | **5/8 proved** | **7/8 決着** |

- **ASSIGN 形式は判定を1つも変えなかった。** モデルは約7分の1になり、決定性が構文的に
  なるので効くはずだと考えたが、`--init zero` / `--init any` の全16通り（8本×2）で
  TRANS 形式と**完全に同じ判定**だった。読みやすさとこの先の配列展開を考えて既定にはしたが、
  **決定率への寄与はゼロ**である。
- **効いたのは large-block だけだった。** 位置数が 36 → 8 に落ちたことで、IC3 が
  探す不変量が「各 pc での条件」ではなく「ループ頭での条件」だけになる。
  タイムアウトしていた `fall` / `fib` / `injective_basics` がすべて証明に転じた。

> **教訓**: ボトルネックはソルバの能力ではなく**問題の与え方**だった。同じ nuXmv・
> 同じ IC3・同じ時間制限で、符号化を変えただけで 2/8 が 5/8 になっている。
> 成熟した道具を使うときは、道具を替える前に**渡している問題を疑う**方が費用対効果が高い。

## 6. 限界（正直に）

- **配列・スタック・構造体は未対応。** 断片の被覆率が低い最大の原因。
- **手続きはインライン展開**なので再帰は深さ上限まで。上限に到達した実行は BOUND 位置へ
  抜け、**継続は到達不能な位置に置かれる**（累積した更新も落ちる）。したがって
  `INVARSPEC pc != ERR` が証明できても、それは**上限に到達しない実行についてのみ**の
  主張である。「深さ16まで正しい」ではなく「深さ16を超えない実行については正しい」。
  ただし `INVARSPEC pc != BOUND` も併せて証明できれば上限に到達する実行が存在しない
  ことになり、ERR の証明は無条件になる（§5.2 の `fib.ja` がこの形）。
  なお `jana_py/nuxmv.py` の判定は全性質の**最弱**を取る（refuted > unknown > proved）ので、
  BOUND が反証されているのに全体が `proved` と報告されることはない。
- **printf の引数エラーは対象外。** ストア意味論だけを見ているので、`printf` の型不一致で
  PyJanus が落ちるプログラムを「安全」と報告する。これは対象外であって誤りではないが、
  「proved」の意味を狭く読む必要がある。
- **非停止は表明破れではない。** ループが止まらないプログラムは ERR に到達しないので
  「proved」になりうる。全域性は「表明が破れない」であって「停止する」ではない。
  停止性は別テーマ（`~/dev/CLAUDE.md` の TRS ツール群、KoAT2/AProVE/CeTA）。
- **剰余モード（`-m BITS` / `-p PRIME`）は対象外で、黙って通さず拒否する。** これらは
  全ての値を巻き込むが本 back-end は無限領域の整数を出すので、モデルは別のプログラムに
  ついてのものになる。実際 `x += 100; x += 100; assert(x = 200)` は `-m 8` で失敗する
  （-56 に巻き込む）のに、無限領域のモデルは nuXmv が **proved** と答える。以前は
  `--smv` が `-m`/`-p` を黙殺していた（2026-08-04 修正。`compile_to_smv` が
  `SmvUnsupported` を投げるので CLI 経由でもライブラリ経由でも塞がっている）。
  符号化する場合の検証済み移行先は `coq/RevSMod.v` / `RevExtSMod.v` だが、
  **義務も変わる**——剰余環では `*=` / `/=` の条件が「非零」ではなく「単元であること」。
- **符号化の健全性は、制御フロー・ERR・式・別名・large-block について機械証明した**
  （§8〜§11）。残るのは**それらの接合**——`RevError.v` の抽象 `prim`/`guard` 層と
  `RevSmvBlock.v` の具体的な `sstmt` 層は、`RevLowerStmt.lower_stmt_iff` を経由して
  繋がってはいるが、CFG 全体を1つの Coq モデルにまとめた形にはなっていない。
  そこは差分テスト（`tests/verify/test_smv_nuxmv.py`）に依存している。

## 7. 次の一手

1. **具体長の配列をスカラーへ展開**する（C++ codegen と回路合成が既にやっている変換）。
   長さ未指定の引数は `N` を与えて具体化し、「長さ N まで、値は無限領域で」証明する。
   **値の有界性を外す**のが既存の `equiv.py` に対する増分なので、長さの有界性は残ってよい。
   §5.4 の教訓から、展開した配列要素をそのまま変数として並べるだけでなく、
   **large-block でどこまで潰せるか**を同時に設計すること。位置数が効く。
2. **等価性検証へ拡張**（本命）。可逆性により `P ≡ Q ⟺ P;Q† ⊑ id ∧ dom P = dom Q` で、
   `Q†` は `invert.py` で構文的に得られる。自己合成／積プログラムが要らないので状態空間が
   半分で済む。`dom P = dom Q` の部分が本文書の全域性検査そのものであり、両者は
   ひとつの体系をなす。対象は `PyJanus2PISA` の peephole と regalloc の translation validation。
3. **BMC への退避**。IC3 がタイムアウトした場合に `check_invar_bmc` で「深さ k までは
   破れない」を得る。SAT 側の証明ログ（DRAT）まで取れば下界側の主張が認証つきになる。

## 8. 符号化の機械検証（`coq/RevError.v`）

検査器は「ERR に到達しない」を証明して「表明が破れない」と結論する。この推論が正しい
ためには **表明破れがあれば必ず ERR に到達する**（＝モデルが見落とさない）ことが要る。
これを Rocq で証明した。

### 8.1 前提として足りていなかったもの

`RevCore.exec` は部分関係なので、**「表明破れ」と「発散」を区別できない**。どちらも
`exec s a b` が成り立たないだけである。したがって検査器が依拠する主張は、そのままでは
**記述すらできなかった**。そこで `execE : stmt -> state -> outcome` を導入した
（`outcome = Ok state | Err`）。

- `execE_ok_iff : exec s a b <-> execE s a (Ok b)` — 成功については既存意味論と一致。
  つまり `execE` は `exec` に失敗を足しただけで、余計なことをしていない。
- 失敗は2種類ある: 成り立たない**ガード**と、**進めない原始**（`X_PrimErr`）。
  `REV_PRIM` は `pstep` の全域性を要求しないので後者は起こりうるし、`smv.py` が
  `x *= 0` / `x /= 0` / 割り切れない `/=` / 除算0 に ERR 辺を出しているのは
  まさにこれである。この規則が無いと `fail_sound` はそれらを覆わず、
  部分的な原始を使うプログラムについて検査器の結論が正当化されない。
- `ok_not_err : exec s a b -> ~ execE s a Err` — 成功と失敗は排他。

### 8.2 ERR は「行き詰まり」である

`smv.py` が明示的な ERR 辺を持つのは **SMV が全域な遷移関係を要求するから**である
（`_render` のコメント「halt: every location must be total」がそれ）。Rocq では
「どの規則も適用できない」を直接書けるので、対応するのは**断片内での行き詰まり**:

```coq
stuck c l a  := forall m x, ~ mstep G c l a m x
mfail c base sz a := exists l x, base <= l < base + sz /\ mrun G c base a l x /\ stuck c l x
```

`l < base + sz` が**厳密に内側**であることが要点で、出口ラベルへの到達は失敗ではない。

### 8.3 証明した定理 — **両方向**

`stuck`（どの規則も適用できない）は call 命令で「呼び先が失敗した」と「呼び先が発散した」を
混同するので、命令自身に見える部分だけを取り出す:

```coq
localstuck c l a := (get c l = IChk g v nxt /\ gtest g a <> v)
                 \/ (get c l = IPrim p nxt /\ forall b, ~ pstep p a b)
```

`INop` と `IBr` は（`gtest` が関数なので）決して局所的に行き詰まらないから、この2通りで尽きる。
そのうえで、**機械側だけで書ける**失敗関係を帰納的に定める（call を跨いで伝播する）:

```coq
Inductive failsP : stmt -> state -> Prop :=
| FP_local  : mrun (entry_code s) 0 a l x -> l < csize s -> localstuck ... -> failsP s a
| FP_call   : ... get (entry_code s) l = ICall p nxt -> failsP (G p) x -> failsP s a
| FP_uncall : ... IUncall ... -> failsP (invert (G p)) x -> failsP s a
```

これで**対応が iff になる**:

```coq
fail_iff : execE s a Err <-> failsP s a
```

つまり **ERR に到達することと、ソースが表明を破ることは同値**。検査器にとっては
「見落としが無い」（`fails_of_execE`）と「誤検出が無い」（`failsP_execE`）の両方が言えたことになる。

`Call`/`Uncall` の扱いが両方向で非自明:
- 順方向は「呼び先が失敗するなら呼び出し命令には遷移が無い」を `crun_complete`
  （コンパイラ完全性）と `ok_not_err` から得る。
- 逆方向は `reach_bad`（`Rc`/`Rlp` の二重帰納法）を使う。要点は主張を
  **「断片内で失敗する、または断片を完走して不良点はその後」という選言**にしたことで、
  これにより「最初到達」の議論が一切不要になり、ループの後退辺で断片が再入されるケースも
  段数の減少だけで処理できる。

### 8.4 射程（正直に）

- framework の `prim`/`guard` は**抽象**なので、式レベルの罠は §8 の層では扱えない。
  → **§9 で別ファイル（`coq/RevSmvExpr.v`）として結線した。**
- `smv.py` は **large-block 符号化**（直線部を1遷移に畳む）だが、`comp` は1命令1ラベル。
  → **§11 で結線した。**ただし `comp` と直接比べたのではなく、large-block が
  **ソース意味論 `sexec` と同じ関係を定める**ことを示した（`comp` 側は `crun_iff` で
  すでに `exec` と一致しており、`lower_stmt_iff` が両者を繋ぐ）。抽象 `prim`/`guard` の
  ままでは `comp` と直接比較できないので、これが到達できる形である。
- 逆向きは **§8.3 で閉じた**。当初は「`stuck`（どの規則も適用できない）では偽」であった —
  `M_Call` が大ステップ命令なので呼び出し命令は呼び先が失敗したときも**発散したときも**
  遷移を持たず、ソースは発散の場合成功も失敗もしないから。`localstuck` と call を跨いで
  伝播する `failsP` に置き換えることで解消した（`smv.py` は call をインライン展開するので
  そもそもこの混同が無く、`failsP` の方が smv.py に近い）。

証明は 5つの `REV_PRIM` 実例すべてに落ちる。`audit.sh` は `RevExt.ExtPrim`
（**配列と `local`/`delocal` を持つ Janus**）での実例を検査しており、
`functional_extensionality` のみで PASS する。

## 9. 式の符号化の機械検証（`coq/RevSmvExpr.v`）

§8 は制御フローと ERR の対応だった。式レベルの罠（§3.1 床除算、§3.2 二ソート）は
framework の抽象 `prim`/`guard` では扱えないので、`RevLowerExpr.v` の**具体的な式**
（`sexpr` / `seval`。vjanus の lowering が使っているのと同じもの）に対して別に証明した。

### 9.1 nuXmv の式言語をモデル化する

`sm` は smv.py が出す SMV 項の断片で、**二ソート**（整数と真偽値、取り違えは値なし）。
要点は `MQuot` を **Rocq の `Z.quot`**（0方向切り捨て）で解釈することで、これは
nuXmv の実際の挙動であり、**Janus の挙動ではない**。

### 9.2 床除算マクロが正しいことの証明

`_div_defines` が出す4つの DEFINE をそのまま項として書き（`mtq` / `mtr` / `mfdiv` /
`mfmod`）、次を証明した。

```coq
floor_from_trunc : b <> 0 ->
  (let q := Z.quot a b in let r := a - b * q in
   if r =? 0 then q else if Bool.eqb (r <? 0) (b <? 0) then q else q - 1) = a / b
mfdiv_correct : y <> 0 -> ⟦mfdiv a b⟧ = ⟦a⟧ / ⟦b⟧      (Rocq の `/` は床除算)
mfmod_correct : y <> 0 -> ⟦mfmod a b⟧ = ⟦a⟧ mod ⟦b⟧
```

罠そのものも反例として機械化した:

```coq
naive_division_is_wrong : ⟦MQuot (-7) 2⟧ = -3  /\  (-7) / 2 = -4
```

**§3.1 で4通りの符号の組で試験したものが、全整数について証明になった。**

### 9.3 二ソートの翻訳

`tri`（整数位置）と `trb`（真偽値位置）は `_iexpr` / `_bexpr` の写しで、定義される所では
`seval` と一致する（`tri_sound` / `trb_sound`）。拒否が空虚でないことも定理にした:

```coq
comparison_is_not_an_integer : tri (SBin SLt a b) = None   (* x += (y > 0) の拒否 *)
variable_is_not_a_condition  : trb (SVar n) = None
bitwise_is_refused           : tri (SBin SXorB a b) = None
```

### 9.4 Python 実装との結線

定理が**実際に動くコードについての主張であり続ける**ように、
`tests/verify/test_smv_expr.py` が smv.py の出力を読み戻して固定する:

- 4つの DEFINE が**検証済みの構造**をしていること（正規表現で形を固定）
- その式を**切り捨て除算で解釈**すると Python の `//` と `%` に一致すること
  （符号の4通りと境界を含む格子上で。`mfdiv_correct` の実行版）

証明は全整数を、テストは**コンパイラが実際に出す文字列**を担保する。
nuXmv 自身との一致は `tests/verify/test_smv_nuxmv.py` が別途閉じている。

### 9.5 まだ結線していないもの

- **別名検査**（§3.3）→ **§10 で結線した。**
- **large-block**（§5.4）→ **§11 で結線した。**

## 10. 別名検査の機械検証（`coq/RevSmvAlias.v`）

§3.3 の別名は「実行時検査を静的に写す」という他の2つと質が違う罠で、
`docs/totality-checking.md` が最も危ないと書いていたものである。これを結線した。

### 10.1 インライン展開＝改名

判定が**そもそも記述できる**理由は、`smv.py` が呼び出しをインライン展開するので、文を
出す時点で全ての名前が環境 `env` を通して SMV 変数に解決済みだからである。別名（2つの
ソース名が1つのスロットを指す）はそこで構文的になる。この解決は**改名**であり、本ファイル
はそれが導く1つの可換図式についてのものである。

```coq
aoccurs env t e                                  (* smv.py が計算するもの（未改名の式に対して） *)
  = soccurs t (rn env e)                         (* sexec が課す側条件（インライン後のプログラムに対して） *)
  = reads 0 (enc lv g) (sloc lv t) (lower lv (rn env e))   (* frame core の実行時検査 *)
```

3つの層——模型検査器のフロントエンド・参照意味論・検証済みコア——で「右辺が左辺の対象を
読むか」が一致する（`aoccurs_rn` / `alias_three_ways`）。

### 10.2 証明した定理 — 両方向

`RevError.fail_iff` と同じ形にした。

```coq
step_alias_ok        : sexec (rn_stmt env s) g h -> alias_ok env s = true
alias_flagged_no_step: alias_ok env s = false -> ~ sexec (rn_stmt env s) g h
alias_check_is_exact : （上の2つの連言）
swap_alias_iff       : alias_ok env (TSwap x y) = false <-> (forall g h, ~ sexec ...)
```

- 前者が **`proved` を支える**: ソースが1歩進めるなら検査器はその文を弾いていない
  ＝別名違反を通常の更新として黙って模型化していない。
- 後者が **`refuted` を支える**: 弾いた文は本当に進めない＝無条件 ERR 辺は誤検出でない。
- swap は失敗経路が別名しかないので、対応が**完全な同値**になる。

`alias_ok` は文ごとの述語で、代入は `negb (aoccurs env (env x) e)`、swap は
`negb (env x =? env y)`、それ以外は `true`。これは PyJanus の `_check_alias_assign` /
`_check_alias_swap` の写しである。

### 10.3 見つかった2つの穴

機械化の産物として §3.3 の追記2件（`self_swap_gap` と
`double_binding_is_not_itself_an_error`）が定理として残っている。前者は
「ソースは走れない」と「no-op 模型は走れる」を並べたもので、後者は
「二重束縛下でも `a += 1` は走る」ことを `sexec` の導出で示したものである。

### 10.4 なぜ検査は pending 代入の**前**でなければならないか

`smv.py` は `_occurs` をその文自身のソース式に対して掛ける。ブロックの pending 写像を
代入した後の式ではない。これは実装の都合ではない: `x += y` の後、`x` の pending 値は
`x + y` であり、続く `y += x` は「`y` が出現する項」を読むことになるが、この文は完全に
合法である。代入後の形で検査すると**これを誤って弾く**
（`the_check_is_on_the_source_expression`）。

### 10.5 Python 実装との結線

`tests/verify/test_smv_alias.py` が、別名を持つ7本と持たない4本について
**PyJanus の終了状態**と**モデルが ERR に到達しうるか**が一致することを固定する。
nuXmv があれば `refuted` / `proved` の判定まで突き合わせる（`test_smv_expr.py` が
床除算についてやったのと同じ二段構え）。上の2つの穴はこのファイルの回帰テストになっている。

## 11. large-block 符号化の機械検証（`coq/RevSmvBlock.v`）

§5.4 のとおり、決定率を動かした唯一の要因が large-block である。したがって符号化の中で
**未検証部分として最も大きい**のがここだった。§8.4 が「この層ではできない」と書いた理由は
2つあり、どちらも framework の抽象 `prim` / `guard` では表現できない:

- 累積更新の**合成順**——`v += g` の後の `h -= v` は、`v` の入口値を引くのか累積値を引くのか
- 経路条件を**どの状態で評価するか**——ブロックの途中で現れたガードは入口値上の項として出る

どちらも `RevLowerStmt.v` の具体的な `sstmt` / `sexec` の上では表現できる。そこで書いた。

### 11.1 pending 写像の形式化

`smv.py` の `self.pending` は「SMV 変数 → ブロック入口の値で書いた式」で、`_val` がそれを
読む（未書き込みなら変数自身）。これを `pmap := nat -> sexpr` とし、`_iexpr` が変数位置で
`_val` を呼ぶことを `subst : pmap -> sexpr -> sexpr` として写した。`sx` が `_stmt` の
直線部の転写で、**smv.py の挙動どおり4値**を返す:

| 結果 | smv.py の挙動 |
|---|---|
| `Ok p` | ブロックが累積する。`p` がそこまでの pending 写像 |
| `Flagged` | ERR への**無条件辺**を出し継続は到達不能（§10 の別名判定）。**モデルは出る** |
| `Refused` | `SmvUnsupported`＝モデルを出さない。この断片では `^=` |
| `Cut` | ブロックがここで終わり通常の制御フロー符号化に移る（`_if`/`_from`）。失敗ではない |

当初は `option pmap` で、この4つのうち3つを `None` に潰していた。挙動が違うものを
同一視していたので補題が弱くなり、別名の補題が「`^=` ではない」という**別名と無関係な
側条件**を持たされていた。分けたことで `sx_flagged_iff` が側条件なしの**両方向**になる。

### 11.2 証明した定理

```coq
seval_subst   : describes g0 p g -> seval g0 (subst p e) = seval g e
guard_at_entry: （同上。経路条件が入口値で書けることそのもの）
block_sound   : sx p s = Some p' -> describes g0 p g -> sexec s g h -> describes g0 p' h
block_from_entry : sx pid s = Some p' -> sexec s g h -> forall x, seval g (p' x) = Some (h x)
block_is_functional : （同じブロックの2つのソース実行は一致する＝遷移が well-defined）
```

**`block_sound` が large-block の同値そのもの**である: 変数ごとの `next(x) := p' x` を
**入口ストア上で同時に**適用した結果が、ソース意味論を1文ずつ走らせた結果に一致する。
`seval_subst` が `option` の等式であることが効いていて、**未定義性も転送される**——
0除算は入口値で書いても0除算になる。だから可除性等の義務を別の ERR 辺として切り出せる。

### 11.3 罠2つ（どちらも1位置1文の符号化では起きない）

- **合成順**（`composition_order_is_observable`）。文書 §2 が引用しているブロック
  `v += g; h -= v; h += halfg; t += 1` について、`h` の累積項が
  `((h - (v + g)) + halfg)` になることを `documented_block_accumulates` で固定した
  （**文字列まで一致**）。入口の `v` を読む素朴な形とは
  `v = g = h = 1, halfg = 0` で −1 と 0 に分かれる。
- **同時性**（`a_swap_must_be_simultaneous`）。swap は pending の2項を**同時に**交換する
  （Python の `p[l], p[r] = before_r, before_l` は右辺タプルを先に評価する）。順に書くと
  2番目が1番目の書いた写像を読んでしまい、**両方の項が `y` になる**。これは単射ですらない
  （`the_sequential_swap_is_not_reversible`）。

### 11.4 射程（正直に）

直線部（`TSkip` / `TAsn` / `TSwap` / `TSeq`）のみ。`smv.py` が1遷移に畳むのはまさにここで、
位置を切る所（`_if` / `_from` / `_seal`）から先は通常の制御フロー符号化＝§8 の対象である。
文ごとの**義務**（`*=` `/=` の `aok`、非零除数）は更新式ではなく別の ERR 辺として出るので、
これも §8 / §9 の対象。ここでは `sexec` の前提として現れる。

### 11.5 Python 実装との結線

`tests/verify/test_smv_block.py` が、4文が**1遷移1位置**になること、`h` の更新式が
上の文字列そのものであること、書かれない変数には `next(...)` が出ないこと（フレーム条件を
`TRUE` 既定が吸収する）、ブロック途中の `assert` が `(x + 1) = 1` と入口値で出ることを固定する。
さらに `h` の累積項を格子上で評価して逐次実行と突き合わせる（`block_sound` の実行版）。
