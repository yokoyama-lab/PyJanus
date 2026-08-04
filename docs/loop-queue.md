# 自走ループの作業キュー

無人で回す（`/loop`）ときに1反復＝先頭1件を消化するためのキュー。**「改善する」を課題に
してはいけない**——終了条件を持たないループは、やることが尽きた時点でドキュメントの
言い換えやリネームを始め、差分だけが増える。ここに書いてある項目だけをやり、
**キューが空になったら止まる**。

関連: 現状把握は `../CLAUDE.md` の「現在の状態」節、検査器の設計は
`totality-checking.md`、証明の claims 表は `../coq/README.md`。

## 毎反復のゲート（全部通ってはじめてコミット）

```bash
make -C coq                                   # 増分ビルド（約1秒）
coq/audit.sh                                  # フルビルド＋公理検査＋未完了証明の検査（約10秒）
python3 -m pytest tests/verify/ -q            # 約4秒
```

`Admitted` / `admit` の repo 全体検査は **`audit.sh` の step 0 に入った**（項目1）ので
別途 grep する必要はない。`Axiom` は repo 全体では検査しない——`Module Type` の義務
（`REV_PRIM` の3法則など）が `Axiom` で宣言されるため。実際に結果へ届く公理は
`Print Assumptions`（step 3）が捕まえる。

コミット前（キュー1件を閉じるとき）にもう1段:

```bash
python3 -m pytest tests/ -q                   # 約10分。1695+ passed / 0 failed
```

**内側ループに入れてはいけないもの**: `tools/verify_corpus.py`（149本×最大120秒）。
判定が変わりうる変更をしたときだけ、error fixture に絞って1回走らせる
（`--init zero --timeout 60 'tests/jana2014/fixtures_errors/*.ja'`、refuted 12 が基準値）。

## 差分ゲート（機械では気づけない劣化を止める）

Rocq は誤った証明を受理しないが、**弱い定理は喜んで受理する**。テストも同じで、
`assert` を緩めれば緑になる。したがって毎反復、`git diff` について次を確認する。
1つでも該当したら**変更を戻して次の項目へ**（人間の判断が要る）。

```bash
git diff | grep -E '^-[[:space:]]*(Theorem|Lemma|Corollary|Example|Definition|Fixpoint|Inductive) '
git diff -- tests/ | grep -E '^-.*self\.assert'
```

どちらも空であること。加えて目視で:

- `Admitted` / `admit.` / `Axiom` / `Parameter` が増えていない
- テストの条件が緩んでいない（`--init any` → `zero`、グリッドの縮小、
  `subTest` 範囲の縮小を含む。削除は上の grep が捕まえるが、**緩和は捕まえない**）
- `docs/*.md` の実測値（本数・秒数・判定）を、測り直さずに書き換えていない

**新しく通るようになったプログラムは1本ずつ PyJanus と突き合わせること。** 判定
（refuted/proved）の一致だけでは足りず、**落ちる理由**まで見る。このセッションで出た
自作の不健全性3件（`int x[0]` を proved、`a[0] <=> a[a[1]]` を proved、
`array-size-mismatch.ja` を proved）は、いずれも数を数えるだけでは通過していた。

**行頭を固定すること。** 素の `grep 'assert'` は散文に当たる（Janus の "exit
assertion" は至る所に出る）。誤検出するゲートは読み飛ばされるようになり、
そうなった時点でゲートとして死ぬ。

## 規約

- 新しい headline 定理を足したら **`coq/audit.sh` にも登録する**
  （登録漏れの定理は公理検査を素通りする）
- 新しい `.v` は `coq/_CoqProject` に登録する
- 外部書き込みは**しない**: `git push` しない、Notion 作業ログはキューが空になった
  ときに**1行だけ**書く（`~/dev/CLAUDE.md` の「1依頼=1行」に合わせる）
- 1反復で1項目。終わったら下の該当行を `[x]` にし、「次は何か」を1〜3行で
  「進捗ログ」に追記する

---

## キュー

### [x] 1. `audit.sh` に repo 全体の `Admitted` 検査を足す

**なぜ**: `audit.sh` は**名指しした191定理**しか見ない（`.v` は55ファイル）。新しい
ファイルを足して登録し忘れると、その中の `Admitted` は緑のまま通る。ループ自身が
このゲートに依存するので、最初に固める。

**完了条件**: `coq/audit.sh` が `grep -rn 'Admitted\|admit\.' *.v` を無条件に実行し、
非空なら exit 1。故意に `Admitted` を1つ入れると赤くなることを手で確認してから戻す。

**規模**: 小（audit.sh に数行）

---

### [x] 2. `--smv` と `-m bits` / `-p prime` の併用を拒否する

**なぜ**: **実証済みの不健全性**。`cli.py` は `compile_to_smv` に剰余モードを渡さない
ので、`-m 8` でも無限領域（`x : integer`）のモデルが出る。

```
procedure main()
    int x
    x += 100
    x += 100
    assert(x = 200)
```

PyJanus `-m 8` は失敗する（x が -56 に巻き込む）が、`--smv -m 8` のモデルを nuXmv に
かけると **proved**。swap の件と同型だが、こちらは特殊なプログラムを要さず、剰余モードの
全プログラムに効く。

**完了条件**: `--smv` と `-m`/`-p` を同時に与えると明示的に落ちる（`SmvUnsupported`
またはCLIエラー）。`tests/verify/test_smv_alias.py` と同じ形で回帰テストを1本
（上のプログラムで、拒否されること）。既存テスト・コーパス判定に変化が無いこと
（どちらも `-m`/`-p` を使っていない）。

**規模**: 小

**注**: これは「拒否するか剰余符号化を実装するか」の設計判断を**先取りしない**。
実装する場合でも、それまでの間は拒否が正しい（黙って別のプログラムの証明を出すより）。
実装側は下の「保留」を参照。

---

### [x] 3. `smv.py` の `_occurs` を fail-closed にする

**なぜ**: `_occurs` は知らないノード型で `return False`（`smv.py` 末尾）。今日は
無害だが——ternary は `_iexpr` が先に `SmvUnsupported` を投げるので `unsupported` 止まり
——**安全が「別の関数が先に落ちる」ことに依存している**。swap のバグはまさにこの構造
だった（`_stmt` が swap を処理する一方、対応する別名検査が無かった）。

**完了条件**: `_occurs` が未知のノード型で `SmvUnsupported` を投げる。ternary を含む
プログラムが（これまで通り）`unsupported` になることをテストで固定。

**規模**: 小

---

### [x] 4. 段数の主張を両方向にする（または表現を片方向に限定する）

**なぜ**: `RevSteps.compilation_is_step_exact` は「n 段の導出は**厳密に n 段の**機械実行に
なる」という**片方向**の定理。「機械実行は必ず n 段」は言えていない（機械の段数決定性が
要る）。`coq/README.md` の見出し "Compilation is step-exact" は両方向に読めてしまう。

**完了条件**: 次のどちらか。
- (a) `mstepn` / `mrunn` の決定性を証明し、`crun_complete` と合わせて逆向き
  （`mrunn G m (entry_code s) 0 a (csize s) b -> execn m s a b`）を出す。
  `pstep_det` と `gtest` が関数であることから相互帰納法。`N_Call` の段数が
  呼び先の実行段数で決まる点が要。→ `audit.sh` に登録
- (b) 決定性まで行かないなら、README と `RevSteps.v` の冒頭を「導出→実行の向きの
  主張である」と明示的に限定する

**規模**: (a) 中 / (b) 小。**まず (a) を試し、詰まったら (b) に落とす**

---

### [x] 5. `RevSmvBlock.sx` の `None` を2つに分ける

**なぜ**: 現在の `None` は「断片外（`SmvUnsupported`＝モデルを出さない）」と
「別名フラグ（ERR への無条件辺＝モデルは出る）」を混同している。smv.py での挙動が
まったく違うので、証明が区別できていないのは弱い。

**完了条件**: 戻り値を3値（`Ok p` / `Flagged` / `Unsupported` 等）にし、
`sx_atomic_alias` / `sx_swap_alias` を「`Flagged` になるのは `alias_ok` が false の
ときに限る」という**両方向**の補題に書き直す。`block_sound` は `Ok` の場合の主張として
そのまま通ること。`audit.sh` に登録。

**規模**: 小〜中

---

### [x] 6. `RevSmvAlias.renv` の部分性を明示する

**なぜ**: `renv := nat -> nat` を全域関数にしたのは単純化。smv.py の `env` は部分写像で、
未束縛名は `SmvUnsupported`（`_lookup`）。射程外であることがファイル冒頭のコメントに
しか書いていない。

**完了条件**: `renv` を `nat -> option nat` にするか、全域のままなら「未束縛名は
smv.py が `_lookup` で拒否するので射程外」を**定理として**書く（例: 束縛集合の外の名前に
ついては `alias_ok` の判定が使われないこと）。前者を選ぶなら `aoccurs_rn` /
`alias_three_ways` / `step_alias_ok` / `alias_flagged_no_step` が通ること。

**規模**: 小〜中

---

### [x] 7. fuel と段数を接続する（連鎖の中に fuel インタプリタを置く）

**なぜ**: 「段数 n の実行は fuel f(n) で必ず値を返す」が言えると、fuel の切り方が
資源量の主張になる。可逆計算の資源解析として自然な次の一歩。

**先に確認済みの前提（重要）**: **既存の抽出インタプリタはどれも `RevSteps` から
直接は使えない。** 調査結果:

| ファイル | 対象コア | 連鎖内か |
|---|---|---|
| `RevExtract.v` | `Janus.v`（自己完結の具体開発） | 外 |
| `RevExtractP.v` | `RevProc.v` | 外 |
| `RevExtractAr.v` | `RevArr.v` | 外 |
| `RevExtractFrame.v` | `RevFrame.v` | 外 |
| `RevExtractMod.v` / `RevExtractSMod.v` | `RevExtMod` / `RevExtSMod`（`RevLang` 実例） | **別インスタンス** |

最後の2つは `RevLang` 実例だが、`RevSteps` が使う
`RevSmallStep → RevDenote → RevFix → RevCompile` の連鎖とは**別の適用**なので、
関手の生成性により別の帰納型になり、`execn` と並べて書けない
（`../CLAUDE.md` の「確定している事実」の1つ目そのもの）。

**完了条件**: `RevSteps.v`（または連鎖から射影した新ファイル）に `Cp.L.stmt` 上の
fuel インタプリタ `runn : nat -> stmt -> state -> option state` を定義し、
`execn n s a b -> runn (f n) s a = Some b` を具体的な `f`（例 `f = S n`）で証明する。
健全性（`runn f s a = Some b -> exec s a b`）も併せて。`audit.sh` に登録。

**規模**: 中（当初「小〜中」と見積もったが、連鎖内に interpreter が無いので実装から）

---

### [x] 8. BOUND の主張を精密にする（ドキュメント）

**なぜ**: `_call` が深さ上限で BOUND に抜けたあと、継続は到達不能な位置に置かれる。
`nuxmv.py` の `status` は最弱を取る（refuted > unknown > proved）ので**報告は誤らない**
が、`totality-checking.md` §6 の「証明はその深さまでの主張にとどまる」は曖昧。
正しくは「**上限に到達しない実行についてのみ**」。

**完了条件**: §6 と `smv.py` の該当コメントを書き換える。実測値には触れない。

**規模**: 小

---

### [x] 9. 配列の宣言を展開する（定数添字まで）

**測定（2026-08-04、97本の examples を `compile_to_smv` で分類）**:

| 分類 | 本数 |
|---|---:|
| スカラのみ（現在の対象。うち通るのは8本、4本は `^=`/`&` で拒否） | 12 |
| **配列のみが障害** | **41** |
| stack を含む | 31 |
| struct を含む | 13 |

**当初の「具体長の配列を展開」は +2本にしかならない**（`reversible_gates.ja` /
`test2.ja` のみ）。配列を正しく扱えば **8 → 49/97**。したがって項目9〜14 は
「具体長だけ」ではなく**配列一般**を対象にする。前提も測定済み:
**範囲外アクセスは実行時エラー**（"Array index `[5]' was out of bounds"）、
**41本中38本が変数添字**、**多次元は2本のみ**（`matrixmult*.ja`）。

**なぜ**: 断片被覆率がこの検査器の最大の制約。まず宣言の展開と定数添字だけを通し、
命名規約と環境表現を確定させる（動的添字は項目10・11）。

**完了条件**: `int a[3]` が3つの SMV 変数に展開され、定数添字 `a[1]` がそれを直接参照する。
**定数添字が範囲外なら無条件 ERR 辺**（別名と同じ扱い。PyJanus は実行時に落ちる）。
`tests/verify/test_smv_array.py` に、展開された変数名・定数添字の参照・範囲外の
ERR 辺を固定するテスト。149本の分類が**悪化していない**こと。

**規模**: 中

---

### [x] 10. 変数添字の**読み**と範囲外の ERR 辺

**なぜ**: 41本中38本が変数添字を使うので、ここを通さないと項目9は 8→10 で終わる。

**完了条件**: `a[i]`（i が変数）が `case i = 0 : a__0; … ; esac` に翻訳され、
`0 <= i < n` を守れないと ERR へ抜ける。PyJanus の範囲外エラーと **nuXmv の判定が一致**
することを `test_smv_nuxmv.py` と同じ二段構え（解釈器の終了状態 vs `refuted`/`proved`）で
固定する。

**規模**: 中

---

### [x] 11. 変数添字の**書き**

**なぜ**: `a[i] += e` は要素ごとの条件付き更新になる（`next(a__k) := case … i = k : …;
TRUE : a__k`）。**ここでモデルが膨らむ**ので §5.4 の教訓（符号化が決定率を左右する）が
そのまま効く。

**完了条件**: 書きが正しく翻訳され、`a[i] <=> a[j]` も含めて解釈器と一致する。
**モデルサイズを測って記録する**（要素数 × 位置数のどちらが効くか）。large-block との
相互作用も1本測る。

**規模**: 中〜大

---

### [x] 12. 別名検査を配列セルへ拡張する

**なぜ**: `a[i] += a[j]` は **i = j のときだけ**エラー——つまり実行時・添字精度の検査で、
スカラの `x += x` と同じ構造。`smv.py` が今これを見ていないなら、**swap・剰余と同じ型の
不健全性**になる。Coq 側には既に答えがある: `RevArr.wf_assign` の `reads_cell` は
「書かれた**セル**が右辺に読まれない」という添字精度の実行時検査で、
`A[j][i] += A[j][k]`（i≠k）を正しく許す。

**完了条件**: 添字が等しくなりうる場合に ERR 辺が立ち、等しくなり得ない場合は立たない。
PyJanus の `_check_alias_assign` / `_check_alias_swap` は `_selector_index_exprs` も
見ているので、そこと一致させる。`RevSmvAlias.v` を配列セルへ広げるか、
広げられない理由を書く。回帰テストは `test_smv_alias.py` と同じ形。

**規模**: 中

---

### [x] 13. 長さ未指定の配列引数を解決する

**なぜ**: `int a[]` は64本に現れる最大の阻害要因。ただし **`smv.py` は既に呼び出しを
インライン展開している**ので、呼び出し地点では実引数の長さが判っている。新しい機構では
なく、既存の env 解決に長さを載せるだけで済むはず（要確認）。

**完了条件**: `procedure f(int a[])` を配列で呼ぶプログラムが展開され、解釈器と一致する。
同じ手続きが**異なる長さで呼ばれる**場合に正しく別々に展開されることをテストで固定。

**規模**: 中

---

### [x] 14. 再測定と文書の更新

**完了条件**: `tools/verify_corpus.py` を149本に対して回し、`docs/totality-checking.md`
§4（被覆率の表）と §5（判定の表）を**実測値で**置き換える。古い数値を推測で書き換えない
こと。符号化サイズの比較（§5.4 の形式）も併記する。**多次元配列は射程外**として明記
（`matrixmult*.ja` の2本。`RevLowering.v` に Cantor fold の単射性はあるので将来の入口）。

**規模**: 小〜中

---

### [x] 15. `_BLOCK_CHARS` を決定率で振る

**なぜ**: 配列は断片に入ったが**9本とも未決**（§5.5）。効いているのは位置数ではなく
**項の大きさ**で、その唯一の調整つまみが `_BLOCK_CHARS`（既定 4000）。§5.4 は
「道具を替える前に渡している問題を疑え」と結論しており、同じ作業が配列について
もう一度要る。**まずこれ**——コードを変えずに測れる。

**完了条件**: 断片内 examples 17本を `_BLOCK_CHARS` ∈ {500, 1000, 2000, 4000, 8000} で
走らせ（`--init zero`・IC3・120秒）、proved / unknown の数とモデルサイズ・位置数を表にする。
最良値が既定と違えば変更し、変わらなければ**「変わらなかった」ことを記録する**
（§5.4 の ASSIGN 形式がそうだったように、効かないと分かることにも価値がある）。
`docs/totality-checking.md` §5.5 に追記。

**規模**: 小（測定が主）

---

### [x] 16. 変数添字の読みを nuXmv の配列型に載せる

**測定済みの前提（2026-08-05）**:

| 試したこと | 結果 |
|---|---|
| `a : array 0..2 of integer` を SMT エンジンで | **動く**（IC3 が証明） |
| 変数添字の**読み** `x + a[i]` | **動く** |
| 変数添字の**書き** `next(a[i]) := …` | **拒否**「Expressions not allowed in array subscripts on left hand side of assignments」 |

**なぜ**: 項が膨らむ主因は読みである。現在 `a[i]` は
`case i=0 : <a_0 の pending>; …` と展開され、**全要素の pending 項を複製する**。
これが乗算的増加の出どころ（§5.5）。配列型なら入口の読みは `a[i]` の一語で済む。
書きは要素ごとのままだが、書きの後に block を切れば読みは常に確定状態を指す
——項は縮み位置は増える。これは §5.4 が測ったトレードオフそのもので、今度は測れる。

**完了条件**: 配列を `array 0..n-1 of integer` として宣言する経路を足し（既定は切替可能に）、
読みを `a[i]` にし、動的書きの直後に `_seal` する。解釈器との一致を
`tests/verify/test_smv_array.py` の既存ケース全部で確認（判定も理由も）。
項目15 と同じ形で proved / unknown とモデルサイズを比較し、**どちらが良いかを数値で決める**。
悪ければ既定に戻し、理由を書く。

**規模**: 中

---

### [ ] 17. 再測定と文書更新（2回目）

**完了条件**: 項目15・16 の結果で `docs/totality-checking.md` §5・§5.5 を更新。
実測値のみ。`CLAUDE.md` の現状節も合わせる。

**規模**: 小

---

## 保留（ループに入れない）

### 設計判断が要るもの — 人間が決めるまで着手しない

- **剰余符号化の実装**（上の項目2の恒久版）。`-m`/`-p` を SMV で表現する。
  検証済みの移行先は `coq/RevSMod.v`（符号付き窓への巻き込み）と `RevExtSMod.v`
  （式の途中まで巻き込む `-m` 忠実な core）。
  **落とし穴**: 剰余環では `*=` / `/=` の可逆条件が「非零」ではなく**単元であること**に
  変わる（`runtime.py` の "Multiplication by {operand} is not invertible modulo
  {modulus}"）。現在の `!= 0` 義務をそのまま流用すると**新しい不健全性を作る**。
  自走に委ねてはいけない理由がこれ。

### 大きすぎてループでは発散するもの

- **stack（31本）と struct（13本）** — 次の被覆率の壁。**ただし決定率より後**にすべき:
  配列で14本が断片に入って決着したのは error fixture の5本だけで、examples は9本とも
  unknown になった。決定率が上がらないまま被覆率だけ広げると `unknown` の列が増えるだけ
  である。項目15〜17 の後に、同じやり方（着手前に実測で scope を決める）で割ること

- **多次元配列**（`matrixmult.ja` / `matrixmult_v1.0.ja` の2本のみ）。項目9〜14 の射程外。
  `RevLowering.v` に Cantor fold の単射性があるので入口はある

- **CFG 全体の接合**（`coq/README.md` の "The large-block encoding" 末尾）。
  `RevError.v`（抽象 `prim`/`guard`）と `RevSmvBlock.v`（具体 `sstmt`）が
  `lower_stmt_iff` で繋がるだけで1つの定理になっていない
- **`--init any` の再測定**。現在8本のみ。配列展開の後にやる

### 検証できないもの

- **論文執筆（情報処理学会 PRO）**。材料は揃っている（言語非依存の可逆性を5実例へ／
  コンパイル後も可逆性と段数が転送／独立実装との差分検証／符号化の機械検証で
  不健全性を実際に1件発見）。自走に不向き

### リポジトリ衛生（人間の判断）

- ~~未 push コミット~~（2026-08-04 に push 済み。`f3d8d4a`）
- `experiments/ultrametric-m0/`（2026-07-10 以来 未追跡）を追跡するか移すか
- この repo の `CLAUDE.md` の現状節が未コミットのまま（追跡下なのでコミットすれば公開される）
- この repo の `CLAUDE.md` を git 追跡下に置き続けるか（グローバル方針の例外）

---

## この repo で必ず踏む罠

反復のたびに数分溶かさないよう、着手前に `../CLAUDE.md` の「注意」節を読むこと。要点:

- `.vo` は**ツールチェーン固有**。「inconsistent assumptions」も「compiled with
  OCaml x.y.z while this instance …」も対処は同じ `cd coq && make clean && make`
- Rocq の `repeat split` は **`reflexivity` で閉じる目標を勝手に消す**ので bullet 数がずれる
- Rocq のコメント内で強調の `*` の直後に `)` が来ると**コメントが途中で閉じる**
- `Open Scope Z_scope` 下では nat 添字も `Z` に取られる → `2%nat`
- `eapply …; [ … | | lia ]` のように空スロットを挟むと、`lia` が未確定の evar を見て
  落ちる。**段数は `with (n1 := …) (n2 := …)` で明示する**
- `induction … using execn_mut` の IH 名は `IHexecn`、複数なら `IHexecn1..3`
- nuXmv は PATH に無い。`jana_py.nuxmv.find_nuxmv()` を使う（テストは未導入なら skip）
- **`RevLang` を2回適用すると別の帰納型になる。** `RevSemantics` / `RevSteps` は
  `RevSmallStep → RevDenote → RevFix → RevCompile` の連鎖から射影している。
  ここに入っていないもの（`Janus.v`・`RevArr`・`RevFrame`・`RevProc`、および
  `RevExtMod` などの別インスタンス）は**並べて書くことすらできない**。
  「あの定理をこのファイルで使う」を思いついたら、まず両者が同じ連鎖にいるか確認する
  （項目7はこれで見積もりが変わった）

---

## 進捗ログ

各反復の最後に1〜3行で追記する（何を終え、次に何をするか）。これが無いと反復ごとに
優先順位を再導出して往復する。

- 2026-08-04 キュー作成。項目1〜8が対象、保留は別掲。次は項目1（`audit.sh` の
  repo 全体 `Admitted` 検査）——ループ自身のゲートなので最初に固める。
- 2026-08-04 項目1 完了。`audit.sh` に step 0 を追加（ビルド前に走るので fail-fast）。
  実装中の発見: `Axiom` は `Module Type` の義務宣言で10箇所正当に使われており repo 全体
  検査は**誤り**、`admit` は散文（"admits a sound fuel"）に5箇所あるのでパターンは
  `Admitted|(^|[^A-Za-z])admit[[:space:]]*[.;]` に限定した（誤検出0を55ファイルで確認）。
  `_CoqProject` に無いファイルでも検出することを合成サンプルで確認済み＝塞ぎたかった穴。
  次は項目2（`--smv` × `-m`/`-p` の拒否）。
- 2026-08-04 項目2 完了。拒否は **`compile_to_smv` 側**に置いた（CLI だけだと
  `tools/verify_corpus.py` 等のライブラリ経由が塞がらない）。`cli.py` は
  `args.mod_bits`/`args.mod_prime` をそのまま渡す。`""` も未指定として扱う
  （`validate_args` がそう扱っているため）。`tests/verify/test_smv_modular.py` 10本、
  うち1本は nuXmv で「無限領域モデルは proved／`-m 8` の実行は失敗」を固定＝拒否の根拠が
  黙って偽になるのを防ぐ。docs §6 に限界として追記。次は項目3（`_occurs` fail-closed）。
- 2026-08-04 項目3 完了。`_occurs` が受理する節点集合を `_iexpr`/`_bexpr` と**同一**にした
  （`Number`/`Boolean`/選択子なし `LvalExpr`/`BinExpr`/`UnaryExpr` 以外は raise、未束縛名も
  `_lookup` 経由で raise）。149本の分類は完全に不変（supported 25 / unsupported 110 /
  parse 7 / static 7）で、`type-error-{empty,top}.ja` の2本が別の関数で拒否されるように
  なっただけ——どちらも元から断片外。`or` の短絡は残した（True は保守側かつ PyJanus 忠実）。
  次は項目4（段数の両方向化。まず (a) 機械決定性を試し、詰まれば (b) 表現限定）。
- 2026-08-04 項目4 完了。**(a) が通ったので (b) への退避は不要**。`step_cases_exact`
  （`Cp.step_cases` は call で `k < n` と段数を落とすので、`n = S k` を保つ版を**追加**。
  既存 lemma は変更していない）→ `machine_det`（`mstepn_mut` の相互帰納、P0 は
  「終点が halt なら段数まで一意」）→ `crun_cost_complete` → `compilation_is_step_exact_iff`。
  ついでに差分ゲートのパターンを行頭固定に厳密化——素の `assert` grep が散文の
  "exit assertion" に当たって誤検出したため。次は項目5（`sx` の None 分離）。
