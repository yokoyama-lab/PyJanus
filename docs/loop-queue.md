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

- `Admitted` / `admit.` / `Axiom` / `Parameter` が増えていない
- **既存の** `Theorem` / `Lemma` / `Corollary` / `Example` の**文**が変わっていない
  （追加は自由。既存の主張を弱めるのは人間の判断）
- テストの `assert*` の削除・条件の緩和が無い
  （`--init any` → `zero`、グリッドの縮小、`subTest` 範囲の縮小を含む）
- `docs/*.md` の実測値（本数・秒数・判定）を、測り直さずに書き換えていない

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

### [ ] 3. `smv.py` の `_occurs` を fail-closed にする

**なぜ**: `_occurs` は知らないノード型で `return False`（`smv.py` 末尾）。今日は
無害だが——ternary は `_iexpr` が先に `SmvUnsupported` を投げるので `unsupported` 止まり
——**安全が「別の関数が先に落ちる」ことに依存している**。swap のバグはまさにこの構造
だった（`_stmt` が swap を処理する一方、対応する別名検査が無かった）。

**完了条件**: `_occurs` が未知のノード型で `SmvUnsupported` を投げる。ternary を含む
プログラムが（これまで通り）`unsupported` になることをテストで固定。

**規模**: 小

---

### [ ] 4. 段数の主張を両方向にする（または表現を片方向に限定する）

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

### [ ] 5. `RevSmvBlock.sx` の `None` を2つに分ける

**なぜ**: 現在の `None` は「断片外（`SmvUnsupported`＝モデルを出さない）」と
「別名フラグ（ERR への無条件辺＝モデルは出る）」を混同している。smv.py での挙動が
まったく違うので、証明が区別できていないのは弱い。

**完了条件**: 戻り値を3値（`Ok p` / `Flagged` / `Unsupported` 等）にし、
`sx_atomic_alias` / `sx_swap_alias` を「`Flagged` になるのは `alias_ok` が false の
ときに限る」という**両方向**の補題に書き直す。`block_sound` は `Ok` の場合の主張として
そのまま通ること。`audit.sh` に登録。

**規模**: 小〜中

---

### [ ] 6. `RevSmvAlias.renv` の部分性を明示する

**なぜ**: `renv := nat -> nat` を全域関数にしたのは単純化。smv.py の `env` は部分写像で、
未束縛名は `SmvUnsupported`（`_lookup`）。射程外であることがファイル冒頭のコメントに
しか書いていない。

**完了条件**: `renv` を `nat -> option nat` にするか、全域のままなら「未束縛名は
smv.py が `_lookup` で拒否するので射程外」を**定理として**書く（例: 束縛集合の外の名前に
ついては `alias_ok` の判定が使われないこと）。前者を選ぶなら `aoccurs_rn` /
`alias_three_ways` / `step_alias_ok` / `alias_flagged_no_step` が通ること。

**規模**: 小〜中

---

### [ ] 7. fuel と段数を接続する（連鎖の中に fuel インタプリタを置く）

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

### [ ] 8. BOUND の主張を精密にする（ドキュメント）

**なぜ**: `_call` が深さ上限で BOUND に抜けたあと、継続は到達不能な位置に置かれる。
`nuxmv.py` の `status` は最弱を取る（refuted > unknown > proved）ので**報告は誤らない**
が、`totality-checking.md` §6 の「証明はその深さまでの主張にとどまる」は曖昧。
正しくは「**上限に到達しない実行についてのみ**」。

**完了条件**: §6 と `smv.py` の該当コメントを書き換える。実測値には触れない。

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

- **配列の具体長展開**（`totality-checking.md` §7-1）。断片被覆率 12/97 の最大要因
  （配列 65 / stack 31 / struct 13）。**本命だが大**。着手するなら先に補題単位へ割る
- **CFG 全体の接合**（`coq/README.md` の "The large-block encoding" 末尾）。
  `RevError.v`（抽象 `prim`/`guard`）と `RevSmvBlock.v`（具体 `sstmt`）が
  `lower_stmt_iff` で繋がるだけで1つの定理になっていない
- **`--init any` の再測定**。現在8本のみ。配列展開の後にやる

### 検証できないもの

- **論文執筆（情報処理学会 PRO）**。材料は揃っている（言語非依存の可逆性を5実例へ／
  コンパイル後も可逆性と段数が転送／独立実装との差分検証／符号化の機械検証で
  不健全性を実際に1件発見）。自走に不向き

### リポジトリ衛生（人間の判断）

- 未 push コミット（`git log origin/development..HEAD`）
- `experiments/ultrametric-m0/`（2026-07-10 以来 未追跡）を追跡するか移すか
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
