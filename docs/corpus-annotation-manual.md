# サンプルプログラム注釈作業 手順書（アルバイト向け）

*対象: 学部3年生 / 前提知識: Python の基本文法とターミナル操作。可逆計算・Janus の
知識は不要（作業しながら覚える形になっている）。*

---

## 0. この作業は何のためにあるか（最初に読む）

PyJanus は **Janus** という「逆向きにも実行できるプログラミング言語」の処理系です。
`tests/jana2014/fixtures/examples/` に、Janus で書かれたサンプルプログラムが **97本**
入っています。ソート、最大公約数、フィボナッチ、圧縮など、教科書に出てくる
アルゴリズムを「逆実行できる形」で書き直したものです。

このリポジトリには自動テストがたくさんありますが、**どれも「前に実行してから
後ろに実行すると元に戻る」といった性質しか調べていません**。
つまり **「そもそも計算結果が合っているか」を誰も確認していない**。
間違った答えを出すプログラムでも、それが可逆でありさえすればテストは全部通ります。

あなたの仕事は、**97本を1本ずつ読んで実行し、「何を計算するプログラムなのか」「その答えが
正しいと確認した根拠」「正しければ成り立つはずの条件」をファイルの先頭に書き足す**ことです。
最後のものは Python の式で書き、機械が毎回検査します。

書き足す情報には決まった形式があり、`tools/check_corpus_meta.py` という検査
プログラムが形式の正しさを自動でチェックします。**形式が合っているかは機械が
判定するので、そこで悩む必要はありません。** あなたが頭を使うのは
「この答えは本当に正しいのか」を確かめる部分だけです。

> **もし「答えが合っていない」プログラムを見つけたら、それは失敗ではなく大当たりです。**
> §6 の手順で報告してください。それを見つけることがこの作業の一番の価値です。

---

## 1. 初日にやること（環境構築）

### 1.1 リポジトリを取得する

GitHub のアカウントを作り、先生にユーザ名を伝えてください。作業は
**fork して自分のコピーで行い、Pull Request で提出**します（元のリポジトリを
直接書き換えることはありません＝壊す心配がありません）。

```bash
# 1. GitHub の https://github.com/yokoyama-lab/PyJanus で Fork ボタンを押す
# 2. 自分のコピーを手元に持ってくる（<自分のID> は自分の GitHub ユーザ名）
git clone https://github.com/<自分のID>/PyJanus.git
cd PyJanus
git remote add upstream https://github.com/yokoyama-lab/PyJanus.git
```

### 1.2 動くことを確認する

Python 3.10 以上が必要です。

```bash
python3 --version                  # 3.10 以上であること

# サンプルを1本動かしてみる
python3 -m jana_py.cli --std jana2014 -s tests/jana2014/fixtures/examples/fib.ja
```

次のように出れば成功です。

```
0 8 13
n = 5
x1 = 0
x2 = 0
```

（`Warning: non-zero values remain ...` という行が出ることがありますが、これは
エラーではありません。詳しくは §4.4。）

### 1.3 検査プログラムを動かしてみる

```bash
python3 tools/check_corpus_meta.py report -q     # 進捗を見る
python3 tools/check_corpus_meta.py check         # 注釈済みのファイルを検査する
```

`report` が `annotated 4/97` のように出て、`check` が `0 failed` で終われば
準備完了です。

もうひとつ、`@oracle`（後述）を書くときに使うコマンドがあります:

```bash
python3 tools/check_corpus_meta.py store tests/jana2014/fixtures/examples/fib.ja
```

これは**プログラムが終わった時点の全変数を Python の値として**表示します。
配列は Python のリスト、構造体は辞書、スタックはリストになります。
`@oracle` はこれらの名前をそのまま使って書きます。

### 1.4 見本を読む

すでに4本だけ注釈済みです。**作業を始める前に必ずこの4本を読んでください。**

| ファイル | 技法 | 読みどころ |
|---|---|---|
| `tests/jana2014/fixtures/examples/fib.ja` | clean-accumulation | いちばん短い。`@confirmed` に「F(6)=8, F(7)=13」と根拠が書いてある |
| `tests/jana2014/fixtures/examples/bubble_sort_g.ja` | history-stack | 捨てる情報をスタックに退避する典型例 |
| `tests/jana2014/fixtures/examples/run_length_enc.ja` | plain | 入力を消費して出力に変える、それ自体が可逆な例 |
| `tests/jana2014/fixtures/examples/gcd_g.ja` | history-stack | **ゴミがある例**。`_g` が付く理由が `@keep` を見ると分かる |

### 1.5 練習（自己採点できます）

`fib.ja` の先頭の `// @` で始まる行を**すべていったん消して**、この手順書を見ながら
自分で復元してみてください。`python3 tools/check_corpus_meta.py check
tests/jana2014/fixtures/examples/fib.ja` が `0 failed` になれば形式は正解です。
終わったら `git checkout tests/jana2014/fixtures/examples/fib.ja` で元に戻します。

---

## 2. 1本あたりの作業手順（これを97回繰り返す）

### 手順1 — 次にやるファイルを決める

```bash
python3 tools/check_corpus_meta.py report
```

`not yet annotated:` に並んでいる中から、**上から順に** 1本選びます。
（順番に迷わないためです。極端に長いファイルに当たったら §5 を見てください。）

以下、選んだファイルを `X.ja` と書きます。実際のパスは
`tests/jana2014/fixtures/examples/X.ja` です。

### 手順2 — プログラムを読む

エディタで開いて、**まず既にあるコメントを読みます**。多くのファイルには
「何のアルゴリズムか」「どの教科書から取ったか」が英語で書いてあります。
これが `@summary` と `@source` の材料になります。

次に `procedure main()` を探します。**ここが出発点**です。main の中で
変数に何が入れられ、どの手続きが `call` されるかを追えば、
「何を入力にして何を計算するのか」がわかります。

> Janus の読み方の最小知識:
> - `x += 3` は「x に 3 を足す」。`x -= 3` は引く。**この2つは互いに逆**
> - `x <=> y` は x と y の入れ替え
> - `call f(a, b)` は手続き呼び出し、**`uncall f(a, b)` は同じ手続きを逆向きに実行**する
> - `from 条件 loop ... until 条件` がループ、`if ... then ... else ... fi 条件` が分岐。
>   **`fi` の後ろにも条件が付く**のが Janus の特徴で、逆向き実行のときに使われます
> - `local int t = 0 ... delocal int t = 0` は一時変数。`delocal` の時点で
>   その値であることを主張しています
> - 詳しい文法は `docs/DIALECTS.md`

### 手順3 — 実行して結果を見る

```bash
python3 -m jana_py.cli --std jana2014 -s tests/jana2014/fixtures/examples/X.ja
```

`-s` を付けると、プログラムの出力に続けて**最後の変数の中身（ストア）**が
表示されます。

### 手順4 — ヘッダの雛形を作る

```bash
python3 tools/check_corpus_meta.py stub tests/jana2014/fixtures/examples/X.ja
```

`@expect:` の行が実行結果から自動で埋まった雛形が印字されます。
**この出力を丸ごとコピーして、`X.ja` のいちばん1行目に貼り付けてください**
（`// ---- paste at the top of ... ----` の行だけは貼らずに捨てます）。
既にあるコメントは消さず、その上に置きます。貼ったら `//` を1行はさみます。

ヘッダは「1行目から始まる」「雛形の順番のまま」「間に空行を入れない」ことが
検査されます。ずれてしまったら

```bash
python3 tools/check_corpus_meta.py normalize tests/jana2014/fixtures/examples/X.ja
```

で自動的に整形できます（コメント以外は一切触りません）。

### 手順5 — 6つの TODO を埋める

貼り付けた雛形には `TODO` が6か所あります。これを埋めるのが本番です。
（`@oracle` だけは、どうしても書けなければ行ごと消して構いません。）

#### `@summary:` — 何を計算するか、英語1行

- 英語1文。難しく書く必要はありません。見本の4本の書き方に揃えてください
- 「何を入力に、何を出力するか」がわかることが条件
- 例: `computes the greatest common divisor of x and y by reversible Euclid, keeping the quotients on a stack`

#### `@technique:` — 可逆にするための技法（5つから選ぶ）

情報を捨てる計算は、そのままでは逆向きに実行できません。Janus のプログラムは
次のどれかの方法でそれを回避しています。**判定表**:

| 選ぶ値 | 見分け方 | 例 |
|---|---|---|
| `clean-accumulation` | 入力をそのまま残し、結果を別の変数に `+=` で積み上げる。`uncall` すると引き算で綺麗に戻る | 合計、内積、フィボナッチ、線形探索 |
| `ancilla-flag` | 比較や判定の結果を、余分な1ビット（フラグ変数・フラグ配列）に記録している | 条件付き交換、二分探索 |
| `history-stack` | `stack` 型の変数があり、`push` / `pop` で捨てる情報を退避している | 可逆ユークリッド互除法、バブルソート |
| `bennett-uncompute` | 補助的な値を計算 → 使う → **同じ計算を逆向きに実行して消す**（`call f` の後に対応する `uncall f` があり、結果だけが残る） | 逆BWT |
| `plain` | 上のどれも使っていない。もともと1対1対応（全単射）の計算で、入力を消費して出力に変えている | ランレングス符号化、グレイコード変換 |

- **迷ったら `stack` という単語がファイルにあるか**を見てください。あれば `history-stack` が有力です
- `plain` と `clean-accumulation` の区別: 実行後に**入力がそのまま残っていれば** `clean-accumulation`、
  **入力がゼロになって消えていれば** `plain`
- どうしても決められないときは §6 でエスカレーションしてください。**当てずっぽうで
  埋めないこと。** この欄は後で教材や論文の分類に使うので、間違いは害になります

#### `@source:` — 出典

- ファイルの既存コメントに教科書名・論文名が書いてあればそれを写す
  （例: `Cormen et al., Introduction to Algorithms, 3rd ed., MIT Press, p. 40`）
- 書いていないが、明らかに有名なアルゴリズムの場合も、**勝手に出典を推測して
  書かないでください**。`original` と書きます
- 出典がありそうなのに特定できない場合は `UNKNOWN -- <気づいたこと>` と書いて §6 へ

#### `@confirmed:` — **この作業のいちばん重要な欄**

`@expect:` に入っている数字は「いま実行したらこう出た」という記録にすぎません。
それが**正しい答えなのか**を確かめて、その根拠を書くのがこの欄です。

確かめ方は、次のうち**できるいちばん上のもの**を使ってください。

1. **定義から手計算する**（入力が小さいときはこれが最良）
   例: `fib.ja` — 「F(1)=F(2)=1 なので 1,1,2,3,5,8,13。n=5 なら (8,13)」
2. **Python で同じ計算をして照合する**（3行程度で書けるなら）
   例: `sorted([50,20,40,60,10,30]) == [10,20,30,40,50,60]` を確認した、と書く
3. **出典に載っている値と突き合わせる**（教科書に例が載っている場合）

書き方は英語で、**「何と何を照合して、なぜ一致と言えるか」が読んでわかる**ように。
見本の4本がちょうどこの形です。

> **どうしても確認できないとき**は、正直に
> `@confirmed: UNVERIFIED -- <なぜ確認できなかったか>`
> と書いてください。**これは失敗ではありません。** `report` がこの行を集めて
> 先生に見せる仕組みになっています。無理に「確認しました」と書くほうが
> はるかに悪い結果になります。

#### `@keep:` — 最後に残ってよい変数（＝ゴミの判定）

可逆プログラムは**情報を捨てられない**ので、計算を逆向きに実行できるようにするために
「本来の答えではない中身」が最後まで残ることがあります。これを**ゴミ (garbage)** と
呼びます。可逆計算では、ゴミがあるか無いかがプログラムの質を決める中心的な指標です。

`store` コマンドが「最後に値が残っている変数」を全部見せてくれます。そのうち

- **入力**（プログラムが壊さずに保存したもの）
- **答え**（求めたかったもの）

**だけ**を `@keep:` に並べてください。**残り全部がゴミ**と判定されます。
何も残らないはずなら `@keep: none` と書きます。

例（`gcd_g.ja`）:

```bash
$ python3 tools/check_corpus_meta.py store tests/jana2014/fixtures/examples/gcd_g.ja
gcd_g.ja:
  a = 12  <- @keep
  b = 12  <- @keep
  log = [0, 0, 1]  <- GARBAGE
```

gcd(48,36)=12 が答えなので `a` と `b` は答え。`log` は「各ステップでどちらが大きかったか」
の記録で、逆実行のためだけに残っているのでゴミです。だから `@keep: a, b` と書きます。

**ゴミがあると判定されたら、ファイル名の末尾に `_g` を付けます。**

```bash
git mv tests/jana2014/fixtures/examples/gcd.ja tests/jana2014/fixtures/examples/gcd_g.ja
```

検査は**両方向**です。ゴミがあるのに `_g` が無ければエラー、`_g` があるのにゴミが
無くてもエラーになります。どちらのメッセージも「どう直せばよいか」を書いてあります。

> **この判定は97本すべて済んでいます**（`tests/jana2014/reference/<名前>.py` の
> `GARBAGE` 宣言。ゴミありは32本）。ですから `_g` の付け外しをする場面は普通は
> ありません。**あなたの `@keep` が参照実装の `GARBAGE` と食い違うと検査が落ちます**。
> 落ちたら、どちらが正しいかを考えて §6 で報告してください——**参照実装のほうが
> 間違っている可能性もあります**。

判断のこつ:

- **入力がそのまま残っている**のはゴミではありません（`fib.ja` の `n = 5` は入力）
- **空になったスタック（`nil`）・全部ゼロの配列はゴミになりません**。
  機械が「中身がすべてゼロなら残っていない」と数えます
- 名前が `log` / `blog` / `hlog` / `gb` / `tr` / `...garbage` のものは、まずゴミです
- **答えかゴミか迷うもの**（例: ソートの結果と一緒に残る「並べ替えの順列」）は、
  **ファイル冒頭のコメントに書いてあることが多い**です。`bubble_sort_g.ja` は
  "with optimal garbage" と書いてあり、順列 `ord` がゴミだと分かります
- どうしても決められなければ §6 でエスカレーションしてください

#### `@oracle:` — 正しければ成り立つはずの条件（Python の式）

`@confirmed` に日本語や英語で書いた根拠を、**そのまま Python の式にしたもの**です。
機械が毎回評価して、`True` でなければテストが落ちます。

使える名前は `store` コマンドが表示したものです:

```bash
$ python3 tools/check_corpus_meta.py store tests/jana2014/fixtures/examples/bubble_sort_g.ja
bubble_sort_g.ja:
  a = [10, 20, 30, 40, 50, 60]
  gb = []
  ord = [4, 1, 3, 5, 0, 2]
  sz = 6
```

これを見て、次のように書きます:

```
// @oracle:    a == sorted([50,20,40,60,10,30]) and ord == [...] and gb == []
```

**書き方の鉄則**: `@expect:` の数字をそのまま写しても意味がありません。
`@oracle` は**プログラムの出力を見ずに、アルゴリズムの定義から書く**ものです。
「入力 `{50,20,40,60,10,30}` をソートしたら `sorted(...)` になるはずだ」という
**あなたの主張**を書いてください。プログラムが間違っていれば、ここで食い違います。

- 使える関数: `sorted`, `len`, `sum`, `min`, `max`, `abs`, `all`, `any`, `range`,
  `sorted`, `reversed`, `zip`, `enumerate`, `divmod`, `pow`, `gcd`, `lcm`,
  `factorial`, `comb`, `isqrt`
- 構造体は `p["x"]` でも `p.x` でも書けます
- 全部を書く必要はありません。**確信の持てる部分だけ**で構いません
  （例: `len(a) == 6 and a == sorted(a)` のように「ソート済みであること」だけ書く）
- **書けないときは `@oracle:` の行ごと削除してください。** 空欄で残すとエラーになります

> 見本の `bubble_sort_g.ja` は、この欄が実際に間違いを捕まえた例です。
> 最初 `ord` を「小さい順に並べたときの元の位置」と読んで `@oracle` を書いたところ
> `False` になり、正しくは「元の位置 i の要素が最終的に行き着く順位」だと判明しました。
> **`@confirmed` の散文だけなら気づかずに通っていた間違いです。**

### 手順6 — 検査を通す

```bash
python3 tools/check_corpus_meta.py check tests/jana2014/fixtures/examples/X.ja
```

`0 failed` になればその1本は完了です。エラーが出たときは §7 を見てください。

### 手順7 — 記録する

作業記録ノート（`~/janus-worklog.md` など、リポジトリの外に作ってください）に
1行足します:

```
2026-08-06  10:00-12:30  2.5h  gcd.ja, gray_code.ja, heap_sort_g.ja の3本  / heap_sort は UNVERIFIED
```

**この記録が謝金の根拠になります。**日付・開始終了時刻・実働時間・
やったファイル名を毎回書いてください。

---

## 3. 10本たまったら提出する（Pull Request）

```bash
# 元のリポジトリの最新を取り込む
git fetch upstream
git checkout main
git merge upstream/main

# 作業用の枝を作る
git checkout -b annotate-batch-1

# 変更を確認する（.ja ファイルだけが変わっているはず）
git status
git diff

# 全体の検査が通ることを確認（ここが緑でなければ提出しない）
python3 tools/check_corpus_meta.py check
python3 -m pytest tests/jana2014/test_corpus_metadata.py -q

# コミットして自分の GitHub に上げる
git add tests/jana2014/fixtures/examples/
git commit -m "docs: annotate 10 corpus examples (batch 1)"
git push -u origin annotate-batch-1
```

その後 GitHub の画面に出る「Compare & pull request」から PR を作ります。
PR の説明欄には次を書いてください:

```
対象: gcd.ja, gray_code.ja, ... （10本）
UNVERIFIED: heap_sort_g.ja（理由: 入力が大きく手計算で追えなかった）
質問: injective_bits.ja の technique が ancilla-flag か plain か判断できませんでした
```

先生のレビューを待つ間は、**次の枝を切って作業を続けて構いません**
（`git checkout main && git checkout -b annotate-batch-2`）。

---

## 4. よくあるつまずき

### 4.1 プログラムが長すぎて読めない

280行を超えるファイルが数本あります（`avl_delete_g.ja`, `permutation_rank.ja`,
`tree_sort_g.ja`）。**全部を理解する必要はありません。** `main` だけを読んで
「何を入力に何が出るか」がわかれば `@summary` は書けます。
`@confirmed` が書けなければ `UNVERIFIED` にして先に進んでください。
**1本に1時間以上かけないこと。**

### 4.2 実行が終わらない

`Ctrl-C` で止めて、そのファイルは飛ばし、§6 で報告してください。

### 4.3 出力が何も出ない

`@expect:` の行が1本も出ない場合があります（何も表示せず、ストアも空）。
その場合は雛形に `// @expect:` が1行だけ出ます。そのまま使って構いません。

### 4.4 `Warning: non-zero values remain at end of execution: ...`

エラーではありません。「実行が終わった時点で、この変数にまだ値が残っている」
という通知です。可逆計算では「計算結果」と「消し残したゴミ」の区別が重要なので、
処理系がわざわざ教えてくれています。この行は標準エラー出力に出るので
`@expect:` には含まれません（含めないでください）。

### 4.5 同じに見えるファイルが2つある

`matrixmult.ja` と `matrixmult_v1.ja` のように紛らわしいものがあります。
**どちらも普通に注釈してください**（統合するかどうかは先生が決めます）。
気づいたことは PR の説明に書いてください。

---

## 5. 効率よく進めるコツ

- **似たファイルはまとめて**。`structs_*.ja` は14本ありますが構造がよく似ています。
  1本理解すれば残りは早く進みます。`injective_*.ja` も同様です
- **短いものから片付けてよい**。`wc -l tests/jana2014/fixtures/examples/*.ja | sort -n`
  で行数順に並びます。ただし飛ばした分は必ず後で戻ってくること
- **1日3〜4時間を上限に**。集中が切れた状態で `@confirmed` を書くと、
  「確認したつもり」の記録が残ってしまい、後で全部見直す羽目になります

---

## 6. 困ったときの報告のしかた（エスカレーション）

次のどれかに当たったら、**その場で悩まず**に記録して次に進んでください。

| 状況 | どうするか |
|---|---|
| 答えが合っていない気がする | `@confirmed: UNVERIFIED -- suspect: <何がおかしいか>` と書く。**最重要の発見** |
| technique が決められない | `@confirmed` に書かず、PR の説明に「質問」として書く。technique は暫定で近いものを入れる |
| 出典が特定できない | `@source: UNKNOWN -- <手がかり>` |
| プログラムが動かない・止まらない | そのファイルは飛ばし、PR の説明に書く |
| **自分が触っていないテストが落ちた** | ヘッダを足すと行番号がずれるため、行番号を直書きしたテストがあると落ちます。落ちたテスト名をそのまま PR の説明に書いてください（**あなたのミスではありません**） |
| 手順書に書いていないことが起きた | PR の説明に書く。手順書のほうを直します |

質問をためて**週1回まとめて聞く**のが効率的です。緊急でなければ PR の説明欄に
書いておけば、先生のレビューのときに一緒に返事が来ます。

---

## 7. 検査プログラムのエラーメッセージの読み方

```
FAIL gcd.ja
     line 2: expected 'x = 12' but got 'x = 6'
```
→ `@expect:` の2行目が実行結果と違います。多くの場合、雛形をコピーし損ねたか、
貼り付けた後にファイルを編集してしまったかです。もう一度 `stub` を実行して
`@expect:` の行を作り直してください。

```
FAIL gcd.ja
     missing `@confirmed:`
```
→ 6つの TODO のうち埋め忘れがあります（`@oracle` は行ごと消せば省略できます）。**途中まで書いたヘッダはエラーになります**
（書きかけと未着手を区別するためです）。全部埋めるか、ヘッダごと消すかのどちらかに
してください。

```
FAIL gcd.ja
     `@technique: history stack` is not one of clean-accumulation, ancilla-flag, ...
```
→ 表記が違います。**ハイフン入りで、表からそのままコピー**してください。

```
FAIL gcd.ja
     line 1: unknown field `@summry:` (known: summary, technique, source, confirmed, expect)
```
→ 綴り間違いです。

```
FAIL gcd.ja
     `@oracle: g == gcd(12, 18)` is false for the final store: g=5, x=12, y=18
```
→ **あなたの主張とプログラムの結果が食い違っています。** どちらが正しいかを
考えてください。多くはあなたの式の書き間違い（変数名・添字のずれ）ですが、
**プログラムの側が間違っている可能性もあります**。式を見直しても納得できなければ
`@confirmed: UNVERIFIED -- suspect: <何がおかしいか>` にして §6 で報告してください。

```
FAIL gcd.ja
     the `@` block must start on line 1 (it starts on line 3)
     fields must appear in the order: summary, technique, source, confirmed, oracle, expect
```
→ ヘッダは**ファイルの1行目から**、**雛形の順番のまま**、**間に空行を入れず**に
置きます。`python3 tools/check_corpus_meta.py normalize <ファイル>` を実行すると
自動で並べ直してくれます。

```
FAIL gcd.ja
     the run leaves garbage (log) but the name does not end in `_g`: rename to gcd_g.ja, or add those to `@keep:`
```
→ `@keep:` に挙げなかった変数に値が残っています。**`log` が本当にゴミなら**
`git mv` でファイル名を `gcd_g.ja` にします。**`log` が実は答えの一部なら**
`@keep: a, b, log` に直します。どちらかを選ぶのがあなたの判断です。

```
FAIL fib_g.ja
     the name ends in `_g` but the run leaves no garbage: rename to fib.ja, or narrow `@keep:`
```
→ 逆向きの不一致です。`@keep:` に挙げすぎている（本当はゴミなのに答えだと書いた）か、
`_g` が余計かのどちらかです。

```
FAIL gcd_g.ja
     `@keep:` names lgo, which the final store does not have (it has: a, b, log)
```
→ 変数名の綴り間違いです。`store` コマンドの表示から写してください。

```
FAIL gcd-2.ja
     filename is not lowercase_with_underscores: gcd-2.ja
```
→ ファイル名は英小文字・数字・アンダースコアのみです（新しくファイルを作る場合）。

```
FAIL gcd.ja
     could not run the program: the program exited with status 1: ...
```
→ ファイルの編集でプログラムを壊してしまった可能性があります。
`git diff tests/jana2014/fixtures/examples/gcd.ja` で、**コメント行以外を
変更していないか**確認してください。`git checkout <ファイル>` でやり直せます。

---

## 8. 用語（最低限）

| 用語 | 意味 |
|---|---|
| 可逆プログラミング言語 | 実行を逆向きに巻き戻せる言語。Janus はその代表 |
| ストア (store) | 実行のある時点での、全変数とその値の一覧 |
| ゴミ (garbage) | 計算結果とは別に残ってしまう中間データ。可逆計算では消せないので設計上の関心事 |
| アンシラ (ancilla) | 可逆にするために追加する補助変数 |
| uncompute | 補助的に計算した値を、逆計算によって消すこと |
| フィクスチャ (fixture) | テストが読み込む入力ファイル。ここでは `.ja` プログラム |
| ゴールデンテスト | 「前に動かしたときの出力」を正解として保存し、変化したら知らせるテスト。`@expect:` がこれ |

---

## 9. 関連文書

- `docs/corpus-cleanup-plan.md` — この作業の全体計画（なぜやるか・何本あるか）
- `docs/textbook-programs-plan.md` — 新しい可逆プログラムを**追加する**ときの手順（この作業の次の段階）
- `docs/DIALECTS.md` — Janus の文法（方言ごとの違い）
- `CLAUDE.md` / `README.md` — リポジトリ全体の説明
