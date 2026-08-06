# テストケース・サンプルプログラムの整理計画

*作成: 2026-08-06 / 対象: `tests/` 配下の `.ja` corpus。実施は学部生アルバイトを想定し、
作業手順は `docs/corpus-annotation-manual.md` に分離した。*

## 1. いま何が問題か（実測）

### 1.1 97本のサンプルは「正しさ」を誰も検査していない

`tests/jana2014/fixtures/examples/*.ja`（97本・計 7,086 行）は、8本のテストが
glob で全数を拾っている:

| テスト | 何を検査するか |
|---|---|
| `test_reversibility_corpus.py` | 前進＋反転でストアが戻る |
| `test_inverse_corpus.py` | 逆写像が求まる |
| `test_format_roundtrip.py` | AST→ソース→AST が一致 |
| `test_codegen_corpus.py` | C++ 生成物とインタプリタが一致 |
| `test_verified_corpus.py` / `test_verified_cores_corpus.py` / `test_vjanus_corpus.py` | Coq 抽出コアと一致 |
| `test_step1_golden.py` | 1ステップ意味論のゴールデン。**ただし一度も走っていない**（下記） |

**しかも `test_step1_golden.py` は Haskell 参照実装（`src/Main.hs`）を要求し、それは
この repo に存在せず git 履歴にも一度もない**。同じ理由で `test_control_flow_parity.py`
と `test_local_parity.py` も常時 skip される。**実際に corpus を見ているのは7本**である
（`docs/corpus-coverage.md` §5）。

**残る7本すべてが自己整合性の検査**である。「間違った計算を、可逆に、C++ とも Coq コアとも
一致して行うプログラム」は全部通る。**どのファイルにも「何を計算するはずか」が
機械可読な形で書かれていない**。

> **2026-08-06 に解消**: `tests/jana2014/reference/` に **97本すべての Python 参照実装**を
> 置き、`test_reference_impls.py` が実行結果と突き合わせる。Janus を移植したのではなく
> アルゴリズムの定義から書いてあるので、**プログラムと食い違いうる**。97本すべて一致。
> 5本だけ答えの一部を予測しきれず、`PARTIAL` で明示している（§5.2）。

対照的に `tests/jana2014_in_out/programs/*.ja`（52本）は
`// case: / in: / out: / error:` という機械検査される仕様ヘッダを持ち、
`test_programs.py` が前進・後退の両方向で照合している。**片方にだけ良い規約がある。**

### 1.2 メタデータの体裁が4種類に割れていた → **解消済み**

97本の先頭コメントは、バナー枠 42、`/* */` ブロック 36、`//` 1行 16、
**コメント無し 3** に割れていた。2026-08-06 に `normalize` で 96本を `//` 体裁へ統一
（散文は1行も落とさず、字下げも保つ）。97本すべてで**実行結果が完全に一致**することを
確認済み。以後は `test_header_is_in_house_style` が冪等性として CI で守る。

内容の欠落（「何を計算するか」「出典」「技法」が書かれていない本がある）は §2 の
ヘッダ付与で埋める。

### 1.3 命名と重複 → **一部解消済み**

2026-08-06 に改名（`git mv` と参照の追随を一括、実行結果は不変）:

| 旧 | 新 |
|---|---|
| `perm-to-code.ja` | `perm_to_code_c.ja` |
| `run-length-enc.ja` | `run_length_enc_c.ja` |
| `run-length-enc-stack.ja` | `run_length_enc_stack_c.ja` |
| `stack-operations.ja` | `stack_operations_c.ja` |
| `matrixmult_v1.0.ja` | `matrixmult_v1_c.ja`（`.` が識別子として使えないため） |

規約 `^[a-z][a-z0-9_]*\.ja$` は `test_filename_is_lowercase_with_underscores` が
全数で強制する。加えて **`_g` 接尾辞＝ゴミを残すプログラム**。2026-08-06 に
参照実装（§5.2）の `GARBAGE` 宣言から **97本を全数判定し、32本を改名**した:

```
avl_delete_g  avl_insert_g  bellman_ford_g  bfs_g  binary_heap_g  bubble_sort_g
convex_hull_g  counting_sort_g  cuckoo_insert_g  depth_first_search_g  dijkstra_g
dynamic_array_g  edit_script_g  ext_gcd_g  floyd_warshall_g  gcd_g  hash_chain_g
heap_sort_g  lomuto_partition_g  kmp_g  kosaraju_scc_g  landauer_interp_g
merge_sort_g  modexp_g  next_permutation_g  prim_mst_g  quick_sort_g
selection_sort_g  sort_rank_g  sqrt_g  topological_sort_g  tree_sort_g
```

残る65本は **`_c`（clean）** を付けた。**97本すべてが `_g` か `_c` のどちらかで終わる**ので、
「まだ分類していない本」が clean に紛れ込めない。**何がゴミかはアルゴリズムから決まり、
実際に残るかは実行が決める**。残る論点:

- **`array_element_arg_c.ja` は「サンプル」ではなく機能テスト**だった。中身は
  `call test_rev(test_array[0]) // doesn't work` の8行で、**配列要素を実引数に渡せるか**
  の回帰用。`array_element_arg_c.ja` などへの改名が妥当（規約自体は満たすので強制ではない）
- **`matrixmult_c.ja` と `matrixmult_v1_c.ja` は別物**（226行差）。前者は `iterate`、
  後者は `from...loop...until` の明示ループで引数構成も違う。**統合すべきでない**
- **`injective_*` 接頭辞は撤去済み**（2026-08-06）。15本は **2026-06-03/04 に11本、06-30 に4本**が追加された一群だった。
  コミットメッセージが意図を述べている（"a staircase of eight reversible procedures
  computing **injective integer functions**" / "Each procedure is a **bijection** on its
  array or pair, **with uncall as the inverse**"）。**実演**——計算して印字し、`uncall` で
  入力が戻ることを見せる——であって、結果を残す計算ではない。実測: `printf` を含むのが
  15/15（他は 17/82）、ゴミを残すのが 1/15（他は 31/82）。ただし
  **同じ形の本が接頭辞なしにも12本ある**（`fall` / `fib` / `bwt_plain` / `glaisher` 等）
  ので、**接頭辞は性質ではなく追加された時期の記録**。`_g` / `_c` と違い機械検査できない。
  そのため接頭辞を外し、9本は素直に剥がし、剥がすと曖昧になる6本は内容に即した名前にした:
  `injective_basics` → `int_bijections_c`、`injective_bits` → `bit_bijections_c`、
  `injective_arithmetic` → `arith_roundtrip_c`、`injective_bennett` → `bennett_divmod_c`、
  `injective_lehmer` → `lehmer_code_c`、`injective_partition` → `lomuto_partition_g`、
  `injective_vm` → `stack_vm_c`。副産物として **`gcd_c` / `gcd_g` が同じ算法のクリーン版と
  ゴミ版として並び**、`arith_coding` / `bwt_inverse` / `lehmer_code` は
  `docs/textbook-programs-plan.md` §1 の二形態（examples 側と programs 側で同名）に揃った
- 二形態（I/O なし／あり）の対応が不揃い: 97本のうち **89本に I/O 版が無い**。
  意図的なのか未整備なのか区別できない

### 1.4 検証コアの被覆が不可視 → **解消済み**

skip は理由つきで数えられているが、pytest の要約は総数しか出さないので、
**どのプログラムがどのコアで検証されていないか**はどこにも書かれていなかった。
§1.1 と同じ穴の別の顔である。

2026-08-07 に `tools/corpus_coverage.py` を作り、`pytest --junitxml` の記録から
`docs/corpus-coverage.md` を生成するようにした。判明したこと:

| 検査 | 被覆率 |
|---|---|
| 可逆性・逆写像・整形往復・C++ codegen・vjanus・vjanus 逆・参照実装・メタデータ | **97/97** |
| 抽出 flat コア | 77/97（`*=` `/=` 4+1本、自己再帰＋局所変数 12本 ほか） |
| **2コア一致** | **1/97**（配列引数 57・未対応文 14・構造体 13 で落ちる） |
| **1ステップ意味論のゴールデン** | **0/97**（Haskell 参照実装が存在しない） |

**生きている10列すべてで検査されているのは `fib_c.ja` 1本だけ**である。

### 1.5 エラー fixture の期待値が散在 → **解消済み**

`tests/jana2014/fixtures_errors/*.ja`（52本）のうち、期待エラーメッセージが
テスト側にハードコードされているのは数本だけだった。残りは「非ゼロ終了する」ことしか
見ておらず、**別のエラーに変わっても気づかない**状態だった。

2026-08-06 に52本すべてへ診断ヘッダを付与:

```
// @summary:    two scalar formals of the same procedure bound to the same variable
// @error-kind: execution
// @error:      Identifiers `a' and `b' are aliases
```

`@error-kind` は PyJanus が1行目に出す区分（`parsing` 37→実行前、`validation`、
`execution`）で、**診断が別の段階へ移るのは実際の挙動変化**なのでこれも固定する。
内訳は execution 37 / parsing 7 / validation 7 / **uncaught 1**。

- **`uncaught` は PyJanus 自身の区分ではない**。診断機構をすり抜けて別の何かが実行を
  終わらせたときにこの工具が付ける印で、現在唯一の該当が `infinite-recursion`
  （Python の `RecursionError` がそのまま漏れて `maximum recursion depth exceeded`
  とだけ出る）。**テストがこの1件という事実を固定している**ので、2件目は黙って
  増えない
- **場所（行番号）は意図的に固定していない**。これらのファイルはコメント行が増えるので、
  行番号に鍵を掛けたゴールデンは編集のたびに壊れる——デバッガのテストから外したのと
  同じ罠である（§5.1）。場所の検査は `tests/test_error_reporting.py` が持つ

## 2. 方針

**追加のみ・機械検査つき・1ファイル1単位。** 既存のテストや実行結果を一切変えず、
ファイル先頭に構造化ヘッダを足す。ヘッダの有無・整合性は
`tools/check_corpus_meta.py` が検査し、`tests/jana2014/test_corpus_metadata.py`
が CI に載せる。**未注釈のファイルは skip 扱い**なので、途中で止めても CI は緑のまま。

ヘッダの形（`bubble_sort_g.ja` の実物）:

```
// @summary:   bubble sort that records each comparison outcome on a garbage stack, ...
// @technique: history-stack
// @source:    Cormen et al., Introduction to Algorithms, 3rd ed., MIT Press, p. 40
// @confirmed: a = {50,20,40,60,10,30} sorts to {10,20,30,40,50,60}. ord[i] is where the ...
// @oracle:    a == sorted([50,20,40,60,10,30]) and ord == [...] and gb == []
// @expect: a[6] = {10, 20, 30, 40, 50, 60}
// @expect: gb = nil
// @expect: ord[6] = {4, 1, 3, 5, 0, 2}
// @expect: sz = 6
```

**機械検査される欄が2つあり、答える問いが違う。**

- **`@expect`** は `pyjanus --std jana2014 -s <file>` の**標準出力そのまま**を1行1個。
  「**いまこのプログラムが何をするか**」を留めるゴールデン。書くのに理解は要らない
  （`stub` が埋める）が、**これまで存在しなかった回帰検知**がこれで入る
- **`@oracle`** は最終ストアに対する **Python の式**で、「**このプログラムは何を
  計算するはずか**」。プログラムの出力を見ずにアルゴリズムの定義から書くので、
  **プログラムと食い違いうる**——そこが要点。書けない本は行ごと省いてよい
- **`@keep`** は「最後に残ってよい変数」＝入力の保存分と答え。**残り全部がゴミ**と
  機械が導出し、**ゴミのある本はファイル名が `_g` で終わる**ことを両方向で強制する
  （ゴミがあるのに `_g` が無い／`_g` があるのにゴミが無い、どちらもエラー）

ストア出力は小さく規則的な文法（整数・配列・多次元配列・構造体・スタック）なので、
`store` サブコマンドが Python の値に変換する。`@oracle` はその名前をそのまま使う。

- `@confirmed` は機械が検査できない部分——「その数値が正しいと、どう独立に確かめたか」。
  `@oracle` を書けた本ではその日本語版、書けない本では唯一の記録になる
- `@technique` は `docs/textbook-programs-plan.md` §3 の4分類 + `plain`。
  埋まれば「アンシラフラグの例を出せ」に即答でき、教材・論文の図表に直結する

> **`@oracle` は導入直後に最初の1件を捕まえた。** 見本の `bubble_sort_g.ja` で、
> `ord` を「小さい順に並べたときの元の位置」（argsort）と読んで `@oracle` を書いたら
> `False` になり、正しくは「元の位置 i の要素が行き着く順位」（rank）だった。
> **散文の `@confirmed` だけなら、誤った説明のまま通っていた。**

## 3. フェーズ（学部生アルバイト想定）

> **2026-08-06 に A〜C は機械側で完了した。** 参照実装97本・注釈97本・命名の全域化が
> 済んでいるため、**残る人手の仕事は「生産」から「検証」へ移った**（§3.2）。

| | 内容 | 見積 | 状態 |
|---|---|---|---|
| **A** | 環境構築・見本の読解・復元練習 | 3h | 手順書に残置（新規参加者向け） |
| **B** | 97本に `@` ヘッダを付与 | 35–45h | **完了**（LLM が全数生成、`check` 緑） |
| **C** | 命名・重複の棚卸し | 6h | **完了**（`_g`/`_c`・接頭辞撤去・`array_element_arg_c`） |
| **D** | 検証被覆マトリクス `docs/corpus-coverage.md` の生成 | 6h | **完了**（`tools/corpus_coverage.py`） |
| **E** | エラー fixture 52本に期待メッセージ付与 | 8h | **完了**（`tools/check_error_fixtures.py`＋52本注釈） |

### 3.2 残った人手の仕事（B の完了後）

| # | 内容 | 見積 | なぜ機械にできないか |
|---|---|---|---|
| 1 | **`@source` 97件の裏取り** | 6–8h | LLM が最も捏造しやすいのが書誌。古典アルゴリズムには `original` や「classical …; the reversible formulation is original」と書いてあるが、**実際に当たって確かめた人はまだいない** |
| 2 | **`@technique` 97件の再判定** | 4h | 判断が割れる本がある（例: `binary_heap_g` はスタックでなく配列に履歴を積むが history-stack にした） |
| 3 | **`UNVERIFIED` 5本を埋める** | 8h | 2つの符号化器のビット割当、Crout の積2本、ヒープの整列順。**参照実装を書き足す仕事** |
| 4 | **`@oracle` を93本に書く** | 15h | 参照実装とは独立に、式1本で仕様を書き直す。**LLM の注釈を人が検算する唯一の経路** |

合計 **33–35h**。予算80h の残りは D・E に充てられる。



### 3.0 日程（謝金の執行期限 2027-02 から逆算）

事務処理の余裕を見て、**作業完了は 2026-12 末〜2027-01 中旬**に置く。

| 時期 | 目安 | 内容 |
|---|---|---|
| 2026-08〜09（夏季休業） | 40h | A + B の大半。授業が無く連続時間が取れる |
| 2026-10〜12 | 30h | B の残り + C/D。週2–3h |
| 2027-01 | 10h | E と積み残し、最終 PR |
| 2027-02 | — | 支払処理（作業はしない） |

### 3.1 なぜこの設計が学部3年生に渡せるか

- **1ファイル = 1単位**。中断・再開が自由で、進捗が `report` で数値化される（時給精算の根拠になる）
- **壊せない**。既存ファイルの本体を編集せず、コメント行を足すだけ。`check` が通らなければ
  その1本が失敗するだけで他に波及しない
- **正解が機械で決まる部分（`@expect`）と人間が判断する部分（`@confirmed`）が分離**
  されているので、レビューは `@summary` / `@technique` / `@confirmed` の3行を読むだけで済む
- 副産物として、学生は可逆計算の4技法を97回反復して身につける。**卒研の下準備になる**

## 4. 決裁の状況

| # | 論点 | 状態 |
|---|---|---|
| 1 | ハイフン等の改名 | **決裁済・実施済**（§1.3） |
| 2 | `array_element_arg_c.ja` の扱い | 保留。**機能テストであってサンプルではない**ことが判明（§1.3） |
| 3 | `matrixmult_v1_c.ja` を残すか | **残す**。別実装であることを確認済（§1.3） |
| 4 | `injective_*` 接頭辞（15本） | **決裁済・実施済**: 接頭辞を撤去（§1.3）。分類は `@technique` / `@summary` が担う |
| 5 | `@source` が突き止められない場合 | `original`、疑わしければ `UNKNOWN` で先生へ |
| 6 | `@confirmed: UNVERIFIED` / `@oracle` 不一致の処理 | 先生が引き取る。**バグの可能性がある本命** |
| 7 | 二形態の対応（I/O 版が無い89本） | 当面揃えない。§1.3 を記録するに留める |
| 8 | 予算上限 | **80時間**（謝金・非雇用、執行期限 2027-02） |

## 5. 現在の状態

- `tools/check_corpus_meta.py` — 検査器。`report` / `check` / `stub` / `store` / `normalize`
- `tests/jana2014/test_corpus_metadata.py` — CI 連結（97本×3種の parametrize）＋
  パーサ・ストア解釈・oracle 評価・正規化の単体テスト
- 命名規約と体裁は**全数で強制済み**（未注釈の本も対象。ここは incremental ではない）
- 見本 4本注釈済み（いずれも `@oracle` つき）: `fib_c.ja`（clean-accumulation・ゴミ無し）/
  `run_length_enc_c.ja`（plain・ゴミ無し）/ `bubble_sort_g.ja`（history-stack・順列がゴミ）/
  `gcd_g.ja`（history-stack・決定ログがゴミ）
- 進捗: **97/97 注釈済み**（`@oracle` は 4/97）。技法の内訳は
  clean-accumulation 30 / history-stack 28 / plain 26 / bennett-uncompute 9 / ancilla-flag 4

### 5.2 参照実装 (`tests/jana2014/reference/`)

97本すべてに `expected()` を持つ Python モジュールがある。**Janus を読まず**（`jana_py`
の import・`.ja` の読み込み・subprocess は衛生テストが禁止）、アルゴリズムの定義から
書いてある。入力だけは Janus の `main` が持つ定数なので転記する。

- **ゴミは主張せず、代わりに `GARBAGE` で名指しする**。決定ログ・商スタック・ソートの
  順列は「この可逆符号化の産物」であって関数の値ではない
- **非自明な残余は `expected()` か `GARBAGE` のどちらかに必ず入る**（
  `test_every_surviving_value_is_accounted_for`）。どちらにも入らない値は
  「誰も説明できていない残余」なので、テストが質問として突きつける
- **答えを予測しきれない5本**（`adaptive_huffman` / `ppm_lite` / `matrixmult` /
  `matrixmult_v1` / `binary_heap`）は `PARTIAL` に理由を書き、テストがその一覧を固定する。
  勝手に増えない
- AVL（`avl_insert` / `avl_delete` / `tree_sort`）は独立実装が **key/left/right/ht/root
  の配列まで完全一致**した。ノード番号の割り当て規約まで含めて合うので、偶然ではない

### 5.1 見本3本を入れた時点で見つかった罠（対処済み）

`test_debugger_cli.py` が `fib_c.ja` を読み、`Break at line 19` のように**行番号を
直書き**していた。ヘッダを9行足しただけで5本が落ちた。**94本ぶんの注釈作業に対する
恒久的な地雷**なので、`tests/jana2014/fixtures/fib_debug.ja` に専用コピーを置いて
切り離した（同ディレクトリの `from_debug_simple.ja` 等と同じ流儀）。
corpus の行番号に依存するテストは、これで残っていない。
