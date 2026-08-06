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
| `test_step1_golden.py` | 1ステップ意味論のゴールデン |

**8本すべてが自己整合性の検査**である。「間違った計算を、可逆に、C++ とも Coq コアとも
一致して行うプログラム」は全部通る。**どのファイルにも「何を計算するはずか」が
機械可読な形で書かれていない**。

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
| `perm-to-code.ja` | `perm_to_code.ja` |
| `run-length-enc.ja` | `run_length_enc.ja` |
| `run-length-enc-stack.ja` | `run_length_enc_stack.ja` |
| `stack-operations.ja` | `stack_operations.ja` |
| `matrixmult_v1.0.ja` | `matrixmult_v1.ja`（`.` が識別子として使えないため） |

規約 `^[a-z][a-z0-9_]*\.ja$` は `test_filename_is_lowercase_with_underscores` が
全数で強制する。加えて **`_g` 接尾辞＝ゴミを残すプログラム**（§2 の `@keep`）:
`gcd.ja` → `gcd_g.ja`、`bubble_sort.ja` → `bubble_sort_g.ja`。注釈が済んだ本から
順に判定されるので、残りは B フェーズの中で確定する。残る論点:

- **`test2.ja` は「サンプル」ではなく機能テスト**だった。中身は
  `call test_rev(test_array[0]) // doesn't work` の8行で、**配列要素を実引数に渡せるか**
  の回帰用。`array_element_arg.ja` などへの改名が妥当（規約自体は満たすので強制ではない）
- **`matrixmult.ja` と `matrixmult_v1.ja` は別物**（226行差）。前者は `iterate`、
  後者は `from...loop...until` の明示ループで引数構成も違う。**統合すべきでない**
- `injective_*` 接頭辞が15本あるが、**接頭辞の意味がどこにも定義されていない**
- 二形態（I/O なし／あり）の対応が不揃い: 97本のうち **89本に I/O 版が無い**。
  意図的なのか未整備なのか区別できない

### 1.4 検証コアの被覆が不可視

`pytest tests/jana2014` は **1170 passed / 248 skipped**（7分9秒）。skip の内訳は
構造化された理由文字列で出ているが、集計表がどこにも無い:

| skip 理由（`test_verified_cores_corpus.py`） | 本数 |
|---|---|
| uses procedures (verified Call needs parameters) | 95 |
| array parameter | 60 |
| uses structs | 22 |
| stmt `['body','enter_decl','exit_decl','pos']`（local/delocal） | 15 |
| array declaration | 12 |
| その他（`*=`, `/`, `%`, `&`, `>=` 等） | 14 |

「どのプログラムがどのコアで検証されているか」の表が無いため、**検証されていない
ことに気づけない**。§1.1 と同じ穴の別の顔である。

### 1.5 エラー fixture の期待値が散在

`tests/jana2014/fixtures_errors/*.ja`（52本）のうち、期待エラーメッセージが
テスト側にハードコードされているのは数本（`division-by-zero`、`no-main-proc` 等）。
残りは「非ゼロ終了する」ことしか見ていない可能性が高い。**メッセージが変わっても
気づかない**。

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

| | 内容 | 見積 | 先生の関与 |
|---|---|---|---|
| **A** | 環境構築・見本3本の読解・復元練習 | 3h | 初回 1h 同席 |
| **B** | 94本に `@` ヘッダを付与（本体） | 35–45h | 10本ごとに PR レビュー |
| **C** | 命名・重複の棚卸し（**提案表を作るだけ**） | 6h | 改名の決裁 |
| **D** | 検証被覆マトリクス `docs/corpus-coverage.md` の生成 | 6h | 表の解釈 |
| **E** | エラー fixture 52本に期待メッセージ付与 | 8h | 事前に検査器の拡張が必要 |

合計 **58–68h**（`@oracle` を含めて B は上限側に寄る）。**予算上限 80h** なので
レビュー往復と積み残しに 12–22h の余裕がある。B だけでも独立に価値がある
（回帰ゴールデン 97本 + 実行可能な仕様 + 技法分類の完成）。
C は学生に改名させない——`git mv` と参照の追随は先生か Claude が一括で行う
（§1.3 の5件は実施済み）。

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
| 2 | `test2.ja` の扱い | 保留。**機能テストであってサンプルではない**ことが判明（§1.3） |
| 3 | `matrixmult_v1.ja` を残すか | **残す**。別実装であることを確認済（§1.3） |
| 4 | `injective_*` 接頭辞の定義（15本） | 保留。`docs/` に定義を書いて残すのが既定案 |
| 5 | `@source` が突き止められない場合 | `original`、疑わしければ `UNKNOWN` で先生へ |
| 6 | `@confirmed: UNVERIFIED` / `@oracle` 不一致の処理 | 先生が引き取る。**バグの可能性がある本命** |
| 7 | 二形態の対応（I/O 版が無い89本） | 当面揃えない。§1.3 を記録するに留める |
| 8 | 予算上限 | **80時間**（謝金・非雇用、執行期限 2027-02） |

## 5. 現在の状態

- `tools/check_corpus_meta.py` — 検査器。`report` / `check` / `stub` / `store` / `normalize`
- `tests/jana2014/test_corpus_metadata.py` — CI 連結（97本×3種の parametrize）＋
  パーサ・ストア解釈・oracle 評価・正規化の単体テスト
- 命名規約と体裁は**全数で強制済み**（未注釈の本も対象。ここは incremental ではない）
- 見本 4本注釈済み（いずれも `@oracle` つき）: `fib.ja`（clean-accumulation・ゴミ無し）/
  `run_length_enc.ja`（plain・ゴミ無し）/ `bubble_sort_g.ja`（history-stack・順列がゴミ）/
  `gcd_g.ja`（history-stack・決定ログがゴミ）
- 進捗: **4/97**

### 5.1 見本3本を入れた時点で見つかった罠（対処済み）

`test_debugger_cli.py` が `fib.ja` を読み、`Break at line 19` のように**行番号を
直書き**していた。ヘッダを9行足しただけで5本が落ちた。**94本ぶんの注釈作業に対する
恒久的な地雷**なので、`tests/jana2014/fixtures/fib_debug.ja` に専用コピーを置いて
切り離した（同ディレクトリの `from_debug_simple.ja` 等と同じ流儀）。
corpus の行番号に依存するテストは、これで残っていない。
