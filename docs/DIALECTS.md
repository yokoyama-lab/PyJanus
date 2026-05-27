# PyJanus ダイアレクト（言語標準）一覧

PyJanus は `--std` で6つの言語標準を切り替えられる。各ダイアレクトは専用パーサ
（`jana_py/parser_<std>.py`）を持ち、すべて共通の AST を生成する。本書の構文は
実際にパーサで検証した挙動に基づく。

## 全体像

6つは大きく **2系統** に分かれる。

- **クラシック Janus 系**（`procedure` + `then/fi`・`from/do/loop/until`、字下げ構文）:
  `janus1982`, `janus1982ext`, `jana2014`, `jana2014basic`, `jana2014_in_out`
- **モダン C 系**（`void` + `{}`・`;`・`==`、C 風）: `janus2026`

歴史的な発展: **1982（オリジナル）→ 2007 Jana（Yokoyama–Glück）→ 2014 → 2026（C 化）**。

## 比較表

| std | main | 手続き引数 | 変数宣言/初期化 | struct | 入力 / 出力 | 系統 |
|---|---|---|---|---|---|---|
| `janus1982` | `procedure main`（括弧任意） | **不可** | 型なしのみ（暗黙 int）、初期化なし | ✗ | 入力なし / ストア | クラシック・最厳格 |
| `janus1982ext` | `procedure main` | 型付き/型なし両対応 | 型付き/型なし、初期化 任意 | ✗ | 入力なし / ストア | クラシック + 拡張 |
| `jana2014` | `procedure main()` | 型付き（`int x`） | 型付き、初期化 可 | ✗ | **入力なし** / `printf`・`show` | クラシック（フル） |
| `jana2014basic` | `procedure main()` | **型なし**（`f(x)`） | 型なし中心（`int` のみ）、初期化なし | ✗ | `read` / `write`（非厳密）・`printf`・`show` | クラシック基本版 |
| `jana2014_in_out` | `procedure main()` | 型付き（`int x`） | 型付き、初期化 可 | ✗ | **厳密可逆 `read` / `write`**・`printf`・`show` | jana2014 + 可逆 I/O |
| `janus2026` | `void main() { … }` | 型付き C 風 | 型付き、初期化 可 | **✓（唯一）** | `scanf`（厳密）・`read`/`write`（非厳密） / `printf` | モダン C 系（既定） |

## 各ダイアレクトの個性

### janus1982 — 厳格オリジナル
- 1982 年のオリジナル Janus に忠実。最も制約が強い。
- 手続きパラメータ **なし**。グローバル変数は型なしのベア宣言（`x`、暗黙 int）。
- パラメータを書くと「`janus1982ext` を使え」と明示的にエラー案内。

### janus1982ext — 1982 + 拡張
- 1982 のベース構文に現代的な利便性を追加。
- 括弧なし `procedure main` のまま、**パラメータ（型付き/型なし両方）と初期化子**を許可。
- クラシック構文を保ちつつ表現力を上げた版。

### jana2014 と jana2014basic — なぜ2つあるか

これは「2014 の新旧」ではなく、**上流の Haskell 版 Jana プロジェクトが持つ2つの別パーサ**を
それぞれ移植したものである（`parser_jana2014.py` の冒頭 docstring 参照）。

- `jana2014` ← 上流 `Jana.Parser`（**フル版**）
- `jana2014basic` ← 上流 `Jana.ParserBasic`（**基本版＝オリジナルの最小 Jana/Janus**）

恣意的な簡易版ではなく、リファレンス実装が元から2系統の文法を持つため両方を再現している。

#### jana2014 — Jana 2007/2014 フル版（標準的クラシック）
- `procedure main()`（括弧あり）、**型付きパラメータ前提**。
- 多様な整数型（`i8`〜`u64`）・`bool`・`stack`(push/pop/empty/top/size)・
  `local`/`delocal`・`ancilla`/`constant`・`iterate`・`printf`/`show`/`print` などフル機能。
- **`read`/`write` は持たない**（入力は変数ストア、出力は `printf` 等）。
- 本リポジトリの可逆性／circuit／pebble などの中核機能テストはこの構文で書かれている。

#### jana2014basic — Jana 基本版（最小モデル）
- `procedure main()` だが、**`int` 型のみ**・**パラメータは型なし**（`procedure f(x)`）。
- `local`/`delocal`・`stack`・`ancilla`/`constant`・`iterate` などは **持たない**。
- 代わりに古典的な入出力文 **`read x` / `write x`** を持つ（ただし**非厳密**：read は
  ゼロ要求なし、write はクリアなし）。
- `;` 始まりの行コメントも許容。教育・最小モデル向け。

### jana2014_in_out — jana2014 + 厳密可逆 I/O（デバッグ用）

`jana2014`（フル版）と同一の構文に、**厳密に可逆な `read` / `write` ペア**を追加した
PyJanus 独自のダイアレクト。入力と期待出力を与え、実行方向を選んで結果を検証する用途。

- `read x` — `x` が **0 であることを要求**し、入力を1つ `x` に取り込む（非ゼロならエラー）。
- `write x` — `x` を出力し、**`x` を 0 にクリア**する。
- `read` と `write` は**厳密な逆**（`invert.py` で `read`↔`write`）。よって
  `順方向(入力)→出力` と `逆方向(出力)→入力` が成り立つ。
- 非消費のデバッグ出力には、継承した `printf` / `show` を使う（read/write と役割分担）。

**CLI（任意の std で使えるが本ダイアレクト向け）:**
- `--direction {forward,backward}` — `backward` は **プログラム全体を逆化して実行**
  （main 本体＋手続きをグローバル反転。`-i` の「逆ソース印字」とは別で、必ず実行する）。
- `--expect TEXT` / `--expect-file PATH` — 実行出力と照合し、一致なら `OK`／終了コード 0、
  不一致なら差分を表示して終了コード 1（末尾改行は無視）。
- 入力は stdin（位置引数が1行ずつ stdin に渡る、またはパイプ）。

```bash
# 入力 3,7 を順方向 → 出力 "7,3" を検証
pyjanus --std jana2014_in_out swap.ja 3 7 --direction forward --expect $'7\n3'   # OK
# その出力を逆方向 → 元入力 "3,7" に戻ることを検証
pyjanus --std jana2014_in_out swap.ja 7 3 --direction backward --expect $'3\n7'  # OK
```

### janus2026 — モダン C 系（既定）
- 唯一の **C スタイル**: `void main() { … }`、文末 `;`、ブロック `{}`、条件は `==`。
- **`struct` をサポートするのはこれだけ。**
- 機能が最も豊富: `for` ループ、`switch/case/break`、C 風 `local … { } delocal …`、
  `ancilla` / `constant`、型キャスト `(u8)x`、三項演算子（要括弧 `(c ? a : b)`）。
- `skip` キーワードは **廃止**。`assert` は条件を括弧で囲む必要がある（`assert (cond)`）。
- 入出力は **`scanf`（厳密：ゼロ要求あり）/ `printf`** が主。`read`/`write` も構文上は
  受理するが**非厳密**（jana2014_in_out のような可逆ペアではない）。
- フォーマッタは全ダイアレクトをこの C 形式で出力する。

## 実装上の癖（共通の可逆性意味論）

- `if … fi` / `switch` は出口条件の整合をアサートする（分岐の取り違えを禁止）。
- `push(x, s)` は `x` を 0 にクリアし、`pop(x, s)` は `x == 0` を要求する。
- `local … delocal …` は delocal 時の値一致を要求する。
- `struct` 機能は janus2026 専用のため、構造体を使うプログラムは他ダイアレクトへ移植不可。
- 入力文を持たない方言（`janus1982`/`janus1982ext`/`jana2014`）では、**入力＝main 変数の初期値**、
  **出力＝最終ストア**（`-s` でダンプ）という古典的な可逆計算モデルになる。
  ランタイム入力が要るなら `jana2014_in_out`（厳密可逆 `read`）/ `jana2014basic`（非厳密 `read`）
  / `janus2026`（`scanf`）を使う。
- `read`/`write` の**厳密な可逆セマンティクス（read はゼロ要求・write はクリア・互いに逆）は
  `jana2014_in_out` 限定**。他方言の `read`/`write` は従来どおり非厳密（ランタイムは `std` で分岐）。

## テストカバレッジの現状（参考）

| std | テスト数 | 状況 |
|---|---|---|
| `jana2014` | ~199 | 充実 |
| `janus2026` | ~168 | 充実 |
| `janus1982` | ~24 | まあまあ |
| `jana2014_in_out` | ~9 | 入出力・順逆実行・検証をカバー |
| `jana2014basic` | 3 | 手薄（スモークのみ） |
| `janus1982ext` | 3 | 手薄（スモークのみ） |

補強する場合は `jana2014basic` と `janus1982ext` が優先。
