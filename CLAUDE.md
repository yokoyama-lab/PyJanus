# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## 現在の状態（handoff: 2026-08-04）

**全域性検査器（`jana_py/smv.py`）の符号化が全項目 Rocq で裏付けられた**セッション。
前回残っていた「別名検査の結線」「large-block 同値」「段数保存」の3つを閉じ、続けて
`docs/loop-queue.md` の14項目（うち後半6項目が**配列対応**）を自走ループで消化した。

### 読む順

1. `coq/README.md` — 何が証明済みかの claims 表。「What compilation costs」
   「What the totality checker rests on」「The checker's aliasing decision」
   「The large-block encoding」の4節が直近の成果
2. `docs/totality-checking.md` — 検査器の設計・3つの罠・実測値・§8〜§11 の機械検証
3. `docs/reversible-categorical-semantics.md` — 圏論層と先行研究の対応（新規性の線引き）
4. `coq/RevSemantics.v` → `RevCompile.v` → `RevSteps.v` → `RevError.v` →
   `RevSmvExpr.v` → `RevSmvAlias.v` → `RevSmvBlock.v`（この順で読むと筋が通る）

### 確定している事実（再確認不要）

- **`RevLang` 関手を2回適用すると別の帰納型になる。** そのため各ファイルが
  `Module L := RevLang P` と書いていた間はファイル跨ぎの一致が**記述すらできなかった**。
  現在は `RevSmallStep → RevDenote → RevFix → RevCompile` の連鎖で1つを共有し、
  `RevSemantics.v` と `RevSteps.v` がそこから射影する。
  **新しい意味論を足すときはこの連鎖に入れる**
- **5意味論の全10ペアが iff**（`RevSemantics.all_agree`）。5つの `REV_PRIM` 実例
  （`RevJanus` / `RevExt`＝配列と `local`/`delocal` 付き Janus / `RevStack` / `RevCA` / `RevToy`）
  すべてで成立を確認済み。`RevArr` / `RevFrame` / `RevProc` は functor の外なので**射程外**
- **検査器の符号化は4項目すべて機械検証済み**: `RevError.fail_iff`（ERR 到達 ⟺ 表明破れ）、
  `RevSmvExpr.mfdiv_correct`（床除算）、`RevSmvAlias.alias_check_is_exact`（別名）、
  `RevSmvBlock.block_sound`（large-block）。残る穴は**それらの接合**（CFG 全体を1つの
  Coq モデルにしていない）だけ
- **コンパイルは段数厳密で両方向**（`RevSteps.compilation_is_step_exact_iff`）＝倍率1。
  機械の決定性（`mstepn_det` / `mrunn_det_halt`）から段数はプログラムの性質であり
  導出に依らない（`execn_unique`）。**逆行のコストは順行と同じ**（`execn_rev`）で、
  コード長も同じ（`csize_invert`）。段数は fuel の十分量でもある（`execn_runn`）が
  **最小ではない**（fuel は深さ・段数は動作数。`the_fuel_bound_is_not_tight`）
- **別名検査の結線で smv.py の穴が2つ出た**（2026-08-04 修正済み）。
  (a) **swap に別名検査が無く**、`x <=> x` が恒等として模型化されて nuXmv が
  「安全」と**証明していた**。(b) 仮引数の二重束縛それ自体を ERR にしていた（誤検出）。
  修正方針は「検査は文ごと、対象は代入と swap の2つ」
- **PyJanus の別名検査は静的でなく実行時**。`x += x` は `validate_program` を通る
- **nuXmv の整数 `/` は0方向切り捨て、`mod` は SMT エンジンでは整数に使えない**。
  パスは `LD_LIBRARY_PATH=~/dev/infra/tools/nuxmv-libs ~/dev/infra/tools/nuXmv`
  （PATH には無い）
- **符号化が決定率を左右した**: large-block（直線部を1遷移に）で `--init zero` が
  2/8 → 5/8 proved。ASSIGN 形式はモデルを1/7にしたが**判定は1つも変えなかった**
- 実測（149本・IC3・120秒・`--init zero`、2026-08-04 の配列対応後）:
  refuted 17 / proved 10 / unknown 12 / unsupported 96 / parse-error 7 / static-error 7。
  **examples の断片内は 8 → 17本**。誤検出ゼロは維持（examples から refuted は出ていない）
- **配列でボトルネックが移った**: 「断片外だから測れない」→「表現できるが決められない」。
  そして**符号化パラメータは3つとも律速でなかった**（`docs/totality-checking.md`
  §5.4〜§5.7）: 位置数（§5.4）、`_BLOCK_CHARS`（§5.6、判定不変）、モデルサイズ
  （§5.7、native 化で 5.9倍縮小・配列長に線形になっても**判定は17本すべて同一**）。
  残る説明は問題そのものの難しさで、**次に触るなら符号化でなく問題の与え方**
  （事前条件・配列長の固定・性質の分割）
- **配列の符号化は2種類**あり既定は `arrays="native"`（nuXmv の `array 0..n-1 of integer`）。
  変数添字の**読み**は配列型で書けるが**書き**は nuXmv が拒否するので要素ごとの条件付き
  更新のまま。`"expand"`（要素展開）も残してあり両方テストで固定
- **`assign` 形式は書かれない変数に `next` を出さないと無拘束**になる（SMV の意味論）。
  2026-08-05 に `next(v) := v;` を出すよう修正。`trans` 形式は免疫があり、§5 の測定は
  そちらなので公表値は無傷。誤検出方向なので既存の proved も有効
- **配列は参照渡し**なので、インライン展開が実引数のタプルを持てば長さ未指定 `int a[]` も
  解決する。新しい機構は要らなかった
- `python3 -m pytest tests/` だけで4つの抽出インタプリタとの一致が走る（`tests/conftest.py`
  が必要なものをビルドする）。**1695 passed / 345 skipped**。`PYJANUS_SKIP_VERIFIED=1` で抑止
- `.vo` は**ツールチェーン固有**。rocq は 2026-07-29 に OCaml 5.3.0 版へ入れ替わった。
  「compiled with OCaml 5.4.1 while this instance ... 5.3.0」も
  「inconsistent assumptions」も対処は同じ `cd coq && make clean && make`
- 論文としての見立て: **情報処理学会 PRO なら1本**。RC は差分の立て方次第。ITP/CPP は厳しい

### 次の作業候補

1. **論文執筆（PRO）** — 材料は揃った。軸は「可逆言語の意味論を言語非依存に一度証明し
   5実例へ落とす／コンパイル後も可逆性と**段数**が転送される／独立実装との差分検証／
   検査器の符号化を機械検証して実際に不健全性を1件発見」（大）
2. **決定率を上げる — ただし符号化ではない**。3案とも測って判定が動かなかった（§5.4〜§5.7）。
   次は**問題の与え方**: `--smv-assume` で事前条件を与える／配列長を小さく固定して
   スケールを見る／性質を分割する（例: ERR の種類ごとに INVARSPEC を分ける）（中）
5. **stack（31本）と struct（13本）** — 次の被覆率の壁。可変長の状態と複合型で、
   配列とは別種の作業（大）
3. **CFG 全体の接合** — `RevError.v`（抽象 `prim`/`guard`）と `RevSmvBlock.v`（具体
   `sstmt`）は `RevLowerStmt.lower_stmt_iff` 経由で繋がるが、1つの Coq モデルには
   なっていない。ここを閉じると検査器の符号化が端から端まで1本になる（大）
4. **`--smv` の剰余符号化** — 現在は `-m`/`-p` との併用を拒否している（2026-08-04）。
   符号化するなら移行先は `RevSMod.v` / `RevExtSMod.v` だが、剰余環では `*=` / `/=` の
   条件が「非零」ではなく**単元**に変わるので現在の義務は流用できない。**設計判断**（中）

### 注意

- **この repo の `CLAUDE.md` は git 追跡下**（グローバル方針の例外）。この現状節は
  未コミットのまま置いてある（`docs/textbook-programs-plan.md` への参照追加・7行も同様）
- **自走ループの手順・ゲート・保留項目は `docs/loop-queue.md`**。キューは一度空になった
  （8/8）。再開するときは項目を足してから `/loop` を回す
- `experiments/ultrametric-m0/` は **2026-07-10 の既存作業で未追跡**。直近セッションの
  産物ではないので消さないこと。追跡するか移すかは要判断
- `coq/audit.sh` の `Print Assumptions` に書くモジュールは、同ファイル冒頭の
  `Require Import` に入っていないと失敗する
- Coq の `repeat split` は **`reflexivity` で閉じる目標を勝手に消す**ので、
  その後の bullet 数がずれる。前セッションで3回、今セッションで1回踏んだ
- Coq のコメント内で `*同時*)` のように強調の `*` の直後に `)` が来ると
  **コメントが途中で閉じる**。`-- 強調 --` で回避
- `Open Scope Z_scope` 下では `p 2` の `2` が `Z` に取られる。nat 添字は `2%nat`
- `induction ... using execn_mut` の IH 名は `IHexecn` / 複数なら `IHexecn1..3`。
  `eapply step_then; [ .. | | lia ]` のように空スロットを挟むと、`lia` が
  未確定の evar を見て落ちる。**段数は `with (n1 := ..) (n2 := ..)` で明示する**
- `.vo` と抽出物（`janus_frame.ml` 等）は gitignore 対象のビルド生成物

## Overview

PyJanus is a dependency-free (Python 3.10+) interpreter for **Janus**, the
reversible programming language. Beyond running programs forwards and backwards,
it provides a debugger, a C++ code generator, an inverse interpreter, and a set
of reversible-computing research tools (Bennett embedding, circuit synthesis,
equivalence checking, pebble-game space profiling).

> **To grow the reversible-program corpus** (adding textbook/pearl programs one
> after another), see `docs/textbook-programs-plan.md` — the add-a-program
> workflow, the two-form layout (`tests/jana2014/fixtures/examples/` +
> `tests/jana2014_in_out/programs/`), two-core verification, and the backlog.
> Its catalog of source material is `docs/reversible-pearls.md`; dialects live in
> `docs/DIALECTS.md`.

## Commands

```bash
# Run a program (default standard: janus2026)
python3 -m jana_py.cli --std jana2014 tests/jana2014/fixtures/examples/fib.ja
python3 -m jana_py.cli --std janus1982 prog.ja   # select language dialect

# Common modes (all via the single CLI entry point)
python3 -m jana_py.cli -i prog.ja        # invert: print inverted source
python3 -m jana_py.cli -a prog.ja        # print AST as JSON
python3 -m jana_py.cli -c prog.ja        # emit C++ code
python3 -m jana_py.cli -d prog.ja        # step-debugger output
python3 -m jana_py.cli --circuit prog.ja --profile prog.ja
python3 -m jana_py.cli --inverse '{"x": 10}' prog.ja   # final store -> initial store
python3 -m jana_py.cli -I mylib prog.ja   # add an #include search dir (repeatable)

# Tests (unittest-based, but run under pytest; organized per dialect under tests/<std>/)
python3 -m pytest tests/ -q
python3 -m pytest tests/jana2014/test_reversibility.py -q          # single file
python3 -m pytest tests/jana2014/test_reversibility.py::ReversibilityTests::test_swap   # single test
python3 tests/jana2014/test_reversibility.py                # unittest-style files also run directly
```

### Standard library

A bundled, all-reversible standard library lives in `jana_py/lib/std/` (it ships
with the package). `#include "std/array.ja"` resolves through the preprocessor's
search path — relative to the including file first, then any `-I DIR`, then the
**dialect-specific** stdlib (`jana_py/lib/<std>/`, e.g. `lib/jana2014/`), then the
canonical janus2026 stdlib (`jana_py/lib/std`). `preprocess.STDLIB_DIR` points at
`jana_py/lib`; the dialect is threaded via `preprocess_text(..., std=args.std)`.
Modules:

| module           | procedures |
|------------------|------------|
| `std/array.ja`   | reverse, rotate_left, xor_into, add_into, cswap |
| `std/bits.ja`    | flip_bit, swap_bits, bit_reverse, rotate_bits_left |
| `std/math.ja`    | mul_acc, divmod, gcd (reversible Euclid w/ quotient stack) |
| `std/stack.ja`   | copy_top, move_all |
| `std/reduce.ja`  | sum_into, dot_into, count_into (clean accumulators); min_into, max_into (need history) |
| `std/sort.ja`    | sort (reversible bubble sort recording swap decisions in flags[]) |

Every library procedure must be reversible (`uncall` undoes `call` exactly) and
have a forward-AND-backward test (`tests/janus2026/test_stdlib_*.py`). Two
recurring reversibility patterns the library encodes: (1) **ancilla flags** — a
value-only comparator (`cswap`/`sort` with `fi (x < y)`) breaks its reversibility
assertion on an already-ordered pair, so it records the swap decision in an extra
flag bit instead; (2) **history** — operations that discard information (`gcd`,
`sort`, `min_into`/`max_into`) are made reversible by keeping just enough history
(a quotient stack, a flag array, a stack of deltas) for `uncall` to replay them
backwards. Clean accumulators (`sum_into` etc.) need neither: they preserve their
input, so `uncall` simply subtracts.

The library is authored **once** in janus2026; copies for other dialects are
*generated* by re-emitting the parsed AST with that dialect's formatter
(`jana_py/_gen_stdlib.py` → `jana_py/lib/jana2014/std/*.ja`). Edit only the
janus2026 source, then run `python -m jana_py._gen_stdlib`;
`tests/janus2026/test_stdlib_dialects.py` asserts the copies are current AND that
each computes the same store as the janus2026 original — it is the correctness
check for the AST→dialect-source formatters.

There is no lint step; the package is pure Python (`pyproject.toml` defines
the `pyjanus` console script → `jana_py.cli:main`). CI
(`.github/workflows/test.yml`) runs the pytest suite on every push/PR
against Python 3.10/3.12/3.14 — install locally with `pip install -e ".[dev]"`.

## Architecture

The interpreter is a linear pipeline, all wired together in `jana_py/cli.py:main`:

```
source text
  → preprocess.preprocess_text   (#define/#include/#ifdef; tracks line_origins for error maps)
  → parser_<dialect>.parse_program  (dialect chosen by --std; all emit the SAME ast.py types)
  → validate.validate_program    (static checks: unique bindings, struct defs, main proc, ...)
  → consumer:
      runtime.Runtime.run        (forward/backward execution + debugger)
      invert.invert_program      (AST→AST: swap call/uncall, reverse statement order)
      format.formatter_for_std   (AST→Janus source; CFormatter = C-style, with
                                  ProcedureFormatter / Janus1982Formatter
                                  subclasses overriding dialect-specific syntax)
      c_codegen.format_program   (AST→C++)
      circuit / pebble / inverse / bennett / equiv  (research tools)
```

**Key design point — multiple dialect parsers, one shared AST.** The original
`parser.py` was split into per-standard modules, all exposing the same
`parse_program(filename, text, line_origins)` signature and producing the same
`jana_py/ast.py` node types. The dialect is selected by `--std`:

| `--std` value   | parser module               |
|-----------------|-----------------------------|
| `janus2026`     | `parser_janus2026.py` (default, C-style) |
| `jana2014`      | `parser_jana2014.py`        |
| `jana2014basic` | `parser_jana2014basic.py` (subclasses the jana2014 parser; 1982-flavored hybrid grammar) |
| `jana2014_in_out` | `parser_jana2014_in_out.py` (subclasses the jana2014 parser; adds reversible `read`/`write` I/O) |
| `janus1982`     | `parser_janus1982.py` (strict original) |
| `janus1982ext`  | `parser_janus1982ext.py` (re-exports `parser_jana2014basic`) |

Because every consumer (runtime, invert, format, codegen, all analysis tools)
operates on the shared AST, **changes to `ast.py` ripple across all of them** —
when adding or changing a node type, update the parser(s), the runtime, `format.py`,
`c_codegen.py`, and `invert.py` together. `invert.py` is the conceptual heart of
reversibility: each statement type must define its own inverse.

**`runtime.py` is large (~2500 lines)** and central. `Runtime` holds the store of
`Cell`s; lvalue aliasing/indexing is handled through proxy cells (`CellProxy`,
`StructFieldProxy`, `ArraySliceProxy`, `ConstantParamProxy`). It also implements
modular arithmetic (`-m` bits / `-p` prime), the debugger, and backward execution.

### Tests

Tests live in per-dialect directories mirroring the `--std` values
(`tests/jana2014/`, `tests/jana2014_in_out/`, `tests/janus2026/`, ...). Most are
`unittest.TestCase` classes (runnable under pytest), but a few files are
pytest-style (fixtures like `capsys`) and silently run nothing under plain
`python3 file.py` — use pytest to run the full suite. Most tests invoke the CLI
via `subprocess` against `python3 -m jana_py.cli`, with `.ja` fixtures in
`tests/<std>/fixtures/` (valid programs) and `tests/<std>/fixtures_errors/`
(programs expected to fail, e.g. aliasing violations, assertion failures, parse
errors). `tests/jana2014_in_out/programs/` holds `.ja` programs with embedded
`// case:/in:/out:` specs that `test_programs.py` runs forward AND backward.
When adding a language feature, add a fixture and assert both forward result and
reversibility.

Note: library helpers `encode.py` and `inverse.py` hardcode the `janus2026`
parser; `parser.py` is only a backwards-compat shim re-exporting
`parser_jana2014.parse_program` for old external callers.

## Formal mechanization (`coq/`)

`coq/` is a Rocq/Coq 9.1 development that machine-checks Janus's reversibility,
**independent of the Python interpreter**. The core abstraction is the module
type `REV_PRIM` + functor `RevLang` (`RevCore.v`): supply the atomic primitives
and three local laws (`pinv_invol`, `pstep_det`, `pstep_rev`) and the functor
proves the headline results once for all instances — `exec_rev`, `exec_iff`,
`exec_det`, and `exec_injective` (reversibility: a final store determines the
initial store). Other `.v` files are instances/extensions (denotational
semantics, dagger-category structure, Bennett embedding, an extracted fuel
interpreter).

- Build: `cd coq && rocq makefile -f _CoqProject -o Makefile && make` (whole dev
  ≈ 6 s). `.vo` files are build products (gitignored), so build with whatever
  single `rocq` is on PATH — currently opam 9.1.1; a `.vo` left over from a
  *different* install fails with "inconsistent assumptions over library
  Corelib.Init.Prelude", fixed by `make clean && make`. If `make` asks for a
  `rocqworker` under a path that no longer exists, the stale dep file is to
  blame: `rm -f coq/.Makefile.d` and regenerate the Makefile.
- `coq/audit.sh` builds the dev and asserts every headline theorem depends on at
  most `functional_extensionality` — no extra axioms, no `Admitted`. CI runs it
  (`.github/workflows/coq.yml`).
- How this development compares to the other machine-checked Janus (Paolini,
  Piccolo & Roversi's Matita formalization, TYPES 2015) — and which of its
  results are still worth importing — is tracked in
  `docs/janus-formalizations.md`.
- **Before claiming anything in the categorical layer is new, read
  `docs/reversible-categorical-semantics.md`.** Glück & Kaarsgaard already give
  the categorical semantics of Janus-class languages (join inverse categories,
  LMCS 2018), and the trace-as-loop, `test†` conditional, join-based recursion
  and rig structure all appear there first. That doc is the theorem-by-theorem
  correspondence and says what is left as genuinely new.

### Differential testing (`coq/harness/`)

The verified development is the oracle for the Python implementation:

- `differentialar.py` / `differential.py` — run the **verified** interpreter
  (`run`, extracted to OCaml from `RevExtract.v` and proved sound) against
  `pyjanus -s` on the same `.ja` program and compare final stores. The two
  interpreters are completely independent (extracted Coq vs hand-written Python).
- `codegen_diff.py` — run PyJanus's interpreter against its **C++ codegen**
  output (compile at `-O0`, run, compare stores). This is what caught the
  codegen wrong-output bugs; it is folded into pytest. When touching `runtime.py`
  or `c_codegen.py`, run these to catch divergence.
  The contract is two-sided and **a compile failure is a test failure, not a
  skip**: what the generator emits must compile *and* must agree with the
  interpreter. A construct the back-end cannot translate must raise out of
  `format_program` (reported `CGERR`, skipped) rather than be emitted as broken
  C++. All 97 examples pass, including structs, rank-*n* arrays and keyword-named
  identifiers. Because C++ resolves every name, this test is also the static
  checker the interpreter lacks — it caught a call to an undefined procedure and
  a body using an undeclared variable, both in unreachable code.
