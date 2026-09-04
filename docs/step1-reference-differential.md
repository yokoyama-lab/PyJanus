# `step1` 列の穴を埋める — Haskell 参照実装との差分検査

*`tools/step1_differential.py` が生成する。最終更新 2026-08-09。*

## 1. なにが 0% だったのか

`docs/corpus-coverage.md` の `step1` 列は **101 本すべてが skip**、被覆率 0% である。
理由は `requires the Haskell reference implementation` の 1 行に畳まれていた。

`tests/janus2026/test_step1_golden.py` は

```python
HAVE_HASKELL = shutil.which("runhaskell") is not None and (ROOT / "src" / "Main.hs").exists()
```

でリポジトリ**内部**の `src/Main.hs` を探している。PyJanus に `src/Main.hs` は無い
（`src/` 自体が無い）ので、この条件は構造的に永久偽である。**参照実装が壊れていたの
ではなく、参照実装がここに置かれることは一度も無かった。**

参照実装の正体は Budde / Nielsen / Kirkedal Thomsen の Jana インタプリタで、この機械の
`~/dev/github.com/kirkedal/Jana-JanusInterp` に checkout 済みだった（`src/Main.hs`
5.5KB、`jana.cabal`）。GHC 9.6.7 と cabal は導入済みで、`cabal build` は
**そのまま通る**（依存で新規に取得が要るのは `arithmoi` のみ。`monad-coroutine` は
cabal ファイルに書かれているが `src/` のどこからも import されていない）。

```bash
cd ~/dev/github.com/kirkedal/Jana-JanusInterp && cabal update && cabal build
# → dist-newstyle/build/x86_64-linux/ghc-9.6.7/jana-1.1/x/jana/build/jana/jana
```

## 2. 差分検査の作法

素朴に両者を突き合わせると全件落ちる。実測した差の原因は 2 つ。

| 差 | 対処 |
|---|---|
| PyJanus の既定方言は `janus2026`（`void`）で、コーパスは `jana2014`（`procedure`） | PyJanus 側に `--std jana2014` を渡す |
| 参照は既定で最終ストアを表示、PyJanus は `-s` が要る | PyJanus 側に `-s` を渡す |
| PyJanus のみ `Warning: …` 行を出す（残留値・`show` の非推奨） | 比較前に `^Warning: .*$` を落とす。**参照は問題を `[ERROR …]` で報告し `Warning:` 行を一切出さない**ので、これで本物の相違を隠すことはない |

`tools/step1_differential.py` はこの正規化を明示的に持つ。隠す行を増やすときは、
参照側がその形の行を出さないことを確かめてから増やすこと。

```bash
JANA_HASKELL_BIN=/path/to/jana python3 tools/step1_differential.py --json /tmp/step1.json
```

`JANA_HASKELL_BIN` が無いときは `PATH` 上の `jana`、次に
`~/dev/github.com/*/Jana-JanusInterp/dist-newstyle/.../jana` を順に探す。

## 3. 実測（2026-08-09、101 本）

```
programs      101
agree          63
mismatch       38
both error      0
```

**0% → 62%。** 残る 38 本の内訳は次のとおりで、**33 本は PyJanus が Jana 2014 を
超えて拡張した部分**である。参照が構文として受け付けないので、これは不一致ではなく
「参照の外」であり、`skip` の正しい理由として記録すべきものである。

| # | 区分 | 本数 | プログラム |
|---|---|---:|---|
| A | 配列型の仮引数 `int a[]`（PyJanus 拡張） | 20 | `adaptive_huffman_c` `arith_coding_c` `bwt_inverse_c` `bwt_plain_c` `ca_rule90_c` `cipher_sbox_c` `cuckoo_insert_g` `cycle_lemma_c` `edit_script_g` `glaisher_c` `hash_chain_g` `iterate_c` `landauer_interp_g` `lehmer_code_c` `lomuto_partition_g` `mini_cipher_c` `ppm_lite_c` `rans_encode_c` `sort_network_c` `sort_rank_g` |
| B | 構造体（PyJanus 拡張） | 13 | `structs_*`（13 本すべて） |
| C | **実引数の別名を参照は実行時エラーにする** | 2 | `avl_delete_g` `avl_insert_g` |
| D | 構文が 2014 の外（その他） | 1 | `int_bijections_c` |
| E | 参照側の実行時エラー（その他） | 2 | `dijkstra_g` `prim_mst_g` |

**両方が正常終了して出力が違うものは 0 本。** ここが重要で、方言の外に出ていない
63 本については PyJanus は参照実装と逐語一致している。

## 4. 判断が要る 5 本（C・D・E）

ここだけが人間の仕事である。

### C: `avl_insert_g` / `avl_delete_g` — 別名（aliasing）の扱い

参照は `arr[node] ^= old` の実行時に

```
[Identifiers `arr' and `node' are aliases, ...]
```

を出して停止する。同一配列を 2 つの仮引数へ渡した呼び出しである。Jana 2014 は
実引数の別名を実行時に検出して拒否し、PyJanus は通している。

**どちらが正しいかはコーパスの位置づけによる。** 別名を許すなら「PyJanus の意図した
拡張」として `DIALECTS.md` に書き、許さないなら 2 本のプログラムを書き換える。
現状はどちらの記録も無い。**この 2 本は可逆性・逆実行・codegen の全列で `o` なので、
別名が実際に非可逆性を生んでいるわけではない**（＝安全側の拡張である可能性が高い）。

### D: `int_bijections_c` — 構文が 2014 の外

A・B のどちらでもない構文差。原因の特定が要る。

### E: `dijkstra_g` / `prim_mst_g` — 参照側の実行時エラー

参照が構文は通したうえで実行時に落ちている。参照実装のバグか、PyJanus 側の意味論の
差か、プログラム自身が 2014 の意味論では動かないのか、3 通りある。**参照実装を疑う
前に、まず最小化した再現例を作ること。**

## 5. `test_step1_golden.py` をどう直すか

現状のテストは (a) リポジトリ内 `src/Main.hs` を探し、(b) 方言を渡さず、(c) 出力を
逐語比較する。3 つとも直す必要がある。最小の変更は

```python
HASKELL_BIN = os.environ.get("JANA_HASKELL_BIN")
HAVE_HASKELL = HASKELL_BIN is not None and Path(HASKELL_BIN).exists()
```

に置き換えたうえで、PyJanus 側に `--std jana2014 -s` を渡し、比較前に `Warning:` 行を
落とすこと。**A・B の 33 本は `pytest.skip` に理由つきで落とす**（`corpus-coverage.md`
の skip 理由がそのまま「PyJanus 拡張」として立つ）。

このリポジトリは並行して別セッションが編集していることがあるため、テスト本体の書き換えは
本ドキュメントでは行っていない。`tools/step1_differential.py` は独立して動く。

## 6. ついでに測った `both cores` 列 — 1 列に 2 つのコアが潰れている

`corpus-coverage.md` の `both cores` 列は「検査済み 1 / skip 100 / 0%」だが、
この列に対応する `test_verified_cores_corpus.py` は**独立した 2 つのコア**を回している。
1 列に潰すと何が起きているか分からないので、`--junitxml` を per-test に割り直して
測った（2026-08-09、対象 120 本＝コーパス 101 ＋ `coq/harness/fixtures` 19）。

| コア | 抽出元 | pass | skip | 被覆率 |
|---|---|---:|---:|---:|
| 素のコア `driver` | `RevExtract.v` | 4 | 116 | **3%** |
| パラメータ化コア `driverp` | `RevExtractP.v` | 7 | 113 | **6%** |

**0% ではなく 3% と 6% である。** そして skip の理由は、コアごとにまったく違う。

**素のコア（`RevExtract.v`）** — 99/116 が `uses procedures (verified Call needs
parameters)`。手続きを持たないコアにコーパスを渡しているのだから当然で、これは
設計どおりであり埋める対象ではない。

**パラメータ化コア（`RevExtractP.v`）** — ここが本命。

| skip 理由 | 本数 |
|---|---:|
| **`array parameter`** | **61** |
| `stmt ['body','enter_decl','exit_decl','pos']`（局所変数ブロック `local`/`delocal`） | 16 |
| `uses structs` | 14 |
| `array declaration` | 7 |
| `operator /` | 3 |
| その他（`operator %`・式の形 2 種） | 5 |

**配列引数だけで 61/113 = 54%。** つまり `RevExtractP.v` に配列引数を足すと、
このコアの被覆率は 6% から一気に 60% 前後へ動く。局所変数ブロック（16）を足せば
さらに 14 ポイント。**「抽出コアを配列引数へ拡張する」は、
成果が被覆率という 1 つの数で測れる形に落ちている。**

（`RevExtractAr.v`＝配列＋手続きのコアは別列 `flat core` で 80/101 = 79% を達成済み。
残り 21 は自己再帰＋局所変数 13、`*=` 4、ほか 4。構造体はこちらでも未対応。）

### 被覆率を 1 列 1 コアにする

`tools/corpus_coverage.py` の `COLUMNS` は `("both cores", "test_verified_cores_corpus", …)`
とモジュール単位で列を作っているため、2 つのコアの結果が 1 セルに潰れる。
`test_core_matches_pyjanus` と `test_param_core_matches_pyjanus` を別列にすれば、
上の表がそのまま `corpus-coverage.md` に載る。**1 行の変更で、いま隠れている
「どちらのコアがどこで止まっているか」が常時見えるようになる。**
