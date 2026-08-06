#!/usr/bin/env python3
"""Tabulate which checker actually looks at which example, and why not.

Eight tests glob `tests/jana2014/fixtures/examples/*.ja`, but several of them
skip most of what they are handed: the extracted Coq cores cover a fragment of
Janus, and a program using procedures, arrays or structs falls outside it. The
skips carry a reason string and are counted in the pytest summary, so "1170
passed, 248 skipped" is all anyone ever sees -- which program is unchecked by
which core has never been written down.

This turns a pytest run into that table. The run is what pytest already does;
`--junitxml` records every outcome with its skip reason, and this reads it back:

    python3 -m pytest tests/ -q --junitxml=coverage.xml
    tools/corpus_coverage.py coverage.xml > docs/corpus-coverage.md

Rows are programs, columns are checkers, cells say checked or why not.
"""

from __future__ import annotations

import argparse
import re
import sys
import xml.etree.ElementTree as ElementTree
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "tests" / "jana2014" / "fixtures" / "examples"

#: The checkers worth a column, in the order they appear in the table, with the
#: pytest node they come from and a heading short enough to read sideways.
#: Anything else in the run is ignored -- this is a table about the corpus, not
#: a test report.
COLUMNS = [
  ("reversibility", "test_reversibility_corpus", "forward then inverse restores the store"),
  ("inverse", "test_inverse_corpus", "the inverse interpreter recovers the initial store"),
  ("format", "test_format_roundtrip", "AST to source to AST is stable"),
  ("codegen", "test_codegen_corpus", "the C++ back-end agrees with the interpreter"),
  ("flat core", "test_verified_corpus", "the extracted flat core agrees"),
  ("both cores", "test_verified_cores_corpus", "both extracted cores agree"),
  ("vjanus", "test_vjanus_corpus", "the extracted frame core agrees"),
  ("vjanus inv", "test_vjanus_inverse", "the frame core agrees running backwards"),
  ("step1", "test_step1_golden", "the small-step semantics matches its golden"),
  ("reference", "test_reference_agrees", "an independent Python implementation agrees"),
  ("metadata", "test_metadata_header", "the header's @expect and @oracle hold"),
]

#: Most corpus tests are parametrized and name the program in brackets.
PARAM_RE = re.compile(r"\[([^\]]+\.ja)\]")
#: test_step1_golden generates one method per file instead, with the path
#: flattened into the method name.
GENERATED_RE = re.compile(r"^test_tests_jana2014_fixtures_examples_(?P<stem>.+)_ja$")


def program_of(name: str) -> str | None:
  match = PARAM_RE.search(name)
  if match:
    return match.group(1)
  generated = GENERATED_RE.match(name)
  return f"{generated.group('stem')}.ja" if generated else None


def read_outcomes(xml: Path) -> dict[tuple[str, str], tuple[str, str]]:
  """(program, checker) -> (outcome, skip reason), keyed by module and function."""
  outcomes: dict[tuple[str, str], tuple[str, str]] = {}
  for case in ElementTree.parse(xml).getroot().iter("testcase"):
    name = case.get("name") or ""
    program = program_of(name)
    if program is None:
      continue
    classname = case.get("classname") or ""
    module = next((part for part in reversed(classname.split(".")) if part.startswith("test_")), "")
    function = name.split("[")[0]
    skipped = case.find("skipped")
    outcome = ("skipped" if skipped is not None else "checked",
               (skipped.get("message") or "") if skipped is not None else "")
    for key in {(program, module), (program, function)}:
      outcomes[key] = outcome
  return outcomes


def shorten(reason: str) -> str:
  """Skip reasons are written for a person reading one; a table needs less."""
  reason = reason.split("\n")[0].strip()
  for long, short in (
    ("uses procedures (verified Call needs parameters)", "procedures"),
    ("self-recursion with local variables (no frame stack)", "self-recursion + locals"),
    ("interpreter returned NONE (out of fuel?)", "out of fuel"),
    ("local struct initialized from a non-variable", "local struct from non-variable"),
    ("array of structs with an array-typed field", "array of structs w/ array field"),
    ("non-variable argument", "non-variable argument"),
    ("array declaration", "array declaration"),
    ("array parameter", "array parameter"),
    ("uses structs", "structs"),
  ):
    if reason == long:
      return short
  reason = re.sub(r"^stmt \[.*\]$", "unsupported statement", reason)
  reason = re.sub(r"^expr \[.*\]$", "unsupported expression", reason)
  reason = re.sub(r"^operator (\S+)$", r"operator \1", reason)
  return reason[:38]


def render(outcomes: dict[tuple[str, str], tuple[str, str]]) -> str:
  programs = sorted(p.name for p in EXAMPLES.glob("*.ja"))
  present = [c for c in COLUMNS if any((p, c[1]) in outcomes for p in programs)]

  out: list[str] = []
  out.append("# 検証被覆マトリクス（`tests/jana2014/fixtures/examples/`）")
  out.append("")
  out.append("*`tools/corpus_coverage.py` が pytest の `--junitxml` から生成する。手で編集しない。*")
  out.append("")
  out.append("```bash")
  out.append("python3 -m pytest tests/ -q --junitxml=/tmp/coverage.xml")
  out.append("python3 tools/corpus_coverage.py /tmp/coverage.xml > docs/corpus-coverage.md")
  out.append("```")
  out.append("")
  out.append("## 1. 何を見ている表か")
  out.append("")
  out.append("8本のテストが97本を全数 glob するが、**そのうち何本かは渡された大半を skip する**。")
  out.append("抽出された Coq コアが扱えるのは Janus の断片で、手続き・配列・構造体を使う")
  out.append("プログラムはその外に出るためである。skip は理由つきで数えられているが、")
  out.append("pytest の要約は総数しか出さないので、**どのプログラムがどのコアで検証されて")
  out.append("いないか**はこれまでどこにも書かれていなかった。")
  out.append("")
  out.append("| 列 | 何を確かめるか |")
  out.append("|---|---|")
  for label, _, description in present:
    out.append(f"| `{label}` | {description} |")
  out.append("")

  out.append("## 2. 列ごとの被覆率")
  out.append("")
  out.append("| 検査 | 検査済み | skip | 被覆率 |")
  out.append("|---|---:|---:|---:|")
  for label, node, _ in present:
    checked = sum(1 for p in programs if outcomes.get((p, node), ("absent", ""))[0] == "checked")
    skipped = sum(1 for p in programs if outcomes.get((p, node), ("absent", ""))[0] == "skipped")
    total = checked + skipped
    rate = f"{100 * checked // total}%" if total else "-"
    out.append(f"| `{label}` | {checked} | {skipped} | {rate} |")
  out.append("")

  out.append("## 3. skip の理由")
  out.append("")
  reasons: Counter[tuple[str, str]] = Counter()
  for label, node, _ in present:
    for program in programs:
      outcome, reason = outcomes.get((program, node), ("absent", ""))
      if outcome == "skipped":
        reasons[(label, shorten(reason))] += 1
  if reasons:
    out.append("| 検査 | 理由 | 本数 |")
    out.append("|---|---|---:|")
    for (label, reason), count in reasons.most_common():
      out.append(f"| `{label}` | {reason} | {count} |")
  else:
    out.append("skip なし。")
  out.append("")

  out.append("## 4. プログラム別")
  out.append("")
  out.append("`o` = 検査済み、空欄 = そのテストの対象外、それ以外は skip の理由。")
  out.append("")
  out.append("| プログラム | " + " | ".join(f"`{label}`" for label, _, _ in present) + " |")
  out.append("|---" * (len(present) + 1) + "|")
  for program in programs:
    cells = []
    for _, node, _ in present:
      outcome, reason = outcomes.get((program, node), ("absent", ""))
      cells.append("o" if outcome == "checked" else ("" if outcome == "absent" else shorten(reason)))
    out.append(f"| `{program}` | " + " | ".join(cells) + " |")
  out.append("")

  dead = [(label, node) for label, node, _ in present
          if not any(outcomes.get((p, node), ("absent", ""))[0] == "checked" for p in programs)]
  if dead:
    out.append("## 5. 一度も走らない検査")
    out.append("")
    out.append("**1本も検査していない列**。テストは存在するが、条件が揃わず全数 skip される。")
    out.append("")
    out.append("| 検査 | 全数 skip の理由 |")
    out.append("|---|---|")
    for label, node in dead:
      reason = next((shorten(r) for p in programs
                     for o, r in [outcomes.get((p, node), ("absent", ""))] if o == "skipped"), "")
      out.append(f"| `{label}` | {reason} |")
    out.append("")

  live = [(label, node) for label, node, _ in present if (label, node) not in dead]
  fully = [p for p in programs
           if all(outcomes.get((p, n), ("absent", ""))[0] != "skipped" for _, n in live)]
  out.append(f"## {6 if dead else 5}. 生きている検査で一度も skip されないプログラム")
  out.append("")
  out.append(f"**{len(fully)}/{len(programs)} 本**が、実際に走る {len(live)} 列すべてで検査されている。")
  if fully:
    out.append("")
    out.append(", ".join(f"`{p}`" for p in fully))
  out.append("")
  return "\n".join(out)


def main() -> int:
  parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
  parser.add_argument("junitxml", help="a pytest --junitxml report of a full run")
  args = parser.parse_args()
  print(render(read_outcomes(Path(args.junitxml))))
  return 0


if __name__ == "__main__":
  sys.exit(main())
