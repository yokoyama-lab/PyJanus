#!/usr/bin/env python3
"""Delete one statement at a time and see whether the verdict flips to `proved`.

`docs/totality-checking.md` §5 exhausted the encoding side of the decidability
question: three encodings changed no verdict, only the faithful zero store moved
one program, and the difficulty tracks neither size nor any single construct.
What is left is to stop synthesising small examples and cut down a real one —
if a program flips to `proved` when one statement goes, that statement is where
the difficulty lives, and that is a fact about the problem rather than about the
encoding.

Each candidate variant is run through PyJanus first: a variant the interpreter
cannot execute is not a smaller program, it is a broken one, and its verdict
would mean nothing.

    python3 tools/ablate.py tests/jana2014/fixtures/examples/run_length_enc_c.ja
    python3 tools/ablate.py PROG --budget 2400 --timeout 120

Reports every deletion that runs, with its verdict, and stops at the overall
budget — an unbounded search has no place in a loop iteration.
"""
from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from jana_py import nuxmv, parser_jana2014, preprocess  # noqa: E402
from jana_py.smv import SmvUnsupported, compile_to_smv  # noqa: E402
from jana_py.validate import validate_program           # noqa: E402

# A line that carries a statement worth deleting.  Comments, blank lines and the
# `procedure` header are not statements; `local`/`delocal` come in pairs and
# deleting one alone never runs, so they are skipped rather than reported.
SKIP = re.compile(r"^\s*(//|/\*|\*|$|procedure\b|local\b|delocal\b"
                  r"|(loop|do|else|then)\s*$)")

# Deleting these does not make the program smaller in the sense the experiment
# means.  A `loop` / `do` line is a keyword, not a statement: removing it
# re-parses the body into a different loop.  And a run that flips to `proved`
# because the algorithm is no longer called, or because the input shrank to one
# iteration, says nothing about which statement carries the difficulty — those
# are reported separately rather than counted as findings.
DEGENERATE = re.compile(r"^\s*(call|uncall)\b")


def variants(src: str):
  """(line number, source with that line removed) for each deletable line."""
  lines = src.splitlines(keepends=True)
  for i, line in enumerate(lines):
    if SKIP.match(line):
      continue
    yield i + 1, line.strip(), "".join(lines[:i] + lines[i + 1:])


def runs_under_pyjanus(src: str) -> bool:
  proc = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", "-"],
                        input=src, capture_output=True, text=True, cwd=ROOT, timeout=120)
  return proc.returncode == 0


def verdict(src: str, timeout: float, init: str) -> str:
  try:
    pt = preprocess.preprocess_text("<ablate>", src, None, "jana2014")
    program = parser_jana2014.parse_program("<ablate>", pt.text, pt.line_origins)
    validate_program(program)
  except Exception as exc:
    return f"parse/validate: {type(exc).__name__}"
  try:
    model = compile_to_smv(program, init=init, style="assign")
  except SmvUnsupported as exc:
    return f"unsupported: {exc}"
  res = nuxmv.check(model, timeout=timeout)
  return res.status


def main(argv=None) -> int:
  ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
  ap.add_argument("program")
  ap.add_argument("--timeout", type=float, default=120.0, help="nuXmv 1 回の上限秒")
  ap.add_argument("--budget", type=float, default=2400.0, help="全体の上限秒")
  ap.add_argument("--init", default="zero", choices=["zero", "any"])
  args = ap.parse_args(argv)

  path = pathlib.Path(args.program)
  src = path.read_text(encoding="utf-8")

  base = verdict(src, args.timeout, args.init)
  print(f"削除なし: {base}\n")
  if base == "proved":
    print("元から proved なので、この実験は意味を持たない")
    return 0

  started = time.time()
  flipped, ran, skipped = [], 0, 0
  for lineno, text, variant in variants(src):
    if time.time() - started > args.budget:
      print(f"\n⚠ 予算 {args.budget:g}s を超えたので打ち切り（残りは未試行）")
      break
    if not runs_under_pyjanus(variant):
      skipped += 1
      print(f"  L{lineno:<3} 実行できない（削るとプログラムが壊れる）: {text[:48]}")
      continue
    ran += 1
    v = verdict(variant, args.timeout, args.init)
    degenerate = bool(DEGENERATE.match(text))
    mark = ("  ← 転じた（退化: アルゴリズムを呼ばなくなっただけ）"
            if v == "proved" and degenerate else
            "  ← 転じた" if v == "proved" else "")
    print(f"  L{lineno:<3} {v:<10} {text[:48]}{mark}")
    if v == "proved" and not degenerate:
      flipped.append((lineno, text))

  print(f"\n削って走った: {ran} 通り / 壊れた: {skipped} 通り / "
        f"所要 {time.time() - started:.0f}s")
  if flipped:
    print("**proved に転じた削除**:")
    for lineno, text in flipped:
      print(f"  L{lineno}: {text}")
  else:
    print("**1文削除では転じなかった**（空振り。これも結論）")
  return 0


if __name__ == "__main__":
  sys.exit(main())
