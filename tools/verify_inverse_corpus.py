#!/usr/bin/env python3
"""Prove `P; P† = id` for every program in a corpus, symbolically.

Janus's inversion is *syntactic* — `invert.py` rewrites the program without
looking at what it computes — and the claim that it is also the *semantic*
inverse is what makes the whole language work.  `jana_py.equiv.check_inverse`
tests that claim by running the round trip on a box of small inputs.  This tool
**proves** it instead: it builds `P; P†` and asks nuXmv's IC3 whether the
composition is the identity on every store, over unbounded integers.

So this is a differential test of `invert.py` against the SMV semantics, run
per program.  A `different` verdict is therefore not a fact about the corpus —
it is a **bug**, in `invert.py`, in the composition, or in the encoding.

The interesting outcome is the split between:

    equivalent   the round trip is the identity and always completes
    partial      the round trip is the identity wherever it completes, but some
                 input drives it into a failed assertion — i.e. the program is
                 a partial injection, which most interesting Janus programs are
    different    a real disagreement — a bug, see above
    unknown      IC3 gave up or timed out
    unsupported  outside the scalar fragment (with the reason)

Usage:
    python3 tools/verify_inverse_corpus.py [--timeout SECONDS] [GLOB ...]
"""

from __future__ import annotations

import argparse
import glob
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from jana_py import nuxmv  # noqa: E402
from jana_py import parser_jana2014  # noqa: E402
from jana_py import preprocess  # noqa: E402
from jana_py.equiv_smv import check_equivalence_smv  # noqa: E402
from jana_py.smv import SmvUnsupported  # noqa: E402
from jana_py.validate import validate_program  # noqa: E402

DEFAULT_GLOBS = ["tests/jana2014/fixtures/examples/*.ja"]


def classify(path: Path, timeout: float, binary) -> tuple[str, str]:
  try:
    text = path.read_text(encoding="utf-8")
    pt = preprocess.preprocess_text(str(path), text, None, "jana2014")
    program = parser_jana2014.parse_program(str(path), pt.text, pt.line_origins)
  except Exception as exc:
    return "parse-error", type(exc).__name__
  try:
    validate_program(program)
  except Exception as exc:
    return "static-error", type(exc).__name__
  try:
    verdict = check_equivalence_smv(program, program, timeout=timeout, binary=binary)
  except SmvUnsupported as exc:
    return "unsupported", str(exc)
  except Exception as exc:
    return "compile-error", f"{type(exc).__name__}: {exc}"
  detail = f"identity={verdict.identity} totality={verdict.totality}"
  if verdict.status == "different":
    store = ", ".join(f"{k}={v}" for k, v in sorted(verdict.counterexample.items()))
    return "different", f"BUG: {store or '-'}"
  return verdict.status, detail


def main() -> int:
  ap = argparse.ArgumentParser()
  ap.add_argument("--timeout", type=float, default=60.0)
  ap.add_argument("globs", nargs="*", default=None)
  args = ap.parse_args()

  binary = nuxmv.find_nuxmv()
  if binary is None:
    print("nuXmv not found; set $NUXMV", file=sys.stderr)
    return 2

  patterns = args.globs or DEFAULT_GLOBS
  paths = sorted({Path(p) for pattern in patterns for p in glob.glob(str(ROOT / pattern))})
  tally: Counter[str] = Counter()
  reasons: Counter[str] = Counter()
  print(f"P;P† = id   timeout={args.timeout}s  files={len(paths)}\n")
  for path in paths:
    status, detail = classify(path, args.timeout, binary)
    tally[status] += 1
    if status in ("unsupported", "compile-error"):
      reasons[detail.split(":")[0]] += 1
    print(f"{status:12s} {path.name:38s} {detail}", flush=True)
  print("\n== summary ==")
  for status, count in tally.most_common():
    print(f"  {status:12s} {count}")
  if reasons:
    print("\n== why unsupported ==")
    for reason, count in reasons.most_common():
      print(f"  {count:3d}  {reason}")
  # A disagreement is a defect in the tooling, not a property of the corpus.
  return 1 if tally["different"] else 0


if __name__ == "__main__":
  raise SystemExit(main())
