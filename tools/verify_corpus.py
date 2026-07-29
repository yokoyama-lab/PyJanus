#!/usr/bin/env python3
"""Run the totality checker over a corpus of Janus programs and tabulate.

For every `.ja` file: parse it, compile it to SMV, hand the model to nuXmv, and
record one of

    proved       no runtime assertion is reachable
    refuted      one is, with the initial store that gets there
    unknown      IC3 gave up or timed out
    unsupported  the program is outside the scalar fragment (with the reason)
    parse-error  it does not parse at all (expected for some error fixtures)

Usage:
    python3 tools/verify_corpus.py [--init any|zero] [--timeout SECONDS] [GLOB ...]
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
from jana_py.smv import SmvUnsupported, compile_to_smv  # noqa: E402
from jana_py.validate import validate_program  # noqa: E402

DEFAULT_GLOBS = [
    "tests/jana2014/fixtures/examples/*.ja",
    "tests/jana2014/fixtures_errors/*.ja",
]


def classify(path: Path, init: str, timeout: float, binary, style: str = "trans") -> tuple[str, str]:
  try:
    text = path.read_text(encoding="utf-8")
    pt = preprocess.preprocess_text(str(path), text, None, "jana2014")
    program = parser_jana2014.parse_program(str(path), pt.text, pt.line_origins)
  except Exception as exc:  # parse/preprocess failures are a legitimate outcome
    return "parse-error", type(exc).__name__
  try:
    validate_program(program)
  except Exception as exc:
    # The static checks are PyJanus's job, not the model checker's; a program
    # that does not validate is out of scope rather than "safe".
    return "static-error", type(exc).__name__
  try:
    model = compile_to_smv(program, init=init, style=style)
  except SmvUnsupported as exc:
    return "unsupported", str(exc)
  except Exception as exc:
    return "compile-error", f"{type(exc).__name__}: {exc}"
  result = nuxmv.check(model, timeout=timeout, binary=binary)
  if result.status == "refuted":
    bad = next(v for v in result.verdicts if v.status == "refuted")
    # `pc != 1` is the inlining bound, not an assertion failure -- say which.
    kind = "bound" if bad.prop.strip().endswith("!= 1") else "assert"
    store = ", ".join(f"{k}={v}" for k, v in sorted(bad.counterexample.items()))
    return "refuted", f"[{kind}] {store or '-'}"
  if result.status == "unknown":
    return "unknown", "timeout" if result.timed_out else "gave up"
  return "proved", f"{len(result.verdicts)} invariant(s)"


def main() -> int:
  ap = argparse.ArgumentParser()
  ap.add_argument("--init", choices=["any", "zero"], default="zero")
  ap.add_argument("--timeout", type=float, default=60.0)
  ap.add_argument("--style", choices=["trans", "assign"], default="trans")
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
  print(f"init={args.init}  style={args.style}  timeout={args.timeout}s  files={len(paths)}\n")
  for path in paths:
    status, detail = classify(path, args.init, args.timeout, binary, args.style)
    tally[status] += 1
    if status in ("unsupported", "compile-error"):
      reasons[detail.split(":")[0]] += 1
    print(f"{status:12s} {path.name:34s} {detail}")
  print("\n== summary ==")
  for status, count in tally.most_common():
    print(f"  {status:12s} {count}")
  if reasons:
    print("\n== why unsupported ==")
    for reason, count in reasons.most_common():
      print(f"  {count:3d}  {reason}")
  return 0


if __name__ == "__main__":
  raise SystemExit(main())
