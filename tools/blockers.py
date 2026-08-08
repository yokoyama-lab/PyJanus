#!/usr/bin/env python3
"""Every reason each corpus program is outside the totality checker's fragment.

`tools/verify_corpus.py` reports the FIRST reason `compile_to_smv` hits, and
the coverage tallies in `docs/` are built from those.  A first-reason tally is
not an upper bound on what implementing a feature would admit: one program can
hold any number of blockers, so removing the one that happens to be reported
first may reveal another immediately.  This project has measured that — four
coverage estimates, three wrong, and the one that held was the one where the
breakdown was counted before starting (`docs/loop-queue.md`, items 21-28).

So: count first.  This walks the same compiler with `smv.collect_unsupported`,
which records a statement's rejection and carries on to the next statement.

    python3 tools/blockers.py                     # the whole table
    python3 tools/blockers.py --feature '^='      # just the programs with `^=`

**Fallout**: skipping a rejected statement leaves the compiler's state
inconsistent, so a later reason can be an artefact of the skip rather than a
real blocker — a variable whose declaration was skipped reads as "variable out
of the fragment".  Those are marked `?` and are NOT counted as independent
blockers.  Numbers reported without that distinction would repeat the very
error this tool exists to avoid.
"""
from __future__ import annotations

import argparse
import collections
import pathlib
import re
import signal
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from jana_py import preprocess, parser_jana2014          # noqa: E402
from jana_py.smv import collect_unsupported              # noqa: E402
from jana_py.validate import validate_program            # noqa: E402

CORPUS = "tests/jana2014/fixtures/examples/*.ja"

# Reason text -> the feature a reader would name.  Anything unmatched keeps its
# own text, so a new rejection message shows up as itself rather than silently
# joining a bucket.
FEATURES = [
    (re.compile(r"assignment operator outside the fragment: (\S+)"), r"\1"),
    (re.compile(r"integer operator outside the fragment: (\S+)"), r"\1"),
    (re.compile(r"unary operator outside the fragment: (\S+)"), r"unary \1"),
    (re.compile(r"\bstack\b", re.I), "stack"),
    (re.compile(r"variable array index"), "variable array index"),
    (re.compile(r"whole-array l-value"), "whole-array l-value"),
    (re.compile(r"whole-struct l-value"), "whole-struct l-value"),
    (re.compile(r"local .*array|array .*local", re.I), "non-scalar local"),
]

# Reasons that can be produced by the skip itself rather than by the program.
FALLOUT = re.compile(r"variable out of the fragment|no such field|"
                     r"indexing a non-array|field of a non-struct")


def feature_of(reason: str) -> str:
    for pat, repl in FEATURES:
        m = pat.search(reason)
        if m:
            return m.expand(repl) if "\\" in repl else repl
    return reason.split(":")[0][:48]


class _Timeout(Exception):
    pass


def _alarm(_sig, _frm):
    raise _Timeout


def blockers(path: pathlib.Path,
             limit: float = 10.0) -> tuple[list[str], list[str]] | None:
    """(real blockers, fallout) as feature names, or None if not analysable.

    Collection is slower than a normal compile — it does not stop at the first
    refusal, so it keeps inlining a program the checker would have abandoned.
    Hence the per-program alarm: an unbounded run has no place in a loop whose
    iteration is supposed to finish in minutes.
    """
    try:
        text = path.read_text(encoding="utf-8")
        pt = preprocess.preprocess_text(str(path), text, None, "jana2014")
        program = parser_jana2014.parse_program(str(path), pt.text, pt.line_origins)
        validate_program(program)
    except Exception:
        return None
    signal.signal(signal.SIGALRM, _alarm)
    signal.setitimer(signal.ITIMER_REAL, limit)
    try:
        reasons = collect_unsupported(program, init="zero", style="assign")
    except _Timeout:
        return ["(収集が %gs を超えた)" % limit], []
    except RecursionError:
        return ["(収集が再帰上限に達した)"], []
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    real, fallout = [], []
    for r in reasons:
        (fallout if FALLOUT.search(r) else real).append(feature_of(r))
    return sorted(set(real)), sorted(set(fallout))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--feature", help="only programs blocked by this feature")
    ap.add_argument("--glob", default=CORPUS)
    ap.add_argument("--md", action="store_true", help="emit a markdown table")
    ap.add_argument("--limit", type=float, default=10.0,
                    help="1 本あたりの収集の上限秒（既定 10）")
    args = ap.parse_args(argv)

    rows, inside, unanalysable = [], [], []
    for path in sorted(ROOT.glob(args.glob)):
        got = blockers(path, args.limit)
        if got is None:
            unanalysable.append(path.name)
            continue
        real, fallout = got
        if not real and not fallout:
            inside.append(path.name)
            continue
        rows.append((path.name, real, fallout))

    if args.feature:
        rows = [r for r in rows if args.feature in r[1]]

    if args.md:
        print("| プログラム | 拒否理由の集合 | "
              f"`{args.feature or '—'}` を消したときに残る要因 |")
        print("|---|---|---|")
        for name, real, fallout in rows:
            rest = [f for f in real if f != args.feature]
            print(f"| `{name}` | {', '.join(f'`{f}`' for f in real)}"
                  + (f" <br>（skip の余波: {', '.join(fallout)}）" if fallout else "")
                  + " | " + (", ".join(f"`{f}`" for f in rest) or "**なし**") + " |")
    else:
        for name, real, fallout in rows:
            extra = f"   [skip の余波: {', '.join(fallout)}]" if fallout else ""
            print(f"{name:<34} {', '.join(real)}{extra}")

    if args.feature:
        alone = [n for n, real, _ in rows if real == [args.feature]]
        print(f"\n`{args.feature}` を持つ: {len(rows)} 本")
        print(f"`{args.feature}` **だけ**が理由: {len(alone)} 本"
              f"{'  → ' + ', '.join(alone) if alone else ''}")
        rest = collections.Counter(f for _, real, _ in rows for f in real
                                   if f != args.feature)
        if rest:
            print("実装しても次に止まる要因: "
                  + ", ".join(f"{f} ({n})" for f, n in rest.most_common()))
    else:
        print(f"\n断片内: {len(inside)} 本 / 断片外: {len(rows)} 本"
              f" / 解析不能（parse・validate 落ち）: {len(unanalysable)} 本")
        tally = collections.Counter(f for _, real, _ in rows for f in real)
        print("要因ごとの本数（1本が複数を持ちうるので合計は一致しない）:")
        for f, n in tally.most_common(14):
            print(f"  {n:3d}  {f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
