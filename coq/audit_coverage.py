#!/usr/bin/env python3
"""Every `Theorem` in coq/*.v is either audited or exempted, with a reason.

`audit.sh` checks the axioms of the theorems it names.  Which theorems it names
is a matter of somebody remembering to add a line, and nothing checks that they
did — an unregistered theorem walks past `Print Assumptions` for good.  A rule
kept by discipline alone fails silently on the day it is forgotten, which is the
day it matters.

Resolving the names is the whole difficulty.  `audit.sh` checks through functor
instances (`Module LlS := RevLoopLemma.LoopLemma RevStack.StackPrim`), so a
theorem written inside a functor is registered under an alias that shares
nothing with its file name.  This maps the aliases back to (file, functor)
before comparing, because comparing bare names instead reports theorems as
missing when they are registered under a different instance of the same functor.

    python3 coq/audit_coverage.py           # exit 3 if anything is unregistered
    python3 coq/audit_coverage.py --list    # print what is missing and stop

Exemptions live in `coq/audit-exempt.txt`, one `name  # reason` per line.  An
exemption without a reason is rejected: the point is to make the decision
visible, not to have a second place to hide things.

The existing backlog is held as a RATCHET rather than a wall.  Deciding which of
the 125 theorems already outside the audit are headline results and which are
scaffolding is a judgement about the development, not something this script may
make; but the rule can be enforced from today regardless.  So the baseline is
recorded and the check fails when the gap GROWS — a theorem added tomorrow has
to be registered or exempted, while the backlog stays visible instead of being
silently blessed.
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
EXEMPT = HERE / "audit-exempt.txt"

THEOREM = re.compile(r"^(\s*)Theorem\s+([A-Za-z_][A-Za-z0-9_']*)", re.M)
MODULE_OPEN = re.compile(r"^\s*Module\s+(?!Type\b)([A-Za-z_][A-Za-z0-9_']*)\s*(?:\(|:=|\.|$)")
MODULE_END = re.compile(r"^\s*End\s+([A-Za-z_][A-Za-z0-9_']*)\s*\.")
ALIAS = re.compile(r"^\s*Module\s+([A-Za-z_][A-Za-z0-9_']*)\s*:=\s*"
                   r"([A-Za-z_][A-Za-z0-9_']*)\.([A-Za-z_][A-Za-z0-9_']*)")
PRINTED = re.compile(r"Print Assumptions\s+([A-Za-z_][A-Za-z0-9_.']*)")


def theorems() -> dict[tuple[str, str], set[str]]:
    """(file stem, enclosing module or "") -> theorem names declared there."""
    out: dict[tuple[str, str], set[str]] = {}
    for path in sorted(HERE.glob("*.v")):
        stack: list[str] = []
        for line in path.read_text(encoding="utf-8").splitlines():
            m = MODULE_END.match(line)
            if m and stack and stack[-1] == m.group(1):
                stack.pop()
                continue
            m = MODULE_OPEN.match(line)
            if m:
                # `Module X := F Y.` is an alias/application closed on the same
                # line: it opens no scope, so it must not be pushed -- otherwise
                # every theorem after it is attributed to X and a Print
                # Assumptions registered under the real module never matches.
                if re.match(r"^\s*Module\s+[A-Za-z_][A-Za-z0-9_']*\s*:=", line):
                    continue
                stack.append(m.group(1))
                continue
            m = re.match(r"^\s*Theorem\s+([A-Za-z_][A-Za-z0-9_']*)", line)
            if m:
                out.setdefault((path.stem, stack[-1] if stack else ""), set()).add(m.group(1))
    return out


def registered() -> tuple[dict[str, set[str]], set[str]]:
    """(alias -> names printed under it, names printed with no qualifier at all).

    The second component must hold *only* the genuinely unqualified prints
    (`Print Assumptions foo.`).  Putting every printed name in it makes the
    check blind to the case it exists for: this development gives the same
    theorem name to the same result on several kernels (`bex_invert` lives in
    RevBack, RevFrameBack and RevArrBack), so a name-only test reports a brand
    new file as audited the moment any other file audits that name.
    """
    text = (HERE / "audit.sh").read_text(encoding="utf-8")
    aliases: dict[str, tuple[str, str]] = {}
    for line in text.splitlines():
        m = ALIAS.match(line)
        if m:
            aliases[m.group(1)] = (m.group(2), m.group(3))   # alias -> (file, functor)
    by_target: dict[str, set[str]] = {}
    bare: set[str] = set()
    for qualified in PRINTED.findall(text):
        parts = qualified.rstrip(".").split(".")
        name = parts[-1]
        if len(parts) == 1:
            bare.add(name)
            continue
        head = parts[0]
        if head in aliases:
            file_, functor = aliases[head]
            by_target.setdefault(f"{file_}::{functor}", set()).add(name)
        else:
            # `File.name` or `File.Module.name`
            by_target.setdefault(f"{head}::{parts[1] if len(parts) > 2 else ''}",
                                 set()).add(name)
    return by_target, bare


def exemptions() -> dict[str, str]:
    if not EXEMPT.exists():
        return {}
    out = {}
    for raw in EXEMPT.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        name, _, reason = line.partition("#")
        name, reason = name.strip(), reason.strip()
        if not reason:
            print(f"audit_coverage: 理由のない除外は認めない: {name}", file=sys.stderr)
            sys.exit(2)
        out[name] = reason
    return out


def missing() -> list[tuple[str, str, str]]:
    by_target, bare = registered()
    exempt = exemptions()
    out = []
    for (stem, module), names in sorted(theorems().items()):
        key = f"{stem}::{module}"
        covered = by_target.get(key, set())
        for name in sorted(names):
            if name in covered or name in exempt:
                continue
            # A functor's theorem may be audited through any instance of it, and
            # instances are keyed by the functor, not the file it came from.
            if any(name in v for k, v in by_target.items()
                   if module and k.endswith(f"::{module}")):
                continue
            # only a genuinely unqualified `Print Assumptions name.` covers a
            # top-level theorem it did not name by file (see registered())
            if not module and name in bare:
                continue
            out.append((stem, module, name))
    return out


BASELINE = HERE / "audit-coverage-baseline"


def baseline() -> set[str]:
    """The known backlog, by NAME rather than by count.

    A count-only ratchet is passed by registering one theorem and adding
    another: the number holds while the set changed.  Names make the check
    exact and let the failure say which theorem is new.
    """
    if not BASELINE.exists():
        return set()
    return {ln.split("#")[0].strip()
            for ln in BASELINE.read_text(encoding="utf-8").splitlines()
            if ln.strip() and not ln.lstrip().startswith("#")}


def key_of(stem: str, module: str, name: str) -> str:
    return f"{stem}::{module}::{name}"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--list", action="store_true", help="内訳を出して常に 0 で終わる")
    ap.add_argument("--set-baseline", action="store_true",
                    help="いまの本数を基準として書き込む（減らすときだけ使う）")
    args = ap.parse_args(argv)

    gaps = missing()
    keys = {key_of(*g) for g in gaps}
    base = baseline()
    new = sorted(keys - base)
    gone = sorted(base - keys)

    if args.set_baseline:
        if new:
            print(f"基準を増やす方向には書き換えない（新たに {len(new)} 本）")
            for k in new:
                print(f"  {k}")
            return 2
        header = ("# audit.sh の対象外の Theorem。**増えたら落ちる**（減るのは歓迎）。\n"
                  "# これは「許した」ではなく「今日以降増やさない」という意味。\n"
                  "# どれが headline でどれが足場かの判断は人の仕事。内訳は\n"
                  "#   python3 coq/audit_coverage.py --list\n")
        BASELINE.write_text(header + "".join(f"{k}\n" for k in sorted(keys)),
                            encoding="utf-8")
        print(f"基準を {len(base)} → {len(keys)} 本に更新した")
        return 0

    if args.list:
        for stem, module, name in gaps:
            where = f"{stem}.v" + (f" (Module {module})" if module else "")
            print(f"  {name:<44} {where}")
        print(f"\n対象外: {len(gaps)} 本（基準 {len(base)} 本）")
        return 0

    if new:
        print(f"AUDIT COVERAGE FAIL: 検査対象になっていない Theorem が {len(new)} 本増えた")
        for k in new:
            stem, module, name = k.split("::")
            where = f"{stem}.v" + (f" (Module {module})" if module else "")
            print(f"  {name:<44} {where}")
        print("\n`Print Assumptions` に登録するか、coq/audit-exempt.txt に "
              "`名前  # 理由` を書くこと。")
        return 3
    if gone:
        print(f"AUDIT COVERAGE OK: 対象外が {len(gone)} 本減った。"
              f"`--set-baseline` で基準を締めること")
        return 0
    print(f"AUDIT COVERAGE OK: 対象外 {len(keys)} 本（基準どおり。増えていない）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
