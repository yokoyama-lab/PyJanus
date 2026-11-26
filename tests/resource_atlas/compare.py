"""Join the static predictions (jana_py/costcheck.py) with the dynamic
measurements (jana_py/pebble.py) over the corpus and the generated variants.

Writes ``data/prediction_vs_measurement.csv`` (one row per program) and
``data/prediction_vs_measurement.md`` (summary + every violation).  A
violation is a measurement that exceeds a sound static bound, i.e. a bug in
the analyzer or in the profiler; the summary lists them all.

Run ``python3 -m tests.resource_atlas.compare`` from the repository root.
"""
from __future__ import annotations

import csv
import sys
from pathlib import Path

from .common import DATA_DIR, Measurement, corpus_files, measure, rel
from .gen_inputs import STD as GEN_STD, variants

FIELDS = [
    "file", "std", "group", "error",
    "acyclic", "depth_bound", "call_depth_peak", "depth_ok", "depth_slack",
    "stack_free", "stack_peak", "stack_ok",
    "call_in_loop", "calls_bound", "total_calls", "calls_ok", "calls_slack",
]


def compare_one(m: Measurement, group: str) -> dict:
    row = {"file": rel(m.path), "std": m.std, "group": group, "error": m.error or ""}
    pred = m.prediction
    if pred is not None:
        row.update({
            "acyclic": pred.acyclic,
            "depth_bound": "" if pred.depth_bound is None else pred.depth_bound,
            "stack_free": pred.stack_free,
            "call_in_loop": pred.call_in_loop,
            "calls_bound": "" if pred.calls_bound is None else pred.calls_bound,
        })
    if m.ok and pred is not None:
        p = m.profile
        row["call_depth_peak"] = p.call_depth_max
        row["stack_peak"] = p.stack_peak
        row["total_calls"] = p.total_calls
        if pred.depth_bound is not None:
            row["depth_ok"] = p.call_depth_max <= pred.depth_bound
            row["depth_slack"] = pred.depth_bound - p.call_depth_max
        else:
            row["depth_ok"] = ""
            row["depth_slack"] = ""
        row["stack_ok"] = (p.stack_peak == 0) if pred.stack_free else ""
        if pred.calls_bound is not None:
            row["calls_ok"] = p.total_calls <= pred.calls_bound
            row["calls_slack"] = pred.calls_bound - p.total_calls
        else:
            row["calls_ok"] = ""
            row["calls_slack"] = ""
    return row


def compare_all() -> list[dict]:
    rows = [compare_one(measure(path, std), "corpus") for path, std in corpus_files()]
    rows += [compare_one(measure(v.path, GEN_STD), "generated") for v in variants()]
    return rows


def summarize(rows: list[dict]) -> str:
    out: list[str] = ["# Prediction vs measurement", ""]
    violations: list[tuple[str, dict]] = []
    for group in ("corpus", "generated"):
        g = [r for r in rows if r["group"] == group]
        ok = [r for r in g if not r["error"]]
        out += [f"## {group} ({len(g)} programs, {len(ok)} measured)", ""]

        # 1. depth bound
        bounded = [r for r in ok if r["depth_bound"] != ""]
        cyclic = [r for r in ok if r["acyclic"] is False]
        d_ok = [r for r in bounded if r["depth_ok"] is True]
        d_bad = [r for r in bounded if r["depth_ok"] is False]
        tight = [r for r in bounded if r["depth_slack"] == 0]
        violations += [("depth", r) for r in d_bad]
        out += [
            "### 1. call_depth_peak <= H (H = longest path in an acyclic call graph)", "",
            "| | count |", "|---|---:|",
            f"| acyclic call graph (bound H exists) | {len(bounded)} |",
            f"| cyclic call graph (no bound) | {len(cyclic)} |",
            f"| bound holds (measured <= H) | {len(d_ok)} |",
            f"| **violations** (measured > H) | {len(d_bad)} |",
            f"| bound tight (measured = H) | {len(tight)} / {len(bounded)} |",
        ]
        slack = sorted(set(r["depth_slack"] for r in bounded))
        out += [f"| slack values H - measured | {', '.join(str(s) for s in slack) or '-'} |", ""]
        if cyclic:
            depths = [r["call_depth_peak"] for r in cyclic]
            out += [f"Cyclic programs measured call_depth_peak in [{min(depths)}, {max(depths)}].", ""]

        # 2. stack-free certificate
        cert = [r for r in ok if r["stack_free"] is True]
        cert_ok = [r for r in cert if r["stack_ok"] is True]
        cert_bad = [r for r in cert if r["stack_ok"] is False]
        uncert = [r for r in ok if r["stack_free"] is False]
        uncert_zero = [r for r in uncert if r["stack_peak"] == 0]
        violations += [("stack", r) for r in cert_bad]
        out += [
            "### 2. stack_peak = 0 certificate (no push/pop reachable from main)", "",
            "| | count |", "|---|---:|",
            f"| certified stack-free | {len(cert)} |",
            f"| certified and measured 0 | {len(cert_ok)} |",
            f"| **violations** (certified but measured > 0) | {len(cert_bad)} |",
            f"| not certified (push/pop reachable) | {len(uncert)} |",
            f"| not certified but measured 0 (imprecision, not unsoundness) | {len(uncert_zero)} |",
            f"| measured stack_peak > 0 | {sum(1 for r in ok if r['stack_peak'] > 0)} |",
            "",
        ]
        if uncert_zero:
            out += ["Not certified yet measured 0: " + ", ".join(Path(r["file"]).name for r in uncert_zero), ""]

        # 3. call count bound
        cb = [r for r in ok if r["calls_bound"] != ""]
        c_ok = [r for r in cb if r["calls_ok"] is True]
        c_bad = [r for r in cb if r["calls_ok"] is False]
        c_tight = [r for r in cb if r["calls_slack"] == 0]
        in_loop = [r for r in ok if r["call_in_loop"] is True]
        violations += [("calls", r) for r in c_bad]
        out += [
            "### 3. total_calls <= C (acyclic and no call inside a loop body)", "",
            "| | count |", "|---|---:|",
            f"| bound C exists | {len(cb)} |",
            f"| bound holds | {len(c_ok)} |",
            f"| **violations** | {len(c_bad)} |",
            f"| bound tight (measured = C) | {len(c_tight)} / {len(cb)} |",
            f"| no bound: call inside a loop | {len(in_loop)} |",
            f"| no bound: recursion | {len([r for r in ok if r['acyclic'] is False])} |",
            "",
        ]
        loose = [r for r in cb if r["calls_slack"] != 0]
        if loose:
            out += ["C not tight (a call site in an untaken if-branch): " +
                    ", ".join(f"{Path(r['file']).name} ({r['total_calls']}<={r['calls_bound']})" for r in loose), ""]

    out += ["## Violations", ""]
    if violations:
        out += ["| kind | file | predicted | measured |", "|---|---|---|---|"]
        for kind, r in violations:
            if kind == "depth":
                out.append(f"| depth | {r['file']} | <= {r['depth_bound']} | {r['call_depth_peak']} |")
            elif kind == "stack":
                out.append(f"| stack | {r['file']} | 0 | {r['stack_peak']} |")
            else:
                out.append(f"| calls | {r['file']} | <= {r['calls_bound']} | {r['total_calls']} |")
    else:
        out.append("None: every measurement is within its static bound.")
    out.append("")
    return "\n".join(out)


def write(rows: list[dict], directory: Path = DATA_DIR) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / "prediction_vs_measurement.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        w.writeheader()
        for row in rows:
            w.writerow({k: row.get(k, "") for k in FIELDS})
    (directory / "prediction_vs_measurement.md").write_text(summarize(rows))


def main() -> int:
    rows = compare_all()
    write(rows, DATA_DIR)
    print((DATA_DIR / "prediction_vs_measurement.md").read_text())
    return 0


if __name__ == "__main__":
    sys.exit(main())
