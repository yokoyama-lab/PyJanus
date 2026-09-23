"""Measure the RC-03 resource vector over the generated variants and the corpus.

Writes (all deterministic, so they can be diffed after a change):

* ``data/scaling.csv`` / ``data/scaling.md``: one row per generated variant
  (family, size, param, steps, stack_peak, call_depth_peak, total_calls,
  final_live_bits, predicted_stack_peak, match) plus the adjacent-ratio
  columns rc03 reports.
* ``data/corpus_atlas.csv``: one row per corpus program (101 files) with the
  resource vector and the per-array census as a JSON column; programs that
  fail to run keep their row with the ``error`` column filled.
* ``data/corpus_arrays.csv``: one row per (program, array).
* ``data/corpus_summary.md``: the aggregates (stack users, arrays that never
  take, arrays that end empty, ...).

Run ``python3 -m tests.resource_atlas.measure`` from the repository root.
"""
from __future__ import annotations

import csv
import json
import statistics
import sys
from collections import Counter
from pathlib import Path

from .common import DATA_DIR, Measurement, corpus_files, measure, rel, resource_row
from .gen_inputs import STD as GEN_STD, Variant, variants

SCALING_FIELDS = [
    "family", "size", "param", "file", "steps", "stack_peak", "call_depth_peak",
    "total_calls", "final_live_bits", "predicted_stack_peak", "match",
    "steps_ratio", "stack_ratio",
]
ATLAS_FIELDS = [
    "file", "std", "steps", "stack_peak", "call_depth_peak", "total_calls",
    "final_live_bits", "erasures", "arrays", "error",
]
ARRAY_FIELDS = [
    "file", "std", "array", "size", "instances", "puts", "takes", "end_nonzero",
    "ends_empty", "written", "live_at_end",
]


# ---------------------------------------------------------------------------
# scaling table
# ---------------------------------------------------------------------------

def measure_variants(vs: list[Variant] | None = None) -> list[dict]:
    rows: list[dict] = []
    prev: dict[str, dict] = {}
    for v in vs if vs is not None else variants():
        m = measure(v.path, GEN_STD)
        if not m.ok:
            rows.append({"family": v.family, "size": v.size, "param": v.param,
                         "file": rel(v.path), "predicted_stack_peak": v.predicted_stack_peak,
                         "match": "ERROR: " + (m.error or "")})
            continue
        row = {"family": v.family, "size": v.size, "param": v.param, "file": rel(v.path)}
        row.update(resource_row(m.profile))
        del row["erasures"]
        row["predicted_stack_peak"] = v.predicted_stack_peak
        row["match"] = row["stack_peak"] == v.predicted_stack_peak
        p = prev.get(v.family)
        if p is not None and v.family in ("gcd_fib", "bubble_sort", "bubble_sort_fwd", "knapsack", "lcs", "edit_distance"):
            row["steps_ratio"] = f"{row['steps'] / p['steps']:.3f}"
            row["stack_ratio"] = (f"{row['stack_peak'] / p['stack_peak']:.3f}"
                                  if p["stack_peak"] else "")
        else:
            row["steps_ratio"] = ""
            row["stack_ratio"] = ""
        prev[v.family] = row
        rows.append(row)
    return rows


def write_scaling(rows: list[dict], directory: Path = DATA_DIR) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / "scaling.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=SCALING_FIELDS, extrasaction="ignore")
        w.writeheader()
        for row in rows:
            w.writerow({k: row.get(k, "") for k in SCALING_FIELDS})

    md: list[str] = [
        "# Scaling table (RC-03 §規模を振った計測, re-measured with ~20 sizes per family)",
        "",
        "`steps_ratio` = steps(size) / steps(previous size) (the adjacent ratio rc03 reports;",
        "no curve fitting).  `match` = measured stack_peak equals the predicted law.",
        "",
    ]
    by_family: dict[str, list[dict]] = {}
    for row in rows:
        by_family.setdefault(row["family"], []).append(row)
    laws = {
        "gcd_fib": "stack_peak = k (number of subtractions; a=F(k+2), b=F(k+1))",
        "gcd_pair": "stack_peak = (sum of Euclid quotients) - 1",
        "bubble_sort": "stack_peak = n(n-1)/2 (reverse-sorted input; call + uncall as in the original)",
        "bubble_sort_fwd": "stack_peak = n(n-1)/2 (reverse-sorted input; forward call only)",
        "bubble_sort_perm": "stack_peak = n(n-1)/2 (pseudo-random permutation: input-order independent)",
        "knapsack": "stack_peak = 0 (bottom-up DP; cap = n+2)",
        "lcs": "stack_peak = 0 (bottom-up DP; m = n)",
        "edit_distance": "stack_peak = 0 (bottom-up DP; m = n)",
    }
    for family, frows in by_family.items():
        md.append(f"## {family}")
        md.append("")
        md.append(f"Predicted law: {laws.get(family, '')}")
        md.append("")
        md.append("| size | param | steps | steps_ratio | stack_peak | predicted | match | call_depth | calls | final_live_bits |")
        md.append("|---:|---|---:|---:|---:|---:|---|---:|---:|---:|")
        for r in frows:
            md.append(
                f"| {r['size']} | {r['param']} | {r.get('steps', '')} | {r.get('steps_ratio', '')} | "
                f"{r.get('stack_peak', '')} | {r['predicted_stack_peak']} | {r['match']} | "
                f"{r.get('call_depth_peak', '')} | {r.get('total_calls', '')} | {r.get('final_live_bits', '')} |"
            )
        n_ok = sum(1 for r in frows if r["match"] is True)
        md.append("")
        md.append(f"{n_ok}/{len(frows)} points match the predicted stack_peak.")
        md.append("")
    (directory / "scaling.md").write_text("\n".join(md))


# ---------------------------------------------------------------------------
# corpus atlas
# ---------------------------------------------------------------------------

def measure_corpus() -> list[Measurement]:
    return [measure(path, std) for path, std in corpus_files()]


def atlas_rows(ms: list[Measurement]) -> tuple[list[dict], list[dict]]:
    atlas: list[dict] = []
    arrays: list[dict] = []
    for m in ms:
        row = {"file": rel(m.path), "std": m.std, "error": m.error or ""}
        if m.ok:
            p = m.profile
            row.update(resource_row(p))
            row["arrays"] = json.dumps({
                name: {"size": st.size, "puts": st.puts, "takes": st.takes,
                       "end_nonzero": st.end_nonzero}
                for name, st in p.arrays.items()
            }, separators=(",", ":"))
            for name, st in p.arrays.items():
                arrays.append({
                    "file": rel(m.path), "std": m.std, "array": name, "size": st.size,
                    "instances": st.instances, "puts": st.puts, "takes": st.takes,
                    "end_nonzero": st.end_nonzero, "ends_empty": st.ends_empty,
                    "written": st.written, "live_at_end": st.live_at_end,
                })
        atlas.append(row)
    return atlas, arrays


def summarize_corpus(atlas: list[dict], arrays: list[dict]) -> str:
    ok = [r for r in atlas if not r["error"]]
    failed = [r for r in atlas if r["error"]]
    written = [a for a in arrays if a["written"]]
    never_take = [a for a in written if a["takes"] == 0]
    end_empty = [a for a in written if a["ends_empty"]]
    stack_users = [r for r in ok if r["stack_peak"] > 0]
    all_zero_end = [r for r in ok if r["final_live_bits"] == 0]

    def med(key: str) -> str:
        vals = [r[key] for r in ok]
        return f"{statistics.median(vals):g}" if vals else "-"

    def mx(key: str) -> str:
        if not ok:
            return "-"
        r = max(ok, key=lambda r: r[key])
        return f"{r[key]} ({Path(r['file']).name})"

    def pct(a: int, b: int) -> str:
        return f"{a}/{b} = {100.0 * a / b:.1f}%" if b else f"{a}/{b}"

    lines = [
        "# Corpus atlas summary",
        "",
        f"Programs: {len(atlas)} total, {len(ok)} measured, {len(failed)} failed to run "
        f"(kept as rows with an `error` column in corpus_atlas.csv).",
        "",
        "| quantity | value |",
        "|---|---|",
        f"| steps median / max | {med('steps')} / {mx('steps')} |",
        f"| stack_peak median / max | {med('stack_peak')} / {mx('stack_peak')} |",
        f"| call_depth_peak median / max | {med('call_depth_peak')} / {mx('call_depth_peak')} |",
        f"| final_live_bits median / max | {med('final_live_bits')} / {mx('final_live_bits')} |",
        f"| programs with stack_peak > 0 | {pct(len(stack_users), len(ok))} |",
        f"| programs ending with all state zero | {pct(len(all_zero_end), len(ok))} |",
        f"| erasures | 0 in all {len(ok)} programs (by construction) |",
        f"| arrays seen / written (puts > 0) | {len(arrays)} / {len(written)} |",
        f"| written arrays that never take (takes = 0) | {pct(len(never_take), len(written))} |",
        f"| written arrays that end empty (all cells 0) | {pct(len(end_empty), len(written))} |",
        "",
        "rc03 (111-program corpus at c6c1656, tex:149-150): 122/189 = 65% written arrays never take,",
        "25/189 = 13% end empty; 36/111 = 32% use a stack; steps median 74; stack_peak median 0.",
        "rc03 on the renamed 101 fixtures (tex:179-181): 121/177 = 68% never take, 23/177 = 13% end empty.",
        "",
        "## Top stack users",
        "",
        "| file | stack_peak | steps |",
        "|---|---:|---:|",
    ]
    for r in sorted(stack_users, key=lambda r: -r["stack_peak"])[:10]:
        lines.append(f"| {r['file']} | {r['stack_peak']} | {r['steps']} |")
    if failed:
        lines += ["", "## Programs that did not run", "", "| file | std | error |", "|---|---|---|"]
        for r in failed:
            lines.append(f"| {r['file']} | {r['std']} | {r['error']} |")
    by_std = Counter(r["std"] for r in atlas)
    lines += ["", "## Programs per dialect", "", "| std | programs | measured |", "|---|---:|---:|"]
    for std, n in sorted(by_std.items()):
        lines.append(f"| {std} | {n} | {sum(1 for r in ok if r['std'] == std)} |")
    return "\n".join(lines) + "\n"


def write_corpus(atlas: list[dict], arrays: list[dict], directory: Path = DATA_DIR) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / "corpus_atlas.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=ATLAS_FIELDS, extrasaction="ignore")
        w.writeheader()
        for row in atlas:
            w.writerow({k: row.get(k, "") for k in ATLAS_FIELDS})
    with (directory / "corpus_arrays.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=ARRAY_FIELDS)
        w.writeheader()
        for row in arrays:
            w.writerow(row)
    (directory / "corpus_summary.md").write_text(summarize_corpus(atlas, arrays))


def main(argv: list[str] | None = None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    what = set(argv) or {"scaling", "corpus"}
    if "scaling" in what:
        rows = measure_variants()
        write_scaling(rows, DATA_DIR)
        bad = [r for r in rows if r["match"] is not True]
        print(f"scaling: {len(rows)} variants, {len(rows) - len(bad)} match predicted stack_peak")
        for r in bad:
            print("  MISMATCH", r["file"], r.get("stack_peak"), "vs", r["predicted_stack_peak"], r["match"])
    if "corpus" in what:
        ms = measure_corpus()
        atlas, arrays = atlas_rows(ms)
        write_corpus(atlas, arrays, DATA_DIR)
        print(f"corpus: {len(atlas)} programs, {sum(1 for r in atlas if not r['error'])} measured")
        print((DATA_DIR / "corpus_summary.md").read_text())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
