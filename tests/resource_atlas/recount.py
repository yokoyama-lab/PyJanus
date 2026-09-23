#!/usr/bin/env python3
"""Recompute the RC-03 array figure split into output / input / garbage.

RC-03 reports: "of the arrays that were written, ~65% never return a cell to
0 and ~13% end empty".  That count cannot tell a legitimate output array from
garbage because Janus has no notion of output.  This script joins the
profiler's per-array CSV with the hand annotations in
``annotations/out_annotations.json`` and recomputes the figure per class.

Usage (from the repository root)::

    python3 tests/resource_atlas/recount.py                       # defaults
    python3 tests/resource_atlas/recount.py --csv path/to/corpus_arrays.csv \
        --annotations tests/resource_atlas/annotations/out_annotations.json \
        --out tests/resource_atlas/data/recount.md

The CSV must have the columns ``file,array,puts,takes,ends_empty,written``
(``file`` may be a repository-relative path or a bare basename; ``ends_empty``
and ``written`` are 0/1 or true/false).  Extra columns are ignored.  The
Markdown report is printed and, unless ``--out -`` is given, written to disk.
"""
from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py.outannot import (  # noqa: E402
  CLASSES, CLASS_CLEAN, CLASS_GARBAGE, CLASS_INPUT, CLASS_OUTPUT,
  Classified, classify_detailed, load_sidecar, sidecar_for, summarize,
)

DEFAULT_CSV = ROOT / "tests" / "resource_atlas" / "data" / "corpus_arrays.csv"
DEFAULT_ANN = ROOT / "tests" / "resource_atlas" / "annotations" / "out_annotations.json"
DEFAULT_OUT = ROOT / "tests" / "resource_atlas" / "data" / "recount.md"


def read_csv(path: Path) -> dict[str, dict[str, dict[str, str]]]:
  """``{file: {array: row}}`` preserving CSV order."""
  per_file: dict[str, dict[str, dict[str, str]]] = defaultdict(dict)
  with open(path, newline="", encoding="utf-8") as f:
    reader = csv.DictReader(f)
    missing = {"file", "array", "puts", "takes", "ends_empty", "written"} - set(reader.fieldnames or [])
    if missing:
      raise SystemExit(f"{path}: missing columns {sorted(missing)}")
    for row in reader:
      per_file[row["file"].strip()][row["array"].strip()] = row
  return per_file


def pct(n: int, d: int) -> str:
  return "-" if d == 0 else f"{100.0 * n / d:.1f}%"


def build_report(per_file, sidecar, *, csv_path: Path, ann_path: Path) -> tuple[str, dict]:
  all_items: list[Classified] = []
  per_program: list[tuple[str, str | None, list[Classified]]] = []
  unmatched_files: list[str] = []
  unmatched_names: list[tuple[str, str]] = []
  for file, arrays in per_file.items():
    ann = sidecar_for(file, sidecar)
    if ann is None:
      unmatched_files.append(file)
    items = classify_detailed(arrays, ann)
    if ann is not None:
      for c in items:
        if c.role is None:
          unmatched_names.append((file, c.name))
    all_items.extend(items)
    per_program.append((file, ann.confidence if ann else None, items))

  s = summarize(all_items)
  written = s["written"]
  never = s["never_take"]
  nb = s["never_take_by_class"]
  lines: list[str] = []
  lines.append("# RC-03 array figure, recomputed with output/garbage annotations")
  lines.append("")
  lines.append(f"- arrays CSV: `{csv_path}`")
  lines.append(f"- annotations: `{ann_path}`")
  lines.append(f"- programs in CSV: {len(per_file)}; arrays: {s['arrays']}; written arrays: {written}")
  lines.append("")
  lines.append("## Headline (written arrays)")
  lines.append("")
  lines.append("RC-03 (unannotated): \"of the written arrays, N never take a cell back to 0, M end empty\".")
  lines.append("")
  lines.append("| quantity | count | % of written |")
  lines.append("|---|---:|---:|")
  lines.append(f"| written arrays | {written} | 100% |")
  lines.append(f"| never take (takes = 0) | {never} | {pct(never, written)} |")
  lines.append(f"| ... of which **output** | {nb[CLASS_OUTPUT]} | {pct(nb[CLASS_OUTPUT], written)} |")
  lines.append(f"| ... of which **input-preserved** | {nb[CLASS_INPUT]} | {pct(nb[CLASS_INPUT], written)} |")
  lines.append(f"| ... of which **garbage** | {nb[CLASS_GARBAGE]} | {pct(nb[CLASS_GARBAGE], written)} |")
  lines.append(f"| ... of which clean (never take yet all-zero: never written non-zero) | {nb[CLASS_CLEAN]} | {pct(nb[CLASS_CLEAN], written)} |")
  lines.append(f"| end empty (ends_empty) | {s['ends_empty']} | {pct(s['ends_empty'], written)} |")
  lines.append("")
  lines.append("Reading: the RC-03 \"never cleared\" share is the *never take* row; the three rows")
  lines.append("below it split it into legitimate outputs, untouched inputs, and garbage proper.")
  lines.append("Garbage among never-take arrays as a share of never-take: "
               f"{pct(nb[CLASS_GARBAGE], never)}; as a share of written arrays: {pct(nb[CLASS_GARBAGE], written)}.")
  lines.append("")
  lines.append("## Per class (written arrays)")
  lines.append("")
  lines.append("| class | count | % of written |")
  lines.append("|---|---:|---:|")
  for cls in CLASSES:
    lines.append(f"| {cls} | {s['by_class'][cls]} | {pct(s['by_class'][cls], written)} |")
  lines.append("")
  lines.append(f"Unannotated written arrays (counted as garbage): {s['unannotated']}")
  if unmatched_files:
    lines.append("")
    lines.append("Programs in the CSV with no annotation entry (all their arrays counted as garbage):")
    for f in unmatched_files:
      lines.append(f"- `{f}`")
  if unmatched_names:
    lines.append("")
    lines.append("Arrays in annotated programs that the sidecar does not name (counted as garbage):")
    for f, n in unmatched_names:
      lines.append(f"- `{f}`: `{n}`")
  if s["mismatches"]:
    lines.append("")
    lines.append("Annotation / measurement mismatches:")
    for name, note in s["mismatches"]:
      lines.append(f"- `{name}`: {note}")
  lines.append("")
  lines.append("## Garbage arrays per program")
  lines.append("")
  lines.append("| program | confidence | garbage arrays (puts/takes) | output | input | clean |")
  lines.append("|---|---|---|---|---|---|")
  for file, conf, items in per_program:
    garbage = [c for c in items if c.cls == CLASS_GARBAGE and c.written]
    outs = [c.name for c in items if c.cls == CLASS_OUTPUT]
    ins = [c.name for c in items if c.cls == CLASS_INPUT]
    clean = [c.name for c in items if c.cls == CLASS_CLEAN]
    g = ", ".join(f"{c.name} ({c.puts}/{c.takes})" + (" *" if c.role is None else "") for c in garbage) or "-"
    lines.append(f"| `{file}` | {conf or '-'} | {g} | {', '.join(outs) or '-'} | {', '.join(ins) or '-'} | {', '.join(clean) or '-'} |")
  lines.append("")
  lines.append("`*` = unannotated array (garbage by default).  puts/takes are the profiler's 0->non-0 and non-0->0 counts.")
  return "\n".join(lines) + "\n", s


def main(argv: list[str] | None = None) -> int:
  ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
  ap.add_argument("--csv", type=Path, default=DEFAULT_CSV, help="profiler CSV (file,array,puts,takes,ends_empty,written)")
  ap.add_argument("--annotations", type=Path, default=DEFAULT_ANN, help="sidecar JSON")
  ap.add_argument("--out", type=Path, default=DEFAULT_OUT, help="Markdown output path ('-' = stdout only)")
  ap.add_argument("--quiet", action="store_true", help="do not echo the report to stdout")
  args = ap.parse_args(argv)

  if not args.csv.exists():
    print(f"error: arrays CSV not found: {args.csv}\n"
          "       (worker A's profiler writes tests/resource_atlas/data/corpus_arrays.csv; pass --csv)", file=sys.stderr)
    return 2
  sidecar = load_sidecar(args.annotations)
  per_file = read_csv(args.csv)
  report, _ = build_report(per_file, sidecar, csv_path=args.csv, ann_path=args.annotations)
  if not args.quiet:
    print(report, end="")
  if str(args.out) != "-":
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(report, encoding="utf-8")
    if not args.quiet:
      print(f"[written {args.out}]", file=sys.stderr)
  return 0


if __name__ == "__main__":
  raise SystemExit(main())
