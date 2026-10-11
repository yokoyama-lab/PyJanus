#!/usr/bin/env bash
# Decide whether the RevExtractAr interpreter's NONE on a program comes from fuel
# exhaustion or from a runtime side condition.  Patches a COPY of the extracted
# janus_arr.ml:  `| O -> None` -> failwith "FUEL_EXHAUSTED";  each
# `| False/True -> None` inside run/runloop -> failwith "NONE_AT_<line>".
# Control: the same patch with fuel 3 must report FUEL_EXHAUSTED on loop_count.ja,
# otherwise the probe proves nothing.
#   fuel_probe.sh <exported-tree-with-extracted-coq>
set -euo pipefail
tree="$1"; p="$(mktemp -d)"; trap 'rm -rf "$p"' EXIT
src="$tree/coq/janus_arr.ml"
lo=$(grep -n '^let rec run ' "$src" | head -1 | cut -d: -f1)
awk -v lo="$lo" '
  NR>=lo && NR<=lo+120 && /\| O -> None/ {sub(/-> None/, "-> failwith \"FUEL_EXHAUSTED\"")}
  NR>=lo && NR<=lo+120 && /(False|True) -> None/ {sub(/-> None/, "-> failwith \"NONE_AT_" NR "\"")}
  {print}' "$src" > "$p/janus_arr.ml"
cp "$tree/coq/janus_arr.mli" "$tree/coq/harness/driverar.ml" "$p/"
sed 's/nat_of_int 3000000/nat_of_int 3/' "$p/driverar.ml" > "$p/driverar_tiny.ml"
(cd "$p" && ocamlc -w -a -o drv janus_arr.mli janus_arr.ml driverar.ml \
          && ocamlc -w -a -o tiny janus_arr.mli janus_arr.ml driverar_tiny.ml)
printf 'patched_sites\t%s\n' "$(grep -c -E 'FUEL_EXHAUSTED|NONE_AT_' "$p/janus_arr.ml")"
printf 'source_lines_tagged\n'; grep -n -E 'FUEL_EXHAUSTED|NONE_AT_' "$p/janus_arr.ml" | sed 's/^/  /'
cd "$tree"
PYTHONPATH="$tree:$tree/coq/harness" python3 - "$p" <<'PY'
import subprocess, sys, differentialar as D
p = sys.argv[1]
def probe(driver, ja):
    sexpr, scalars, _, _ = D.translate(ja)
    full = sexpr + " " + str(len(scalars)) + " " + " ".join(f"(rs {g})" for _, g in scalars)
    r = subprocess.run([driver], input=full, capture_output=True, text=True)
    return (r.stdout.strip().split("\n")[0][:60] or "-", r.stderr.strip()[-60:] or "-")
print("control_tiny_fuel_loop_count", *probe(f"{p}/tiny", "coq/harness/fixtures/loop_count.ja"), sep="\t")
print("structs_array_field_c", *probe(f"{p}/drv", "tests/jana2014/fixtures/examples/structs_array_field_c.ja"), sep="\t")
PY
