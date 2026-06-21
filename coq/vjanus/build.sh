#!/usr/bin/env bash
# Build `vjanus`: extract the verified interpreter from Coq (if needed), then
# compile the standalone OCaml front-end against it.  Honours $ROCQ / $OCAMLC.
set -euo pipefail
cd "$(dirname "$0")/.."          # -> coq/

ROCQ="${ROCQ:-$(command -v rocq)}"
OCAMLC="${OCAMLC:-$(command -v ocamlc)}"

[ -f janus_arr.ml ] || "$ROCQ" compile RevExtractAr.v >/dev/null

"$OCAMLC" -w -a -I . -I vjanus -o vjanus/vjanus \
  janus_arr.mli janus_arr.ml \
  vjanus/glue.ml vjanus/ast.ml vjanus/lexer.ml vjanus/parser.ml vjanus/lower.ml vjanus/main.ml

echo "built coq/vjanus/vjanus"
