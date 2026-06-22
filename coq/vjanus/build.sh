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

# Phase 2a: the frame-stacked core (depth-indexed locals → recursion with locals).
# Until the lowering targets it, exercise the extracted frame interpreter end to
# end on the recursion-with-locals case the flat core cannot represent.
[ -f janus_frame.ml ] || "$ROCQ" compile RevExtractFrame.v >/dev/null

"$OCAMLC" -w -a -I . -I vjanus -o vjanus/frame_smoke \
  janus_frame.mli janus_frame.ml \
  vjanus/glue_frame.ml vjanus/frame_smoke.ml

vjanus/frame_smoke

# vjanusf: the standalone front-end on the frame core (own parser, frame-aware
# lowering).  Grows toward replacing vjanus; for now it covers the scalar +
# control-flow + call subset and skips (exit 3) on arrays/stacks.
"$OCAMLC" -w -a -I . -I vjanus -o vjanus/vjanusf \
  janus_frame.mli janus_frame.ml \
  vjanus/glue_frame.ml vjanus/ast.ml vjanus/lexer.ml vjanus/parser.ml \
  vjanus/lower_frame.ml vjanus/mainf.ml

echo "built coq/vjanus/vjanusf"
