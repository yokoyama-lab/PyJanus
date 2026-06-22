#!/usr/bin/env bash
# Build `vjanus`: extract the verified frame-stacked interpreter from Coq (if
# needed), then compile the standalone OCaml front-end against it.  Honours
# $ROCQ / $OCAMLC.
set -euo pipefail
cd "$(dirname "$0")/.."          # -> coq/

ROCQ="${ROCQ:-$(command -v rocq)}"
OCAMLC="${OCAMLC:-$(command -v ocamlc)}"

# the verified evaluation core: depth-indexed local frames (recursion with
# locals), arrays, by-reference calls — extracted from RevExtractFrame.v and
# proved sound vs. RevFrame.exec (itself proved reversible).
[ -f janus_frame.ml ] || "$ROCQ" compile RevExtractFrame.v >/dev/null

# frame_smoke: a direct end-to-end check of the extracted core on the
# recursion-with-locals case (the flat model cannot represent it).
"$OCAMLC" -w -a -I . -I vjanus -o vjanus/frame_smoke \
  janus_frame.mli janus_frame.ml \
  vjanus/glue.ml vjanus/frame_smoke.ml
vjanus/frame_smoke

# vjanus: own jana2014 lexer/parser + frame-aware lowering -> extracted run.
"$OCAMLC" -w -a -I . -I vjanus -o vjanus/vjanus \
  janus_frame.mli janus_frame.ml \
  vjanus/glue.ml vjanus/ast.ml vjanus/lexer.ml vjanus/parser.ml \
  vjanus/lower.ml vjanus/main.ml

echo "built coq/vjanus/vjanus"
