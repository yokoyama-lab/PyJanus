#!/usr/bin/env bash
# Axiom audit: build the Rocq development and assert that every headline theorem
# depends on at most `functional_extensionality` -- no extra axioms, no Admitted.
# Run from anywhere; honours $ROCQ (default: rocq on PATH).
set -euo pipefail
cd "$(dirname "$0")"

ROCQ="${ROCQ:-$(command -v rocq)}"
ROCQ_DIR="$(dirname "$ROCQ")"
export PATH="$ROCQ_DIR:$PATH"
echo "== using $("$ROCQ" --version | head -1) =="

# 1. Build the whole development.
"$ROCQ" makefile -f _CoqProject -o Makefile >/dev/null
make -j2

# 2. Print the assumptions of the headline results.
AUDIT="$(mktemp auditXXXXXX.v)"
BASE="${AUDIT%.v}"
cleanup() { rm -f "$AUDIT" "$BASE.vo" "$BASE.glob" ".$BASE.aux"; }
trap cleanup EXIT

cat > "$AUDIT" <<'EOF'
Require Import Janus RevCore RevExtract RevInvert RevStack RevCA
               RevDenote RevInverse RevCat RevBennett.
Require Import RevArr RevExtractAr RevFrame RevExtractFrame.
Require Import RevPipeline RevPipelineArr RevGolomb RevVarint RevZigzag RevDeltaN.
Module DnS := RevDenote.Denote RevStack.StackPrim.
Module HS  := RevInverse.InvMonoidHom RevStack.StackPrim.
(* core reversibility *)
Print Assumptions Janus.exec_injective.
Print Assumptions Janus.exec_iff.
(* instances sharing nothing with Janus *)
Print Assumptions stack_reversible.
Print Assumptions stack_invert_correct.
Print Assumptions ca_reversible.
(* executable interpreter: soundness + completeness + inverse correctness *)
Print Assumptions RevExtract.run_sound.
Print Assumptions run_complete.
Print Assumptions run_invert_iff.
(* arrays core + its extracted interpreter *)
Print Assumptions RevArr.exec_injective.
Print Assumptions RevExtractAr.run_sound.
(* frame-stacked core (recursion with locals) + its extracted interpreter *)
Print Assumptions RevFrame.exec_injective.
Print Assumptions RevFrame.exec_iff.
Print Assumptions RevFrame.run_sound.
(* denotational: adequacy + full abstraction + inverter = converse *)
Print Assumptions DnS.adequacy.
Print Assumptions DnS.full_abstraction.
Print Assumptions DnS.denote_invert.
(* inverse-monoid / dagger category *)
Print Assumptions HS.image_inverse_law.
Print Assumptions pinj_inverse_law.
Print Assumptions rst_comp.
(* Bennett reversibilization *)
Print Assumptions bennett_correct.
Print Assumptions bennett_pinj.
(* verified clean-reversible construction pipeline:
   proven-injective spec  ==>  proven clean-reversible Janus (exec) + free reversibility *)
Print Assumptions RevPipeline.R_reversible.
Print Assumptions RevPipelineArr.Rdelta_reversible.
Print Assumptions RevPipelineArr.Rloop_reversible.
Print Assumptions RevGolomb.golomb_encode.
Print Assumptions RevGolomb.golomb_decode.
Print Assumptions RevGolomb.f_gr_injective.
Print Assumptions RevVarint.varint_decode.
Print Assumptions RevVarint.f_vi_injective.
Print Assumptions RevZigzag.zigzag_decode.
Print Assumptions RevZigzag.zig_unzig.
Print Assumptions RevDeltaN.deltaN_computes.
Print Assumptions RevDeltaN.deltaN_reversible.
EOF

OUT="$("$ROCQ" compile -Q . "" "$AUDIT" 2>&1)"
echo "$OUT"

# 3. Verdict.  Print Assumptions lists each axiom's name at column 0 as
#    `Name : type`; the only one we permit is functional_extensionality.
if printf '%s\n' "$OUT" | grep -qiE 'error|Admitted'; then
  echo "AUDIT FAILED: error or Admitted in the development." >&2
  exit 1
fi
bad="$(printf '%s\n' "$OUT" \
        | grep -E '^[A-Za-z_][A-Za-z0-9_.]* :' \
        | grep -v 'functional_extensionality_dep' || true)"
if [ -n "$bad" ]; then
  echo "AUDIT FAILED: unexpected axioms:" >&2
  printf '%s\n' "$bad" >&2
  exit 1
fi
echo "AUDIT OK: every headline theorem uses at most functional_extensionality."
