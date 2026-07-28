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
               RevDenote RevFix RevInverse RevCat RevTrace RevCtrl RevPPR RevBennett.
Require Import RevArr RevExtractAr RevFrame RevExtractFrame.
Require Import RevPipeline RevPipelineArr RevGolomb RevVarint RevZigzag RevDeltaN.
Require Import RevIO RevMul RevLowering RevLowerExpr RevLowerStmt RevMod RevExtMod RevExtractMod RevSMod RevExtSMod RevExtractSMod.
Module ModFacts256 := RevMod.ModFacts RevMod.M256.
Module ExtModFacts256 := RevExtMod.ExtModFacts RevExtMod.M256.
Module SModFacts8 := RevSMod.SModFacts RevSMod.B8.
Module ExtSModFacts8 := RevExtSMod.ExtSModFacts RevExtSMod.B8.
Module DnS := RevDenote.Denote RevStack.StackPrim.
Module FxS := RevFix.DenoteFix RevStack.StackPrim.
Module StS := RevCtrl.Struct RevStack.StackPrim.
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
Print Assumptions RevExtractAr.run_complete.
Print Assumptions RevExtractAr.run_none_no_exec.
(* frame-stacked core (recursion with locals) + its extracted interpreter *)
Print Assumptions RevFrame.exec_injective.
Print Assumptions RevFrame.exec_iff.
Print Assumptions RevFrame.run_sound.
Print Assumptions RevFrame.run_complete.
Print Assumptions RevFrame.run_none_no_exec.
Print Assumptions RevFrame.app_ainv.
Print Assumptions RevFrame.aok_ainv.
(* denotational: adequacy + full abstraction + inverter = converse *)
Print Assumptions DnS.adequacy.
Print Assumptions DnS.full_abstraction.
Print Assumptions DnS.denote_invert.
(* denotational, closed: procedure meanings as a least fixed point *)
Print Assumptions FxS.fix_adequacy.
Print Assumptions FxS.Dfix_fixed.
Print Assumptions FxS.Dfix_least.
Print Assumptions FxS.exec_is_lfp.
Print Assumptions FxS.denote_fix_reversible.
Print Assumptions FxS.denote_fix_injective.
(* inverse-monoid / dagger category *)
Print Assumptions HS.image_inverse_law.
Print Assumptions pinj_inverse_law.
Print Assumptions rst_comp.
(* PInj is traced over the coproduct; the Janus loop IS a trace *)
Print Assumptions pinj_sumH.
Print Assumptions convH_sumH.
Print Assumptions pinj_traceH.
Print Assumptions trace_conv.
Print Assumptions trace_yanking.
Print Assumptions trace_vanishing.
Print Assumptions trace_natural_l.
Print Assumptions loop_is_trace.
Print Assumptions pinj_turn.
Print Assumptions rev_loop_via_trace.
(* the control constructors ARE PInj structure: exit assertion = dagger of the test *)
Print Assumptions pinj_testH.
Print Assumptions test_dagger.
Print Assumptions if_is_test_sum.
Print Assumptions rev_if_via_cat.
Print Assumptions StS.denote_If.
Print Assumptions StS.denote_Loop.
Print Assumptions StS.denote_reversible_structural.
(* Paolini-Piccolo-Roversi's parametric Janus as a REV_PRIM instance;
   its list-store Janus needs no funext at all *)
Print Assumptions JZ.ppr_reversible.
Print Assumptions janus_list_reversible.
Print Assumptions janus_list_iff.
Print Assumptions ex_add_runs.
Print Assumptions ex_add_inverts.
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
(* reversible I/O (jana2014_in_out read/write), multiplicative update,
   and the two nontrivial vjanus lowering encodings *)
Print Assumptions RevIO.io_reversible.
Print Assumptions RevIO.io_iff.
Print Assumptions RevMul.mul_reversible.
Print Assumptions RevLowering.xor3_swaps.
Print Assumptions RevLowering.xor3_selfinverse.
Print Assumptions RevLowering.xor3_alias_zero.
Print Assumptions RevLowering.add_zero_noop.
Print Assumptions RevLowering.pop_push.
Print Assumptions RevLowering.push_clean.
Print Assumptions RevLowering.addr_injective.
Print Assumptions RevLowering.cantor2_injective.
Print Assumptions RevLowering.tri_closed.
(* the expression lowering preserves values (vjanus lowering soundness, slice 1) *)
Print Assumptions RevLowerExpr.lower_expr_sound.
Print Assumptions RevLowerExpr.and_encoding.
Print Assumptions RevLowerExpr.or_encoding.
Print Assumptions RevLowerExpr.lower_expr_safe.
Print Assumptions RevLowerExpr.isbool_isb.
Print Assumptions RevLowerExpr.and_needs_wf.
Print Assumptions RevLowerExpr.lower_expr_ok.
Print Assumptions RevFrame.safe_ncell.
(* statement lowering: forward simulation and what vjanus needs from it *)
Print Assumptions RevLowerStmt.swap_lowering.
Print Assumptions RevLowerStmt.reads_lower.
Print Assumptions RevLowerStmt.loceqb_sloc.
Print Assumptions RevLowerStmt.lower_stmt_sound.
Print Assumptions RevLowerStmt.lower_stmt_correct.
Print Assumptions RevLowerStmt.lower_stmt_reversible.
Print Assumptions RevLowerStmt.seval_defined.
Print Assumptions RevLowerStmt.lower_stmt_complete.
Print Assumptions RevLowerStmt.lower_stmt_iff.
Print Assumptions ModFacts256.mod_reversible.
Print Assumptions RevMod.i8_wraps.
Print Assumptions ExtModFacts256.extmod_reversible.
Print Assumptions RevExtMod.i8_cell_wraps.
Print Assumptions RevExtractMod.Run256.run_sound.
Print Assumptions RevExtractMod.Run256.run_injective.
Print Assumptions SModFacts8.smod_reversible.
Print Assumptions RevSMod.s8_wraps.
Print Assumptions ExtSModFacts8.extsmod_reversible.
Print Assumptions RevExtSMod.i8_cell_swraps.
Print Assumptions RevExtSMod.expr_wraps_mid_computation.
Print Assumptions RevExtractSMod.Run8.run_sound.
Print Assumptions RevExtractSMod.Run8.run_injective.
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
