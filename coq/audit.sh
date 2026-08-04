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

# 0. Repo-wide: no unfinished proof anywhere.
#
#    Steps 2-3 below only inspect the theorems this script *names*, so a new file
#    whose results were never added here could carry an `Admitted` and still come
#    out green.  This check does not depend on the list, and runs first because it
#    needs no build.
#
#    Deliberately NOT grepped repo-wide: `Axiom`.  A `Module Type` obligation is
#    declared with `Axiom` and is exactly how `REV_PRIM` states the three local
#    laws an instance must discharge (`RevCore.v`, `RevCoreP.v`, `RevMod.v`, ...),
#    so a blanket check would reject the framework's own design.  Real axioms
#    reaching a result are what `Print Assumptions` reports, which is step 3.
#
#    The pattern matches the vernacular `Admitted` and the `admit` tactic, not
#    the English word: `admits a sound fuel interpreter` and the like appear in
#    several file headers and must not trip it.
UNFINISHED="$(grep -nE 'Admitted|(^|[^A-Za-z])admit[[:space:]]*[.;]' ./*.v || true)"
if [ -n "$UNFINISHED" ]; then
  echo "AUDIT FAILED: unfinished proof in the development:" >&2
  printf '%s\n' "$UNFINISHED" >&2
  exit 1
fi

# 1. Build the whole development.
"$ROCQ" makefile -f _CoqProject -o Makefile >/dev/null
make -j2

# 2. Print the assumptions of the headline results.
AUDIT="$(mktemp auditXXXXXX.v)"
BASE="${AUDIT%.v}"
cleanup() { rm -f "$AUDIT" "$BASE.vo" "$BASE.glob" ".$BASE.aux"; }
trap cleanup EXIT

cat > "$AUDIT" <<'EOF'
Require Import Janus RevCore RevExt RevExtract RevInvert RevStack RevCA RevSmallStep
               RevDenote RevFix RevInverse RevCat RevTrace RevSMC RevTraced RevCtrl RevJoin RevCompile RevSemantics RevSteps RevError RevPPR RevBennett.
Require Import RevArr RevExtractAr RevFrame RevExtractFrame.
Require Import RevPipeline RevPipelineArr RevGolomb RevVarint RevZigzag RevDeltaN.
Require Import RevIO RevMul RevLowering RevLowerExpr RevLowerStmt RevSmvExpr RevSmvAlias RevSmvBlock RevMod RevExtMod RevExtractMod RevSMod RevExtSMod RevExtractSMod.
Module ModFacts256 := RevMod.ModFacts RevMod.M256.
Module ExtModFacts256 := RevExtMod.ExtModFacts RevExtMod.M256.
Module SModFacts8 := RevSMod.SModFacts RevSMod.B8.
Module ExtSModFacts8 := RevExtSMod.ExtSModFacts RevExtSMod.B8.
Module SsS := RevSmallStep.SmallStep RevStack.StackPrim.
Module DnS := RevDenote.Denote RevStack.StackPrim.
Module FxS := RevFix.DenoteFix RevStack.StackPrim.
Module StS := RevCtrl.Struct RevStack.StackPrim.
Module JnS := RevJoin.FixJoin RevStack.StackPrim.
Module SemS := RevSemantics.Semantics RevStack.StackPrim.
Module StpS := RevSteps.Steps RevStack.StackPrim.
Module ErrE := RevError.ErrSem RevExt.ExtPrim.
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
(* the small-step semantics is not step-reversible (Lanese-Vidal) *)
Print Assumptions SsS.step_not_backward_deterministic.
Print Assumptions SsS.exit_assertion_collapses.
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
(* PInj is symmetric monoidal for both the coproduct and the product,
   and the two are related by a distributor *)
Print Assumptions pinj_assocS.
Print Assumptions iso_assocS.
Print Assumptions sumS_pentagon.
Print Assumptions sumS_triangle.
Print Assumptions sumS_hexagon.
Print Assumptions assocS_natural.
Print Assumptions swapS_natural.
Print Assumptions lunitS_natural.
Print Assumptions runitS_natural.
Print Assumptions pinj_prodH.
Print Assumptions prodP_pentagon.
Print Assumptions prodP_triangle.
Print Assumptions prodP_hexagon.
Print Assumptions assocP_natural.
Print Assumptions swapP_natural.
Print Assumptions pinj_distrH.
Print Assumptions iso_distrH.
Print Assumptions distrH_natural.
Print Assumptions trace_natural_r.
Print Assumptions trace_superposing.
(* the control constructors ARE PInj structure: exit assertion = dagger of the test *)
Print Assumptions pinj_testH.
Print Assumptions test_dagger.
Print Assumptions if_is_test_sum.
Print Assumptions test_negation.
(* join structure of PInj *)
Print Assumptions pinj_join.
Print Assumptions pinj_join_chain.
Print Assumptions traceH_is_join_fam.
Print Assumptions pinj_traceH_via_join.
Print Assumptions decisions_closed_neg.
Print Assumptions decisions_closed_and.
Print Assumptions decisions_closed_or.
Print Assumptions dfalse_and.
Print Assumptions testH_decompose.
Print Assumptions JnS.Dfix_reversible_via_join.
(* five semantics of the framework language, and their agreement *)
Print Assumptions SemS.big_small_iff.
Print Assumptions SemS.big_den_iff.
Print Assumptions SemS.big_inv_iff.
Print Assumptions SemS.small_den_iff.
Print Assumptions SemS.small_inv_iff.
Print Assumptions SemS.den_inv_iff.
Print Assumptions SemS.all_agree4.
Print Assumptions SemS.big_fix_iff.
Print Assumptions SemS.big_flat_iff.
Print Assumptions SemS.small_flat_iff.
Print Assumptions SemS.den_flat_iff.
Print Assumptions SemS.inv_flat_iff.
Print Assumptions SemS.all_agree.
Print Assumptions SemS.flat_inverse_iff.
Print Assumptions SemS.small_injective.
Print Assumptions SemS.flat_injective.
(* the cost of compiling, and the cost of running backwards *)
Print Assumptions StpS.execn_exec.
Print Assumptions StpS.exec_execn.
Print Assumptions StpS.comp_cost.
Print Assumptions StpS.compilation_is_step_exact.
Print Assumptions StpS.mstepn_det.
Print Assumptions StpS.mrunn_det_halt.
Print Assumptions StpS.crun_cost_complete.
Print Assumptions StpS.compilation_is_step_exact_iff.
Print Assumptions StpS.csize_invert.
Print Assumptions StpS.execn_rev.
Print Assumptions StpS.execn_iff.
Print Assumptions StpS.inverse_costs_the_same.
(* assertion failure as an outcome, and the compiled ERR location *)
Print Assumptions ErrE.execE_ok_iff.
Print Assumptions ErrE.ok_not_err.
Print Assumptions ErrE.fail_sound.
Print Assumptions ErrE.fails_of_execE.
Print Assumptions ErrE.failsP_execE.
Print Assumptions ErrE.fail_iff.
Print Assumptions ErrE.no_fail_no_error.
(* the checker's expression encoding *)
Print Assumptions RevSmvExpr.floor_from_trunc.
Print Assumptions RevSmvExpr.mfdiv_correct.
Print Assumptions RevSmvExpr.mfmod_correct.
Print Assumptions RevSmvExpr.tri_sound.
Print Assumptions RevSmvExpr.trb_sound.
Print Assumptions RevSmvExpr.naive_division_is_wrong.
(* the checker's aliasing decision *)
Print Assumptions RevSmvAlias.aoccurs_rn.
Print Assumptions RevSmvAlias.alias_three_ways.
Print Assumptions RevSmvAlias.step_alias_ok.
Print Assumptions RevSmvAlias.alias_flagged_no_step.
Print Assumptions RevSmvAlias.alias_check_is_exact.
Print Assumptions RevSmvAlias.swap_alias_iff.
(* the checker's large-block encoding *)
Print Assumptions RevSmvBlock.seval_subst.
Print Assumptions RevSmvBlock.guard_at_entry.
Print Assumptions RevSmvBlock.block_sound.
Print Assumptions RevSmvBlock.block_from_entry.
Print Assumptions RevSmvBlock.block_is_functional.
Print Assumptions RevSmvBlock.the_unchecked_swap_models_a_run_the_source_has_not.
Print Assumptions RevSmvBlock.sx_flagged_iff.
Print Assumptions RevSmvBlock.sx_flagged_alias.
Print Assumptions RevSmvBlock.sx_refused_iff.
Print Assumptions RevSmvBlock.swap_is_never_refused.
Print Assumptions RevSmvBlock.accumulated_block_is_alias_free.
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

OUT="$("$ROCQ" compile -Q . "" "$AUDIT" 2>&1 || true)"
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
