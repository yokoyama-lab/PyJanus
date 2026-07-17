(** * RevLevel1.v — Level-1 reversibility for the extracted array interpreter.

    Combines [RevExtractAr.run_sound] (a successful [run] is a genuine [exec]
    derivation) with [RevArr.exec_injective] (a final store determines the
    initial store) into the single reusable corollary

      [run_injective : run f1 Γ s a = Some b -> run f2 Γ s a' = Some b -> a = a'.]

    Any program that the verified extracted interpreter runs successfully is
    therefore injective on stores — "reversible by construction" as a
    machine-checked theorem about the *lowered form* itself, rather than a
    property trusted of the surface language implementation.  Downstream
    projects instantiate this per lowered program (e.g. yokoyama-lab/RevLZ's
    handbook codecs, whose lowered stmt terms are emitted by the differential
    harness's translator). *)

From Stdlib Require Import ZArith.
Require Import RevArr RevExtractAr.

Theorem run_injective : forall f1 f2 Γ s a a' b,
  run f1 Γ s a = Some b -> run f2 Γ s a' = Some b -> a = a'.
Proof.
  intros f1 f2 Γ s a a' b H1 H2.
  eapply exec_injective; eapply run_sound; eauto.
Qed.

(* the mirror corollary: one initial store cannot reach two final stores *)
Theorem run_deterministic : forall f1 f2 Γ s a b b',
  run f1 Γ s a = Some b -> run f2 Γ s a = Some b' -> b = b'.
Proof.
  intros f1 f2 Γ s a b b' H1 H2.
  eapply exec_det; eapply run_sound; eauto.
Qed.
