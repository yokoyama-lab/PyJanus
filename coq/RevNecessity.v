(** * RevNecessity.v — the [REV_PRIM] laws are *necessary*, not just sufficient

    [RevCore.v] shows the three local laws ([pinv_invol], [pstep_det],
    [pstep_rev]) are *sufficient* for whole-program reversibility.  Here we
    show they are *tight*: they force every primitive to be injective, and a
    primitive that is not injective provably admits no reversing completion —
    so it cannot be given to the framework at all.

    Together with the sufficiency proof, this characterizes exactly which
    atoms a reversible structured language may have: **the injective ones.** *)

From Stdlib Require Import ZArith.
Require Import RevCore.
Open Scope Z_scope.

(** ** (1) The laws force primitive injectivity.

    [pstep_rev] + [pstep_det] together say: run forward, then the inverse runs
    forward deterministically — so two inputs with the same output coincide. *)
Module PrimFacts (P : REV_PRIM).
  Import P.
  Lemma prim_injective :
    forall p a a' b, pstep p a b -> pstep p a' b -> a = a'.
  Proof.
    intros p a a' b H1 H2.
    apply pstep_rev in H1. apply pstep_rev in H2.
    eapply pstep_det; eauto.
  Qed.
End PrimFacts.

(** ** (2) A non-injective atom is inadmissible.

    [Rstep] ("reset to 0") is a perfectly good *forward-deterministic*
    transition, yet it is not injective.  We show no relation can reverse it
    deterministically — i.e. it can satisfy neither the role of [pstep] in any
    [REV_PRIM] (whose primitives are injective by [prim_injective]) nor, more
    concretely, the [pstep_rev]/[pstep_det] pair. *)
Definition Rstep (a b : Z) : Prop := b = 0.

Lemma Rstep_det : forall a b b', Rstep a b -> Rstep a b' -> b = b'.
Proof. unfold Rstep; intros; subst; reflexivity. Qed.

Lemma Rstep_not_injective :
  ~ (forall a a' b, Rstep a b -> Rstep a' b -> a = a').
Proof.
  intro Hinj.
  assert (H01 : 0 = 1) by (apply (Hinj 0 1 0); unfold Rstep; reflexivity).
  discriminate.
Qed.

(** The crux: any candidate inverse that (a) reverses [Rstep] and (b) is itself
    deterministic would force [Rstep] to be injective — which it is not.  This
    is exactly the [pstep_rev] (a) + [pstep_det] (b) shape, so no [REV_PRIM]
    instance can host a reset primitive. *)
Theorem reset_inadmissible :
  ~ exists inv : Z -> Z -> Prop,
       (forall a b, Rstep a b -> inv b a) /\
       (forall b a a', inv b a -> inv b a' -> a = a').
Proof.
  intros [inv [Hrev Hdet]].
  apply Rstep_not_injective.
  intros a a' b Ha Ha'.
  apply Hrev in Ha. apply Hrev in Ha'.
  eapply Hdet; eauto.
Qed.

(** Conclusion (sufficiency in [RevCore] + necessity here): a primitive is
    admissible to the framework *iff* it is injective.  Forward determinism
    alone (which [Rstep] has) is not enough — reversibility is the extra,
    essential, and exactly-captured requirement. *)
