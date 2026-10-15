(** * RevNecessity.v — the [REV_PRIM] laws are *necessary*, not just sufficient

    [RevCore.v] shows the three local laws ([pinv_invol], [pstep_det],
    [pstep_rev]) are *sufficient* for whole-program reversibility.  Here we
    show they are *tight*: they force every primitive to be injective, and a
    primitive that is not injective provably admits no reversing completion —
    so it cannot be given to the framework at all.

    Section (3) proves the converse: every deterministic, injective atom family
    can be completed to primitives satisfying the three laws
    ([admissible_iff_injective], and the [REV_PRIM] instance [Complete]).
    Together with the sufficiency proof, this characterizes exactly which
    forward-deterministic atoms a reversible structured language may have:
    **the injective ones.** *)

From Stdlib Require Import ZArith Lia.
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

(** ** (3) Every deterministic, injective atom is admissible (the converse).

    [admissible R] says: the atom family [R] can be hosted by primitives that
    satisfy exactly the three [REV_PRIM] laws, i.e. there is a primitive type
    with an involutive [pinv], a deterministic and reversing [pstep], and an
    embedding of the atoms whose step is [R].  The converse direction adjoins a
    formal inverse to every atom: primitives are [atom * bool], the [false]
    copy runs [R] backwards, and [pinv] flips the flag.  Determinism of the
    backward copy is exactly injectivity of [R].  So, among forward-
    deterministic atoms, admissibility is equivalent to injectivity. *)
Section Admissible.
  Context {state atom : Type}.

  Definition admissible (R : atom -> state -> state -> Prop) : Prop :=
    exists (prim : Type) (emb : atom -> prim)
           (pstep : prim -> state -> state -> Prop) (pinv : prim -> prim),
      (forall p, pinv (pinv p) = p) /\
      (forall p a b b', pstep p a b -> pstep p a b' -> b = b') /\
      (forall p a b, pstep p a b -> pstep (pinv p) b a) /\
      (forall x a b, pstep (emb x) a b <-> R x a b).

  Definition atom_det (R : atom -> state -> state -> Prop) : Prop :=
    forall x a b b', R x a b -> R x a b' -> b = b'.
  Definition atom_inj (R : atom -> state -> state -> Prop) : Prop :=
    forall x a a' b, R x a b -> R x a' b -> a = a'.

  (** The completion: each atom together with its formal inverse. *)
  Definition cstep (R : atom -> state -> state -> Prop)
             (p : atom * bool) (a b : state) : Prop :=
    if snd p then R (fst p) a b else R (fst p) b a.
  Definition cinv (p : atom * bool) : atom * bool := (fst p, negb (snd p)).

  Theorem admissible_iff_injective :
    forall R, admissible R <-> (atom_det R /\ atom_inj R).
  Proof.
    intro R; split.
    - intros (prim & emb & pstep & pinv & Hinv & Hdet & Hrev & Hemb). split.
      + intros x a b b' H1 H2. apply Hemb in H1, H2. eapply Hdet; eauto.
      + intros x a a' b H1 H2. apply Hemb in H1, H2.
        apply Hrev in H1, H2. eapply Hdet; eauto.
    - intros [Hdet Hinj].
      exists (atom * bool)%type, (fun x => (x, true)), (cstep R), cinv.
      repeat split.
      + intros [x d]. unfold cinv; simpl. rewrite Bool.negb_involutive. reflexivity.
      + intros [x []] a b b'; unfold cstep; simpl; intros H1 H2.
        * eapply Hdet; eauto.
        * eapply Hinj; eauto.
      + intros [x []] a b; unfold cstep, cinv; simpl; auto.
      + auto.
      + auto.
  Qed.
End Admissible.

(** The same completion as a [REV_PRIM] instance, so that [RevLang] can be
    applied to it directly: any deterministic, injective atom family yields a
    reversible structured language whose [Prim (x, true)] runs atom [x]. *)
Module Type ATOMS.
  Parameter state : Type.
  Parameter atom  : Type.
  Parameter guard : Type.
  Parameter gtest : guard -> state -> bool.
  Parameter astep : atom -> state -> state -> Prop.
  Axiom astep_det : forall x a b b', astep x a b -> astep x a b' -> b = b'.
  Axiom astep_inj : forall x a a' b, astep x a b -> astep x a' b -> a = a'.
End ATOMS.

Module Complete (A : ATOMS) <: REV_PRIM.
  Definition state := A.state.
  Definition prim  := (A.atom * bool)%type.
  Definition guard := A.guard.
  Definition gtest := A.gtest.
  Definition pstep : prim -> state -> state -> Prop := cstep A.astep.
  Definition pinv  : prim -> prim := cinv.
  Lemma pinv_invol : forall p, pinv (pinv p) = p.
  Proof. intros [x d]. unfold pinv, cinv; simpl. rewrite Bool.negb_involutive. reflexivity. Qed.
  Lemma pstep_det : forall p a b b', pstep p a b -> pstep p a b' -> b = b'.
  Proof.
    intros [x []] a b b'; unfold pstep, cstep; simpl; intros H1 H2.
    - eapply A.astep_det; eauto.
    - eapply A.astep_inj; eauto.
  Qed.
  Lemma pstep_rev : forall p a b, pstep p a b -> pstep (pinv p) b a.
  Proof. intros [x []] a b; unfold pstep, cstep, pinv, cinv; simpl; auto. Qed.
  Lemma pstep_emb : forall x a b, pstep (x, true) a b <-> A.astep x a b.
  Proof. reflexivity. Qed.
End Complete.

(** Tests: an injective increment is admissible, the reset atom is not. *)
Example incr_admissible :
  admissible (fun (_ : unit) (a b : Z) => b = a + 1).
Proof.
  apply admissible_iff_injective. split.
  - intros _ a b b' H1 H2. subst. reflexivity.
  - intros _ a a' b H1 H2. lia.
Qed.

Example reset_not_admissible :
  ~ admissible (fun (_ : unit) (a b : Z) => b = 0).
Proof.
  rewrite admissible_iff_injective. intros [_ Hinj].
  assert (H : (0 : Z) = 1) by (apply (Hinj tt 0 1 0); reflexivity).
  discriminate.
Qed.

(** Conclusion (sufficiency in [RevCore], [prim_injective] in (1), the converse
    [admissible_iff_injective] in (3)): a forward-deterministic atom is
    admissible to the framework *iff* it is injective.  Forward determinism
    alone (which [Rstep] has) is not enough. *)
