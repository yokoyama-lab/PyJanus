(** * RevAlgebra.v — reversibility as an algebra of relations (combinators open)

    [RevCore.v] fixes the control-flow constructors (Seq/If/Loop/Call) and proves
    the whole language reversible.  Here we go one level further and make the
    *combinators themselves* abstract: a program denotes a relation on an
    abstract [state], a relation is [reversible] when it is a partial injection
    (deterministic forwards and backwards), and each control-flow construct is a
    relational *combinator* whose reversibility is a **closure theorem**:

      reversible R -> reversible S -> reversible (R `combinator` S),

    with the inverse computed as the relational converse [conv].  The class of
    admissible combinators is *open*: a new one needs only its own closure lemma,
    proved against the same interface — no fixed syntax to extend.  We give

      - the basic combinators: [idR] (skip), [compR] (seq), [conv] (uncall);
      - [ifR] — assertion-guarded choice;
      - [loopR] — the Janus loop (from/do/loop/until);
      - [iterR] — bounded repetition, a combinator *not* present in [RevCore]'s
        syntax, shown reversible in three lines (openness demo);

    and finally [Connect], which exhibits [RevCore]'s [exec] constructors as
    exactly these combinators — so the fixed syntax is just one choice. *)

From Stdlib Require Import Bool.
Require Import RevCore.

(* ===================================================================== *)
(** ** The relational algebra over an abstract state. *)
Section Algebra.
Context {state : Type}.

Definition rel := state -> state -> Prop.
Definition det (R : rel) : Prop := forall a b b', R a b -> R a b' -> b = b'.
Definition conv (R : rel) : rel := fun a b => R b a.

(** Reversible = partial injection: deterministic forwards *and* backwards. *)
Definition reversible (R : rel) : Prop := det R /\ det (conv R).

Lemma rev_conv : forall R, reversible R -> reversible (conv R).
Proof. intros R [H1 H2]; split; [ exact H2 | exact H1 ]. Qed.

(** *** Skip. *)
Definition idR : rel := fun a b => a = b.
Lemma rev_id : reversible idR.
Proof. split; intros a b b' H1 H2; unfold idR, conv in *; congruence. Qed.

(** *** Sequential composition. *)
Definition compR (R S : rel) : rel := fun a c => exists b, R a b /\ S b c.

Lemma conv_comp : forall R S a b,
  conv (compR R S) a b <-> compR (conv S) (conv R) a b.
Proof.
  intros R S a b; unfold conv, compR; split; intros [m [H1 H2]]; exists m; tauto.
Qed.

Lemma rev_comp : forall R S, reversible R -> reversible S -> reversible (compR R S).
Proof.
  intros R S [dR cR] [dS cS]; split.
  - intros a c c' [b [Hab Hbc]] [b' [Hab' Hbc']].
    assert (b = b') by (eapply dR; eauto). subst. eapply dS; eauto.
  - intros a c c' [b [Hcb Hba]] [b' [Hcb' Hba']].
    assert (b = b') by (eapply cS; eauto). subst. eapply cR; eauto.
Qed.

(** *** Assertion-guarded choice  [if g1 then R else S fi g2].
    The *exit* assertion [g2] is what makes the converse deterministic: it
    records which branch ran. *)
Definition ifR (g1 : state -> bool) (R S : rel) (g2 : state -> bool) : rel :=
  fun a b => (g1 a = true  /\ R a b /\ g2 b = true)
          \/ (g1 a = false /\ S a b /\ g2 b = false).

Lemma conv_if : forall g1 R S g2 a b,
  conv (ifR g1 R S g2) a b <-> ifR g2 (conv R) (conv S) g1 a b.
Proof. intros; unfold conv, ifR; tauto. Qed.

Lemma rev_if : forall g1 R S g2,
  reversible R -> reversible S -> reversible (ifR g1 R S g2).
Proof.
  intros g1 R S g2 [dR cR] [dS cS]; split.
  - intros a b b' H1 H2; unfold ifR in *.
    destruct H1 as [[? [? ?]]|[? [? ?]]]; destruct H2 as [[? [? ?]]|[? [? ?]]];
      try congruence; [ eapply dR; eauto | eapply dS; eauto ].
  - intros a b b' H1 H2; unfold ifR, conv in *.
    destruct H1 as [[? [? ?]]|[? [? ?]]]; destruct H2 as [[? [? ?]]|[? [? ?]]];
      try congruence; [ eapply cR; eauto | eapply cS; eauto ].
Qed.

(** *** Bounded repetition — a combinator NOT in RevCore's syntax.
    Reversible purely by the closure lemmas: openness in three lines. *)
Fixpoint iterR (n : nat) (R : rel) : rel :=
  match n with O => idR | S k => compR R (iterR k R) end.

Lemma rev_iter : forall n R, reversible R -> reversible (iterR n R).
Proof.
  induction n; intros R H; simpl; [ apply rev_id | apply rev_comp; [ exact H | apply IHn, H ] ].
Qed.

(** *** The Janus loop  [from g1 do R loop S until g2].
    [lpR] is the loop body  R (S R)^n ;  [loopR] adds the entry assertion. *)
Inductive lpR (g1 : state -> bool) (R S : rel) (g2 : state -> bool) : rel :=
| lp_one  : forall a b, R a b -> g2 b = true -> lpR g1 R S g2 a b
| lp_more : forall a a1 a2 b,
    R a a1 -> g2 a1 = false -> S a1 a2 -> g1 a2 = false ->
    lpR g1 R S g2 a2 b -> lpR g1 R S g2 a b.

Definition loopR (g1 : state -> bool) (R S : rel) (g2 : state -> bool) : rel :=
  fun a b => g1 a = true /\ lpR g1 R S g2 a b.

Lemma lpR_exit : forall g1 R S g2 a b, lpR g1 R S g2 a b -> g2 b = true.
Proof. intros until b; intro H; induction H; assumption. Qed.

(** Open iteration of continuing rounds, for the reversal argument. *)
Inductive itero (g1 : state -> bool) (R S : rel) (g2 : state -> bool) : rel :=
| io_nil  : forall a, itero g1 R S g2 a a
| io_cons : forall a a1 a2 b,
    R a a1 -> g2 a1 = false -> S a1 a2 -> g1 a2 = false ->
    itero g1 R S g2 a2 b -> itero g1 R S g2 a b.

Lemma itero_snoc : forall g1 R S g2 a m m1 m2,
  itero g1 R S g2 a m -> R m m1 -> g2 m1 = false -> S m1 m2 -> g1 m2 = false ->
  itero g1 R S g2 a m2.
Proof.
  intros g1 R S g2 a m m1 m2 H. revert m1 m2.
  induction H; intros m1 m2 Hr He Hs Hg.
  - eapply io_cons; eauto. apply io_nil.
  - eapply io_cons; eauto.
Qed.

Lemma itero_to_lpR : forall g1 R S g2 a m b,
  itero g1 R S g2 a m -> R m b -> g2 b = true -> lpR g1 R S g2 a b.
Proof.
  intros g1 R S g2 a m b H. induction H; intros Hr Hg.
  - apply lp_one; assumption.
  - eapply lp_more; eauto.
Qed.

(** Loop reversal: the converse of a loop is the loop of the converses, with
    entry/exit assertions swapped.  Mirrors [RevCore.exec_rev]'s loop case. *)
Lemma lpR_rev : forall g1 R S g2 a b,
  lpR g1 R S g2 a b ->
  exists q, itero g2 (conv R) (conv S) g1 b q /\ conv R q a.
Proof.
  intros g1 R S g2 a b H. induction H.
  - exists b. split; [ apply io_nil | exact H ].
  - destruct IHlpR as [q [Hit Hq]].
    exists a1. split.
    + eapply itero_snoc; [ exact Hit | exact Hq | exact H2 | exact H1 | exact H0 ].
    + exact H.
Qed.

Lemma loopR_rev : forall g1 R S g2 a b,
  loopR g1 R S g2 a b -> loopR g2 (conv R) (conv S) g1 b a.
Proof.
  intros g1 R S g2 a b [Hg1 Hlp]. split.
  - eapply lpR_exit; eauto.
  - destruct (lpR_rev _ _ _ _ _ _ Hlp) as [q [Hit Hq]].
    eapply itero_to_lpR; [ exact Hit | exact Hq | exact Hg1 ].
Qed.

Lemma conv_loop : forall g1 R S g2 a b,
  conv (loopR g1 R S g2) a b <-> loopR g2 (conv R) (conv S) g1 a b.
Proof.
  intros; split; intro H.
  - apply loopR_rev in H; exact H.
  - apply loopR_rev in H. exact H.
Qed.

(** Forward determinism of the loop body, given the parts are deterministic. *)
Lemma lpR_det : forall g1 R S g2, det R -> det S ->
  forall a b, lpR g1 R S g2 a b -> forall b', lpR g1 R S g2 a b' -> b = b'.
Proof.
  intros g1 R S g2 dR dS a b H. induction H; intros b' Hb'.
  - inversion Hb'; subst.
    + eapply dR; eauto.
    + match goal with
      | HR' : R a ?x, Hgf : g2 ?x = false |- _ =>
          assert (b = x) by (eapply dR; eauto); subst; congruence
      end.
  - inversion Hb'; subst.
    + assert (a1 = b') by (eapply dR; eauto). subst. congruence.
    + match goal with
      | Hrec : lpR g1 R S g2 ?x b' |- _ =>
        match goal with
        | HS' : S ?y x |- _ =>
            assert (a1 = y) by (eapply dR; eauto); subst;
            assert (a2 = x) by (eapply dS; eauto); subst;
            apply IHlpR; exact Hrec
        end
      end.
Qed.

Lemma det_loopR : forall g1 R S g2, det R -> det S -> det (loopR g1 R S g2).
Proof.
  intros g1 R S g2 dR dS a b b' [_ H1] [_ H2].
  eapply lpR_det; [ exact dR | exact dS | exact H1 | exact H2 ].
Qed.

Lemma rev_loop : forall g1 R S g2,
  reversible R -> reversible S -> reversible (loopR g1 R S g2).
Proof.
  intros g1 R S g2 [dR cR] [dS cS]; split.
  - apply det_loopR; assumption.
  - intros a b b' H1 H2.
    apply loopR_rev in H1. apply loopR_rev in H2.
    eapply det_loopR; [ exact cR | exact cS | exact H1 | exact H2 ].
Qed.

End Algebra.

(* ===================================================================== *)
(** ** Connection: RevCore's [exec] constructors ARE these combinators.

    So the fixed syntax of [RevLang] is just one selection from the open class:
    each constructor's denotation is a reversible combinator, and reversibility
    of whole programs is exactly closure of the algebra. *)
Module Connect (P : REV_PRIM).
Import P.
Module L := RevLang P.

Section WithEnv.
Variable Γ : L.pname -> L.stmt.
Notation den s := (L.exec Γ s).

(** Atoms are reversible — [pstep_det] is forward, [pstep_rev]+[pstep_det] is
    backward (= primitive injectivity). *)
Lemma reversible_prim : forall p, reversible (den (L.Prim p)).
Proof.
  intro p; split.
  - intros a b b' H1 H2; inversion H1; subst; inversion H2; subst.
    eapply pstep_det; eauto.
  - intros a b b' H1 H2; unfold conv in H1, H2;
      inversion H1; subst; inversion H2; subst.
    match goal with
    | Ha : pstep p b a, Hb : pstep p b' a |- _ =>
        apply pstep_rev in Ha; apply pstep_rev in Hb; eapply pstep_det; eauto
    end.
Qed.

(** [Seq] is [compR]. *)
Lemma exec_Seq : forall s1 s2 a b,
  den (L.Seq s1 s2) a b <-> compR (den s1) (den s2) a b.
Proof.
  intros; split.
  - intro H; inversion H; subst; eexists; eauto.
  - intros [m [H1 H2]]; eapply L.E_Seq; eauto.
Qed.

(** [If] is [ifR]. *)
Lemma exec_If : forall g1 s1 s2 g2 a b,
  den (L.If g1 s1 s2 g2) a b <-> ifR (gtest g1) (den s1) (den s2) (gtest g2) a b.
Proof.
  intros; split.
  - intro H; inversion H; subst; [ left | right ]; eauto.
  - intros [[H1 [H2 H3]]|[H1 [H2 H3]]]; [ apply L.E_IfT | apply L.E_IfF ]; assumption.
Qed.

(** [Loop] is [loopR]. *)
Lemma exec_lp : forall g1 s1 s2 g2 a b,
  L.lp Γ g1 s1 s2 g2 a b <-> lpR (gtest g1) (den s1) (den s2) (gtest g2) a b.
Proof.
  intros; split; intro H; induction H.
  - apply lp_one; assumption.
  - eapply lp_more; eauto.
  - apply L.L_one; assumption.
  - eapply L.L_more; eauto.
Qed.

Lemma exec_Loop : forall g1 s1 s2 g2 a b,
  den (L.Loop g1 s1 s2 g2) a b <-> loopR (gtest g1) (den s1) (den s2) (gtest g2) a b.
Proof.
  intros; split.
  - intro H; inversion H; subst; split; [ assumption | apply exec_lp; assumption ].
  - intros [Hg Hlp]; apply L.E_Loop; [ assumption | apply exec_lp; assumption ].
Qed.

End WithEnv.
End Connect.
