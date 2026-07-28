(** * RevFix.v — procedure meanings as a least fixed point (denotation closed)

    [RevDenote.v] gives a compositional denotation [denote D s], but its header
    concedes one gap: "the denotation cannot recurse into the environment, so
    the procedure meanings are a parameter".  [adequacy] is therefore stated for
    [D := Dexec], the *operational* meaning of each procedure — the denotational
    semantics still borrows recursion from [exec].

    Paolini--Piccolo--Roversi's Matita development (TYPES 2015,
    doi:10.4230/LIPIcs.TYPES.2015.7) does not: there the meaning of a program is
    [den_program = fix (...)], the Knaster--Tarski least fixed point of the
    environment functional in a CPO of [Pinj] morphisms, and the two directions
    against the (fuel-indexed) operational semantics are proved separately as
    [den_stm_correct] and [den_stm_complete].

    This file closes that gap for the framework.  For a fixed environment [Γ]:

      - [step E p := denote E (Γ p)]  — the environment functional;
      - [approx n]                    — its Kleene chain from the empty
                                        environment [botenv];
      - [Dfix p a b := exists n, approx n p a b]  — the least fixed point.

    Proved (all axiom-free):

      - [Dfix_fixed]     : [Dfix] *is* a fixed point of [step];
      - [Dfix_least]     : it is below every pre-fixed point (Knaster--Tarski);
      - [fix_adequacy]   : [denote Dfix s = exec Γ s] — adequacy with **no**
                           operational input in the denotation.  The two
                           inclusions are [exec_approx] (Matita's
                           [den_stm_correct]: every operational run is realized
                           at some finite approximant) and [approx_exec]
                           (its [den_stm_complete]);
      - [exec_is_lfp]    : hence [exec Γ] itself *is* the least fixed point of
                           the denotational functional;
      - [Dfix_reversible]/[denote_fix_reversible] : reversibility of recursive
                           procedures proved **purely denotationally** — each
                           approximant is a partial injection and the chain is
                           increasing, so its union is one (this is what the
                           Matita model gets from the CPO structure of [Pinj]).
                           [RevDenote.denote_reversible] needed
                           [forall p, reversible (D p)] as a hypothesis,
                           dischargeable before only via [exec].

    Everything is a union over a chain of relations — relations under inclusion
    form a complete lattice, so no domain theory is needed.

    **Prior work.**  Getting reversible recursion from *joins* is the established
    route: Axelsen and Kaarsgaard model it in **join inverse categories**
    (FoSSaCS 2016, doi:10.1007/978-3-662-49630-5_5; JLAMP 87, 2017,
    doi:10.1016/j.jlamp.2016.08.003), where the fixed point of a functional is
    the join of its finite approximants.  The union of the Kleene chain here is
    that join, taken concretely in the lattice of relations; so this file is a
    machine-checked instance of that construction rather than a new one.  See
    docs/reversible-categorical-semantics.md. *)

From Stdlib Require Import Bool Arith.
Require Import RevCore RevAlgebra RevDenote.

Module DenoteFix (P : REV_PRIM).
Module D := Denote P.
Import P.
Module L := D.L.

(** Inclusion of procedure environments — the order of the lattice. *)
Definition dle (E1 E2 : D.denv) : Prop := forall p a b, E1 p a b -> E2 p a b.

Lemma dle_refl : forall E, dle E E.
Proof. intros E p a b H; exact H. Qed.

(** The denotation is monotone in the environment.  ([conv] is monotone too, so
    [Uncall] is no obstacle.) *)
Lemma denote_mono : forall E1 E2, dle E1 E2 ->
  forall s a b, D.denote E1 s a b -> D.denote E2 s a b.
Proof.
  intros E1 E2 H s; induction s; intros a b; simpl.
  - (* Skip *) trivial.
  - (* Prim *) trivial.
  - (* Seq *) intros [m [H1 H2]]; exists m; split; [ apply IHs1 | apply IHs2 ]; assumption.
  - (* If *)
    intros [[Hg [Hd Hg2]]|[Hg [Hd Hg2]]];
      [ left;  split; [ exact Hg | split; [ apply IHs1; exact Hd | exact Hg2 ] ]
      | right; split; [ exact Hg | split; [ apply IHs2; exact Hd | exact Hg2 ] ] ].
  - (* Loop *)
    intros [Hg Hl]; split; [ exact Hg | ].
    eapply D.lpR_mono; [ apply IHs1 | apply IHs2 | exact Hl ].
  - (* Call *) apply H.
  - (* Uncall *) unfold conv; apply H.
Qed.

(* ===================================================================== *)
(** ** The Kleene chain of the environment functional. *)
Section WithEnv.
Variable Γ : L.pname -> L.stmt.

Definition botenv : D.denv := fun _ _ _ => False.

(** The environment functional: a procedure means the denotation of its body. *)
Definition step (E : D.denv) : D.denv := fun p => D.denote E (Γ p).

Fixpoint approx (n : nat) : D.denv :=
  match n with O => botenv | S k => step (approx k) end.

(** The least fixed point: the union of the chain. *)
Definition Dfix : D.denv := fun p a b => exists n, approx n p a b.

Lemma approx_step : forall n, dle (approx n) (approx (S n)).
Proof.
  induction n.
  - intros p a b [].
  - intros p a b Hb; unfold approx in *; fold approx in *; unfold step in *.
    eapply denote_mono; [ exact IHn | exact Hb ].
Qed.

Lemma approx_le : forall n m, n <= m -> dle (approx n) (approx m).
Proof.
  intros n m H; induction H.
  - apply dle_refl.
  - intros p a b Hb; apply approx_step; apply IHle; exact Hb.
Qed.

Lemma denote_approx_le : forall n m, n <= m ->
  forall s a b, D.denote (approx n) s a b -> D.denote (approx m) s a b.
Proof.
  intros n m H s a b Hb; eapply denote_mono; [ apply approx_le; exact H | exact Hb ].
Qed.

Lemma approx_Dfix : forall n, dle (approx n) Dfix.
Proof. intros n p a b Hb; exists n; exact Hb. Qed.

(* ===================================================================== *)
(** ** Correctness: every operational run is realized at a finite approximant.

    Matita's [den_stm_correct].  The fuel there is explicit in the operational
    semantics; here it is the *index of the approximant*, extracted from the
    derivation.  [Seq]/[If]/[Loop] take the max of the sub-bounds; [Call] and
    [Uncall] consume exactly one level. *)
Lemma exec_approx : forall s a b,
  L.exec Γ s a b -> exists n, D.denote (approx n) s a b.
Proof.
  intros s a b H.
  induction H using L.exec_mut
    with (P0 := fun g1 s1 s2 g2 a b (_ : L.lp Γ g1 s1 s2 g2 a b) =>
      exists n, lpR (gtest g1) (D.denote (approx n) s1)
                    (D.denote (approx n) s2) (gtest g2) a b).
  - (* E_Skip *) exists 0; reflexivity.
  - (* E_Prim *) exists 0; exact p0.
  - (* E_Seq *)
    destruct IHexec1 as [n1 H1]; destruct IHexec2 as [n2 H2].
    exists (Nat.max n1 n2); exists m; split.
    + eapply denote_approx_le; [ apply Nat.le_max_l | exact H1 ].
    + eapply denote_approx_le; [ apply Nat.le_max_r | exact H2 ].
  - (* E_IfT *) destruct IHexec as [n Hn]; exists n; left; auto.
  - (* E_IfF *) destruct IHexec as [n Hn]; exists n; right; auto.
  - (* E_Loop *) destruct IHexec as [n Hn]; exists n; split; [ exact e | exact Hn ].
  - (* E_Call *) destruct IHexec as [n Hn]; exists (S n); exact Hn.
  - (* E_Uncall *)
    destruct IHexec as [n Hn]; exists (S n).
    apply (proj1 (D.denote_invert (approx n) (Γ p) a b)); exact Hn.
  - (* L_one *) destruct IHexec as [n Hn]; exists n; apply lp_one; assumption.
  - (* L_more *)
    destruct IHexec1 as [n1 H1]; destruct IHexec2 as [n2 H2].
    destruct IHexec3 as [n3 H3].
    exists (Nat.max n1 (Nat.max n2 n3)); eapply lp_more.
    + eapply denote_approx_le; [ apply Nat.le_max_l | exact H1 ].
    + exact e.
    + eapply denote_approx_le;
        [ eapply Nat.le_trans; [ apply Nat.le_max_l | apply Nat.le_max_r ] | exact H2 ].
    + exact e0.
    + eapply D.lpR_mono; [ | | exact H3 ];
        intros x y Hxy; eapply denote_approx_le;
        [ eapply Nat.le_trans; [ apply Nat.le_max_r | apply Nat.le_max_r ]
        | exact Hxy
        | eapply Nat.le_trans; [ apply Nat.le_max_r | apply Nat.le_max_r ]
        | exact Hxy ].
Qed.

(* ===================================================================== *)
(** ** Completeness: no approximant invents behaviour.  Matita's
    [den_stm_complete] (there: the denotation is below the *least* pre-fixed
    point, which the operational semantics is shown to be). *)
Lemma approx_exec : forall n, dle (approx n) (D.Dexec Γ).
Proof.
  induction n.
  - intros p a b [].
  - intros p a b Hb; unfold approx in Hb; fold approx in Hb; unfold step in Hb.
    unfold D.Dexec; apply (proj1 (D.adequacy Γ (Γ p) a b)).
    eapply denote_mono; [ exact IHn | exact Hb ].
Qed.

Lemma Dfix_Dexec : forall p a b, Dfix p a b <-> D.Dexec Γ p a b.
Proof.
  intros p a b; split.
  - intros [n Hn]; eapply approx_exec; exact Hn.
  - intro H; destruct (exec_approx (Γ p) a b H) as [n Hn]; exists (S n); exact Hn.
Qed.

(** Adequacy for the *closed* denotation: no [exec] occurs in [Dfix]. *)
Theorem fix_adequacy : forall s a b, D.denote Dfix s a b <-> L.exec Γ s a b.
Proof.
  intros s a b; split; intro H.
  - apply (proj1 (D.adequacy Γ s a b)).
    eapply denote_mono; [ | exact H ].
    intros p x y Hx; apply (proj1 (Dfix_Dexec p x y)); exact Hx.
  - apply (proj2 (D.adequacy Γ s a b)) in H.
    eapply denote_mono; [ | exact H ].
    intros p x y Hx; apply (proj2 (Dfix_Dexec p x y)); exact Hx.
Qed.

(* ===================================================================== *)
(** ** Knaster--Tarski: [Dfix] is the least fixed point. *)

Theorem Dfix_fixed : forall p a b, Dfix p a b <-> step Dfix p a b.
Proof.
  intros p a b; unfold step; split; intro H.
  - apply (proj2 (fix_adequacy (Γ p) a b)).
    apply (proj1 (Dfix_Dexec p a b)); exact H.
  - apply (proj2 (Dfix_Dexec p a b)).
    apply (proj1 (fix_adequacy (Γ p) a b)); exact H.
Qed.

Lemma approx_below : forall E, dle (step E) E -> forall n, dle (approx n) E.
Proof.
  intros E Hpre; induction n.
  - intros p a b [].
  - intros p a b Hb; apply Hpre; unfold step.
    eapply denote_mono; [ exact IHn | exact Hb ].
Qed.

Theorem Dfix_least : forall E, dle (step E) E -> dle Dfix E.
Proof. intros E Hpre p a b [n Hn]; eapply approx_below; eauto. Qed.

(** Hence the operational semantics *is* the least fixed point of the
    denotational environment functional — the framework-level counterpart of
    Paolini--Piccolo--Roversi's correctness + completeness pair. *)
Corollary exec_is_lfp :
  (forall p a b, D.Dexec Γ p a b <-> step (D.Dexec Γ) p a b)
  /\ (forall E, dle (step E) E -> dle (D.Dexec Γ) E).
Proof.
  split.
  - intros p a b; unfold step, D.Dexec; symmetry; apply (D.adequacy Γ (Γ p) a b).
  - intros E Hpre p a b H.
    apply Dfix_least; [ exact Hpre | apply (proj2 (Dfix_Dexec p a b)); exact H ].
Qed.

(* ===================================================================== *)
(** ** Reversibility, purely denotationally.

    Each approximant is a partial injection (by the closure lemmas of
    [RevAlgebra], with [botenv] trivially one), and the chain is increasing —
    so its union is a partial injection.  That last step is the content of the
    Matita model's CPO of [Pinj] morphisms; over relations it is two lines. *)

Lemma botenv_reversible : forall p, reversible (botenv p).
Proof. intro p; split; intros a b b' [] _. Qed.

Lemma approx_reversible : forall n p, reversible (approx n p).
Proof.
  induction n; intro p.
  - apply botenv_reversible.
  - unfold approx; fold approx; unfold step.
    apply D.denote_reversible; exact IHn.
Qed.

Lemma Dfix_reversible : forall p, reversible (Dfix p).
Proof.
  intro p; split.
  - intros a b b' [n Hn] [m Hm].
    destruct (approx_reversible (Nat.max n m) p) as [Hd _].
    eapply Hd.
    + eapply approx_le; [ apply Nat.le_max_l | exact Hn ].
    + eapply approx_le; [ apply Nat.le_max_r | exact Hm ].
  - intros a b b' Hb Hb'; unfold conv in Hb, Hb'.
    destruct Hb as [n Hn]; destruct Hb' as [m Hm].
    destruct (approx_reversible (Nat.max n m) p) as [_ Hc]; unfold conv, det in Hc.
    eapply Hc.
    + eapply approx_le; [ apply Nat.le_max_l | exact Hn ].
    + eapply approx_le; [ apply Nat.le_max_r | exact Hm ].
Qed.

(** The headline: every program is reversible under the *closed* denotation,
    with no appeal to [exec_injective] and no hypothesis on the environment. *)
Theorem denote_fix_reversible : forall s, reversible (D.denote Dfix s).
Proof. intro s; apply D.denote_reversible; apply Dfix_reversible. Qed.

Corollary denote_fix_injective : forall s a a' b,
  D.denote Dfix s a b -> D.denote Dfix s a' b -> a = a'.
Proof.
  intros s a a' b H1 H2.
  destruct (denote_fix_reversible s) as [_ Hc]; unfold conv, det in Hc.
  eapply Hc; eassumption.
Qed.

(** The inverter is still the converse under the closed denotation. *)
Corollary denote_fix_invert : forall s a b,
  D.denote Dfix (L.invert s) a b <-> conv (D.denote Dfix s) a b.
Proof. intros; apply D.denote_invert. Qed.

End WithEnv.

(* ===================================================================== *)
(** ** Sanity: the fixed point really is the *least* one.

    A procedure whose body is just a call to itself denotes the empty relation.
    A greatest fixed point would let it denote anything. *)
Example fix_diverges : forall Γ,
  (forall p, Γ p = L.Call p) -> forall p a b, ~ Dfix Γ p a b.
Proof.
  intros Γ Hd p a b [n Hn]; revert p a b Hn.
  induction n; intros p a b Hn.
  - exact Hn.
  - unfold approx in Hn; fold approx in Hn; unfold step in Hn.
    rewrite Hd in Hn; simpl in Hn; eapply IHn; exact Hn.
Qed.

End DenoteFix.
