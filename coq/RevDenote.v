(** * RevDenote.v — a compositional denotational semantics, adequate to [exec]

    [RevAlgebra.v] shows each control construct *is* a reversible relational
    combinator, but its "denotation" of a statement is still the operational
    [exec] itself.  Here we close the last gap to the on-paper denotational
    accounts (and to Paolini--Piccolo--Roversi's full-abstraction result): a
    genuinely *compositional* denotation

        [denote D : stmt -> (state -> state -> Prop)]

    defined by structural recursion on the statement, interpreting each
    constructor by the matching combinator of the algebra ([idR], [compR],
    [ifR], [loopR], [conv]).  [D : pname -> rel] supplies the meaning of
    procedures (the denotation cannot recurse into the environment, so the
    procedure meanings are a parameter).

    We then prove, against the functor's own [exec] (one [RevLang P] instance,
    so the statement types coincide):

      - [adequacy]        : with [D] the operational meaning of each procedure,
                            [denote D s = exec Γ s] (as relations, pointwise);
      - [denote_invert]   : [denote D (invert s) = conv (denote D s)] — the
                            inverter computes the relational converse,
                            denotationally;
      - [denote_reversible]/[denote_injective] : a *second*, purely denotational
                            proof of reversibility, straight from the algebra's
                            closure lemmas — independent of [exec_injective];
      - [denote_cong]     : the denotation is a *congruence* (compositionality):
                            denotationally-equal procedure meanings can be
                            substituted anywhere;
      - [full_abstraction]: denotational equality coincides with observational
                            (input/output) equivalence.

    Adequacy + compositionality is the constructive content of full abstraction
    at the level of the language-independent framework.  The development is
    axiom-free. *)

From Stdlib Require Import Bool Setoid.
Require Import RevCore RevAlgebra RevSmallStep.

Module Denote (P : REV_PRIM).
Import P.
(* The language instance is taken from [RevSmallStep] rather than built afresh:
   applying the [RevLang] functor twice yields two *distinct* inductive types, so
   two files that each say [Module L := RevLang P] cannot even state that their
   semantics agree.  Chaining the instantiations makes [RevSemantics.v] possible.
   Nothing below changes -- [L] still denotes the same language. *)
Module SSx := RevSmallStep.SmallStep P.
Module L := SSx.L.

(* ===================================================================== *)
(** ** Congruence (extensionality) of the combinators in their relations. *)
Section Ext.
Context {st : Type}.

Lemma conv_ext : forall R R' : @rel st,
  (forall a b, R a b <-> R' a b) -> forall a b, conv R a b <-> conv R' a b.
Proof. intros R R' H a b; unfold conv; exact (H b a). Qed.

Lemma compR_ext : forall R R' S S' : @rel st,
  (forall a b, R a b <-> R' a b) -> (forall a b, S a b <-> S' a b) ->
  forall a b, compR R S a b <-> compR R' S' a b.
Proof.
  intros R R' S S' HR HS a b; unfold compR; split; intros [m [H1 H2]]; exists m; split.
  - apply (proj1 (HR a m)); exact H1.
  - apply (proj1 (HS m b)); exact H2.
  - apply (proj2 (HR a m)); exact H1.
  - apply (proj2 (HS m b)); exact H2.
Qed.

Lemma ifR_ext : forall (g1 g2 : st -> bool) (R R' S S' : @rel st),
  (forall a b, R a b <-> R' a b) -> (forall a b, S a b <-> S' a b) ->
  forall a b, ifR g1 R S g2 a b <-> ifR g1 R' S' g2 a b.
Proof.
  intros g1 g2 R R' S S' HR HS a b; unfold ifR; split;
    intros [[H1 [H2 H3]]|[H1 [H2 H3]]].
  - left;  split; [exact H1| split; [apply (proj1 (HR a b)); exact H2|exact H3]].
  - right; split; [exact H1| split; [apply (proj1 (HS a b)); exact H2|exact H3]].
  - left;  split; [exact H1| split; [apply (proj2 (HR a b)); exact H2|exact H3]].
  - right; split; [exact H1| split; [apply (proj2 (HS a b)); exact H2|exact H3]].
Qed.

Lemma lpR_mono : forall (g1 g2 : st -> bool) (R R' S S' : @rel st),
  (forall a b, R a b -> R' a b) -> (forall a b, S a b -> S' a b) ->
  forall a b, lpR g1 R S g2 a b -> lpR g1 R' S' g2 a b.
Proof.
  intros g1 g2 R R' S S' HR HS a b H; induction H.
  - apply lp_one; [ apply HR; assumption | assumption ].
  - eapply lp_more;
      [ apply HR; eassumption | assumption | apply HS; eassumption
      | assumption | assumption ].
Qed.

Lemma lpR_ext : forall (g1 g2 : st -> bool) (R R' S S' : @rel st),
  (forall a b, R a b <-> R' a b) -> (forall a b, S a b <-> S' a b) ->
  forall a b, lpR g1 R S g2 a b <-> lpR g1 R' S' g2 a b.
Proof.
  intros g1 g2 R R' S S' HR HS a b; split.
  - apply lpR_mono.
    + intros x y Hxy; apply (proj1 (HR x y)); exact Hxy.
    + intros x y Hxy; apply (proj1 (HS x y)); exact Hxy.
  - apply lpR_mono.
    + intros x y Hxy; apply (proj2 (HR x y)); exact Hxy.
    + intros x y Hxy; apply (proj2 (HS x y)); exact Hxy.
Qed.

Lemma loopR_ext : forall (g1 g2 : st -> bool) (R R' S S' : @rel st),
  (forall a b, R a b <-> R' a b) -> (forall a b, S a b <-> S' a b) ->
  forall a b, loopR g1 R S g2 a b <-> loopR g1 R' S' g2 a b.
Proof.
  intros g1 g2 R R' S S' HR HS a b; unfold loopR; split; intros [Hg Hl];
    (split; [ exact Hg | ]).
  - apply (proj1 (lpR_ext g1 g2 R R' S S' HR HS a b)); exact Hl.
  - apply (proj2 (lpR_ext g1 g2 R R' S S' HR HS a b)); exact Hl.
Qed.

End Ext.

(* ===================================================================== *)
(** ** The compositional denotation. *)

Definition denv := L.pname -> @rel state.

Fixpoint denote (D : denv) (s : L.stmt) : state -> state -> Prop :=
  match s with
  | L.Skip            => idR
  | L.Prim p          => pstep p
  | L.Seq s1 s2       => compR (denote D s1) (denote D s2)
  | L.If g1 s1 s2 g2  => ifR (gtest g1) (denote D s1) (denote D s2) (gtest g2)
  | L.Loop g1 s1 s2 g2=> loopR (gtest g1) (denote D s1) (denote D s2) (gtest g2)
  | L.Call p          => D p
  | L.Uncall p        => conv (D p)
  end.

(* --------------------------------------------------------------------- *)
(** ** The inverter is the relational converse, denotationally.  Independent of
    any procedure environment, so stated outside the [Γ] section. *)
Theorem denote_invert : forall D s a b,
  denote D (L.invert s) a b <-> conv (denote D s) a b.
Proof.
  intros D s; induction s; intros a b; simpl.
  - (* Skip *)   unfold conv, idR; split; intro H; symmetry; exact H.
  - (* Prim p *)
    unfold conv; split; intro H.
    + apply pstep_rev in H; rewrite pinv_invol in H; exact H.
    + apply pstep_rev in H; exact H.
  - (* Seq s1 s2 *)
    apply (iff_trans (compR_ext _ _ _ _ IHs2 IHs1 a b)
                     (iff_sym (conv_comp (denote D s1) (denote D s2) a b))).
  - (* If g1 s1 s2 g2 *)
    apply (iff_trans (ifR_ext _ _ _ _ _ _ IHs1 IHs2 a b)
                     (iff_sym (conv_if (gtest g1) (denote D s1) (denote D s2) (gtest g2) a b))).
  - (* Loop g1 s1 s2 g2 *)
    apply (iff_trans (loopR_ext _ _ _ _ _ _ IHs1 IHs2 a b)
                     (iff_sym (conv_loop (gtest g1) (denote D s1) (denote D s2) (gtest g2) a b))).
  - (* Call p *)   unfold conv; tauto.
  - (* Uncall p *) unfold conv; tauto.
Qed.

(* ===================================================================== *)
(** ** Operational comparison: a procedure environment [Γ]. *)
Section WithEnv.
Variable Γ : L.pname -> L.stmt.

(** The canonical procedure environment: each procedure denotes its own
    operational behaviour.  Adequacy is stated for this [D]. *)
Definition Dexec : denv := fun p => L.exec Γ (Γ p).

(** The loop body relation [lpR] over the operational meanings of [s1],[s2]
    coincides with the functor's own loop-body relation [lp].  Proved against
    [exec] directly (no [denote]), so inducting on the mutually-defined [lp]
    via [L.lp_mut] has no outer hypotheses to conflict with. *)
Lemma lp_lpR_exec : forall g1 s1 s2 g2 x y,
  lpR (gtest g1) (L.exec Γ s1) (L.exec Γ s2) (gtest g2) x y
  <-> L.lp Γ g1 s1 s2 g2 x y.
Proof.
  intros g1 s1 s2 g2 x y; split.
  - intro K; induction K.
    + apply L.L_one; assumption.
    + eapply L.L_more; eassumption.
  - intro K;
      induction K using L.lp_mut
        with (P := fun s a b (_ : L.exec Γ s a b) => True);
      try exact I.
    + apply lp_one; assumption.
    + eapply lp_more; eassumption.
Qed.

(* --------------------------------------------------------------------- *)
(** ** Adequacy: [denote Dexec] coincides with [exec Γ]. *)
Theorem adequacy : forall s a b, denote Dexec s a b <-> L.exec Γ s a b.
Proof.
  induction s; intros a b; simpl.
  - (* Skip *)
    split; [ intro H; red in H; subst; apply L.E_Skip
           | intro H; inversion H; subst; reflexivity ].
  - (* Prim p *)
    split; [ intro H; apply L.E_Prim; exact H
           | intro H; inversion H; subst; assumption ].
  - (* Seq s1 s2 *)
    split.
    + intros [m [H1 H2]];
        apply (proj1 (IHs1 _ _)) in H1; apply (proj1 (IHs2 _ _)) in H2;
        eapply L.E_Seq; eassumption.
    + intro H; inversion H; subst; eexists; split;
        [ apply (proj2 (IHs1 a _)); eassumption
        | apply (proj2 (IHs2 _ b)); eassumption ].
  - (* If g1 s1 s2 g2 *)
    split.
    + intros [[Hg1 [Hd Hg2]]|[Hg1 [Hd Hg2]]];
        [ apply L.E_IfT; [ exact Hg1 | apply (proj1 (IHs1 a b)); exact Hd | exact Hg2 ]
        | apply L.E_IfF; [ exact Hg1 | apply (proj1 (IHs2 a b)); exact Hd | exact Hg2 ] ].
    + intro H; inversion H; subst;
        [ left;  split; [ assumption | split; [ apply (proj2 (IHs1 a b)); assumption | assumption ] ]
        | right; split; [ assumption | split; [ apply (proj2 (IHs2 a b)); assumption | assumption ] ] ].
  - (* Loop g1 s1 s2 g2 *)
    assert (Hbridge : forall x y,
              lpR (gtest g1) (denote Dexec s1) (denote Dexec s2) (gtest g2) x y
              <-> lpR (gtest g1) (L.exec Γ s1) (L.exec Γ s2) (gtest g2) x y).
    { intros x y; apply lpR_ext; [ exact IHs1 | exact IHs2 ]. }
    split.
    + intros [Hg Hl]; apply L.E_Loop;
        [ exact Hg | apply lp_lpR_exec, Hbridge; exact Hl ].
    + intro H; inversion H; subst; split;
        [ assumption | apply Hbridge, lp_lpR_exec; assumption ].
  - (* Call p *)
    split; [ intro H; apply L.E_Call; exact H
           | intro H; inversion H; subst; assumption ].
  - (* Uncall p *)
    unfold conv; split.
    + intro H; apply L.E_Uncall; apply (proj1 (L.exec_iff Γ (Γ p) b a)); exact H.
    + intro H; inversion H; subst;
        apply (proj2 (L.exec_iff Γ (Γ p) b a)); assumption.
Qed.

(* --------------------------------------------------------------------- *)
(** ** A purely denotational proof of reversibility. *)
Lemma reversible_pstep : forall p, reversible (pstep p).
Proof.
  intro p; split.
  - intros a b b' H1 H2; eapply pstep_det; eassumption.
  - intros a b b' H1 H2; unfold conv in *;
      apply pstep_rev in H1; apply pstep_rev in H2; eapply pstep_det; eassumption.
Qed.

Lemma reversible_exec : forall s, reversible (L.exec Γ s).
Proof.
  intro s; split.
  - intros a b b' H1 H2; eapply L.exec_det; eassumption.
  - intros a b b' H1 H2; unfold conv in *; eapply L.exec_injective; eassumption.
Qed.

Lemma denote_reversible : forall D,
  (forall p, reversible (D p)) -> forall s, reversible (denote D s).
Proof.
  intros D HD; induction s; simpl.
  - apply rev_id.
  - apply reversible_pstep.
  - apply rev_comp; assumption.
  - apply rev_if; assumption.
  - apply rev_loop; assumption.
  - apply HD.
  - apply rev_conv; apply HD.
Qed.

Corollary denote_injective : forall D,
  (forall p, reversible (D p)) ->
  forall s a a' b, denote D s a b -> denote D s a' b -> a = a'.
Proof.
  intros D HD s a a' b H1 H2.
  destruct (denote_reversible D HD s) as [_ Hc]; unfold conv, det in Hc.
  eapply Hc; eassumption.
Qed.

(* --------------------------------------------------------------------- *)
(** ** Compositionality (congruence) and full abstraction. *)

(** Denotationally-equal procedure meanings can be substituted anywhere. *)
Lemma denote_cong : forall D D',
  (forall p a b, D p a b <-> D' p a b) ->
  forall s a b, denote D s a b <-> denote D' s a b.
Proof.
  intros D D' HD; induction s; intros a b; simpl.
  - tauto.
  - tauto.
  - apply compR_ext; assumption.
  - apply ifR_ext; assumption.
  - apply loopR_ext; assumption.
  - apply HD.
  - apply conv_ext; intros x y; apply HD.
Qed.

Definition obs_equiv (s1 s2 : L.stmt) : Prop :=
  forall a b, L.exec Γ s1 a b <-> L.exec Γ s2 a b.
Definition den_equiv (s1 s2 : L.stmt) : Prop :=
  forall a b, denote Dexec s1 a b <-> denote Dexec s2 a b.

(** Full abstraction (input/output observations): denotational equality holds
    exactly for observationally-equivalent programs.  Immediate from adequacy;
    together with [denote_cong] (the denotation is a congruence), this is the
    constructive content of full abstraction at the framework level. *)
Theorem full_abstraction : forall s1 s2, den_equiv s1 s2 <-> obs_equiv s1 s2.
Proof.
  intros s1 s2; unfold den_equiv, obs_equiv; split; intros H a b.
  - rewrite <- (adequacy s1 a b), <- (adequacy s2 a b); apply H.
  - rewrite (adequacy s1 a b), (adequacy s2 a b); apply H.
Qed.

End WithEnv.
End Denote.
