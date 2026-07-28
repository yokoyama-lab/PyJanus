(** * RevCtrl.v — Janus's control constructors ARE PInj structure

    [RevAlgebra.v] gives each control construct as a *bespoke* combinator with a
    bespoke closure lemma: [ifR] is a disjunction and [rev_if] a case analysis on
    it.  Paolini--Piccolo--Roversi's Matita model does not work that way.  There
    ([rel_interpretation.ma]) the conditional is *assembled from the categorical
    structure*:

    [[
      test e1 ; δ ; ((q1 × id) + (q2 × id)) ; δ⁻¹ ; (test e2)†
    ]]

    where [test e : state → state × (1+1)] evaluates the guard **reversibly** —
    the decision bit is not discarded but XOR-ed into a fresh slot ([ru … XOR …]),
    which is the *ancilla flag* pattern of PyJanus's standard library — and the
    distributor [δ] then opens [state × bool] into [state + state].

    The reading that matters: **Janus's exit assertion is the dagger of the exit
    test.**  The [fi g2] that Janus programmers write to make a conditional
    reversible is not an extra proof obligation bolted on; it is the *converse of
    the very morphism that opened the branch*.

    **This is not new.**  It is exactly how Glueck and Kaarsgaard define the
    conditional for structured reversible flowchart languages (Janus among them):
    [[ if p then c1 else c2 fi q ]] = [[q]]dagger ([[c1]] + [[c2]]) [[p]]
    (LMCS 14(3:16), 2018, doi:10.23638/LMCS-14(3:16)2018), with their extensivity
    /decision machinery playing the part of [testH] here.  What this file adds is
    the *direction*: they take that composite as the definition, whereas
    [if_is_test_sum] **derives** it from [RevCore]'s inductive [exec], so the two
    presentations are proved to agree.  See docs/reversible-categorical-semantics.md
    for the full correspondence.

    This file makes that precise.  We take the composite [state → state + state]
    directly as [testH] rather than routing through [× (1+1)] and [δ] (which
    would need the product monoidal structure and distributivity — see the note
    at the end), and prove

      - [pinj_testH]    : the test is a partial injection;
      - [test_dagger]   : its dagger merges the summands, defined on [inl b]
                          exactly when the guard holds at [b];
      - [if_is_test_sum]: [ifR g1 R S g2 = testH g1 ; (R + S) ; (testH g2)†];
      - [rev_if_via_cat]: hence [rev_if] is a *corollary* of [pinj_sumH],
                          [pinj_compH] and [pinj_convH] — no case analysis.

    With [RevTrace.loop_is_trace] this completes the table (module [Struct]):

    | constructor | PInj structure                        |
    |-------------|---------------------------------------|
    | [Skip]      | [idH]                                 |
    | [Seq]       | [compH]                               |
    | [If]        | [testH ; (+) ; testH†]                 |
    | [Loop]      | [traceH]                              |
    | [Uncall]    | the dagger [convH]                    |

    so [denote_reversible_structural] re-proves reversibility of every program
    from the closure properties of \textsf{PInj} alone — no constructor-specific
    lemma anywhere.  Axiom-free. *)

From Stdlib Require Import Bool.
Require Import RevCore RevAlgebra RevDenote RevCat RevTrace RevSMC.

(* ===================================================================== *)
(** ** The reversible test. *)

(** [testH g] routes a state into the left summand when the guard holds and the
    right summand when it does not — keeping the state itself, so no information
    is discarded.  (Their [test] lands in [state × (1+1)]; this is that composed
    with the distributor.) *)
Definition testH {A : Type} (g : A -> bool) : hrel A (A + A) :=
  fun a x => if g a then x = inl a else x = inr a.

Lemma pinj_testH : forall A (g : A -> bool), pinj (testH g).
Proof.
  intros A g; split.
  - intros a x x' H1 H2; unfold testH in *; destruct (g a); congruence.
  - intros x a a' H1 H2; unfold convH, testH in *.
    destruct (g a) eqn:Ha; destruct (g a') eqn:Ha'; subst;
      try discriminate; injection H2; auto.
Qed.

(** The dagger of a test *merges* the two summands: it accepts [inl b] exactly
    when the guard holds at [b], and [inr b] exactly when it fails.  This is the
    exit assertion of a Janus conditional. *)
Lemma test_dagger : forall A (g : A -> bool) (y : A + A) (b : A),
  convH (testH g) y b <-> (y = inl b /\ g b = true) \/ (y = inr b /\ g b = false).
Proof.
  intros A g y b; unfold convH, testH; destruct (g b) eqn:Hb; split.
  - intro H; left; split; [ exact H | reflexivity ].
  - intros [[H _]|[_ H]]; [ exact H | discriminate ].
  - intro H; right; split; [ exact H | reflexivity ].
  - intros [[_ H]|[H _]]; [ discriminate | exact H ].
Qed.

(* ===================================================================== *)
(** ** The conditional is a composite. *)

Theorem if_is_test_sum :
  forall (state : Type) (g1 g2 : state -> bool) (R S : @rel state) a b,
    ifR g1 R S g2 a b
    <-> compH (testH g1) (compH (sumH R S) (convH (testH g2))) a b.
Proof.
  intros state g1 g2 R S a b; unfold ifR, compH; split.
  - intros [[Hg1 [HR Hg2]]|[Hg1 [HS Hg2]]].
    + exists (inl a); split; [ unfold testH; rewrite Hg1; reflexivity | ].
      exists (inl b); split; [ exact HR | ].
      unfold convH, testH; rewrite Hg2; reflexivity.
    + exists (inr a); split; [ unfold testH; rewrite Hg1; reflexivity | ].
      exists (inr b); split; [ exact HS | ].
      unfold convH, testH; rewrite Hg2; reflexivity.
  - intros [x [Hx [y [Hy Hb]]]].
    unfold testH in Hx; unfold convH, testH in Hb.
    destruct (g1 a) eqn:Hg1; subst x.
    + (* entered on the left *)
      destruct y as [c|c]; simpl in Hy; [ | contradiction ].
      destruct (g2 b) eqn:Hg2; [ | discriminate ].
      injection Hb; intro; subst c.
      left; split; [ reflexivity | split; [ exact Hy | reflexivity ] ].
    + (* entered on the right *)
      destruct y as [c|c]; simpl in Hy; [ contradiction | ].
      destruct (g2 b) eqn:Hg2; [ discriminate | ].
      injection Hb; intro; subst c.
      right; split; [ reflexivity | split; [ exact Hy | reflexivity ] ].
Qed.

(** Reversibility of the conditional, with no case analysis: it is a composite
    of a test, a coproduct and a dagger, each of which preserves partial
    injections. *)
Corollary rev_if_via_cat :
  forall (state : Type) (g1 g2 : state -> bool) (R S : @rel state),
    reversible R -> reversible S -> reversible (ifR g1 R S g2).
Proof.
  intros state g1 g2 R S HR HS.
  assert (Hc : pinj (compH (testH g1) (compH (sumH R S) (convH (testH g2))))).
  { apply pinj_compH; [ apply pinj_testH | ].
    apply pinj_compH.
    - apply pinj_sumH; apply (proj2 (pinj_reversible state _)); assumption.
    - apply pinj_convH, pinj_testH. }
  destruct Hc as [d c]; split.
  - intros a b b' H1 H2; eapply d; apply if_is_test_sum; eassumption.
  - intros a b b' H1 H2; unfold conv in *;
      eapply c; unfold convH; apply if_is_test_sum; eassumption.
Qed.

(* ===================================================================== *)
(** ** Every constructor, as PInj structure. *)

Module Struct (P : REV_PRIM).
Module Dn := RevDenote.Denote P.
Import P.
Module L := Dn.L.

Section WithDenv.
Variable D : Dn.denv.

Notation den s := (Dn.denote D s).

Lemma denote_Skip : forall a b, den L.Skip a b <-> idH a b.
Proof. intros; simpl; unfold idR, idH; tauto. Qed.

Lemma denote_Seq : forall s1 s2 a b,
  den (L.Seq s1 s2) a b <-> compH (den s1) (den s2) a b.
Proof. intros; simpl; unfold compR, compH; tauto. Qed.

(** The conditional: open with a test, run the coproduct of the branches, close
    with the *dagger* of the exit test. *)
Lemma denote_If : forall g1 s1 s2 g2 a b,
  den (L.If g1 s1 s2 g2) a b
  <-> compH (testH (gtest g1))
            (compH (sumH (den s1) (den s2)) (convH (testH (gtest g2)))) a b.
Proof. intros; simpl; apply if_is_test_sum. Qed.

(** The loop: the trace of one turn (RevTrace). *)
Lemma denote_Loop : forall g1 s1 s2 g2 a b,
  den (L.Loop g1 s1 s2 g2) a b
  <-> traceH (turn (gtest g1) (gtest g2) (den s1) (den s2)) a b.
Proof.
  intros; simpl; symmetry;
    apply (loop_is_trace (gtest g1) (gtest g2) (den s1) (den s2) a b).
Qed.

Lemma denote_Uncall : forall p a b, den (L.Uncall p) a b <-> convH (D p) a b.
Proof. intros; simpl; unfold conv, convH; tauto. Qed.

(** Reversibility of every program, from the closure properties of PInj alone:
    identity, composition, coproduct, dagger, test and trace.  Not one
    constructor-specific argument. *)
Theorem denote_reversible_structural :
  (forall p, pinj (D p)) -> forall s, pinj (den s).
Proof.
  intros HD s; induction s.
  - (* Skip *) split; intros a b b' H1 H2; apply denote_Skip in H1, H2;
      unfold idH, convH in *; congruence.
  - (* Prim *) apply (proj2 (pinj_reversible state _)), Dn.reversible_pstep.
  - (* Seq *)
    assert (Hc : pinj (compH (den s1) (den s2))) by (apply pinj_compH; assumption).
    destruct Hc as [d c]; split.
    + intros a b b' H1 H2; eapply d; apply denote_Seq; eassumption.
    + intros a b b' H1 H2; unfold convH in *;
        eapply c; unfold convH; apply denote_Seq; eassumption.
  - (* If *)
    apply (proj2 (pinj_reversible state _)).
    apply rev_if_via_cat; apply (proj1 (pinj_reversible state _)); assumption.
  - (* Loop *)
    assert (Ht : pinj (traceH (turn (gtest g1) (gtest g2) (den s1) (den s2)))).
    { apply pinj_traceH, pinj_turn; apply (proj1 (pinj_reversible state _)); assumption. }
    destruct Ht as [d c]; split.
    + intros a b b' H1 H2; eapply d; apply denote_Loop; eassumption.
    + intros a b b' H1 H2; unfold convH in *;
        eapply c; unfold convH; apply denote_Loop; eassumption.
  - (* Call *) apply HD.
  - (* Uncall *)
    assert (Hc : pinj (convH (D p))) by (apply pinj_convH, HD).
    destruct Hc as [d c]; split.
    + intros a b b' H1 H2; eapply d; apply denote_Uncall; eassumption.
    + intros a b b' H1 H2; unfold convH in *;
        eapply c; unfold convH; apply denote_Uncall; eassumption.
Qed.

End WithDenv.
End Struct.

(* ===================================================================== *)
(** ** Note on faithfulness to the Matita construction.

    Their [test] lands in [state × (1+1)] and the split into [state + state] is
    performed by the distributivity isomorphism [δ] of [Pinj_Distr]; the branches
    are then [(q1 × id) + (q2 × id)].  We take the composite directly, which
    needs no product monoidal structure and no distributor — at the cost of not
    exhibiting the decision *bit* as a separate object.  Building [×] and [δ]
    (their [rel_prod.ma] / [rel_distr.ma]) would recover their exact factoring
    and is what a full "PInj is a distributive traced symmetric monoidal
    category" claim would require; see [RevTrace.v]'s closing note. *)

(* ===================================================================== *)
(** ** Decisions are closed under Boolean operations (Glueck--Kaarsgaard Thm 9).

    Their "decisions" -- the reversible representation of a predicate, which
    [testH] is here -- are proved closed under negation, conjunction and
    disjunction (LMCS 14(3:16), 2018, Thm 9).  Negation needs nothing beyond the
    symmetry of the coproduct, and is the whole of it: *)

Theorem test_negation : forall A (g : A -> bool),
  heq (testH (fun a => negb (g a))) (compH (testH g) (@swapS A A)).
Proof.
  intros A g a x; unfold testH, compH, swapS, fnH, swapS_f.
  destruct (g a) eqn:Hg; simpl; split.
  - intro H; subst x; exists (inl a); split; reflexivity.
  - intros [m [Hm Hx]]; subst m; simpl in Hx; exact Hx.
  - intro H; subst x; exists (inr a); split; reflexivity.
  - intros [m [Hm Hx]]; subst m; simpl in Hx; exact Hx.
Qed.

(** Conjunction and disjunction are a different matter, and the difference is
    informative.  Running [testH g2] on the left branch of [testH g1] and the
    identity on the right lands in [(A + A) + A]; collapsing that to [A + A] --
    "either guard failed" -- is *not* a partial injection as a bare map, since
    [inl (inr a)] and [inr a] both have to reach [inr a].  It is only well
    defined because those two cases have **disjoint domains** ([g1] holds in the
    first, fails in the second), i.e. it is a *join of disjoint maps*.

    That is exactly the structure Glueck--Kaarsgaard rely on and that this
    development has not exposed: their decisions live in an inverse category
    with **disjoint joins**, where Thm 9 is available wholesale.  [testH] here is
    defined pointwise and carries no join structure, so the Boolean connectives
    beyond negation are out of reach until it is recast -- the same conclusion
    [RevTraced.v] reaches for vanishing-II and dinaturality.  See
    docs/reversible-categorical-semantics.md. *)
