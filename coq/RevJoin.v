(** * RevJoin.v — the join structure of PInj

    Three separate things in this development stalled at the same place:

      - [RevCtrl.v] could add only the *negation* case of Glueck--Kaarsgaard's
        Theorem 9 (decisions closed under Boolean operations); conjunction and
        disjunction need a map that is injective only because two of its cases
        have **disjoint domains**;
      - [RevTraced.v]'s two open axioms (vanishing-II, dinaturality) are
        statements about the countable supremum the execution formula takes,
        which [traceH] never exposes;
      - [RevFix.v] proved its fixed point reversible by a bespoke argument about
        *increasing chains*, which is a special case of the same fact.

    All three want the structure the literature builds \textsf{PInj} out of: a
    **join inverse category** — an inverse category in which compatible families
    of morphisms have joins (Axelsen and Kaarsgaard, FoSSaCS 2016; Kaarsgaard,
    Axelsen and Glueck, JLAMP 87, 2017; Glueck and Kaarsgaard, LMCS 14(3:16),
    2018).  Over [hrel] the join is just union, so what has to be proved is that
    unions of *compatible* partial injections are partial injections, and that
    the categorical operations distribute over them.

    This file supplies that, and then collects the three payoffs:

      - [pinj_join]        — the join of a pairwise-compatible family of partial
                             injections is a partial injection.  This is the
                             theorem the other three were each re-deriving;
      - [traceH_is_join]   — the execution formula *is* a join, exhibited;
      - [decisions_closed_and] / [_or] / [_neg] — Theorem 9 in full, with the
        disjointness that makes the Boolean cases work made explicit. *)

From Stdlib Require Import Bool Arith.
Require Import RevCore RevAlgebra RevDenote RevFix RevCat RevTrace RevSMC RevCtrl.

(* ===================================================================== *)
(** ** Order, compatibility, disjointness, joins. *)

(** The order of the inverse category: inclusion of relations. *)
Definition hle {A B : Type} (R S : hrel A B) : Prop := forall a b, R a b -> S a b.

Lemma hle_refl : forall A B (R : hrel A B), hle R R.
Proof. intros A B R a b H; exact H. Qed.

Lemma hle_trans : forall A B (R S T : hrel A B), hle R S -> hle S T -> hle R T.
Proof. intros A B R S T H1 H2 a b H; apply H2, H1, H. Qed.

Lemma hle_antisym : forall A B (R S : hrel A B), hle R S -> hle S R -> heq R S.
Proof. intros A B R S H1 H2 a b; split; [ apply H1 | apply H2 ]. Qed.

(** Two maps are **compatible** when they agree wherever both are defined —
    forwards *and* backwards, which is what a partial injection needs. *)
Definition compatH {A B : Type} (R S : hrel A B) : Prop :=
  (forall a b b', R a b -> S a b' -> b = b')
  /\ (forall a a' b, R a b -> S a' b -> a = a').

(** They are **disjoint** when they are never both defined — the special case
    the Boolean connectives use. *)
Definition disjH {A B : Type} (R S : hrel A B) : Prop :=
  (forall a b b', R a b -> S a b' -> False)
  /\ (forall a a' b, R a b -> S a' b -> False).

Lemma disjH_compatH : forall A B (R S : hrel A B), disjH R S -> compatH R S.
Proof.
  intros A B R S [d1 d2]; split;
    [ intros a b b' H1 H2; exfalso; eapply d1 | intros a a' b H1 H2; exfalso; eapply d2 ];
    eassumption.
Qed.

Lemma compatH_sym : forall A B (R S : hrel A B), compatH R S -> compatH S R.
Proof.
  intros A B R S [c1 c2]; split;
    [ intros a b b' H1 H2; symmetry; eapply c1 | intros a a' b H1 H2; symmetry; eapply c2 ];
    eassumption.
Qed.

(** A partial injection is compatible with itself; that is exactly what [pinj]
    says. *)
Lemma pinj_compatH_self : forall A B (R : hrel A B), pinj R -> compatH R R.
Proof.
  intros A B R [d c]; split;
    [ intros a b b' H1 H2; eapply d | intros a a' b H1 H2; eapply c; unfold convH ];
    eassumption.
Qed.

Lemma heq_sym : forall A B (R S : hrel A B), heq R S -> heq S R.
Proof.
  intros A B R S H a b; split; intro Hx;
    [ apply (proj2 (H a b)) | apply (proj1 (H a b)) ]; exact Hx.
Qed.

(** [pinj] only depends on the extension of a relation. *)
Lemma pinj_heq : forall A B (R S : hrel A B), heq R S -> pinj R -> pinj S.
Proof.
  intros A B R S H [d c]; split.
  - intros a b b' H1 H2; eapply d;
      [ apply (proj2 (H a b)); exact H1 | apply (proj2 (H a b')); exact H2 ].
  - intros b a a' H1 H2; unfold convH in *; eapply c; unfold convH;
      [ apply (proj2 (H a b)); exact H1 | apply (proj2 (H a' b)); exact H2 ].
Qed.

(** The join of a family, and of two maps. *)
Definition joinH {I A B : Type} (F : I -> hrel A B) : hrel A B :=
  fun a b => exists i, F i a b.

Definition joinH2 {A B : Type} (R S : hrel A B) : hrel A B :=
  fun a b => R a b \/ S a b.

Definition zeroH {A B : Type} : hrel A B := fun _ _ => False.

Lemma pinj_zeroH : forall A B, pinj (@zeroH A B).
Proof. intros A B; split; intros a b b' []. Qed.

(** The join is the least upper bound. *)
Lemma joinH_ub : forall I A B (F : I -> hrel A B) i, hle (F i) (joinH F).
Proof. intros I A B F i a b H; exists i; exact H. Qed.

Lemma joinH_lub : forall I A B (F : I -> hrel A B) (S : hrel A B),
  (forall i, hle (F i) S) -> hle (joinH F) S.
Proof. intros I A B F S H a b [i Hi]; eapply H; exact Hi. Qed.

(* ===================================================================== *)
(** ** The theorem the rest of the development kept re-deriving. *)

Theorem pinj_join : forall I A B (F : I -> hrel A B),
  (forall i, pinj (F i)) -> (forall i j, compatH (F i) (F j)) -> pinj (joinH F).
Proof.
  intros I A B F Hp Hc; split.
  - intros a b b' [i Hi] [j Hj]; destruct (Hc i j) as [c1 _]; eapply c1; eassumption.
  - intros b a a' Ha Ha'; unfold convH in *.
    destruct Ha as [i Hi]; destruct Ha' as [j Hj].
    destruct (Hc i j) as [_ c2]; eapply c2; eassumption.
Qed.

Corollary pinj_joinH2 : forall A B (R S : hrel A B),
  pinj R -> pinj S -> compatH R S -> pinj (joinH2 R S).
Proof.
  intros A B R S HR HS Hc.
  assert (Hj : pinj (joinH (fun b : bool => if b then R else S))).
  { apply pinj_join.
    - intros [|]; assumption.
    - intros [|] [|];
        solve [ apply pinj_compatH_self; assumption
              | exact Hc | apply compatH_sym; exact Hc ]. }
  destruct Hj as [d c]; split.
  - intros a b b' H1 H2; eapply d;
      [ destruct H1 as [H1|H1]; [ exists true | exists false ]; exact H1
      | destruct H2 as [H2|H2]; [ exists true | exists false ]; exact H2 ].
  - intros b a a' H1 H2; unfold convH in *; eapply c; unfold convH;
      [ destruct H1 as [H1|H1]; [ exists true | exists false ]; exact H1
      | destruct H2 as [H2|H2]; [ exists true | exists false ]; exact H2 ].
Qed.

(** An increasing chain is pairwise compatible, so [RevFix]'s argument is an
    instance. *)
Corollary pinj_join_chain : forall A B (F : nat -> hrel A B),
  (forall n, pinj (F n)) -> (forall n m, n <= m -> hle (F n) (F m)) ->
  pinj (joinH F).
Proof.
  intros A B F Hp Hmono; apply pinj_join; [ exact Hp | ].
  intros i j; destruct (Nat.le_ge_cases i j) as [H|H].
  - assert (Hij : hle (F i) (F j)) by (apply Hmono; exact H).
    destruct (pinj_compatH_self A B (F j) (Hp j)) as [c1 c2]; split.
    + intros a b b' H1 H2; eapply c1; [ apply Hij; exact H1 | exact H2 ].
    + intros a a' b H1 H2; eapply c2; [ apply Hij; exact H1 | exact H2 ].
  - assert (Hji : hle (F j) (F i)) by (apply Hmono; exact H).
    destruct (pinj_compatH_self A B (F i) (Hp i)) as [c1 c2]; split.
    + intros a b b' H1 H2; eapply c1; [ exact H1 | apply Hji; exact H2 ].
    + intros a a' b H1 H2; eapply c2; [ exact H1 | apply Hji; exact H2 ].
Qed.

(* ===================================================================== *)
(** ** The categorical operations distribute over joins.

    For relations these hold with no side conditions at all — which is why the
    join is the right structure to have exposed. *)

Lemma compH_joinH_l : forall I A B C (F : I -> hrel A B) (S : hrel B C),
  heq (compH (joinH F) S) (joinH (fun i => compH (F i) S)).
Proof.
  intros I A B C F S a c; unfold compH, joinH; split.
  - intros [b [[i Hi] Hb]]; exists i, b; split; assumption.
  - intros [i [b [Hi Hb]]]; exists b; split; [ exists i | ]; assumption.
Qed.

Lemma compH_joinH_r : forall I A B C (R : hrel A B) (F : I -> hrel B C),
  heq (compH R (joinH F)) (joinH (fun i => compH R (F i))).
Proof.
  intros I A B C R F a c; unfold compH, joinH; split.
  - intros [b [Hb [i Hi]]]; exists i, b; split; assumption.
  - intros [i [b [Hb Hi]]]; exists b; split; [ | exists i ]; assumption.
Qed.

Lemma convH_joinH : forall I A B (F : I -> hrel A B),
  heq (convH (joinH F)) (joinH (fun i => convH (F i))).
Proof. intros I A B F b a; unfold convH, joinH; tauto. Qed.

Lemma compH_joinH2_l : forall A B C (R S : hrel A B) (T : hrel B C),
  heq (compH (joinH2 R S) T) (joinH2 (compH R T) (compH S T)).
Proof.
  intros A B C R S T a c; unfold compH, joinH2; split.
  - intros [b [[H|H] Hb]]; [ left | right ]; exists b; split; assumption.
  - intros [[b [H Hb]]|[b [H Hb]]]; exists b; split; solve [ left; assumption
    | right; assumption | assumption ].
Qed.

(* ===================================================================== *)
(** ** Payoff 1: the execution formula is a join. *)

Definition trace11 {A B U : Type} (R : hrel (A + U) (B + U)) : hrel A B :=
  fun a b => R (inl a) (inl b).

Definition tracen {A B U : Type} (R : hrel (A + U) (B + U)) (n : nat) : hrel A B :=
  fun a b => exists u u', R (inl a) (inr u) /\ pathn R n u u' /\ R (inr u') (inl b).

(** [traceH R = R11 ∨ ⋁_{n∈ω} R21 R22ⁿ R12] — Glueck--Kaarsgaard's Prop. 2, now
    with the join it always was made explicit rather than hidden in an [exists]. *)
Theorem traceH_is_join : forall A B U (R : hrel (A + U) (B + U)),
  heq (traceH R) (joinH2 (trace11 R) (joinH (tracen R))).
Proof.
  intros A B U R a b; unfold traceH, joinH2, joinH, trace11, tracen; split.
  - intros [H | [n [u [u' H]]]]; [ left; exact H | right; exists n, u, u'; exact H ].
  - intros [H | [n [u [u' H]]]]; [ left; exact H | right; exists n, u, u'; exact H ].
Qed.

(** Indexed form: [None] is the immediate exit, [Some n] the runs of length [n]. *)
Definition tracefam {A B U : Type} (R : hrel (A + U) (B + U)) (i : option nat)
  : hrel A B :=
  match i with
  | None => trace11 R
  | Some n => tracen R n
  end.

Theorem traceH_is_join_fam : forall A B U (R : hrel (A + U) (B + U)),
  heq (traceH R) (joinH (tracefam R)).
Proof.
  intros A B U R a b; unfold traceH, joinH; split.
  - intros [H | [n [u [u' H]]]].
    + exists None; exact H.
    + exists (Some n); simpl; exists u, u'; exact H.
  - intros [[n|] H]; simpl in H.
    + destruct H as [u [u' H]]; right; exists n, u, u'; exact H.
    + left; exact H.
Qed.

(** Reading a run backwards is a run of the converse, at the same length. *)
Lemma tracen_conv : forall A B U (R : hrel (A + U) (B + U)) n a b,
  tracen R n a b -> tracen (convH R) n b a.
Proof.
  intros A B U R n a b [u [u' [E1 [Hp E2]]]].
  exists u', u; split; [ exact E2 | split ].
  - apply (proj2 (pathn_conv A B U R n u' u)); exact Hp.
  - exact E1.
Qed.

(** Runs out of the same point end at the same point, whatever their lengths —
    [path_exit_unique] repackaged as *compatibility of the summands*. *)
Lemma tracen_det : forall A B U (R : hrel (A + U) (B + U)), detH R ->
  forall n m a b b', tracen R n a b -> tracen R m a b' -> b = b'.
Proof.
  intros A B U R dR n m a b b' [u [u' [E1 [P1 X1]]]] [v [v' [E2 [P2 X2]]]].
  assert (Hi : @inr B U u = inr v) by (eapply dR; eassumption).
  injection Hi; intro; subst v.
  exact (path_exit_unique R dR n m u u' v' b b' P1 X1 P2 X2).
Qed.

(** The whole family is pairwise compatible: the two kinds of summand are
    *disjoint* (a state either exits at once or enters the wire, never both),
    and two runs of different lengths agree. *)
Lemma compatH_tracefam : forall A B U (R : hrel (A + U) (B + U)), pinj R ->
  forall i j, compatH (tracefam R i) (tracefam R j).
Proof.
  intros A B U R [d c] [n|] [m|]; simpl; split.
  (* Some n / Some m *)
  - intros a b b' H1 H2; eapply tracen_det; eassumption.
  - intros a a' b H1 H2.
    apply (tracen_conv A B U R n) in H1; apply (tracen_conv A B U R m) in H2.
    eapply tracen_det; [ exact c | exact H1 | exact H2 ].
  (* Some n / None: disjoint *)
  - intros a b b' [u [u' [E1 _]]] H2; unfold trace11 in H2.
    assert (Hi : @inr B U u = inl b') by (eapply d; eassumption); discriminate.
  - intros a a' b [u [u' [_ [_ X1]]]] H2; unfold trace11 in H2.
    assert (Hi : @inr A U u' = inl a') by (eapply c; unfold convH; eassumption).
    discriminate.
  (* None / Some m: disjoint *)
  - intros a b b' H1 [v [v' [E2 _]]]; unfold trace11 in H1.
    assert (Hi : @inl B U b = inr v) by (eapply d; eassumption); discriminate.
  - intros a a' b H1 [v [v' [_ [_ X2]]]]; unfold trace11 in H1.
    assert (Hi : @inl A U a = inr v') by (eapply c; unfold convH; eassumption).
    discriminate.
  (* None / None *)
  - intros a b b' H1 H2; unfold trace11 in *.
    assert (Hi : @inl B U b = inl b') by (eapply d; eassumption).
    injection Hi; auto.
  - intros a a' b H1 H2; unfold trace11 in *.
    assert (Hi : @inl A U a = inl a') by (eapply c; unfold convH; eassumption).
    injection Hi; auto.
Qed.

(** So [PInj]'s closure under the trace is now an *instance* of [pinj_join]: the
    execution formula is a join of pairwise-compatible partial injections.  This
    reproves [RevTrace.pinj_traceH] from the join structure rather than by
    reasoning about paths. *)
Theorem pinj_traceH_via_join : forall A B U (R : hrel (A + U) (B + U)),
  pinj R -> pinj (traceH R).
Proof.
  intros A B U R Hp.
  apply (pinj_heq _ _ (joinH (tracefam R)) (traceH R)).
  - apply heq_sym, traceH_is_join_fam.
  - apply pinj_join.
    + intros i; destruct (compatH_tracefam A B U R Hp i i) as [c1 c2]; split.
      * intros a b b' H1 H2; eapply c1; eassumption.
      * intros b a a' H1 H2; unfold convH in *; eapply c2; eassumption.
    + apply compatH_tracefam; exact Hp.
Qed.

(* ===================================================================== *)
(** ** Payoff 2: decisions, and Theorem 9 in full.

    A decision splits its object into the two halves a predicate cuts it into.
    Those halves are the *partial identities* below, and the Boolean operations
    live there: intersection is composition, complement swaps the halves, and
    **union is a join** — which is the case [RevCtrl.v] could not reach. *)

Definition dtrue {A : Type} (g : A -> bool) : hrel A A :=
  fun a b => a = b /\ g a = true.
Definition dfalse {A : Type} (g : A -> bool) : hrel A A :=
  fun a b => a = b /\ g a = false.

Lemma pinj_dtrue : forall A (g : A -> bool), pinj (dtrue g).
Proof.
  intros A g; split; intros x y y' [H1 H2] [H3 H4]; unfold convH in *; congruence.
Qed.

Lemma pinj_dfalse : forall A (g : A -> bool), pinj (dfalse g).
Proof.
  intros A g; split; intros x y y' [H1 H2] [H3 H4]; unfold convH in *; congruence.
Qed.

Lemma disjH_dtrue_dfalse : forall A (g : A -> bool), disjH (dtrue g) (dfalse g).
Proof.
  intros A g; split; intros x y y' [H1 H2] [H3 H4]; congruence.
Qed.

(** The decision [testH g] is the join of its two disjoint halves. *)
Theorem testH_decompose : forall A (g : A -> bool),
  heq (testH g) (joinH2 (compH (dtrue g) inlH) (compH (dfalse g) inrH)).
Proof.
  intros A g a x; unfold testH, joinH2, compH, dtrue, dfalse, inlH, inrH; split.
  - destruct (g a) eqn:Hg; intro H; subst x.
    + left; exists a; repeat split; reflexivity.
    + right; exists a; repeat split; reflexivity.
  - intros [[m [[Hm Hg] Hx]]|[m [[Hm Hg] Hx]]]; subst m; rewrite Hg; congruence.
Qed.

(** *** Theorem 9: closure under negation, conjunction and disjunction. *)

Theorem decisions_closed_neg : forall A (g : A -> bool),
  heq (dtrue (fun a => negb (g a))) (dfalse g).
Proof.
  intros A g a b; unfold dtrue, dfalse; split; intros [H1 H2]; split;
    try exact H1; destruct (g a); simpl in *; congruence.
Qed.

(** Intersection is composition. *)
Theorem decisions_closed_and : forall A (g1 g2 : A -> bool),
  heq (dtrue (fun a => g1 a && g2 a)) (compH (dtrue g1) (dtrue g2)).
Proof.
  intros A g1 g2 a b; unfold dtrue, compH; split.
  - intros [H1 H2]; apply andb_true_iff in H2 as [Ha Hb].
    exists a; repeat split; [ exact Ha | exact H1 | exact Hb ].
  - intros [m [[Hm H1] [Hn H2]]]; subst; split;
      [ reflexivity | apply andb_true_iff; split; assumption ].
Qed.

(** **Union is a join** — this is the case that needed this file.  The two
    summands overlap (both guards may hold), so they are *compatible* rather than
    disjoint, which is exactly why join inverse categories ask for compatible
    joins and not merely disjoint ones. *)
Theorem decisions_closed_or : forall A (g1 g2 : A -> bool),
  heq (dtrue (fun a => g1 a || g2 a)) (joinH2 (dtrue g1) (dtrue g2)).
Proof.
  intros A g1 g2 a b; unfold dtrue, joinH2; split.
  - intros [H1 H2]; apply orb_true_iff in H2 as [Ha|Ha];
      [ left | right ]; split; assumption.
  - intros [[H1 H2]|[H1 H2]]; split; try assumption;
      apply orb_true_iff; [ left | right ]; assumption.
Qed.

Lemma compatH_dtrue : forall A (g1 g2 : A -> bool), compatH (dtrue g1) (dtrue g2).
Proof.
  intros A g1 g2; split; intros x y y' [H1 _] [H3 _]; congruence.
Qed.

(** So the join of two decisions' true-halves is again a partial injection: the
    Boolean algebra of decisions stays inside \textsf{PInj}. *)
Corollary pinj_decisions_or : forall A (g1 g2 : A -> bool),
  pinj (dtrue (fun a => g1 a || g2 a)).
Proof.
  intros A g1 g2.
  destruct (pinj_joinH2 A A (dtrue g1) (dtrue g2)
              (pinj_dtrue A g1) (pinj_dtrue A g2) (compatH_dtrue A g1 g2)) as [d c].
  split.
  - intros x y y' H1 H2; eapply d; apply decisions_closed_or; eassumption.
  - intros y x x' H1 H2; unfold convH in *; eapply c; unfold convH;
      apply decisions_closed_or; eassumption.
Qed.

(** The false half of a conjunction, likewise, is a join of two **disjoint**
    halves ([g1] fails, or [g1] holds and [g2] fails) — the decomposition
    [RevCtrl.v] could not express. *)
Theorem dfalse_and : forall A (g1 g2 : A -> bool),
  heq (dfalse (fun a => g1 a && g2 a))
      (joinH2 (dfalse g1) (compH (dtrue g1) (dfalse g2))).
Proof.
  intros A g1 g2 a b; unfold dfalse, dtrue, joinH2, compH; split.
  - intros [H1 H2]; apply andb_false_iff in H2 as [Ha|Ha].
    + left; split; assumption.
    + destruct (g1 a) eqn:Hg1.
      (* [destruct ... eqn] rewrote [g1 a] in the goal, so the guard components
         are already discharged; what is left is the equation and [g2]. *)
      * right; exists a; repeat split; [ exact H1 | exact Ha ].
      * left; split; [ exact H1 | reflexivity ].
  - intros [[H1 H2]|[m [[Hm H1] [Hn H2]]]].
    + split; [ exact H1 | apply andb_false_iff; left; exact H2 ].
    + subst; split;
        [ reflexivity | apply andb_false_iff; right; exact H2 ].
Qed.

Lemma disjH_dfalse_and : forall A (g1 g2 : A -> bool),
  disjH (dfalse g1) (compH (dtrue g1) (dfalse g2)).
Proof.
  intros A g1 g2; split; intros x y y';
    intros [H1 H2] [m [[Hm H3] [Hn H4]]]; congruence.
Qed.

(* ===================================================================== *)
(** ** Payoff 3: the least fixed point is a join.

    [RevFix.Dfix] is the union of the Kleene chain of approximants, and it was
    proved reversible there by an ad-hoc argument (take the max of the two
    indices).  That argument is exactly [pinj_join_chain]: an increasing chain
    is a compatible family.  Here the fixed point's reversibility is obtained
    from the join structure instead. *)

Module FixJoin (P : REV_PRIM).
Module F := RevFix.DenoteFix P.

Section WithEnv.
Variable G : F.L.pname -> F.L.stmt.

Theorem Dfix_is_join : forall p,
  heq (F.Dfix G p) (joinH (fun n => F.approx G n p)).
Proof. intros p a b; unfold F.Dfix, joinH; split; intro H; exact H. Qed.

Corollary Dfix_reversible_via_join : forall p, reversible (F.Dfix G p).
Proof.
  intro p; apply (proj1 (pinj_reversible _ _)).
  apply (pinj_heq _ _ (joinH (fun n => F.approx G n p)) (F.Dfix G p)).
  - apply heq_sym, Dfix_is_join.
  - apply pinj_join_chain.
    + intro n; apply (proj2 (pinj_reversible _ _)); apply F.approx_reversible.
    + intros n m Hnm a b H; eapply F.approx_le; eassumption.
Qed.

End WithEnv.
End FixJoin.
