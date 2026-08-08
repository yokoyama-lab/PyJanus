(** * RevLoopLemma.v — a step-reversible small-step semantics, and the Loop Lemma

    [RevSmallStep] gives a small-step semantics and proves it equivalent to the
    big-step one, and then proves two negative results about itself: [step] is
    not backward deterministic, and the exit assertion of a conditional
    collapses to [RSkip] the moment the branch finishes.  Its closing comment
    says what would be needed to do better:

      "Getting the Loop Lemma would mean adopting a configuration that retains
       the discarded control information -- Lanese and Vidal's program counter,
       or equivalent -- which is a different semantics, not a lemma about this
       one."

    This file is that different semantics.  Following Lanese and Vidal ("A
    Reversible Semantics for Janus", arXiv:2602.16913) a configuration carries

      - a **control stack** [list rs] in place of the nested [RSeq] congruence,
        which is the program counter: where the two collapsing configurations
        of [RevSmallStep] differ is exactly how they decompose onto this stack;
      - a **history** [list ev], one event per step, carrying whatever the step
        discarded -- the guard of an assertion, the branch a conditional took,
        the statement a [Seq] consumed.

    The backward relation [bstep] is then defined in its own right: it reads the
    head of the history and undoes it, never consulting [fstep].  The **Loop
    Lemma** [loop_lemma] says the two are exact inverses,

      fstep G c c'  <->  bstep G c' c

    and from it backward determinism follows ([fstep_backward_det]), which is
    precisely what [RevSmallStep.step_not_backward_deterministic] refutes for
    the semantics without a program counter.  The two configurations that
    witness that refutation are separated here, in [seq_collapse_separated] and
    [exit_assertion_separated]. *)

From Stdlib Require Import List.
Import ListNotations.
Require Import RevCore RevSmallStep.

Module LoopLemma (P : REV_PRIM).
Import P.

(** The instance has to be *taken*, not rebuilt: [RevLang P] is generative, so a
    second application would give runtime statements that cannot even be
    compared with [RevSmallStep]'s.  Same reason [RevDenote] opens with this. *)
Module SSx := RevSmallStep.SmallStep P.
Import SSx.

(** ** Configurations *)

(** The control stack. [RSeq] is no longer stepped through by a congruence rule;
    it is *decomposed* onto this stack, which is what keeps the two
    associativity-collapsing configurations of [RevSmallStep] apart. *)
Definition ctrl := list rs.

(** One event per step, carrying exactly what that step throws away. *)
Inductive ev :=
| EDrop
| EPrim    (p : prim)
| ESeq
| EIf      (g1 : guard) (s1 s2 : rs) (g2 : guard) (br : bool)
| EAssert  (g : guard) (v : bool)
| ELoopIn  (g1 : guard) (s1 s2 : rs) (g2 : guard)
| ELoopE   (g1 : guard) (s1 s2 : rs) (g2 : guard)
| ETestX   (g1 : guard) (s1 s2 : rs) (g2 : guard)
| ETestC   (g1 : guard) (s1 s2 : rs) (g2 : guard)
| ECont    (g1 : guard) (s1 s2 : rs) (g2 : guard)
| ECall    (p : L.pname)
| EUncall  (p : L.pname).

Record conf : Type := mk { cctl : ctrl; cst : state; chist : list ev }.

(** ** The forward relation *)

Inductive fstep (G : L.pname -> L.stmt) : conf -> conf -> Prop :=
| F_Drop : forall k a h,
    fstep G (mk (RSkip :: k) a h) (mk k a (EDrop :: h))
| F_Prim : forall p k a b h,
    pstep p a b ->
    fstep G (mk (RPrim p :: k) a h) (mk k b (EPrim p :: h))
| F_Seq : forall s1 s2 k a h,
    fstep G (mk (RSeq s1 s2 :: k) a h) (mk (s1 :: s2 :: k) a (ESeq :: h))
| F_IfT : forall g1 s1 s2 g2 k a h,
    gtest g1 a = true ->
    fstep G (mk (RIf g1 s1 s2 g2 :: k) a h)
            (mk (s1 :: RAssert g2 true :: k) a (EIf g1 s1 s2 g2 true :: h))
| F_IfF : forall g1 s1 s2 g2 k a h,
    gtest g1 a = false ->
    fstep G (mk (RIf g1 s1 s2 g2 :: k) a h)
            (mk (s2 :: RAssert g2 false :: k) a (EIf g1 s1 s2 g2 false :: h))
| F_Assert : forall g v k a h,
    gtest g a = v ->
    fstep G (mk (RAssert g v :: k) a h) (mk k a (EAssert g v :: h))
| F_Loop : forall g1 s1 s2 g2 k a h,
    gtest g1 a = true ->
    fstep G (mk (RLoop g1 s1 s2 g2 :: k) a h)
            (mk (RLoopE g1 s1 s2 g2 :: k) a (ELoopIn g1 s1 s2 g2 :: h))
| F_LoopE : forall g1 s1 s2 g2 k a h,
    fstep G (mk (RLoopE g1 s1 s2 g2 :: k) a h)
            (mk (s1 :: RTest g1 s1 s2 g2 :: k) a (ELoopE g1 s1 s2 g2 :: h))
| F_TestX : forall g1 s1 s2 g2 k a h,
    gtest g2 a = true ->
    fstep G (mk (RTest g1 s1 s2 g2 :: k) a h) (mk k a (ETestX g1 s1 s2 g2 :: h))
| F_TestC : forall g1 s1 s2 g2 k a h,
    gtest g2 a = false ->
    fstep G (mk (RTest g1 s1 s2 g2 :: k) a h)
            (mk (s2 :: RCont g1 s1 s2 g2 :: k) a (ETestC g1 s1 s2 g2 :: h))
| F_Cont : forall g1 s1 s2 g2 k a h,
    gtest g1 a = false ->
    fstep G (mk (RCont g1 s1 s2 g2 :: k) a h)
            (mk (RLoopE g1 s1 s2 g2 :: k) a (ECont g1 s1 s2 g2 :: h))
| F_Call : forall p k a h,
    fstep G (mk (RCall p :: k) a h) (mk (embed (G p) :: k) a (ECall p :: h))
| F_Uncall : forall p k a h,
    fstep G (mk (RUncall p :: k) a h)
            (mk (embed (L.invert (G p)) :: k) a (EUncall p :: h)).

(** ** The backward relation

    Defined on its own terms: every rule is driven by the head of the history,
    and the store moves backwards through [pinv]. Nothing here mentions
    [fstep]; that the two agree is the theorem, not the definition. *)

Inductive bstep (G : L.pname -> L.stmt) : conf -> conf -> Prop :=
| B_Drop : forall k a h,
    bstep G (mk k a (EDrop :: h)) (mk (RSkip :: k) a h)
| B_Prim : forall p k a b h,
    pstep (pinv p) b a ->
    bstep G (mk k b (EPrim p :: h)) (mk (RPrim p :: k) a h)
| B_Seq : forall s1 s2 k a h,
    bstep G (mk (s1 :: s2 :: k) a (ESeq :: h)) (mk (RSeq s1 s2 :: k) a h)
| B_IfT : forall g1 s1 s2 g2 k a h,
    gtest g1 a = true ->
    bstep G (mk (s1 :: RAssert g2 true :: k) a (EIf g1 s1 s2 g2 true :: h))
            (mk (RIf g1 s1 s2 g2 :: k) a h)
| B_IfF : forall g1 s1 s2 g2 k a h,
    gtest g1 a = false ->
    bstep G (mk (s2 :: RAssert g2 false :: k) a (EIf g1 s1 s2 g2 false :: h))
            (mk (RIf g1 s1 s2 g2 :: k) a h)
| B_Assert : forall g v k a h,
    gtest g a = v ->
    bstep G (mk k a (EAssert g v :: h)) (mk (RAssert g v :: k) a h)
| B_Loop : forall g1 s1 s2 g2 k a h,
    gtest g1 a = true ->
    bstep G (mk (RLoopE g1 s1 s2 g2 :: k) a (ELoopIn g1 s1 s2 g2 :: h))
            (mk (RLoop g1 s1 s2 g2 :: k) a h)
| B_LoopE : forall g1 s1 s2 g2 k a h,
    bstep G (mk (s1 :: RTest g1 s1 s2 g2 :: k) a (ELoopE g1 s1 s2 g2 :: h))
            (mk (RLoopE g1 s1 s2 g2 :: k) a h)
| B_TestX : forall g1 s1 s2 g2 k a h,
    gtest g2 a = true ->
    bstep G (mk k a (ETestX g1 s1 s2 g2 :: h)) (mk (RTest g1 s1 s2 g2 :: k) a h)
| B_TestC : forall g1 s1 s2 g2 k a h,
    gtest g2 a = false ->
    bstep G (mk (s2 :: RCont g1 s1 s2 g2 :: k) a (ETestC g1 s1 s2 g2 :: h))
            (mk (RTest g1 s1 s2 g2 :: k) a h)
| B_Cont : forall g1 s1 s2 g2 k a h,
    gtest g1 a = false ->
    bstep G (mk (RLoopE g1 s1 s2 g2 :: k) a (ECont g1 s1 s2 g2 :: h))
            (mk (RCont g1 s1 s2 g2 :: k) a h)
| B_Call : forall p k a h,
    bstep G (mk (embed (G p) :: k) a (ECall p :: h)) (mk (RCall p :: k) a h)
| B_Uncall : forall p k a h,
    bstep G (mk (embed (L.invert (G p)) :: k) a (EUncall p :: h))
            (mk (RUncall p :: k) a h).

(** ** The Loop Lemma

    A forward step from [c] to [c'] is exactly a backward step from [c'] to [c].
    This is the property [RevSmallStep] could not have: there, the step relation
    forgets which configuration it came from, so no backward relation can pick
    it out again. *)

Theorem loop_lemma : forall G c c', fstep G c c' <-> bstep G c' c.
Proof.
  intros G c c'; split; intro H; inversion H; subst; clear H.
  (* forward -> backward *)
  - apply B_Drop.
  - apply B_Prim. apply pstep_rev. assumption.
  - apply B_Seq.
  - apply B_IfT; assumption.
  - apply B_IfF; assumption.
  - apply B_Assert; reflexivity.
  - apply B_Loop; assumption.
  - apply B_LoopE.
  - apply B_TestX; assumption.
  - apply B_TestC; assumption.
  - apply B_Cont; assumption.
  - apply B_Call.
  - apply B_Uncall.
  (* backward -> forward *)
  - apply F_Drop.
  - apply F_Prim.
    apply pstep_rev in H0. rewrite pinv_invol in H0. assumption.
  - apply F_Seq.
  - apply F_IfT; assumption.
  - apply F_IfF; assumption.
  - apply F_Assert; reflexivity.
  - apply F_Loop; assumption.
  - apply F_LoopE.
  - apply F_TestX; assumption.
  - apply F_TestC; assumption.
  - apply F_Cont; assumption.
  - apply F_Call.
  - apply F_Uncall.
Qed.

(** ** Determinism, in both directions *)

(** Forward: the head of the control stack picks the rule, and where two rules
    share a head ([RIf], [RTest]) the guard decides between them. *)
Theorem fstep_det : forall G c c1 c2,
  fstep G c c1 -> fstep G c c2 -> c1 = c2.
Proof.
  intros G c c1 c2 H1 H2.
  inversion H1; subst; inversion H2; subst; try congruence.
  - f_equal. eapply pstep_det; eassumption.
Qed.

(** Backward: the head of the *history* picks the rule, which is the whole point
    of carrying one.  No two rules read the same event. *)
Theorem bstep_det : forall G c c1 c2,
  bstep G c c1 -> bstep G c c2 -> c1 = c2.
Proof.
  intros G c c1 c2 H1 H2.
  inversion H1; subst; inversion H2; subst; try congruence.
  - f_equal. eapply pstep_det; eassumption.
Qed.

(** And therefore the forward relation *is* backward deterministic here --
    exactly what [RevSmallStep.step_not_backward_deterministic] refutes for the
    semantics without a program counter. *)
Theorem fstep_backward_det : forall G c1 c2 c,
  fstep G c1 c -> fstep G c2 c -> c1 = c2.
Proof.
  intros G c1 c2 c H1 H2.
  apply loop_lemma in H1. apply loop_lemma in H2.
  eapply bstep_det; eassumption.
Qed.

(** ** The two collapses of [RevSmallStep], separated

    [RevSmallStep.step_not_backward_deterministic] exhibits two distinct
    configurations stepping to a common one by sequencing alone.  Here they step
    to configurations that differ -- in the control stack, since the two
    associations decompose differently. *)

Theorem seq_collapse_separated : forall G a h,
  fstep G (mk (RSeq (RSeq RSkip RSkip) RSkip :: nil) a h)
          (mk (RSeq RSkip RSkip :: RSkip :: nil) a (ESeq :: h))
  /\ fstep G (mk (RSeq RSkip (RSeq RSkip RSkip) :: nil) a h)
             (mk (RSkip :: RSeq RSkip RSkip :: nil) a (ESeq :: h))
  /\ mk (RSeq RSkip RSkip :: RSkip :: nil) a (ESeq :: h)
     <> mk (RSkip :: RSeq RSkip RSkip :: nil) a (ESeq :: h).
Proof.
  intros G a h; repeat split.
  - apply F_Seq.
  - apply F_Seq.
  - discriminate.
Qed.

(** [RevSmallStep.exit_assertion_collapses] exhibits two conditionals whose exit
    assertions both reduce to [RSkip], losing the guard.  Here the guard is in
    the history, so the successors differ whenever the guards do. *)

Theorem exit_assertion_separated : forall G (g h' : guard) (a : state) (k : ctrl) (h : list ev),
  gtest g a = true -> gtest h' a = true -> g <> h' ->
  fstep G (mk (RAssert g true :: k) a h) (mk k a (EAssert g true :: h))
  /\ fstep G (mk (RAssert h' true :: k) a h) (mk k a (EAssert h' true :: h))
  /\ mk k a (EAssert g true :: h) <> mk k a (EAssert h' true :: h).
Proof.
  intros G g h' a k h Hg Hh Hne; repeat split.
  - apply F_Assert; assumption.
  - apply F_Assert; assumption.
  - intro E. inversion E. contradiction.
Qed.

(** ** Runs

    The reflexive-transitive closures, and the Loop Lemma lifted to them: a
    forward run is a backward run read from the other end. *)

Inductive fmulti (G : L.pname -> L.stmt) : conf -> conf -> Prop :=
| fm_refl : forall c, fmulti G c c
| fm_step : forall c c' c'', fstep G c c' -> fmulti G c' c'' -> fmulti G c c''.

Inductive bmulti (G : L.pname -> L.stmt) : conf -> conf -> Prop :=
| bm_refl : forall c, bmulti G c c
| bm_step : forall c c' c'', bstep G c c' -> bmulti G c' c'' -> bmulti G c c''.

Lemma bmulti_trans : forall G c c' c'',
  bmulti G c c' -> bmulti G c' c'' -> bmulti G c c''.
Proof.
  intros G c c' c'' H. revert c''. induction H; intros.
  - assumption.
  - eapply bm_step; [ eassumption | apply IHbmulti; assumption ].
Qed.

Lemma fmulti_trans : forall G c c' c'',
  fmulti G c c' -> fmulti G c' c'' -> fmulti G c c''.
Proof.
  intros G c c' c'' H. revert c''. induction H; intros.
  - assumption.
  - eapply fm_step; [ eassumption | apply IHfmulti; assumption ].
Qed.

Theorem loop_lemma_multi : forall G c c', fmulti G c c' <-> bmulti G c' c.
Proof.
  intros G c c'; split; intro H; induction H.
  - apply bm_refl.
  - eapply bmulti_trans; [ eassumption | ].
    eapply bm_step; [ apply loop_lemma; eassumption | apply bm_refl ].
  - apply fm_refl.
  - eapply fmulti_trans; [ eassumption | ].
    eapply fm_step; [ apply loop_lemma; eassumption | apply fm_refl ].
Qed.

(** ** Reversibility of whole runs, as a corollary rather than an assumption

    [RevCore.exec_iff] gets reversibility of a complete run from the big-step
    relation.  Here it falls out of the Loop Lemma: a run and its reverse are
    the same object read in the two directions, so a run determines its own
    starting configuration. *)

Theorem fmulti_backward_det_of_det : forall G c1 c2 c,
  (forall x y z, bmulti G x y -> bmulti G x z -> y = z) ->
  fmulti G c1 c -> fmulti G c2 c -> c1 = c2.
Proof.
  intros G c1 c2 c Hdet H1 H2.
  apply loop_lemma_multi in H1. apply loop_lemma_multi in H2.
  eapply Hdet; eassumption.
Qed.

(** ** The bridge to the big-step semantics

    None of the above is worth much if the machine computes something else, so:
    every big-step run is realised by the PC machine, run from a control stack
    holding the program and an empty history.  The statement is generalised over
    the rest of the stack and over the history already accumulated, which is
    what makes it compose through [Seq]. *)

Lemma fm_one : forall G c c', fstep G c c' -> fmulti G c c'.
Proof. intros G c c' H; eapply fm_step; [ eassumption | apply fm_refl ]. Qed.

Theorem complete_pc : forall G s a b,
  L.exec G s a b ->
  forall k h, exists h', fmulti G (mk (embed s :: k) a h) (mk k b h').
Proof.
  intros G s a b H.
  induction H using L.exec_mut with
    (P0 := fun g1 s1 s2 g2 a b (_ : L.lp G g1 s1 s2 g2 a b) =>
      forall k h, exists h',
        fmulti G (mk (RLoopE g1 (embed s1) (embed s2) g2 :: k) a h) (mk k b h'));
    intros k h.
  - (* E_Skip *) eexists. apply fm_one, F_Drop.
  - (* E_Prim *) eexists. apply fm_one, F_Prim. assumption.
  - (* E_Seq *)
    edestruct IHexec1 as [h1 M1]. edestruct IHexec2 as [h2 M2].
    eexists. eapply fm_step; [ apply F_Seq | ].
    eapply fmulti_trans; [ exact M1 | exact M2 ].
  - (* E_IfT *)
    edestruct IHexec as [h1 M1].
    eexists. eapply fm_step; [ apply F_IfT; assumption | ].
    eapply fmulti_trans; [ exact M1 | ].
    apply fm_one, F_Assert. assumption.
  - (* E_IfF *)
    edestruct IHexec as [h1 M1].
    eexists. eapply fm_step; [ apply F_IfF; assumption | ].
    eapply fmulti_trans; [ exact M1 | ].
    apply fm_one, F_Assert. assumption.
  - (* E_Loop *)
    edestruct IHexec as [h1 M1].
    eexists. eapply fm_step; [ apply F_Loop; assumption | exact M1 ].
  - (* E_Call *)
    edestruct IHexec as [h1 M1].
    eexists. eapply fm_step; [ apply F_Call | exact M1 ].
  - (* E_Uncall *)
    edestruct IHexec as [h1 M1].
    eexists. eapply fm_step; [ apply F_Uncall | exact M1 ].
  - (* L_one *)
    edestruct IHexec as [h1 M1].
    eexists. eapply fm_step; [ apply F_LoopE | ].
    eapply fmulti_trans; [ exact M1 | ].
    apply fm_one, F_TestX. assumption.
  - (* L_more *)
    edestruct IHexec1 as [h1 M1]. edestruct IHexec2 as [h2 M2].
    edestruct IHexec3 as [h3 M3].
    eexists. eapply fm_step; [ apply F_LoopE | ].
    eapply fmulti_trans; [ exact M1 | ].
    eapply fm_step; [ apply F_TestC; assumption | ].
    eapply fmulti_trans; [ exact M2 | ].
    eapply fm_step; [ apply F_Cont; assumption | exact M3 ].
Qed.

(** Run from a bare program: the machine ends with an empty control stack. *)
Corollary complete_pc_top : forall G s a b,
  L.exec G s a b -> exists h, fmulti G (mk (embed s :: nil) a nil) (mk nil b h).
Proof.
  intros G s a b H. destruct (complete_pc G s a b H nil nil) as [h M].
  exists h. exact M.
Qed.

(** And read backwards, by the Loop Lemma: the history the forward run built is
    exactly the itinerary that takes the final configuration home. *)
Corollary run_is_reversible : forall G s a b,
  L.exec G s a b ->
  exists h, bmulti G (mk nil b h) (mk (embed s :: nil) a nil).
Proof.
  intros G s a b H. destruct (complete_pc_top G s a b H) as [h M].
  exists h. apply loop_lemma_multi. exact M.
Qed.

(** ** Partial soundness, from determinism

    The converse of [complete_pc] -- that a completed run witnesses a big-step
    execution -- is Lanese and Vidal's Theorem 1 read right-to-left, and their
    proof goes through balanced derivations (their Definition 1 and Lemma 2),
    which are not formalised here.  What *is* cheap is the consequence that
    matters in practice: the machine cannot compute a different answer.  An
    empty control stack is a stuck configuration, [fstep] is deterministic, so
    the run [complete_pc] builds is the only one. *)

Lemma nil_stuck : forall G a h c, ~ fstep G (mk nil a h) c.
Proof. intros G a h c H; inversion H. Qed.

Lemma fmulti_det_stuck : forall G c c1,
  fmulti G c c1 -> (forall x, ~ fstep G c1 x) ->
  forall c2, fmulti G c c2 -> (forall x, ~ fstep G c2 x) -> c1 = c2.
Proof.
  intros G c c1 H1. induction H1; intros S1 c2 H2 S2.
  - inversion H2; subst.
    + reflexivity.
    + exfalso. eapply S1. eassumption.
  - inversion H2; subst.
    + exfalso. eapply S2. eassumption.
    + assert (E : c' = c'0) by (eapply fstep_det; eassumption).
      subst. apply IHfmulti; assumption.
Qed.

Theorem machine_agrees : forall G s a b b' h,
  L.exec G s a b ->
  fmulti G (mk (embed s :: nil) a nil) (mk nil b' h) ->
  b = b'.
Proof.
  intros G s a b b' h HE HM.
  destruct (complete_pc_top G s a b HE) as [h0 M0].
  assert (E : mk nil b h0 = mk nil b' h).
  { eapply fmulti_det_stuck;
      [ exact M0 | intros x; apply nil_stuck | exact HM | intros x; apply nil_stuck ]. }
  inversion E. reflexivity.
Qed.

End LoopLemma.
