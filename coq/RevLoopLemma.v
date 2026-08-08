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
    [exit_assertion_separated].

    The second half of the file follows the paper's other thread: *balanced
    derivations* (their Definition 1), the decomposition lemma that cuts one
    (their Lemma 2), and from those the equivalence with the big-step semantics
    in both directions (their Theorem 1) -- [exec_iff_fbal] at any control
    stack, [exec_iff_pc] at the top. *)

From Stdlib Require Import List Arith Lia Wf_nat.
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
    proof goes through balanced derivations (their Definition 1 and Lemma 2).
    That route is taken in full below, in [sound_pc] and [exec_iff_pc].  What is
    proved here first is the consequence that matters in practice and costs
    nothing: the machine cannot compute a different answer.  An empty control
    stack is a stuck configuration, [fstep] is deterministic, so the run
    [complete_pc] builds is the only one.  [exec_iff_pc] subsumes this, but the
    two arguments are independent, so both are kept. *)

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

(** ** Balanced derivations, and the converse -- Lanese and Vidal's Theorem 1

    [complete_pc] is the "only if" half of their Theorem 1.  The "if" half --
    that a run of the machine witnesses a big-step execution -- goes, in the
    paper, through *balanced derivations* (their Definition 1) and their
    Lemma 2.  A derivation is balanced with respect to a control stack [k] when
    it never steps from a configuration whose control has already shrunk to [k]:
    it runs whatever was pushed on top of [k], and stops the moment [k] is
    uncovered again.

    Why [fmulti] will not do: [fmulti G (mk (s :: k) a h) (mk k b h')] does not
    rule out a run that drops below [k] and builds back up, since [F_Drop]
    shrinks the stack.  Without pinning every intermediate configuration above
    [k] the decomposition below has nothing to cut at.  That is exactly why the
    paper introduces Definition 1.

    The relation is indexed by the number of steps, because the decomposition
    cuts a run into two shorter ones and recurses on *both* -- structural
    induction on the derivation never sees the pieces. *)

Definition suffix (k c : ctrl) : Prop := exists j, c = j ++ k.

Lemma suffix_refl : forall k, suffix k k.
Proof. intro k; exists nil; reflexivity. Qed.

Lemma suffix_cons : forall k x c, suffix k c -> suffix k (x :: c).
Proof. intros k x c [j E]; exists (x :: j); simpl; rewrite E; reflexivity. Qed.

Lemma suffix_len : forall k c, suffix k c -> length k <= length c.
Proof. intros k c [j E]; subst c; induction j; simpl; lia. Qed.

Lemma suffix_uncons : forall k x c,
  suffix k (x :: c) -> length k <= length c -> suffix k c.
Proof.
  intros k x c [j E] Hl; destruct j as [| y j'].
  - simpl in E; subst; simpl in Hl; lia.
  - simpl in E; inversion E; subst; exists j'; reflexivity.
Qed.

Lemma suffix_eq : forall k c, suffix k c -> length c <= length k -> c = k.
Proof.
  intros k c [j E] Hl; subst c; destruct j as [| x j']; [ reflexivity | ].
  exfalso; simpl in Hl.
  assert (length k <= length (j' ++ k)) by (apply suffix_len; exists j'; reflexivity).
  lia.
Qed.

Lemma ctrl_cons_neq : forall (x : rs) (k : ctrl), x :: k <> k.
Proof.
  intros x k E.
  assert (length (x :: k) = length k) by (rewrite E; reflexivity).
  simpl in *; lia.
Qed.

(** A step only ever rewrites the head of the control stack, so anything sitting
    strictly below the head survives it.  This is what makes "above [k]" an
    invariant, and it is the one place the shape of all thirteen rules is used. *)
Lemma fstep_suffix : forall G c c' k0,
  fstep G c c' -> suffix k0 (cctl c) -> length k0 < length (cctl c) ->
  suffix k0 (cctl c').
Proof.
  intros G c c' k0 H Hs Hl.
  inversion H; subst; simpl in *;
    assert (Hk : suffix k0 k) by (eapply suffix_uncons; [ exact Hs | lia ]);
    repeat apply suffix_cons; exact Hk.
Qed.

(** *** Definition 1: balanced derivations *)

Inductive fbaln (G : L.pname -> L.stmt) (k : ctrl) : nat -> conf -> conf -> Prop :=
| fbn_done : forall a h, fbaln G k 0 (mk k a h) (mk k a h)
| fbn_step : forall n c c' c'',
    fstep G c c' -> length k < length (cctl c) ->
    fbaln G k n c' c'' -> fbaln G k (S n) c c''.

Definition fbal (G : L.pname -> L.stmt) (k : ctrl) (c c' : conf) : Prop :=
  exists n, fbaln G k n c c'.

(** A three-step balanced derivation, run by hand: [Seq Skip Skip] decomposes
    onto the stack, then drops twice, and the history records exactly that. *)
Example fbal_seq_skip : forall G a,
  fbaln G nil 3 (mk (embed (L.Seq L.Skip L.Skip) :: nil) a nil)
                (mk nil a (EDrop :: EDrop :: ESeq :: nil)).
Proof.
  intros G a; simpl.
  eapply fbn_step; [ apply F_Seq | simpl; lia | ].
  eapply fbn_step; [ apply F_Drop | simpl; lia | ].
  eapply fbn_step; [ apply F_Drop | simpl; lia | ].
  apply fbn_done.
Qed.

(** *** Plumbing *)

Lemma fbaln_bottom : forall G k n a h b h',
  fbaln G k n (mk k a h) (mk k b h') -> a = b.
Proof.
  intros G k n a h b h' H; inversion H; subst.
  - congruence.
  - exfalso; simpl in *; lia.
Qed.

Lemma fbaln_pop : forall G k n x a h c'',
  fbaln G k n (mk (x :: k) a h) c'' ->
  exists m c', n = S m /\ fstep G (mk (x :: k) a h) c' /\ fbaln G k m c' c''.
Proof.
  intros G k n x a h c'' H; inversion H; subst.
  - exfalso; eapply ctrl_cons_neq;
      solve [ eassumption | symmetry; eassumption ].
  - eexists; eexists; split; [ reflexivity | split; eassumption ].
Qed.

(** Concatenation: a derivation balanced at a deeper level [k0] can be followed
    by one balanced at [k], because "above [k0]" implies "above [k]". *)
Lemma fbaln_app : forall G k0 k n1 c m,
  fbaln G k0 n1 c m -> length k <= length k0 ->
  forall n2 c'', fbaln G k n2 m c'' -> fbaln G k (n1 + n2) c c''.
Proof.
  intros G k0 k n1 c m H Hle; induction H; intros n2 cf H2.
  - exact H2.
  - simpl; eapply fbn_step; [ eassumption | lia | apply IHfbaln; assumption ].
Qed.

(** *** Lemma 2: cutting a balanced derivation

    A derivation balanced at [k] that starts strictly above an intermediate
    level [k0] must pass through [k0] exactly -- it cannot jump past it, since
    a step preserves "[k0] is a suffix", and a configuration at [k0]'s length
    with [k0] as a suffix *is* [k0].  Cutting there splits the step count. *)
Lemma fbaln_cut : forall G k n c c'',
  fbaln G k n c c'' ->
  forall k0, suffix k k0 -> suffix k0 (cctl c) -> length k0 < length (cctl c) ->
  exists n1 n2 b1 h1,
    n = n1 + n2
    /\ fbaln G k0 n1 c (mk k0 b1 h1)
    /\ fbaln G k n2 (mk k0 b1 h1) c''.
Proof.
  intros G k n c c'' H; induction H; intros k0 Hsk Hs0 Hl.
  - exfalso; simpl in Hl; apply suffix_len in Hsk; lia.
  - assert (Hs' : suffix k0 (cctl c')) by (eapply fstep_suffix; eassumption).
    destruct (le_lt_dec (length (cctl c')) (length k0)) as [Hle | Hgt].
    + assert (Ec : cctl c' = k0) by (apply suffix_eq; assumption).
      destruct c' as [kk aa hh]; simpl in Ec; subst kk.
      exists 1, n, aa, hh; split; [ reflexivity | split ].
      * eapply fbn_step; [ eassumption | assumption | apply fbn_done ].
      * assumption.
    + destruct (IHfbaln k0 Hsk Hs' Hgt) as [n1 [n2 [b1 [h1 [Em [M1 M2]]]]]].
      exists (S n1), n2, b1, h1; split; [ simpl; rewrite Em; reflexivity | split ].
      * eapply fbn_step; [ eassumption | assumption | exact M1 ].
      * exact M2.
Qed.

(** The only shape the decomposition below ever needs: one runtime statement
    pushed on top of the level it will return to. *)
Lemma fbaln_cut1 : forall G k k0 x n a h c'',
  fbaln G k n (mk (x :: k0) a h) c'' -> suffix k k0 ->
  exists n1 n2 b1 h1,
    n = n1 + n2
    /\ fbaln G k0 n1 (mk (x :: k0) a h) (mk k0 b1 h1)
    /\ fbaln G k n2 (mk k0 b1 h1) c''.
Proof.
  intros G k k0 x n a h c'' H Hsk.
  eapply fbaln_cut; try eassumption.
  - apply suffix_cons, suffix_refl.
  - simpl; lia.
Qed.

(** An exit assertion is a whole balanced derivation on its own: one step, which
    can only be [F_Assert], and then the stack is uncovered. *)
Lemma fbaln_assert : forall G k n g v a h b h',
  fbaln G k n (mk (RAssert g v :: k) a h) (mk k b h') -> a = b /\ gtest g b = v.
Proof.
  intros G k n g v a h b h' H.
  destruct (fbaln_pop _ _ _ _ _ _ _ H) as [m [c' [_ [Hst HR]]]].
  inversion Hst; subst.
  apply fbaln_bottom in HR; subst; split; congruence.
Qed.

(** *** Soundness

    The converse of [complete_pc], by strong induction on the number of steps.
    The loop clause is the [P0] of [complete_pc] read backwards, and has to be
    proved simultaneously: a balanced derivation from [RLoopE] is a [lp]. *)
Lemma sound_bal_n : forall n,
  (forall G k s a b h h',
     fbaln G k n (mk (embed s :: k) a h) (mk k b h') -> L.exec G s a b)
  /\ (forall G k g1 s1 s2 g2 a b h h',
     fbaln G k n (mk (RLoopE g1 (embed s1) (embed s2) g2 :: k) a h) (mk k b h') ->
     L.lp G g1 s1 s2 g2 a b).
Proof.
  intro n; induction n as [n IH] using (well_founded_ind lt_wf); split.
  - (* statements *)
    intros G k s a b h h' HB.
    destruct (fbaln_pop _ _ _ _ _ _ _ HB) as [m [c1 [En [Hst HR]]]]; subst n.
    destruct s as [ | p | s1 s2 | g1 s1 s2 g2 | g1 s1 s2 g2 | p | p ]; simpl in Hst.
    + (* Skip *)
      inversion Hst; subst.
      apply fbaln_bottom in HR; subst; apply L.E_Skip.
    + (* Prim *)
      inversion Hst; subst.
      apply fbaln_bottom in HR; subst; apply L.E_Prim; assumption.
    + (* Seq *)
      inversion Hst; subst.
      assert (Hsf : suffix k (embed s2 :: k)) by (apply suffix_cons, suffix_refl).
      destruct (fbaln_cut1 _ _ _ _ _ _ _ _ HR Hsf)
        as [n1 [n2 [b1 [h1 [Em [M1 M2]]]]]].
      apply (proj1 (IH n1 ltac:(lia))) in M1.
      apply (proj1 (IH n2 ltac:(lia))) in M2.
      eapply L.E_Seq; eassumption.
    + (* If *)
      inversion Hst; subst.
      * (* then *)
        assert (Hsf : suffix k (RAssert g2 true :: k)) by (apply suffix_cons, suffix_refl).
        destruct (fbaln_cut1 _ _ _ _ _ _ _ _ HR Hsf)
          as [n1 [n2 [b1 [h1 [Em [M1 M2]]]]]].
        apply (proj1 (IH n1 ltac:(lia))) in M1.
        destruct (fbaln_assert _ _ _ _ _ _ _ _ _ M2) as [Eb Hg2]; subst b1.
        apply L.E_IfT; assumption.
      * (* else *)
        assert (Hsf : suffix k (RAssert g2 false :: k)) by (apply suffix_cons, suffix_refl).
        destruct (fbaln_cut1 _ _ _ _ _ _ _ _ HR Hsf)
          as [n1 [n2 [b1 [h1 [Em [M1 M2]]]]]].
        apply (proj1 (IH n1 ltac:(lia))) in M1.
        destruct (fbaln_assert _ _ _ _ _ _ _ _ _ M2) as [Eb Hg2]; subst b1.
        apply L.E_IfF; assumption.
    + (* Loop *)
      inversion Hst; subst.
      apply (proj2 (IH m ltac:(lia))) in HR.
      apply L.E_Loop; assumption.
    + (* Call *)
      inversion Hst; subst.
      apply (proj1 (IH m ltac:(lia))) in HR.
      apply L.E_Call; assumption.
    + (* Uncall *)
      inversion Hst; subst.
      apply (proj1 (IH m ltac:(lia))) in HR.
      apply L.E_Uncall; assumption.
  - (* loop bodies *)
    intros G k g1 s1 s2 g2 a b h h' HB.
    destruct (fbaln_pop _ _ _ _ _ _ _ HB) as [m [c1 [En [Hst HR]]]]; subst n.
    inversion Hst; subst.
    assert (Hsf : suffix k (RTest g1 (embed s1) (embed s2) g2 :: k))
      by (apply suffix_cons, suffix_refl).
    destruct (fbaln_cut1 _ _ _ _ _ _ _ _ HR Hsf)
      as [n1 [n2 [b1 [h1 [Em [M1 M2]]]]]].
    apply (proj1 (IH n1 ltac:(lia))) in M1.
    destruct (fbaln_pop _ _ _ _ _ _ _ M2) as [m2 [c2 [En2 [Hst2 HR2]]]].
    inversion Hst2; subst.
    + (* the loop exits: L_one *)
      apply fbaln_bottom in HR2; subst.
      apply L.L_one; assumption.
    + (* the loop continues: L_more *)
      assert (Hsf2 : suffix k (RCont g1 (embed s1) (embed s2) g2 :: k))
        by (apply suffix_cons, suffix_refl).
      destruct (fbaln_cut1 _ _ _ _ _ _ _ _ HR2 Hsf2)
        as [n3 [n4 [b2 [h2 [Em2 [M3 M4]]]]]].
      apply (proj1 (IH n3 ltac:(lia))) in M3.
      destruct (fbaln_pop _ _ _ _ _ _ _ M4) as [m4 [c4 [En4 [Hst4 HR4]]]].
      inversion Hst4; subst.
      apply (proj2 (IH m4 ltac:(lia))) in HR4.
      eapply L.L_more; eassumption.
Qed.

Theorem sound_pc : forall G k s a b h h',
  fbal G k (mk (embed s :: k) a h) (mk k b h') -> L.exec G s a b.
Proof.
  intros G k s a b h h' [n HB].
  exact (proj1 (sound_bal_n n) G k s a b h h' HB).
Qed.

(** *** Completeness in balanced form

    [complete_pc] builds a run; the run it builds is in fact balanced, at every
    level of the stack.  This is the paper's Lemma 1 with Definition 1 attached,
    and it is what makes the equivalence an iff at every [k], not just at the
    top.  The proof is [complete_pc]'s, with [fbaln_app] in place of
    [fmulti_trans]: the obligation each concatenation adds is that the level
    being returned to is no deeper than the one just finished. *)
Theorem complete_pc_bal : forall G s a b,
  L.exec G s a b ->
  forall k h, exists n h', fbaln G k n (mk (embed s :: k) a h) (mk k b h').
Proof.
  intros G s a b H.
  induction H using L.exec_mut with
    (P0 := fun g1 s1 s2 g2 a b (_ : L.lp G g1 s1 s2 g2 a b) =>
      forall k h, exists n h',
        fbaln G k n (mk (RLoopE g1 (embed s1) (embed s2) g2 :: k) a h) (mk k b h'));
    intros k h.
  - (* E_Skip *)
    do 2 eexists; eapply fbn_step; [ apply F_Drop | simpl; lia | apply fbn_done ].
  - (* E_Prim *)
    do 2 eexists.
    eapply fbn_step; [ apply F_Prim; eassumption | simpl; lia | apply fbn_done ].
  - (* E_Seq *)
    destruct (IHexec1 (embed s2 :: k) (ESeq :: h)) as [n1 [h1 M1]].
    destruct (IHexec2 k h1) as [n2 [h2 M2]].
    do 2 eexists.
    eapply fbn_step; [ apply F_Seq | simpl; lia | ].
    eapply fbaln_app; [ exact M1 | simpl; lia | exact M2 ].
  - (* E_IfT *)
    destruct (IHexec (RAssert g2 true :: k)
                     (EIf g1 (embed s1) (embed s2) g2 true :: h)) as [n1 [h1 M1]].
    do 2 eexists.
    eapply fbn_step; [ apply F_IfT; assumption | simpl; lia | ].
    eapply fbaln_app; [ exact M1 | simpl; lia | ].
    eapply fbn_step; [ apply F_Assert; eassumption | simpl; lia | apply fbn_done ].
  - (* E_IfF *)
    destruct (IHexec (RAssert g2 false :: k)
                     (EIf g1 (embed s1) (embed s2) g2 false :: h)) as [n1 [h1 M1]].
    do 2 eexists.
    eapply fbn_step; [ apply F_IfF; assumption | simpl; lia | ].
    eapply fbaln_app; [ exact M1 | simpl; lia | ].
    eapply fbn_step; [ apply F_Assert; eassumption | simpl; lia | apply fbn_done ].
  - (* E_Loop *)
    destruct (IHexec k (ELoopIn g1 (embed s1) (embed s2) g2 :: h)) as [n1 [h1 M1]].
    do 2 eexists.
    eapply fbn_step; [ apply F_Loop; assumption | simpl; lia | exact M1 ].
  - (* E_Call *)
    destruct (IHexec k (ECall p :: h)) as [n1 [h1 M1]].
    do 2 eexists.
    eapply fbn_step; [ apply F_Call | simpl; lia | exact M1 ].
  - (* E_Uncall *)
    destruct (IHexec k (EUncall p :: h)) as [n1 [h1 M1]].
    do 2 eexists.
    eapply fbn_step; [ apply F_Uncall | simpl; lia | exact M1 ].
  - (* L_one *)
    destruct (IHexec (RTest g1 (embed s1) (embed s2) g2 :: k)
                     (ELoopE g1 (embed s1) (embed s2) g2 :: h)) as [n1 [h1 M1]].
    do 2 eexists.
    eapply fbn_step; [ apply F_LoopE | simpl; lia | ].
    eapply fbaln_app; [ exact M1 | simpl; lia | ].
    eapply fbn_step; [ apply F_TestX; assumption | simpl; lia | apply fbn_done ].
  - (* L_more *)
    destruct (IHexec1 (RTest g1 (embed s1) (embed s2) g2 :: k)
                      (ELoopE g1 (embed s1) (embed s2) g2 :: h)) as [n1 [h1 M1]].
    destruct (IHexec2 (RCont g1 (embed s1) (embed s2) g2 :: k)
                      (ETestC g1 (embed s1) (embed s2) g2 :: h1)) as [n2 [h2 M2]].
    destruct (IHexec3 k (ECont g1 (embed s1) (embed s2) g2 :: h2)) as [n3 [h3 M3]].
    do 2 eexists.
    eapply fbn_step; [ apply F_LoopE | simpl; lia | ].
    eapply fbaln_app; [ exact M1 | simpl; lia | ].
    eapply fbn_step; [ apply F_TestC; assumption | simpl; lia | ].
    eapply fbaln_app; [ exact M2 | simpl; lia | ].
    eapply fbn_step; [ apply F_Cont; assumption | simpl; lia | exact M3 ].
Qed.

(** *** Theorem 1, both directions

    At any level of the control stack: a big-step execution of [s] is exactly a
    balanced derivation that runs [s] off the top of the stack. *)
Theorem exec_iff_fbal : forall G k s a b h,
  L.exec G s a b <-> exists h', fbal G k (mk (embed s :: k) a h) (mk k b h').
Proof.
  intros G k s a b h; split.
  - intro H. destruct (complete_pc_bal G s a b H k h) as [n [h' M]].
    exists h', n; exact M.
  - intros [h' M]. eapply sound_pc; exact M.
Qed.

(** At the top of the stack, balancedness is free: an empty control stack is
    stuck, so no run can drop below it and come back.  That collapses the
    balanced statement to the paper's own, which is about [→*]. *)
Lemma fmulti_nil_fbaln : forall G c b h,
  fmulti G c (mk nil b h) -> exists n, fbaln G nil n c (mk nil b h).
Proof.
  intros G c b h H.
  remember (mk nil b h) as cf eqn:Ecf; revert b h Ecf.
  induction H; intros bb hh Ecf; subst.
  - exists 0; apply fbn_done.
  - destruct (IHfmulti bb hh eq_refl) as [n Hn].
    exists (S n); eapply fbn_step; [ eassumption | | eassumption ].
    destruct c as [kk aa hh']; simpl.
    destruct kk as [| x kk']; [ exfalso; eapply nil_stuck; eassumption | simpl; lia ].
Qed.

(** **Theorem 1** of Lanese and Vidal: [ϵ ⊢ s ⇓ σ] iff [⟨ϵ,s,[]⟩ →* ⟨σ,skip,[]⟩].
    Their [skip] with an empty continuation stack is our empty control stack. *)
Theorem exec_iff_pc : forall G s a b,
  L.exec G s a b <-> exists h, fmulti G (mk (embed s :: nil) a nil) (mk nil b h).
Proof.
  intros G s a b; split.
  - apply complete_pc_top.
  - intros [h M]. apply fmulti_nil_fbaln in M. destruct M as [n Hn].
    exact (proj1 (sound_bal_n n) G nil s a b nil h Hn).
Qed.

(** The example above, decoded: a balanced derivation is read back as the
    big-step execution it came from. *)
Example sound_seq_skip : forall G a, L.exec G (L.Seq L.Skip L.Skip) a a.
Proof.
  intros G a. apply (sound_pc G nil _ a a nil (EDrop :: EDrop :: ESeq :: nil)).
  exists 3; apply fbal_seq_skip.
Qed.

End LoopLemma.
