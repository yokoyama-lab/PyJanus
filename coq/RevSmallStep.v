(** * RevSmallStep.v — a small-step semantics, equivalent to the big-step one

    Mechanizing the heart of "A Small-Step Semantics for Janus" (RC 2024,
    hal-04610285) for the generic framework: we give a structural operational
    (small-step) semantics for the reversible structured language of
    [RevCore.RevLang] and prove it **equivalent** to the big-step [exec].

    Runtime configurations are [(rs, state)] where [rs] extends the source
    statements with the *runtime markers* needed to make control flow
    single-step:

      - [RAssert g v]                  — check [gtest g a = v], then finish;
        this realizes the *exit assertions* of [if] (both branches) at the
        point where the branch body has completed;
      - [RLoopE]/[RTest]/[RCont]       — the three phases of one loop turn
        (run [s1]; test [g2]: exit / run [s2]; assert [¬ g1]; repeat).

    This file proves **completeness** ([exec ⇒ multistep]); soundness (the
    converse, via a reverse simulation) is the next step. *)

From Stdlib Require Import ZArith.
Require Import RevCore.

Module SmallStep (P : REV_PRIM).
Import P.
Module L := RevLang P.

(** ** Runtime statements and the embedding of source statements. *)
Inductive rs :=
| RSkip
| RPrim   (p : prim)
| RSeq    (a b : rs)
| RAssert (g : guard) (v : bool)
| RIf     (g1 : guard) (a b : rs) (g2 : guard)
| RLoop   (g1 : guard) (a b : rs) (g2 : guard)
| RLoopE  (g1 : guard) (a b : rs) (g2 : guard)   (* entered loop: do s1, then test *)
| RTest   (g1 : guard) (a b : rs) (g2 : guard)   (* s1 done: test g2 *)
| RCont   (g1 : guard) (a b : rs) (g2 : guard)   (* s2 done: assert ¬g1, repeat *)
| RCall   (p : L.pname)
| RUncall (p : L.pname).

Fixpoint embed (s : L.stmt) : rs :=
  match s with
  | L.Skip => RSkip
  | L.Prim p => RPrim p
  | L.Seq a b => RSeq (embed a) (embed b)
  | L.If g1 a b g2 => RIf g1 (embed a) (embed b) g2
  | L.Loop g1 a b g2 => RLoop g1 (embed a) (embed b) g2
  | L.Call p => RCall p
  | L.Uncall p => RUncall p
  end.

(** ** One small step. *)
Inductive step (Γ : L.pname -> L.stmt) : rs -> state -> rs -> state -> Prop :=
| S_Prim : forall p a b, pstep p a b -> step Γ (RPrim p) a RSkip b
| S_SeqDone : forall s a, step Γ (RSeq RSkip s) a s a
| S_SeqStep : forall s a s' a' k,
    step Γ s a s' a' -> step Γ (RSeq s k) a (RSeq s' k) a'
| S_IfT : forall g1 s1 s2 g2 a,
    gtest g1 a = true -> step Γ (RIf g1 s1 s2 g2) a (RSeq s1 (RAssert g2 true)) a
| S_IfF : forall g1 s1 s2 g2 a,
    gtest g1 a = false -> step Γ (RIf g1 s1 s2 g2) a (RSeq s2 (RAssert g2 false)) a
| S_Assert : forall g v a, gtest g a = v -> step Γ (RAssert g v) a RSkip a
| S_Loop : forall g1 s1 s2 g2 a,
    gtest g1 a = true -> step Γ (RLoop g1 s1 s2 g2) a (RLoopE g1 s1 s2 g2) a
| S_LoopE : forall g1 s1 s2 g2 a,
    step Γ (RLoopE g1 s1 s2 g2) a (RSeq s1 (RTest g1 s1 s2 g2)) a
| S_TestExit : forall g1 s1 s2 g2 a,
    gtest g2 a = true -> step Γ (RTest g1 s1 s2 g2) a RSkip a
| S_TestCont : forall g1 s1 s2 g2 a,
    gtest g2 a = false -> step Γ (RTest g1 s1 s2 g2) a (RSeq s2 (RCont g1 s1 s2 g2)) a
| S_Cont : forall g1 s1 s2 g2 a,
    gtest g1 a = false -> step Γ (RCont g1 s1 s2 g2) a (RLoopE g1 s1 s2 g2) a
| S_Call : forall p a, step Γ (RCall p) a (embed (Γ p)) a
| S_Uncall : forall p a, step Γ (RUncall p) a (embed (L.invert (Γ p))) a.

(** ** Reflexive–transitive closure. *)
Inductive multistep (Γ : L.pname -> L.stmt) : rs -> state -> rs -> state -> Prop :=
| ms_refl : forall r a, multistep Γ r a r a
| ms_step : forall r a r' a' r'' a'',
    step Γ r a r' a' -> multistep Γ r' a' r'' a'' -> multistep Γ r a r'' a''.

Lemma ms_trans : forall Γ r a r' a' r'' a'',
  multistep Γ r a r' a' -> multistep Γ r' a' r'' a'' -> multistep Γ r a r'' a''.
Proof.
  intros Γ r a r' a' r'' a'' H. revert r'' a''.
  induction H; intros.
  - assumption.
  - eapply ms_step; [ eassumption | apply IHmultistep; assumption ].
Qed.

(** Sequencing congruence: stepping the head carries through [RSeq _ k]. *)
Lemma ms_seq : forall Γ s a s' a' k,
  multistep Γ s a s' a' -> multistep Γ (RSeq s k) a (RSeq s' k) a'.
Proof.
  intros Γ s a s' a' k H. induction H.
  - apply ms_refl.
  - eapply ms_step; [ apply S_SeqStep; eassumption | assumption ].
Qed.

(** ** Completeness: every big-step run is realized by the small-step machine. *)
Theorem complete : forall Γ s a b,
  L.exec Γ s a b -> multistep Γ (embed s) a RSkip b.
Proof.
  intros Γ s a b H.
  induction H using L.exec_mut with
    (P0 := fun g1 s1 s2 g2 a b (_ : L.lp Γ g1 s1 s2 g2 a b) =>
      multistep Γ (RLoopE g1 (embed s1) (embed s2) g2) a RSkip b).
  - (* E_Skip *) apply ms_refl.
  - (* E_Prim *) eapply ms_step; [ apply S_Prim; eassumption | apply ms_refl ].
  - (* E_Seq *) simpl.
    eapply ms_trans; [ eapply ms_seq; exact IHexec1 | ].
    eapply ms_step; [ apply S_SeqDone | exact IHexec2 ].
  - (* E_IfT *) simpl.
    eapply ms_step; [ apply S_IfT; eassumption | ].
    eapply ms_trans; [ eapply ms_seq; exact IHexec | ].
    eapply ms_step; [ apply S_SeqDone | ].
    eapply ms_step; [ apply S_Assert; eassumption | apply ms_refl ].
  - (* E_IfF *) simpl.
    eapply ms_step; [ apply S_IfF; eassumption | ].
    eapply ms_trans; [ eapply ms_seq; exact IHexec | ].
    eapply ms_step; [ apply S_SeqDone | ].
    eapply ms_step; [ apply S_Assert; eassumption | apply ms_refl ].
  - (* E_Loop *) simpl.
    eapply ms_step; [ apply S_Loop; eassumption | exact IHexec ].
  - (* E_Call *) simpl.
    eapply ms_step; [ apply S_Call | exact IHexec ].
  - (* E_Uncall *) simpl.
    eapply ms_step; [ apply S_Uncall | exact IHexec ].
  - (* L_one *)
    eapply ms_step; [ apply S_LoopE | ].
    eapply ms_trans; [ eapply ms_seq; exact IHexec | ].
    eapply ms_step; [ apply S_SeqDone | ].
    eapply ms_step; [ apply S_TestExit; eassumption | apply ms_refl ].
  - (* L_more *)
    eapply ms_step; [ apply S_LoopE | ].
    eapply ms_trans; [ eapply ms_seq; exact IHexec1 | ].
    eapply ms_step; [ apply S_SeqDone | ].
    eapply ms_step; [ apply S_TestCont; eassumption | ].
    eapply ms_trans; [ eapply ms_seq; exact IHexec2 | ].
    eapply ms_step; [ apply S_SeqDone | ].
    eapply ms_step; [ apply S_Cont; eassumption | exact IHexec3 ].
Qed.

(* ===================================================================== *)
(** ** Soundness: every terminating small-step run is a big-step run.

    We give a big-step semantics [bexec] on runtime statements (the loop
    markers [RLoopE]/[RTest]/[RCont] re-express the phases of [lp]), show each
    [step] preserves [bexec] backward ([sim]), lift this along [multistep], and
    finally decode [bexec (embed s)] back to [exec]. *)

Inductive bexec (Γ : L.pname -> L.stmt) : rs -> state -> state -> Prop :=
| BSkip : forall a, bexec Γ RSkip a a
| BPrim : forall p a b, pstep p a b -> bexec Γ (RPrim p) a b
| BSeq  : forall r1 r2 a m b, bexec Γ r1 a m -> bexec Γ r2 m b -> bexec Γ (RSeq r1 r2) a b
| BAssert : forall g v a, gtest g a = v -> bexec Γ (RAssert g v) a a
| BIfT : forall g1 s1 s2 g2 a b,
    gtest g1 a = true -> bexec Γ s1 a b -> gtest g2 b = true -> bexec Γ (RIf g1 s1 s2 g2) a b
| BIfF : forall g1 s1 s2 g2 a b,
    gtest g1 a = false -> bexec Γ s2 a b -> gtest g2 b = false -> bexec Γ (RIf g1 s1 s2 g2) a b
| BLoop : forall g1 s1 s2 g2 a b,
    gtest g1 a = true -> bexec Γ (RLoopE g1 s1 s2 g2) a b -> bexec Γ (RLoop g1 s1 s2 g2) a b
| BLoopE : forall g1 s1 s2 g2 a m b,
    bexec Γ s1 a m -> bexec Γ (RTest g1 s1 s2 g2) m b -> bexec Γ (RLoopE g1 s1 s2 g2) a b
| BTestExit : forall g1 s1 s2 g2 a,
    gtest g2 a = true -> bexec Γ (RTest g1 s1 s2 g2) a a
| BTestCont : forall g1 s1 s2 g2 a m b,
    gtest g2 a = false -> bexec Γ s2 a m -> bexec Γ (RCont g1 s1 s2 g2) m b ->
    bexec Γ (RTest g1 s1 s2 g2) a b
| BCont : forall g1 s1 s2 g2 a b,
    gtest g1 a = false -> bexec Γ (RLoopE g1 s1 s2 g2) a b -> bexec Γ (RCont g1 s1 s2 g2) a b
| BCall : forall p a b, bexec Γ (embed (Γ p)) a b -> bexec Γ (RCall p) a b
| BUncall : forall p a b, bexec Γ (embed (L.invert (Γ p))) a b -> bexec Γ (RUncall p) a b.

(** A single step preserves [bexec] backward (reverse simulation). *)
Lemma sim : forall Γ r a r' a',
  step Γ r a r' a' -> forall b, bexec Γ r' a' b -> bexec Γ r a b.
Proof.
  intros Γ r a r' a' Hstep; induction Hstep; intros b0 Hb.
  - (* S_Prim *) inversion Hb; subst; apply BPrim; assumption.
  - (* S_SeqDone *) eapply BSeq; [ apply BSkip | exact Hb ].
  - (* S_SeqStep *) inversion Hb; subst.
    match goal with
    | H1 : bexec Γ s' a' ?m, H2 : bexec Γ k ?m b0 |- _ =>
        eapply BSeq; [ apply IHHstep; exact H1 | exact H2 ]
    end.
  - (* S_IfT *) inversion Hb; subst.
    match goal with H2 : bexec Γ (RAssert _ _) _ _ |- _ => inversion H2; subst end.
    apply BIfT; assumption.
  - (* S_IfF *) inversion Hb; subst.
    match goal with H2 : bexec Γ (RAssert _ _) _ _ |- _ => inversion H2; subst end.
    apply BIfF; assumption.
  - (* S_Assert *) inversion Hb; subst; apply BAssert; first [ assumption | reflexivity ].
  - (* S_Loop *) apply BLoop; assumption.
  - (* S_LoopE *) inversion Hb; subst.
    match goal with
    | H1 : bexec Γ s1 a ?m, H2 : bexec Γ (RTest _ _ _ _) ?m b0 |- _ =>
        eapply BLoopE; [ exact H1 | exact H2 ]
    end.
  - (* S_TestExit *) inversion Hb; subst; apply BTestExit; assumption.
  - (* S_TestCont *) inversion Hb; subst.
    match goal with
    | H1 : bexec Γ s2 a ?m, H2 : bexec Γ (RCont _ _ _ _) ?m b0 |- _ =>
        eapply BTestCont; [ assumption | exact H1 | exact H2 ]
    end.
  - (* S_Cont *) apply BCont; assumption.
  - (* S_Call *) apply BCall; assumption.
  - (* S_Uncall *) apply BUncall; assumption.
Qed.

Lemma run_back : forall Γ r a t c,
  multistep Γ r a t c -> forall b, bexec Γ t c b -> bexec Γ r a b.
Proof.
  intros Γ r a t c H; induction H; intros b0 Hb.
  - exact Hb.
  - apply IHmultistep in Hb. eapply sim; eassumption.
Qed.

Corollary ms_bexec : forall Γ r a b, multistep Γ r a RSkip b -> bexec Γ r a b.
Proof. intros Γ r a b H. eapply run_back; [ exact H | apply BSkip ]. Qed.

(** Decode a runtime big-step back to the source big-step.  The four conjuncts
    treat, respectively, embedded statements and the three loop phases. *)
Ltac vcn := let H := fresh in intros ? ? ? ? H; discriminate H.
Ltac vc1 := let s := fresh "s" in let H := fresh in
            intros s H; destruct s; simpl in H; discriminate H.

Lemma bexec_sound : forall Γ r a b, bexec Γ r a b ->
  (forall s, r = embed s -> L.exec Γ s a b) /\
  (forall G1 S1 S2 G2, r = RLoopE G1 (embed S1) (embed S2) G2 ->
     L.lp Γ G1 S1 S2 G2 a b) /\
  (forall G1 S1 S2 G2, r = RTest G1 (embed S1) (embed S2) G2 ->
     forall a0, L.exec Γ S1 a0 a -> L.lp Γ G1 S1 S2 G2 a0 b) /\
  (forall G1 S1 S2 G2, r = RCont G1 (embed S1) (embed S2) G2 ->
     gtest G1 a = false /\ L.lp Γ G1 S1 S2 G2 a b).
Proof.
  intros Γ r a b Hb. induction Hb.
  - (* BSkip *) split; [ intros s Hs; destruct s; simpl in Hs; try discriminate Hs;
      apply L.E_Skip | split; [ vcn | split; [ vcn | vcn ] ] ].
  - (* BPrim *) split; [ intros s Hs; destruct s; simpl in Hs; try discriminate Hs;
      injection Hs as Hs; subst; apply L.E_Prim; assumption
      | split; [ vcn | split; [ vcn | vcn ] ] ].
  - (* BSeq *) split; [ | split; [ vcn | split; [ vcn | vcn ] ] ].
    intros s Hs; destruct s; simpl in Hs; try discriminate Hs.
    injection Hs as Hs1 Hs2.
    match goal with I : (forall s0, r1 = embed s0 -> _) /\ _ |- _ => destruct I as [I1 _] end.
    match goal with I : (forall s0, r2 = embed s0 -> _) /\ _ |- _ => destruct I as [I2 _] end.
    eapply L.E_Seq; [ apply I1; exact Hs1 | apply I2; exact Hs2 ].
  - (* BAssert *) split; [ vc1 | split; [ vcn | split; [ vcn | vcn ] ] ].
  - (* BIfT *) split; [ | split; [ vcn | split; [ vcn | vcn ] ] ].
    intros s Hs; destruct s; simpl in Hs; try discriminate Hs.
    injection Hs as Hg1 Hs1 Hs2 Hg2.
    match goal with I : (forall s0, s1 = embed s0 -> _) /\ _ |- _ => destruct I as [I1 _] end.
    apply L.E_IfT; [ rewrite <- Hg1; assumption | apply I1; exact Hs1 | rewrite <- Hg2; assumption ].
  - (* BIfF *) split; [ | split; [ vcn | split; [ vcn | vcn ] ] ].
    intros s Hs; destruct s; simpl in Hs; try discriminate Hs.
    injection Hs as Hg1 Hs1 Hs2 Hg2.
    match goal with I : (forall s0, s2 = embed s0 -> _) /\ _ |- _ => destruct I as [I2 _] end.
    apply L.E_IfF; [ rewrite <- Hg1; assumption | apply I2; exact Hs2 | rewrite <- Hg2; assumption ].
  - (* BLoop *) split; [ | split; [ vcn | split; [ vcn | vcn ] ] ].
    intros s Hs; destruct s; simpl in Hs; try discriminate Hs.
    injection Hs as Hg1 Hs1 Hs2 Hg2.
    match goal with I : (forall s0, RLoopE g1 s1 s2 g2 = embed s0 -> _) /\ _ |- _ =>
      destruct I as [_ [Ic2 _]] end.
    apply L.E_Loop; [ rewrite <- Hg1; assumption
      | apply Ic2; rewrite Hg1, Hs1, Hs2, Hg2; reflexivity ].
  - (* BLoopE *) split; [ vc1 | split; [ | split; [ vcn | vcn ] ] ].
    intros G1 S1 S2 G2 Hq. injection Hq as Hg1 Hs1 Hs2 Hg2.
    match goal with I : (forall s0, s1 = embed s0 -> _) /\ _ |- _ => destruct I as [Is1 _] end.
    match goal with I : (forall s0, RTest g1 s1 s2 g2 = embed s0 -> _) /\ _ |- _ =>
      destruct I as [_ [_ [Itest _]]] end.
    assert (Heq : RTest g1 s1 s2 g2 = RTest G1 (embed S1) (embed S2) G2)
      by (rewrite Hg1, Hs1, Hs2, Hg2; reflexivity).
    apply (Itest G1 S1 S2 G2 Heq a); apply Is1; exact Hs1.
  - (* BTestExit *) split; [ vc1 | split; [ vcn | split; [ | vcn ] ] ].
    intros G1 S1 S2 G2 Hq. injection Hq as Hg1 Hs1 Hs2 Hg2. intros a0 Hex.
    apply L.L_one; [ exact Hex | rewrite <- Hg2; assumption ].
  - (* BTestCont *) split; [ vc1 | split; [ vcn | split; [ | vcn ] ] ].
    intros G1 S1 S2 G2 Hq. injection Hq as Hg1 Hs1 Hs2 Hg2. intros a0 Hex.
    match goal with I : (forall s0, s2 = embed s0 -> _) /\ _ |- _ => destruct I as [Is2 _] end.
    match goal with I : (forall s0, RCont g1 s1 s2 g2 = embed s0 -> _) /\ _ |- _ =>
      destruct I as [_ [_ [_ Icont]]] end.
    assert (HeqC : RCont g1 s1 s2 g2 = RCont G1 (embed S1) (embed S2) G2)
      by (rewrite Hg1, Hs1, Hs2, Hg2; reflexivity).
    destruct (Icont G1 S1 S2 G2 HeqC) as [Hgf Hlp].
    eapply L.L_more; [ exact Hex | rewrite <- Hg2; assumption
      | apply Is2; exact Hs2 | exact Hgf | exact Hlp ].
  - (* BCont *) split; [ vc1 | split; [ vcn | split; [ vcn | ] ] ].
    intros G1 S1 S2 G2 Hq. injection Hq as Hg1 Hs1 Hs2 Hg2.
    match goal with I : (forall s0, RLoopE g1 s1 s2 g2 = embed s0 -> _) /\ _ |- _ =>
      destruct I as [_ [Ic2 _]] end.
    split; [ rewrite <- Hg1; assumption | ].
    assert (HeqL : RLoopE g1 s1 s2 g2 = RLoopE G1 (embed S1) (embed S2) G2)
      by (rewrite Hg1, Hs1, Hs2, Hg2; reflexivity).
    exact (Ic2 G1 S1 S2 G2 HeqL).
  - (* BCall *) split; [ | split; [ vcn | split; [ vcn | vcn ] ] ].
    intros s Hs; destruct s; simpl in Hs; try discriminate Hs.
    injection Hs as Hp; subst. apply L.E_Call.
    match goal with I : (forall s0, embed (Γ _) = embed s0 -> _) /\ _ |- _ =>
      destruct I as [I1 _] end.
    apply I1; reflexivity.
  - (* BUncall *) split; [ | split; [ vcn | split; [ vcn | vcn ] ] ].
    intros s Hs; destruct s; simpl in Hs; try discriminate Hs.
    injection Hs as Hp; subst. apply L.E_Uncall.
    match goal with I : (forall s0, embed (L.invert (Γ _)) = embed s0 -> _) /\ _ |- _ =>
      destruct I as [I1 _] end.
    apply I1; reflexivity.
Qed.

(** Soundness, and hence the full equivalence. *)
Theorem sound : forall Γ s a b,
  multistep Γ (embed s) a RSkip b -> L.exec Γ s a b.
Proof.
  intros Γ s a b H. apply ms_bexec in H.
  destruct (bexec_sound Γ (embed s) a b H) as [Hc1 _].
  apply Hc1; reflexivity.
Qed.

Theorem equiv : forall Γ s a b,
  L.exec Γ s a b <-> multistep Γ (embed s) a RSkip b.
Proof. intros; split; [ apply complete | apply sound ]. Qed.

(* ===================================================================== *)
(** ** Scope: this semantics is *not* step-reversible, and that is expected.

    Lanese and Vidal ("A Reversible Semantics for Janus", arXiv:2602.16913,
    2026) observe that the small-step semantics this file mechanizes is not
    reversible *as a small-step relation*: it discards information going
    forwards, so an individual step cannot be undone.  Their example is a
    conditional [if e1 then skip else s2 fi e2] reducing to [skip] once the exit
    guard holds -- from [skip] the conditional cannot be recovered.  They repair
    it with a program-counter/CFG presentation satisfying the **Loop Lemma**
    (every reduction has an inverse), proved equivalent to both the big-step and
    the previous small-step semantics.  Their development is not mechanized.

    The same defect is present here, and it is worth pinning down rather than
    leaving implicit, because it bounds what [equiv] may be read as saying.

    Two *distinct* configurations that step to the *same* one, so [step] is not
    backward deterministic.  First, unconditionally, from the sequencing rules
    alone: *)

Theorem step_not_backward_deterministic : forall Γ (a : state),
  step Γ (RSeq (RSeq RSkip RSkip) RSkip) a (RSeq RSkip RSkip) a
  /\ step Γ (RSeq RSkip (RSeq RSkip RSkip)) a (RSeq RSkip RSkip) a
  /\ RSeq (RSeq RSkip RSkip) RSkip <> RSeq RSkip (RSeq RSkip RSkip).
Proof.
  intros Γ a; repeat split.
  - apply S_SeqStep, S_SeqDone.
  - apply S_SeqDone.
  - discriminate.
Qed.

(** And second, in exactly Lanese and Vidal's shape: the *exit assertion* of a
    conditional collapses to [RSkip], so two conditionals with different exit
    guards become indistinguishable the moment they finish. *)
Theorem exit_assertion_collapses : forall Γ (g h : guard) (a : state),
  gtest g a = true -> gtest h a = true ->
  step Γ (RAssert g true) a RSkip a /\ step Γ (RAssert h true) a RSkip a.
Proof. intros Γ g h a Hg Hh; split; apply S_Assert; assumption. Qed.

(** What survives is the statement [equiv] actually makes: reversibility here is
    a property of *whole runs*, not of single steps.  [RevCore.exec_iff] inverts
    a complete [exec], and [equiv] transports that to [multistep]; neither
    claims, nor needs, that [step] itself is invertible.  Getting the Loop Lemma
    would mean adopting a configuration that retains the discarded control
    information -- Lanese and Vidal's program counter, or equivalent -- which is
    a different semantics, not a lemma about this one. *)

End SmallStep.
