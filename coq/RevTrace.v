(** * RevTrace.v — PInj is traced over the coproduct, and the Janus loop IS a trace

    [RevCat.v] builds \textsf{PInj} as a dagger *restriction* category: composition,
    identities, the dagger [convH], and the inverse law.  That is the structure
    needed to say "[invert] is the partial inverse".  It says nothing about how
    *iteration* is modelled.

    Paolini--Piccolo--Roversi's Matita development (TYPES 2015) does: their
    [Pinj] carries the symmetric monoidal structures of both product and
    coproduct, is distributive, and — crucially — is **traced** over the
    coproduct ([pinj.ma]'s [Pinj_Traced], built by [rel_trace.ma]'s
    [Abs_Sum_Trace_Rel]).  The Janus loop is then interpreted as
    [trace (loop_fun …)] ([rel_interpretation.ma]).

    This file supplies that missing layer:

      - the coproduct on \textsf{PInj}: [sumH], the injections [inlH]/[inrH],
        functoriality, and dagger compatibility ([convH_sumH]);
      - the **trace** [traceH R] of [R : hrel (A+U) (B+U)] — run [R], and while
        it lands in the right summand feed the value back through [U]:
        [traceH R = R11 ∪ (R12 ; fb* ; R21)], the "execution formula";
      - [pinj_traceH] — **the trace of a partial injection is a partial
        injection** (their [good_rel_trace_inj]), so \textsf{PInj} really is
        traced;
      - [trace_conv] — the trace commutes with the dagger (a run read backwards
        is a run of the converse), [trace_yanking] and [trace_vanishing]
        (the yanking and vanishing-I axioms), and [trace_natural_l]
        (left naturality);
      - [loop_is_trace] — **the payoff**: [from g1 do R loop S until g2] is
        exactly [traceH turn], where [turn] is one turn of the loop body with the
        feedback wire carrying the state at the top of the body.  The entry and
        exit assertions [g1]/[g2] are precisely what makes [turn] a partial
        injection ([pinj_turn]) — the *left* summand cannot be re-entered
        because a continuing turn lands where [g1] is false, while an entry
        lands where [g1] is true.

    Hence [rev_loop] (RevAlgebra's closure lemma for the loop, proved there by a
    bespoke reversal argument) is re-derived as an *instance of the trace*:
    [rev_loop_via_trace].  The development is axiom-free.

    Not covered: the vanishing-II and superposing axioms, which need the
    associativity/symmetry coherence of the coproduct monoidal structure. *)

From Stdlib Require Import Bool Arith.
Require Import RevCore RevAlgebra RevDenote RevCat.

(* ===================================================================== *)
(** ** [pinj] on endorelations is [RevAlgebra]'s [reversible]. *)

Lemma pinj_reversible : forall (st : Type) (R : @rel st), pinj R <-> reversible R.
Proof.
  intros st R; unfold pinj, reversible, detH, det, convH, conv; tauto.
Qed.

(* ===================================================================== *)
(** ** The coproduct on PInj. *)

Definition sumH {A B C D : Type} (R : hrel A C) (S : hrel B D) : hrel (A + B) (C + D) :=
  fun x y =>
    match x, y with
    | inl a, inl c => R a c
    | inr b, inr d => S b d
    | _, _ => False
    end.

Definition inlH {A B : Type} : hrel A (A + B) := fun a x => x = inl a.
Definition inrH {A B : Type} : hrel B (A + B) := fun b x => x = inr b.

Lemma pinj_inlH : forall A B, pinj (@inlH A B).
Proof.
  intros A B; split; intros a b b' H1 H2; unfold inlH, convH in *;
    [ congruence | subst; injection H2; auto ].
Qed.

Lemma pinj_inrH : forall A B, pinj (@inrH A B).
Proof.
  intros A B; split; intros a b b' H1 H2; unfold inrH, convH in *;
    [ congruence | subst; injection H2; auto ].
Qed.

Lemma pinj_sumH : forall A B C D (R : hrel A C) (S : hrel B D),
  pinj R -> pinj S -> pinj (sumH R S).
Proof.
  intros A B C D R S [dR cR] [dS cS]; split.
  - intros [a|b] [c|d] [c'|d'] H1 H2; simpl in *; try contradiction;
      [ f_equal; eapply dR | f_equal; eapply dS ]; eauto.
  - intros [c|d] [a|b] [a'|b'] H1 H2; unfold convH in *; simpl in *;
      try contradiction;
      [ f_equal; eapply cR | f_equal; eapply cS ]; unfold convH; eauto.
Qed.

(** The dagger distributes over the coproduct. *)
Lemma convH_sumH : forall A B C D (R : hrel A C) (S : hrel B D),
  heq (convH (sumH R S)) (sumH (convH R) (convH S)).
Proof.
  intros A B C D R S [c|d] [a|b]; unfold convH; simpl; tauto.
Qed.

Lemma sumH_idH : forall A B, heq (sumH (@idH A) (@idH B)) idH.
Proof.
  intros A B [a|b] [a'|b']; unfold idH; simpl; split; intro H.
  - subst; reflexivity.
  - injection H; auto.
  - contradiction.
  - discriminate.
  - contradiction.
  - discriminate.
  - subst; reflexivity.
  - injection H; auto.
Qed.

(** Functoriality of [+]. *)
Lemma sumH_compH : forall A B C D E F
                          (R : hrel A C) (R' : hrel C E)
                          (S : hrel B D) (S' : hrel D F),
  heq (sumH (compH R R') (compH S S')) (compH (sumH R S) (sumH R' S')).
Proof.
  intros A B C D E F R R' S S' [a|b] [e|f]; unfold compH; simpl; split.
  - intros [m [H1 H2]]; exists (inl m); simpl; tauto.
  - intros [[m|m] [H1 H2]]; simpl in *; [ exists m; tauto | contradiction ].
  - contradiction.
  - intros [[m|m] [H1 H2]]; simpl in *; contradiction.
  - contradiction.
  - intros [[m|m] [H1 H2]]; simpl in *; contradiction.
  - intros [m [H1 H2]]; exists (inr m); simpl; tauto.
  - intros [[m|m] [H1 H2]]; simpl in *; [ contradiction | exists m; tauto ].
Qed.

(* ===================================================================== *)
(** ** The trace (feedback) over the coproduct. *)

Section Trace.
Context {A B U : Type}.

(** The part of [R] that stays on the feedback wire. *)
Definition fb (R : hrel (A + U) (B + U)) : hrel U U :=
  fun u u' => R (inr u) (inr u').

(** [n] trips around the wire. *)
Fixpoint pathn (R : hrel (A + U) (B + U)) (n : nat) : hrel U U :=
  match n with
  | O => idH
  | S k => compH (fb R) (pathn R k)
  end.

(** The execution formula: exit immediately, or enter the wire, loop on it a
    finite number of times, and leave. *)
Definition traceH (R : hrel (A + U) (B + U)) : hrel A B :=
  fun a b =>
    R (inl a) (inl b)
    \/ exists n u u', R (inl a) (inr u) /\ pathn R n u u' /\ R (inr u') (inl b).

(** A path can be decomposed at its last edge as well as its first. *)
Lemma pathn_snoc : forall R n u u',
  pathn R (S n) u u' <-> exists m, pathn R n u m /\ fb R m u'.
Proof.
  intros R n; induction n; intros u u'; simpl.
  - unfold compH, idH; split.
    + intros [m [H1 H2]]; subst m; exists u; split; [ reflexivity | exact H1 ].
    + intros [m [H1 H2]]; subst m; exists u'; split; [ exact H2 | reflexivity ].
  - split.
    + intros [m [H1 H2]].
      apply (proj1 (IHn m u')) in H2; destruct H2 as [k [Hk Hk']].
      exists k; split; [ exists m; split; assumption | exact Hk' ].
    + intros [m [[k [Hk Hk']] Hm]].
      exists k; split; [ exact Hk | apply (proj2 (IHn k u')); exists m; split; assumption ].
Qed.

(** Determinism: whatever the length of the run, the exit is the same. *)
Lemma path_exit_unique : forall (R : hrel (A + U) (B + U)), detH R ->
  forall n m u u1 u2 b1 b2,
    pathn R n u u1 -> R (inr u1) (inl b1) ->
    pathn R m u u2 -> R (inr u2) (inl b2) -> b1 = b2.
Proof.
  intros R dR n; induction n; intros m u u1 u2 b1 b2 H1 E1 H2 E2.
  - simpl in H1; unfold idH in H1; subst u1.
    destruct m as [|k].
    + simpl in H2; unfold idH in H2; subst u2.
      assert (Hi : @inl B U b1 = inl b2) by (eapply dR; eassumption).
      injection Hi; auto.
    + simpl in H2; destruct H2 as [w [Hw _]]; unfold fb in Hw.
      assert (Hi : @inl B U b1 = inr w) by (eapply dR; eassumption); discriminate.
  - simpl in H1; destruct H1 as [w [Hw Hp1]]; unfold fb in Hw.
    destruct m as [|k].
    + simpl in H2; unfold idH in H2; subst u2.
      assert (Hi : @inr B U w = inl b2) by (eapply dR; eassumption); discriminate.
    + simpl in H2; destruct H2 as [w2 [Hw2 Hp2]]; unfold fb in Hw2.
      assert (Hi : @inr B U w = inr w2) by (eapply dR; eassumption).
      injection Hi; intro; subst w2.
      eapply IHn; eassumption.
Qed.

Lemma detH_traceH : forall R, detH R -> detH (traceH R).
Proof.
  intros R dR a b b' H1 H2; unfold traceH in *.
  destruct H1 as [H1|[n [u [u' [E1 [P1 X1]]]]]];
  destruct H2 as [H2|[m [v [v' [E2 [P2 X2]]]]]].
  - assert (Hi : @inl B U b = inl b') by (eapply dR; eassumption).
    injection Hi; auto.
  - assert (Hi : @inl B U b = inr v) by (eapply dR; eassumption); discriminate.
  - assert (Hi : @inr B U u = inl b') by (eapply dR; eassumption); discriminate.
  - assert (Hi : @inr B U u = inr v) by (eapply dR; eassumption).
    injection Hi; intro; subst v.
    exact (path_exit_unique R dR n m u u' v' b b' P1 X1 P2 X2).
Qed.

End Trace.

(** Reading a path backwards is a path of the converse.  ([A] and [B] swap, so
    this is stated outside the section that fixes them.) *)
Lemma pathn_conv : forall A B U (R : hrel (A + U) (B + U)) n u u',
  pathn (convH R) n u u' <-> pathn R n u' u.
Proof.
  intros A B U R n; induction n; intros u u'; simpl.
  - unfold idH; split; intro H; symmetry; exact H.
  - split.
    + intros [m [H1 H2]].
      apply (proj2 (pathn_snoc R n u' u)); exists m; split.
      * apply (proj1 (IHn m u')); exact H2.
      * exact H1.
    + intro H; apply (proj1 (pathn_snoc R n u' u)) in H; destruct H as [m [Hp He]].
      exists m; split; [ exact He | apply (proj2 (IHn m u')); exact Hp ].
Qed.

(** The trace commutes with the dagger: a run read backwards is a run of the
    converse.  (The Matita model gets this from [Pinj]'s dagger structure.) *)
Lemma trace_conv : forall A B U (R : hrel (A + U) (B + U)) b a,
  convH (traceH R) b a <-> traceH (convH R) b a.
Proof.
  intros A B U R b a; unfold convH, traceH; split.
  - intros [H|[n [u [u' [E1 [Hp E2]]]]]]; [ left; exact H | ].
    right; exists n, u', u; repeat split;
      [ exact E2 | apply (proj2 (pathn_conv A B U R n u' u)); exact Hp | exact E1 ].
  - intros [H|[n [u [u' [E1 [Hp E2]]]]]]; [ left; exact H | ].
    right; exists n, u', u; repeat split;
      [ exact E2 | apply (proj1 (pathn_conv A B U R n u u')); exact Hp | exact E1 ].
Qed.

(** **The** structural theorem: PInj is traced over the coproduct. *)
Theorem pinj_traceH : forall A B U (R : hrel (A + U) (B + U)),
  pinj R -> pinj (traceH R).
Proof.
  intros A B U R [d c]; split.
  - apply detH_traceH; exact d.
  - intros b a a' H1 H2.
    apply (proj1 (trace_conv A B U R b a)) in H1.
    apply (proj1 (trace_conv A B U R b a')) in H2.
    eapply detH_traceH; eassumption.
Qed.

(* ===================================================================== *)
(** ** Trace axioms: yanking, vanishing-I, left naturality. *)

(** Yanking: tracing the symmetry gives the identity. *)
Definition symH {A : Type} : hrel (A + A) (A + A) :=
  fun x y =>
    match x, y with
    | inl a, inr a' => a = a'
    | inr a, inl a' => a = a'
    | _, _ => False
    end.

Theorem trace_yanking : forall A, heq (traceH (@symH A)) idH.
Proof.
  intros A a b; unfold traceH, idH; split.
  - intros [H|[n [u [u' [E1 [Hp E2]]]]]]; simpl in *; [ contradiction | ].
    subst u.
    destruct n as [|k]; simpl in Hp.
    + unfold idH in Hp; subst u'; exact E2.
    + destruct Hp as [w [Hw _]]; unfold fb in Hw; simpl in Hw; contradiction.
  - intro H; subst b; right; exists 0, a, a; simpl; unfold idH; auto.
Qed.

(** Vanishing-I: a trace over the empty wire does nothing. *)
Theorem trace_vanishing : forall A B (R : hrel (A + Empty_set) (B + Empty_set)),
  heq (traceH R) (fun a b => R (inl a) (inl b)).
Proof.
  intros A B R a b; unfold traceH; split.
  - intros [H|[_ [[] _]]]; exact H.
  - intro H; left; exact H.
Qed.

(** Left naturality: [traceH ((F + id) ; R) = F ; traceH R]. *)
Theorem trace_natural_l : forall A A' B U (F : hrel A' A) (R : hrel (A + U) (B + U)),
  heq (traceH (compH (sumH F (@idH U)) R)) (compH F (traceH R)).
Proof.
  intros A A' B U F R a' b.
  assert (Hfb : forall u u', fb (compH (sumH F (@idH U)) R) u u' <-> fb R u u').
  { intros u u'; unfold fb, compH; simpl; split.
    - intros [[x|x] [H1 H2]]; simpl in H1; [ contradiction | unfold idH in H1; subst x; exact H2 ].
    - intro H; exists (inr u); simpl; unfold idH; auto. }
  assert (Hpath : forall n u u',
            pathn (compH (sumH F (@idH U)) R) n u u' <-> pathn R n u u').
  { intro n; induction n; intros u u'; simpl; [ tauto | ].
    unfold compH; split.
    - intros [m [H1 H2]]; exists m; split;
        [ apply (proj1 (Hfb u m)); exact H1 | apply (proj1 (IHn m u')); exact H2 ].
    - intros [m [H1 H2]]; exists m; split;
        [ apply (proj2 (Hfb u m)); exact H1 | apply (proj2 (IHn m u')); exact H2 ]. }
  unfold traceH; split.
  - intros [[[x|x] [H1 H2]]|[n [u [u' [[[x|x] [E1 E2]] [Hp X]]]]]]; simpl in *;
      try contradiction.
    + exists x; split; [ exact H1 | left; exact H2 ].
    + destruct X as [[y|y] [HX1 HX2]]; simpl in HX1; [ contradiction | ].
      unfold idH in HX1; subst y.
      exists x; split; [ exact E1 | ].
      right; exists n, u, u'; repeat split;
        [ exact E2 | apply (proj1 (Hpath n u u')); exact Hp | exact HX2 ].
  - intros [a [HF [H|[n [u [u' [E1 [Hp X]]]]]]]].
    + left; exists (inl a); simpl; split; [ exact HF | exact H ].
    + right; exists n, u, u'; repeat split.
      * exists (inl a); simpl; split; [ exact HF | exact E1 ].
      * apply (proj2 (Hpath n u u')); exact Hp.
      * exists (inr u'); simpl; split; [ reflexivity | exact X ].
Qed.

(* ===================================================================== *)
(** ** The Janus loop is a trace.

    [from g1 do R1 loop R2 until g2] runs [R1]; if [g2] holds it exits, otherwise
    it runs [R2], asserts [¬g1], and goes round again.  As a trace: the left
    summand is the *outside* of the loop (entry on the way in, exit on the way
    out), the right summand is the **feedback wire**, carrying the state at the
    top of the body.  One [turn] is one edge of that graph.

    (The loop's two bodies are [R1]/[R2] rather than [RevAlgebra]'s [R]/[S]
    because [S] is [nat]'s successor, which the path lengths need.) *)

Section LoopTrace.
Context {state : Type}.
Variables (g1 g2 : state -> bool).
Variables (R1 R2 : @rel state).

Definition turn : hrel (state + state) (state + state) :=
  fun x y =>
    match x, y with
    (* enter the loop: the entry assertion [g1] holds *)
    | inl a, inr u => g1 a = true /\ u = a
    (* a final turn: run [R1], the exit assertion [g2] holds, leave *)
    | inr u, inl b => R1 u b /\ g2 b = true
    (* a continuing turn: run [R1], [g2] fails, run [R2], [¬g1] holds *)
    | inr u, inr u' => exists m, R1 u m /\ g2 m = false /\ R2 m u' /\ g1 u' = false
    (* the outside is never reached from the outside *)
    | inl _, inl _ => False
    end.

(** Trips around the wire are exactly [RevAlgebra]'s open iteration. *)
Lemma pathn_itero : forall n u u', pathn turn n u u' -> itero g1 R1 R2 g2 u u'.
Proof.
  induction n; intros u u' H; simpl in H.
  - unfold idH in H; subst u'; apply io_nil.
  - destruct H as [m [Hm Hp]]; unfold fb in Hm; simpl in Hm.
    destruct Hm as [x [HR [Hg2 [HS Hg1]]]].
    eapply io_cons; [ exact HR | exact Hg2 | exact HS | exact Hg1 | apply IHn; exact Hp ].
Qed.

Lemma itero_pathn : forall u u', itero g1 R1 R2 g2 u u' -> exists n, pathn turn n u u'.
Proof.
  intros u u' H; induction H.
  - exists 0; simpl; reflexivity.
  - destruct IHitero as [n Hn]; exists (S n); simpl.
    exists a2; split; [ | exact Hn ].
    unfold fb; simpl; exists a1; repeat split; assumption.
Qed.

(** Every [lpR] run splits as "some continuing turns, then a final [R1]". *)
Lemma lpR_split : forall a b, lpR g1 R1 R2 g2 a b ->
  exists m, itero g1 R1 R2 g2 a m /\ R1 m b /\ g2 b = true.
Proof.
  intros a b H; induction H.
  - exists a; split; [ apply io_nil | split; assumption ].
  - destruct IHlpR as [m [Hit [HR Hg]]].
    exists m; split; [ | split; assumption ].
    eapply io_cons; eassumption.
Qed.

(** **The payoff**: the Janus loop *is* the trace of one turn. *)
Theorem loop_is_trace : forall a b, traceH turn a b <-> loopR g1 R1 R2 g2 a b.
Proof.
  intros a b; unfold traceH, loopR; split.
  - intros [H|[n [u [u' [E1 [Hp X]]]]]]; simpl in *; [ contradiction | ].
    destruct E1 as [Hg1 Hu]; subst u.
    destruct X as [HR Hg2].
    split; [ exact Hg1 | ].
    eapply itero_to_lpR; [ exact (pathn_itero n a u' Hp) | exact HR | exact Hg2 ].
  - intros [Hg1 Hlp].
    apply lpR_split in Hlp; destruct Hlp as [m [Hit [HR Hg2]]].
    apply itero_pathn in Hit; destruct Hit as [n Hn].
    right; exists n, a, m; repeat split; assumption.
Qed.

(** The entry/exit assertions are exactly what makes one turn a partial
    injection: a continuing turn lands where [g1] is *false*, an entry lands
    where [g1] is *true*, so the wire can never be entered twice. *)
Lemma pinj_turn : reversible R1 -> reversible R2 -> pinj turn.
Proof.
  intros [dR cR] [dS cS]; split.
  - intros [a|u] [b|v] [b'|v'] H1 H2; simpl in *; try contradiction.
    + (* inl a -> inr v, inr v' : two entries *)
      destruct H1 as [_ Hv]; destruct H2 as [_ Hv']; subst; reflexivity.
    + (* inr u -> inl b, inl b' : two exits *)
      destruct H1 as [HR _]; destruct H2 as [HR' _].
      f_equal; eapply dR; eassumption.
    + (* inr u -> inl b, inr v' : exit vs. continue — [g2] decides *)
      destruct H1 as [HR Hg2]; destruct H2 as [x [HR' [Hg2' _]]].
      assert (b = x) by (eapply dR; eassumption); subst x; congruence.
    + (* inr u -> inr v, inl b' : continue vs. exit *)
      destruct H2 as [HR Hg2]; destruct H1 as [x [HR' [Hg2' _]]].
      assert (b' = x) by (eapply dR; eassumption); subst x; congruence.
    + (* inr u -> inr v, inr v' : two continuing turns *)
      destruct H1 as [x [HR [_ [HS _]]]]; destruct H2 as [y [HR' [_ [HS' _]]]].
      assert (x = y) by (eapply dR; eassumption); subst y.
      f_equal; eapply dS; eassumption.
  - intros [b|v] [a|u] [a'|u'] H1 H2; unfold convH in *; simpl in *; try contradiction.
    + (* into inl b, from inr u and inr u' *)
      destruct H1 as [HR _]; destruct H2 as [HR' _].
      f_equal; eapply cR; unfold conv; eassumption.
    + (* into inr v, from inl a and inl a' *)
      destruct H1 as [_ ?]; destruct H2 as [_ ?]; congruence.
    + (* into inr v, from inl a and inr u' : contradictory guards *)
      destruct H1 as [Hg1 Hv]; subst v.
      destruct H2 as [_ [_ [_ [_ Hg1']]]]; congruence.
    + (* into inr v, from inr u and inl a' : contradictory guards *)
      destruct H2 as [Hg1 Hv]; subst v.
      destruct H1 as [_ [_ [_ [_ Hg1']]]]; congruence.
    + (* into inr v, from inr u and inr u' *)
      destruct H1 as [x [HR [_ [HS _]]]]; destruct H2 as [y [HR' [_ [HS' _]]]].
      assert (x = y) by (eapply cS; unfold conv; eassumption); subst y.
      f_equal; eapply cR; unfold conv; eassumption.
Qed.

(** Hence the loop's reversibility is *an instance of the trace closure* —
    a second, structural proof of [RevAlgebra.rev_loop]. *)
Corollary rev_loop_via_trace :
  reversible R1 -> reversible R2 -> reversible (loopR g1 R1 R2 g2).
Proof.
  intros HR HS.
  assert (Ht : pinj (traceH turn)) by (apply pinj_traceH, pinj_turn; assumption).
  destruct Ht as [d c]; split.
  - intros a b b' H1 H2; eapply d; apply (proj2 (loop_is_trace _ _)); eassumption.
  - intros a b b' H1 H2; eapply c; unfold convH, conv in *;
      apply (proj2 (loop_is_trace _ _)); eassumption.
Qed.

End LoopTrace.
