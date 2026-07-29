(** * RevError.v — assertion failure as an outcome, and the compiled ERR location

    [jana_py/smv.py] compiles a Janus program to a transition system whose
    distinguished location [ERR] is reached exactly when a runtime assertion
    fails, and the totality checker proves [ERR] unreachable.  For that to mean
    anything, two things have to line up:

      - the *source* must have a notion of "this execution fails an assertion",
        and [RevCore.exec] does not: it is a partial relation, so a program that
        fails an assertion and a program that diverges are both simply outside
        it.  [execE] below adds the outcome [Err] and propagates it;
      - the *machine* must reach [ERR] exactly then.  The compiled machine of
        [RevCompile.v] has no [ERR] label — a failed [IChk] simply has no step.
        That is the same situation: [smv.py] needs an explicit [ERR] edge only
        because SMV requires a total transition relation (its own comment says
        "halt: every location must be total"), whereas in Rocq "no rule applies"
        is expressible directly.  So the statement to prove is that source
        failure coincides with the machine being **stuck strictly inside the
        fragment**.

    What is proved here:

      - [exec_execE] / [execE_exec] — the two semantics agree on success, so
        [execE] really is [exec] plus failure and nothing else;
      - [ok_not_err] — success and failure are exclusive;
      - [fail_sound] — **a source assertion failure makes the compiled code get
        stuck inside the fragment**.  This is the direction the checker's claim
        rests on: it is what rules out a failure the model does not see, i.e. a
        proof of [ERR]-unreachability that is a lie.

    Scope, honestly.  The framework's primitives and guards are abstract, so the
    *expression-level* traps of [smv.py] (floor division, two-sorted
    expressions, aliasing) are out of reach here; those are formalized against
    Janus's concrete expressions in [RevLowerExpr.v]/[RevLowerStmt.v].  And
    [smv.py] emits a **large-block** encoding, merging straight-line runs into a
    single transition, whereas [comp] emits one instruction per label; that
    those two describe the same relation is not proved here.  What is aligned is
    the control-flow skeleton and the meaning of ERR. *)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
Require Import RevCore RevSmallStep RevDenote RevFix RevCompile.

Module ErrSem (P : REV_PRIM).

Module Cp := RevCompile.Compile P.
Module L := Cp.L.
Import L.

(* ===================================================================== *)
(** ** The source semantics with an error outcome. *)

Inductive outcome :=
| Ok (a : P.state)
| Err.

Section Sem.
Variable G : pname -> stmt.

Inductive execE : stmt -> P.state -> outcome -> Prop :=
(* --- success: exactly the rules of [exec] --- *)
| X_Skip : forall a, execE Skip a (Ok a)
| X_Prim : forall p a b, P.pstep p a b -> execE (Prim p) a (Ok b)
| X_Seq : forall s1 s2 a m o,
    execE s1 a (Ok m) -> execE s2 m o -> execE (Seq s1 s2) a o
| X_IfT : forall g1 s1 s2 g2 a b,
    P.gtest g1 a = true -> execE s1 a (Ok b) -> P.gtest g2 b = true ->
    execE (If g1 s1 s2 g2) a (Ok b)
| X_IfF : forall g1 s1 s2 g2 a b,
    P.gtest g1 a = false -> execE s2 a (Ok b) -> P.gtest g2 b = false ->
    execE (If g1 s1 s2 g2) a (Ok b)
| X_Loop : forall g1 s1 s2 g2 a o,
    P.gtest g1 a = true -> lpE g1 s1 s2 g2 a o -> execE (Loop g1 s1 s2 g2) a o
| X_Call : forall p a o, execE (G p) a o -> execE (Call p) a o
| X_Uncall : forall p a o, execE (invert (G p)) a o -> execE (Uncall p) a o
(* --- failure: an assertion that does not hold --- *)
| X_SeqErr : forall s1 s2 a, execE s1 a Err -> execE (Seq s1 s2) a Err
| X_IfTBodyErr : forall g1 s1 s2 g2 a,
    P.gtest g1 a = true -> execE s1 a Err -> execE (If g1 s1 s2 g2) a Err
| X_IfTExitErr : forall g1 s1 s2 g2 a b,
    P.gtest g1 a = true -> execE s1 a (Ok b) -> P.gtest g2 b = false ->
    execE (If g1 s1 s2 g2) a Err
| X_IfFBodyErr : forall g1 s1 s2 g2 a,
    P.gtest g1 a = false -> execE s2 a Err -> execE (If g1 s1 s2 g2) a Err
| X_IfFExitErr : forall g1 s1 s2 g2 a b,
    P.gtest g1 a = false -> execE s2 a (Ok b) -> P.gtest g2 b = true ->
    execE (If g1 s1 s2 g2) a Err
| X_LoopEntryErr : forall g1 s1 s2 g2 a,
    P.gtest g1 a = false -> execE (Loop g1 s1 s2 g2) a Err

with lpE : P.guard -> stmt -> stmt -> P.guard -> P.state -> outcome -> Prop :=
| LE_one : forall g1 s1 s2 g2 a b,
    execE s1 a (Ok b) -> P.gtest g2 b = true -> lpE g1 s1 s2 g2 a (Ok b)
| LE_more : forall g1 s1 s2 g2 a a1 a2 o,
    execE s1 a (Ok a1) -> P.gtest g2 a1 = false ->
    execE s2 a1 (Ok a2) -> P.gtest g1 a2 = false ->
    lpE g1 s1 s2 g2 a2 o -> lpE g1 s1 s2 g2 a o
| LE_doErr : forall g1 s1 s2 g2 a,
    execE s1 a Err -> lpE g1 s1 s2 g2 a Err
| LE_loopErr : forall g1 s1 s2 g2 a a1,
    execE s1 a (Ok a1) -> P.gtest g2 a1 = false -> execE s2 a1 Err ->
    lpE g1 s1 s2 g2 a Err
| LE_backErr : forall g1 s1 s2 g2 a a1 a2,
    execE s1 a (Ok a1) -> P.gtest g2 a1 = false ->
    execE s2 a1 (Ok a2) -> P.gtest g1 a2 = true ->
    lpE g1 s1 s2 g2 a Err.

Scheme execE_mut := Induction for execE Sort Prop
  with lpE_mut   := Induction for lpE   Sort Prop.

(* ===================================================================== *)
(** ** [execE] is [exec] plus failure: the two agree on success. *)

Lemma exec_execE : forall s a b, exec G s a b -> execE s a (Ok b).
Proof.
  intros s a b H.
  induction H using L.exec_mut
    with (P0 := fun g1 s1 s2 g2 a b (_ : lp G g1 s1 s2 g2 a b) =>
                  lpE g1 s1 s2 g2 a (Ok b)).
  - apply X_Skip.
  - apply X_Prim; assumption.
  - eapply X_Seq; eassumption.
  - eapply X_IfT; eassumption.
  - eapply X_IfF; eassumption.
  - eapply X_Loop; eassumption.
  - apply X_Call; assumption.
  - apply X_Uncall; assumption.
  - eapply LE_one; eassumption.
  - eapply LE_more; eassumption.
Qed.

Lemma execE_exec : forall s a o, execE s a o -> forall b, o = Ok b -> exec G s a b.
Proof.
  intros s a o H.
  induction H using execE_mut
    with (P0 := fun g1 s1 s2 g2 a o (_ : lpE g1 s1 s2 g2 a o) =>
                  forall b, o = Ok b -> lp G g1 s1 s2 g2 a b);
    intros bb Heq; try discriminate.
  - injection Heq as ->; apply E_Skip.
  - injection Heq as ->; apply E_Prim; assumption.
  - eapply E_Seq; [ apply IHexecE1; reflexivity | apply IHexecE2; exact Heq ].
  - injection Heq as ->; eapply E_IfT; [ eassumption | apply IHexecE; reflexivity
                                       | assumption ].
  - injection Heq as ->; eapply E_IfF; [ eassumption | apply IHexecE; reflexivity
                                       | assumption ].
  - eapply E_Loop; [ eassumption | apply IHexecE; exact Heq ].
  - apply E_Call; apply IHexecE; exact Heq.
  - apply E_Uncall; apply IHexecE; exact Heq.
  - injection Heq as ->; apply L_one; [ apply IHexecE; reflexivity | assumption ].
  - eapply L_more; [ apply IHexecE1; reflexivity | eassumption
                   | apply IHexecE2; reflexivity | eassumption
                   | apply IHexecE3; exact Heq ].
Qed.

Corollary execE_ok_iff : forall s a b, exec G s a b <-> execE s a (Ok b).
Proof.
  intros s a b; split; intro H.
  - apply exec_execE; exact H.
  - eapply execE_exec; [ exact H | reflexivity ].
Qed.

(* ===================================================================== *)
(** ** Success and failure are exclusive.

    Proved against [exec] rather than through a determinism argument for
    [execE]: [exec_det] already pins the intermediate states down, which is all
    the [Seq]/[If]/[Loop] cases need.  [pin] does that pinning without depending
    on the names [inversion] invents. *)

Lemma execE_ok_exec : forall s a b, execE s a (Ok b) -> exec G s a b.
Proof. intros s a b H; eapply execE_exec; [ exact H | reflexivity ]. Qed.

Ltac pin :=
  repeat match goal with
  | Ha : execE ?s ?a (Ok ?x), Hb : exec _ ?s ?a ?y |- _ =>
      tryif unify x y then fail else
        (let E := fresh in
         assert (E : x = y) by
           (eapply exec_det; [ apply execE_ok_exec; exact Ha | exact Hb ]);
         subst)
  end.

Lemma ok_not_err : forall s a b, exec G s a b -> ~ execE s a Err.
Proof.
  intros s a b H.
  induction H using L.exec_mut
    with (P0 := fun g1 s1 s2 g2 a b (_ : lp G g1 s1 s2 g2 a b) =>
                  ~ lpE g1 s1 s2 g2 a Err);
    intro Hbad; inversion Hbad; subst; pin; try congruence; eauto.
Qed.

(* ===================================================================== *)
(** ** The machine side: getting stuck, and where.

    [smv.py]'s ERR location and "no instruction applies" are the same situation;
    the explicit edge exists there only because SMV wants a total transition
    relation. *)

Definition stuck (c : Cp.code) (l : nat) (a : P.state) : Prop :=
  forall m x, ~ Cp.mstep G c l a m x.

(** A run from [start] that gets stuck at a label inside [lo .. lo + sz - 1] —
    strictly inside, so reaching the fragment's exit does not count. *)
Definition mfailf (c : Cp.code) (start lo sz : nat) (a : P.state) : Prop :=
  exists l x, lo <= l /\ l < lo + sz /\ Cp.mrun G c start a l x /\ stuck c l x.

Definition mfail (c : Cp.code) (base sz : nat) (a : P.state) : Prop :=
  mfailf c base base sz a.

Lemma mfailf_widen : forall c start lo sz lo' sz' a,
  lo <= lo' -> lo' + sz' <= lo + sz -> mfailf c start lo' sz' a -> mfailf c start lo sz a.
Proof.
  intros c start lo sz lo' sz' a H1 H2 [l [x [Ha [Hb [Hr Hst]]]]].
  exists l, x; repeat split; try lia; assumption.
Qed.

Lemma mfailf_prefix : forall c start mid lo sz a x,
  Cp.mrun G c start a mid x -> mfailf c mid lo sz x -> mfailf c start lo sz a.
Proof.
  intros c start mid lo sz a x Hpre [l [y [Ha [Hb [Hr Hst]]]]].
  exists l, y; repeat split; try assumption.
  eapply Cp.mrun_trans; eassumption.
Qed.

(** A check whose guard does not hold has no step. *)
Lemma stuck_chk : forall c l g v nxt a,
  Cp.get c l = Cp.IChk g v nxt -> P.gtest g a <> v -> stuck c l a.
Proof.
  intros c l g v nxt a Hi Hne m x [n Hs].
  pose proof (Cp.step_cases G n c l a m x Hs) as Hsc; rewrite Hi in Hsc; simpl in Hsc.
  destruct Hsc as [_ [_ [_ Hg]]]; congruence.
Qed.

(** A call has no step when the callee cannot reach its own exit — which is the
    case when the callee fails, by [crun_complete] and [ok_not_err]. *)
Lemma stuck_call_body : forall s a,
  execE s a Err -> forall x, ~ Cp.crun G s a x.
Proof.
  intros s a He x Hc.
  eapply ok_not_err; [ eapply Cp.crun_complete; exact Hc | exact He ].
Qed.

Lemma stuck_call : forall c l p nxt a,
  Cp.get c l = Cp.ICall p nxt -> execE (G p) a Err -> stuck c l a.
Proof.
  intros c l p nxt a Hi He m x [n Hs].
  pose proof (Cp.step_cases G n c l a m x Hs) as Hsc; rewrite Hi in Hsc; simpl in Hsc.
  destruct Hsc as [_ [k [_ Hsub]]].
  eapply stuck_call_body; [ exact He | exists k; exact Hsub ].
Qed.

Lemma stuck_uncall : forall c l p nxt a,
  Cp.get c l = Cp.IUncall p nxt -> execE (invert (G p)) a Err -> stuck c l a.
Proof.
  intros c l p nxt a Hi He m x [n Hs].
  pose proof (Cp.step_cases G n c l a m x Hs) as Hsc; rewrite Hi in Hsc; simpl in Hsc.
  destruct Hsc as [_ [k [_ Hsub]]].
  eapply stuck_call_body; [ exact He | exists k; exact Hsub ].
Qed.

(* ===================================================================== *)
(** ** The theorem the totality checker rests on.

    A source assertion failure makes the compiled code get stuck strictly inside
    the fragment.  Contrapositively: if the compiled code never gets stuck inside
    (i.e. [ERR] is unreachable in [smv.py]'s model), then no assertion can fail —
    which is exactly what the checker concludes from a proof of
    [INVARSPEC pc != ERR]. *)

Definition Pfail (s : stmt) (a : P.state) (o : outcome) : Prop :=
  o = Err -> forall c base,
    Cp.holds c base (Cp.comp s base) -> mfail c base (Cp.csize s) a.

Definition Qfail (g1 : P.guard) (s1 s2 : stmt) (g2 : P.guard)
                 (a : P.state) (o : outcome) : Prop :=
  o = Err -> forall c base,
    Cp.holds c base (Cp.comp (Loop g1 s1 s2 g2) base) ->
    mfailf c (S base) base (Cp.csize (Loop g1 s1 s2 g2)) a.

Lemma fail_sound : forall s a o, execE s a o -> Pfail s a o.
Proof.
  intros s a o H.
  induction H using execE_mut
    with (P0 := fun g1 s1 s2 g2 a o (_ : lpE g1 s1 s2 g2 a o) => Qfail g1 s1 s2 g2 a o);
    unfold Pfail, Qfail in *; intros Heq c base Hh; try discriminate.
  (* X_Seq with an error in the second half *)
  - apply Cp.holds_app in Hh as [Hh1 Hh2]; rewrite Cp.comp_length in Hh2.
    eapply mfailf_widen; [ | | eapply mfailf_prefix ].
    + instantiate (1 := base + Cp.csize s1). lia.
    + instantiate (1 := Cp.csize s2). simpl; lia.
    + apply (Cp.comp_sound G s1 a m (execE_ok_exec s1 a m H) c base Hh1).
    + apply (IHexecE2 Heq c (base + Cp.csize s1) Hh2).
  (* X_Loop with an error inside the iteration *)
  - assert (Hlo := Hh); apply Cp.holds_loop in Hlo as [Hck [_ [_ [_ _]]]].
    destruct (IHexecE Heq c base Hh) as [ll [xx [Ha [Hb [Hr Hst]]]]].
    exists ll, xx; repeat split; try lia; try assumption.
    eapply Cp.MR_step; [ eapply Cp.M_Chk; [ exact Hck | exact e ] | exact Hr ].
  (* X_Call *)
  - simpl in Hh; apply Cp.holds_cons in Hh as [Hi _]. subst o.
    exists base, a; repeat split; [ lia | simpl; lia | apply Cp.MR_refl | ].
    eapply stuck_call; [ exact Hi | assumption ].
  (* X_Uncall *)
  - simpl in Hh; apply Cp.holds_cons in Hh as [Hi _]. subst o.
    exists base, a; repeat split; [ lia | simpl; lia | apply Cp.MR_refl | ].
    eapply stuck_uncall; [ exact Hi | assumption ].
  (* X_SeqErr *)
  - apply Cp.holds_app in Hh as [Hh1 _].
    eapply mfailf_widen; [ | | apply (IHexecE eq_refl c base Hh1) ];
      [ lia | simpl; lia ].
  (* X_IfTBodyErr *)
  - apply Cp.holds_if in Hh as [Hbr [Hh1 [_ [_ _]]]].
    destruct (IHexecE eq_refl c (S base) Hh1) as [ll [xx [Ha [Hb [Hr Hst]]]]].
    exists ll, xx; repeat split; try (simpl; lia); try assumption.
    eapply Cp.MR_step; [ eapply Cp.M_BrT; [ exact Hbr | exact e ] | exact Hr ].
  (* X_IfTExitErr: the exit assertion fails *)
  - apply Cp.holds_if in Hh as [Hbr [Hh1 [Hck1 [_ _]]]].
    exists (S base + Cp.csize s1), b; repeat split; try (simpl; lia).
    + eapply Cp.MR_step; [ eapply Cp.M_BrT; [ exact Hbr | exact e ] | ].
      apply (Cp.comp_sound G s1 a b (execE_ok_exec s1 a b H) c (S base) Hh1).
    + eapply stuck_chk; [ exact Hck1 | rewrite e0; discriminate ].
  (* X_IfFBodyErr *)
  - apply Cp.holds_if in Hh as [Hbr [_ [_ [Hh2 _]]]].
    destruct (IHexecE eq_refl c (S base + Cp.csize s1 + 1) Hh2)
      as [ll [xx [Ha [Hb [Hr Hst]]]]].
    exists ll, xx; repeat split; try (simpl; lia); try assumption.
    eapply Cp.MR_step; [ eapply Cp.M_BrF; [ exact Hbr | exact e ] | exact Hr ].
  (* X_IfFExitErr *)
  - apply Cp.holds_if in Hh as [Hbr [_ [_ [Hh2 Hck2]]]].
    exists (S base + Cp.csize s1 + 1 + Cp.csize s2), b; repeat split; try (simpl; lia).
    + eapply Cp.MR_step; [ eapply Cp.M_BrF; [ exact Hbr | exact e ] | ].
      apply (Cp.comp_sound G s2 a b (execE_ok_exec s2 a b H) c
               (S base + Cp.csize s1 + 1) Hh2).
    + eapply stuck_chk; [ exact Hck2 | rewrite e0; discriminate ].
  (* X_LoopEntryErr: the entry assertion fails *)
  - apply Cp.holds_loop in Hh as [Hck [_ [_ [_ _]]]].
    exists base, a; repeat split; try (simpl; lia).
    + apply Cp.MR_refl.
    + eapply stuck_chk; [ exact Hck | rewrite e; discriminate ].
  (* LE_more with an error further round *)
  - assert (Hlo := Hh); apply Cp.holds_loop in Hlo as [_ [Hh1 [Hbr [Hh2 Hck]]]].
    destruct (IHexecE3 Heq c base Hh) as [ll [xx [Ha [Hb [Hr Hst]]]]].
    exists ll, xx; repeat split; try lia; try assumption.
    eapply Cp.mrun_trans;
      [ apply (Cp.comp_sound G s1 a a1 (execE_ok_exec s1 a a1 H) c (S base) Hh1) | ].
    eapply Cp.MR_step; [ eapply Cp.M_BrF; [ exact Hbr | exact e ] | ].
    eapply Cp.mrun_trans;
      [ apply (Cp.comp_sound G s2 a1 a2 (execE_ok_exec s2 a1 a2 H0) c
                 (S base + Cp.csize s1 + 1) Hh2) | ].
    eapply Cp.MR_step; [ eapply Cp.M_Chk; [ exact Hck | exact e0 ] | exact Hr ].
  (* LE_doErr *)
  - apply Cp.holds_loop in Hh as [_ [Hh1 [_ [_ _]]]].
    eapply mfailf_widen; [ | | apply (IHexecE eq_refl c (S base) Hh1) ];
      [ lia | simpl; lia ].
  (* LE_loopErr *)
  - assert (Hlo := Hh); apply Cp.holds_loop in Hlo as [_ [Hh1 [Hbr [Hh2 _]]]].
    destruct (IHexecE2 eq_refl c (S base + Cp.csize s1 + 1) Hh2)
      as [ll [xx [Ha [Hb [Hr Hst]]]]].
    exists ll, xx; repeat split; try (simpl; lia); try assumption.
    eapply Cp.mrun_trans;
      [ apply (Cp.comp_sound G s1 a a1 (execE_ok_exec s1 a a1 H) c (S base) Hh1) | ].
    eapply Cp.MR_step; [ eapply Cp.M_BrF; [ exact Hbr | exact e ] | exact Hr ].
  (* LE_backErr: the back-edge assertion fails *)
  - assert (Hlo := Hh); apply Cp.holds_loop in Hlo as [_ [Hh1 [Hbr [Hh2 Hck]]]].
    exists (S base + Cp.csize s1 + 1 + Cp.csize s2), a2; repeat split; try (simpl; lia).
    + eapply Cp.mrun_trans;
        [ apply (Cp.comp_sound G s1 a a1 (execE_ok_exec s1 a a1 H) c (S base) Hh1) | ].
      eapply Cp.MR_step; [ eapply Cp.M_BrF; [ exact Hbr | exact e ] | ].
      apply (Cp.comp_sound G s2 a1 a2 (execE_ok_exec s2 a1 a2 H0) c
               (S base + Cp.csize s1 + 1) Hh2).
    + eapply stuck_chk; [ exact Hck | rewrite e0; discriminate ].
Qed.

(** The form the checker uses: no reachable stuck state inside the compiled
    program means no assertion can fail. *)
Corollary no_stuck_no_error : forall s a,
  ~ mfail (Cp.entry_code s) 0 (Cp.csize s) a -> ~ execE s a Err.
Proof.
  intros s a Hno He; apply Hno.
  apply (fail_sound s a Err He eq_refl (Cp.entry_code s) 0 (Cp.holds_entry s)).
Qed.

End Sem.
End ErrSem.
