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
      - [fail_iff] — **the compiled program fails exactly when the source fails
        an assertion**, so a proof of [ERR]-unreachability really does mean "no
        assertion can fail": no missed failure ([fails_of_execE]) and no false
        alarm ([failsP_execE]).  "Failure" covers both a guard that does not hold
        and a *primitive with nowhere to go* ([X_PrimErr]): [pstep] is not
        required to be total, and that is exactly how [smv.py] treats `x *= 0`,
        `x /= 0`, an inexact `/=` and division by zero.

    Scope, honestly.  The framework's primitives and guards are abstract, so the
    *expression-level* traps of [smv.py] (floor division, two-sorted
    expressions, aliasing) are out of reach here; those are formalized against
    Janus's concrete expressions in [RevLowerExpr.v]/[RevLowerStmt.v].  And
    [smv.py] emits a **large-block** encoding, merging straight-line runs into a
    single transition, whereas [comp] emits one instruction per label; that those
    two describe the same relation is not proved here, and cannot be at this
    layer: what could go wrong in a large-block encoding is the composition order
    of the accumulated updates and the state a path condition is evaluated in,
    neither of which is expressible while [prim] and [guard] are abstract.  What
    is aligned is the control-flow skeleton and the meaning of ERR. *)

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
(* [pstep] is only required to be deterministic and reversible, not total, so a
   primitive can simply have nowhere to go.  That is not a corner case: it is how
   [smv.py] treats `x *= 0`, `x /= 0`, an inexact `/=` and division by zero in an
   expression -- all of them get an ERR edge.  Without this rule [fail_sound]
   would not cover them and the checker's conclusion would not be justified for
   any program using a partial primitive. *)
| X_PrimErr : forall p a,
    (forall b, ~ P.pstep p a b) -> execE (Prim p) a Err

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
    intro Hbad; inversion Hbad; subst; pin; try congruence;
    try (match goal with
         | Hn : forall _, ~ P.pstep _ _ _ |- _ => exfalso; eapply Hn; eassumption
         end);
    eauto.
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

(** *** Stuck for a *local* reason.

    [stuck] is "no rule applies", which at a call instruction conflates a callee
    that fails with one that diverges.  [localstuck] is the part that is visible
    at the instruction itself: a check whose guard does not hold, or a primitive
    with nowhere to go.  [INop] and [IBr] are never locally stuck ([gtest] is a
    function), so those are the only two ways. *)

Definition localstuck (c : Cp.code) (l : nat) (a : P.state) : Prop :=
  (exists g v nxt, Cp.get c l = Cp.IChk g v nxt /\ P.gtest g a <> v)
  \/ (exists p nxt, Cp.get c l = Cp.IPrim p nxt /\ forall b, ~ P.pstep p a b).

(** The machine-only notion of failure: the run reaches a label strictly inside
    the program whose instruction is locally stuck, or a call whose callee fails.
    Nothing here mentions the source — this is what a model checker observes. *)
Inductive failsP : stmt -> P.state -> Prop :=
| FP_local : forall s a l x,
    Cp.mrun G (Cp.entry_code s) 0 a l x -> l < Cp.csize s ->
    localstuck (Cp.entry_code s) l x -> failsP s a
| FP_call : forall s a l x p nxt,
    Cp.mrun G (Cp.entry_code s) 0 a l x -> l < Cp.csize s ->
    Cp.get (Cp.entry_code s) l = Cp.ICall p nxt -> failsP (G p) x -> failsP s a
| FP_uncall : forall s a l x p nxt,
    Cp.mrun G (Cp.entry_code s) 0 a l x -> l < Cp.csize s ->
    Cp.get (Cp.entry_code s) l = Cp.IUncall p nxt ->
    failsP (invert (G p)) x -> failsP s a.

(** The same, relative to a fragment placed at [base] in a larger code. *)
Definition badpointP (c : Cp.code) (l : nat) (a : P.state) : Prop :=
  localstuck c l a
  \/ (exists p nxt, Cp.get c l = Cp.ICall p nxt /\ failsP (G p) a)
  \/ (exists p nxt, Cp.get c l = Cp.IUncall p nxt /\ failsP (invert (G p)) a).

Definition failsAtP (c : Cp.code) (start lo sz : nat) (a : P.state) : Prop :=
  exists l x, lo <= l /\ l < lo + sz /\ Cp.mrun G c start a l x /\ badpointP c l x.

Lemma failsAtP_top : forall s a,
  failsAtP (Cp.entry_code s) 0 0 (Cp.csize s) a -> failsP s a.
Proof.
  intros s a [l [x [_ [Hb [Hr Hbp]]]]].
  destruct Hbp as [Hls | [[p [nxt [Hi Hf]]] | [p [nxt [Hi Hf]]]]].
  - eapply FP_local; [ exact Hr | lia | exact Hls ].
  - eapply FP_call; [ exact Hr | lia | exact Hi | exact Hf ].
  - eapply FP_uncall; [ exact Hr | lia | exact Hi | exact Hf ].
Qed.

Lemma failsAtP_widen : forall c start lo sz lo' sz' a,
  lo <= lo' -> lo' + sz' <= lo + sz ->
  failsAtP c start lo' sz' a -> failsAtP c start lo sz a.
Proof.
  intros c start lo sz lo' sz' a H1 H2 [l [x [Ha [Hb [Hr Hbp]]]]].
  exists l, x; repeat split; try lia; assumption.
Qed.

Lemma failsAtP_prefix : forall c start mid lo sz a y,
  Cp.mrun G c start a mid y -> failsAtP c mid lo sz y -> failsAtP c start lo sz a.
Proof.
  intros c start mid lo sz a y Hpre [l [x [Ha [Hb [Hr Hbp]]]]].
  exists l, x; repeat split; try assumption.
  eapply Cp.mrun_trans; eassumption.
Qed.

(** A primitive with nowhere to go has no step. *)
Lemma stuck_prim : forall c l p nxt a,
  Cp.get c l = Cp.IPrim p nxt -> (forall b, ~ P.pstep p a b) -> stuck c l a.
Proof.
  intros c l p nxt a Hi Hno m x [n Hs].
  pose proof (Cp.step_cases G n c l a m x Hs) as Hsc; rewrite Hi in Hsc; simpl in Hsc.
  destruct Hsc as [_ [_ Hp]]; eapply Hno; exact Hp.
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
    Cp.holds c base (Cp.comp s base) -> failsAtP c base base (Cp.csize s) a.

Definition Qfail (g1 : P.guard) (s1 s2 : stmt) (g2 : P.guard)
                 (a : P.state) (o : outcome) : Prop :=
  o = Err -> forall c base,
    Cp.holds c base (Cp.comp (Loop g1 s1 s2 g2) base) ->
    failsAtP c (S base) base (Cp.csize (Loop g1 s1 s2 g2)) a.

(** Witness builders, one per way of being a bad point. *)
Ltac bad_chk H := left; left; do 3 eexists; split; [ exact H | ].
Ltac bad_prim H := left; right; do 2 eexists; split; [ exact H | ].

Lemma fail_sound : forall s a o, execE s a o -> Pfail s a o.
Proof.
  intros s a o H.
  induction H using execE_mut
    with (P0 := fun g1 s1 s2 g2 a o (_ : lpE g1 s1 s2 g2 a o) => Qfail g1 s1 s2 g2 a o);
    unfold Pfail, Qfail in *; intros Heq c base Hh; try discriminate.
  (* X_Seq with an error in the second half *)
  - apply Cp.holds_app in Hh as [Hh1 Hh2]; rewrite Cp.comp_length in Hh2.
    eapply failsAtP_widen; [ | | eapply failsAtP_prefix ].
    + instantiate (1 := base + Cp.csize s1). lia.
    + instantiate (1 := Cp.csize s2). simpl; lia.
    + apply (Cp.comp_sound G s1 a m (execE_ok_exec s1 a m H) c base Hh1).
    + apply (IHexecE2 Heq c (base + Cp.csize s1) Hh2).
  (* X_Loop with an error inside the iteration *)
  - assert (Hlo := Hh); apply Cp.holds_loop in Hlo as [Hck [_ [_ [_ _]]]].
    destruct (IHexecE Heq c base Hh) as [ll [xx [Ha [Hb [Hr Hbp]]]]].
    exists ll, xx; repeat split; try lia; try assumption.
    eapply Cp.MR_step; [ eapply Cp.M_Chk; [ exact Hck | exact e ] | exact Hr ].
  (* X_Call *)
  - simpl in Hh; apply Cp.holds_cons in Hh as [Hi _]. subst o.
    exists base, a; repeat split; [ lia | simpl; lia | apply Cp.MR_refl | ].
    right; left; exists p, (S base); split; [ exact Hi | ].
    apply failsAtP_top.
    apply (IHexecE eq_refl (Cp.entry_code (G p)) 0 (Cp.holds_entry (G p))).
  (* X_Uncall *)
  - simpl in Hh; apply Cp.holds_cons in Hh as [Hi _]. subst o.
    exists base, a; repeat split; [ lia | simpl; lia | apply Cp.MR_refl | ].
    right; right; exists p, (S base); split; [ exact Hi | ].
    apply failsAtP_top.
    apply (IHexecE eq_refl (Cp.entry_code (invert (G p))) 0
             (Cp.holds_entry (invert (G p)))).
  (* X_SeqErr *)
  - apply Cp.holds_app in Hh as [Hh1 _].
    eapply failsAtP_widen; [ | | apply (IHexecE eq_refl c base Hh1) ];
      [ lia | simpl; lia ].
  (* X_IfTBodyErr *)
  - apply Cp.holds_if in Hh as [Hbr [Hh1 [_ [_ _]]]].
    destruct (IHexecE eq_refl c (S base) Hh1) as [ll [xx [Ha [Hb [Hr Hbp]]]]].
    exists ll, xx; repeat split; try (simpl; lia); try assumption.
    eapply Cp.MR_step; [ eapply Cp.M_BrT; [ exact Hbr | exact e ] | exact Hr ].
  (* X_IfTExitErr: the exit assertion fails *)
  - apply Cp.holds_if in Hh as [Hbr [Hh1 [Hck1 [_ _]]]].
    exists (S base + Cp.csize s1), b; repeat split; try (simpl; lia).
    + eapply Cp.MR_step; [ eapply Cp.M_BrT; [ exact Hbr | exact e ] | ].
      apply (Cp.comp_sound G s1 a b (execE_ok_exec s1 a b H) c (S base) Hh1).
    + bad_chk Hck1. rewrite e0; discriminate.
  (* X_IfFBodyErr *)
  - apply Cp.holds_if in Hh as [Hbr [_ [_ [Hh2 _]]]].
    destruct (IHexecE eq_refl c (S base + Cp.csize s1 + 1) Hh2)
      as [ll [xx [Ha [Hb [Hr Hbp]]]]].
    exists ll, xx; repeat split; try (simpl; lia); try assumption.
    eapply Cp.MR_step; [ eapply Cp.M_BrF; [ exact Hbr | exact e ] | exact Hr ].
  (* X_IfFExitErr *)
  - apply Cp.holds_if in Hh as [Hbr [_ [_ [Hh2 Hck2]]]].
    exists (S base + Cp.csize s1 + 1 + Cp.csize s2), b; repeat split; try (simpl; lia).
    + eapply Cp.MR_step; [ eapply Cp.M_BrF; [ exact Hbr | exact e ] | ].
      apply (Cp.comp_sound G s2 a b (execE_ok_exec s2 a b H) c
               (S base + Cp.csize s1 + 1) Hh2).
    + bad_chk Hck2. rewrite e0; discriminate.
  (* X_LoopEntryErr: the entry assertion fails *)
  - apply Cp.holds_loop in Hh as [Hck [_ [_ [_ _]]]].
    exists base, a; repeat split; try (simpl; lia).
    + apply Cp.MR_refl.
    + bad_chk Hck. rewrite e; discriminate.
  (* X_PrimErr: the primitive has nowhere to go *)
  - simpl in Hh; apply Cp.holds_cons in Hh as [Hi _].
    exists base, a; repeat split; try (simpl; lia).
    + apply Cp.MR_refl.
    + bad_prim Hi. exact n.
  (* LE_more with an error a further round in *)
  - assert (Hlo := Hh); apply Cp.holds_loop in Hlo as [_ [Hh1 [Hbr [Hh2 Hck]]]].
    destruct (IHexecE3 Heq c base Hh) as [ll [xx [Ha [Hb [Hr Hbp]]]]].
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
    eapply failsAtP_widen; [ | | apply (IHexecE eq_refl c (S base) Hh1) ];
      [ lia | simpl; lia ].
  (* LE_loopErr *)
  - assert (Hlo := Hh); apply Cp.holds_loop in Hlo as [_ [Hh1 [Hbr [Hh2 _]]]].
    destruct (IHexecE2 eq_refl c (S base + Cp.csize s1 + 1) Hh2)
      as [ll [xx [Ha [Hb [Hr Hbp]]]]].
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
    + bad_chk Hck. rewrite e0; discriminate.
Qed.

(** Half of the correspondence: a source failure is a machine failure. *)
Corollary fails_of_execE : forall s a, execE s a Err -> failsP s a.
Proof.
  intros s a He; apply failsAtP_top.
  apply (fail_sound s a Err He eq_refl (Cp.entry_code s) 0 (Cp.holds_entry s)).
Qed.

(* ===================================================================== *)
(** ** The converse: a machine failure is a source failure.

    [badpoint] is the source-side reading of a bad point: locally stuck, or a
    call whose callee fails *in the source*.  The outer induction on [failsP]
    turns the machine-side callee failure into that, so the two notions meet. *)

Definition badpoint (c : Cp.code) (l : nat) (a : P.state) : Prop :=
  localstuck c l a
  \/ (exists p nxt, Cp.get c l = Cp.ICall p nxt /\ execE (G p) a Err)
  \/ (exists p nxt, Cp.get c l = Cp.IUncall p nxt /\ execE (invert (G p)) a Err).

Lemma badpoint_nop : forall c l nxt a, Cp.get c l = Cp.INop nxt -> ~ badpoint c l a.
Proof.
  intros c l nxt a Hi [[[g [v [n [Hj _]]]] | [p [n [Hj _]]]]
                     | [[p [n [Hj _]]] | [p [n [Hj _]]]]]; congruence.
Qed.

Lemma badpoint_br : forall c l g lt lf a,
  Cp.get c l = Cp.IBr g lt lf -> ~ badpoint c l a.
Proof.
  intros c l g lt lf a Hi [[[g' [v [n [Hj _]]]] | [p [n [Hj _]]]]
                          | [[p [n [Hj _]]] | [p [n [Hj _]]]]]; congruence.
Qed.

Lemma badpoint_chk : forall c l g v nxt a,
  Cp.get c l = Cp.IChk g v nxt -> badpoint c l a -> P.gtest g a <> v.
Proof.
  intros c l g v nxt a Hi [[[g' [v' [n [Hj Hne]]]] | [p [n [Hj _]]]]
                          | [[p [n [Hj _]]] | [p [n [Hj _]]]]];
    congruence.   (* the good case too: congruence chains g'=g, v'=v with Hne *)
Qed.

Lemma badpoint_prim : forall c l p nxt a,
  Cp.get c l = Cp.IPrim p nxt -> badpoint c l a -> forall b, ~ P.pstep p a b.
Proof.
  intros c l p nxt a Hi [[[g [v [n [Hj _]]]] | [p' [n [Hj Hno]]]]
                        | [[p' [n [Hj _]]] | [p' [n [Hj _]]]]];
    try congruence.
  assert (p' = p) by congruence; subst; exact Hno.
Qed.

Lemma badpoint_call : forall c l p nxt a,
  Cp.get c l = Cp.ICall p nxt -> badpoint c l a -> execE (G p) a Err.
Proof.
  intros c l p nxt a Hi [[[g [v [n [Hj _]]]] | [p' [n [Hj _]]]]
                        | [[p' [n [Hj He]]] | [p' [n [Hj _]]]]];
    congruence.
Qed.

Lemma badpoint_uncall : forall c l p nxt a,
  Cp.get c l = Cp.IUncall p nxt -> badpoint c l a -> execE (invert (G p)) a Err.
Proof.
  intros c l p nxt a Hi [[[g [v [n [Hj _]]]] | [p' [n [Hj _]]]]
                        | [[p' [n [Hj _]]] | [p' [n [Hj He]]]]];
    congruence.
Qed.

(** "A run from a fragment's entry that ends at a bad point either fails inside
    the fragment, or completes it and the bad point comes afterwards."  The
    disjunction is what makes this compose: no statement about *first* arrivals
    is needed, and a fragment re-entered by a loop back edge is handled by the
    step count going down. *)
Definition Rc (n : nat) : Prop :=
  forall s c base a l x,
    Cp.holds c base (Cp.comp s base) ->
    Cp.mrunn G n c base a l x -> badpoint c l x ->
    execE s a Err
    \/ (exists y n2, exec G s a y
          /\ Cp.mrunn G n2 c (base + Cp.csize s) y l x /\ n2 < n).

Definition Rlp (n : nat) : Prop :=
  forall g1 s1 s2 g2 c base a l x,
    Cp.holds c base (Cp.comp (Loop g1 s1 s2 g2) base) ->
    Cp.mrunn G n c (S base) a l x -> badpoint c l x ->
    lpE g1 s1 s2 g2 a Err
    \/ (exists y n2, lp G g1 s1 s2 g2 a y
          /\ Cp.mrunn G n2 c (base + Cp.csize (Loop g1 s1 s2 g2)) y l x /\ n2 < n).

Lemma reach_bad : forall n, Rc n /\ Rlp n.
Proof.
  intro n; induction n as [n IH] using (well_founded_induction lt_wf).
  assert (IHc : forall m, m < n -> Rc m) by (intros m Hm; apply (IH m Hm)).
  assert (IHl : forall m, m < n -> Rlp m) by (intros m Hm; apply (IH m Hm)).
  clear IH.
  assert (Hc : Rc n).
  { unfold Rc; induction s; intros c base a l x Hh Hr Hbp.
    (* Skip *)
    - simpl in Hh; apply Cp.holds_cons in Hh as [Hi _].
      destruct (Cp.run_cases G n c base a l x Hr)
        as [[Hz [Hl Hb]] | [k1 [k2 [mm [yy [Hn [Hs Hrest]]]]]]].
      + subst; exfalso; eapply badpoint_nop; eassumption.
      + pose proof (Cp.step_cases G k1 c base a mm yy Hs) as Hsc;
          rewrite Hi in Hsc; simpl in Hsc; destruct Hsc as [Hk1 [Hm Hx]]; subst.
        right; exists a, k2; repeat split; [ apply E_Skip | | lia ].
        replace (base + Cp.csize Skip) with (S base) by (simpl; lia). exact Hrest.
    (* Prim *)
    - simpl in Hh; apply Cp.holds_cons in Hh as [Hi _].
      destruct (Cp.run_cases G n c base a l x Hr)
        as [[Hz [Hl Hb]] | [k1 [k2 [mm [yy [Hn [Hs Hrest]]]]]]].
      + subst; left; apply X_PrimErr; eapply badpoint_prim; eassumption.
      + pose proof (Cp.step_cases G k1 c base a mm yy Hs) as Hsc;
          rewrite Hi in Hsc; simpl in Hsc; destruct Hsc as [Hk1 [Hm Hps]]; subst.
        right; exists yy, k2; repeat split; [ apply E_Prim; exact Hps | | lia ].
        replace (base + Cp.csize (Prim p)) with (S base) by (simpl; lia). exact Hrest.
    (* Seq *)
    - simpl in Hh; apply Cp.holds_app in Hh as [Hh1 Hh2];
        rewrite Cp.comp_length in Hh2.
      destruct (IHs1 c base a l x Hh1 Hr Hbp) as [Herr | [y [n2 [Hex1 [Hr2 Hlt2]]]]].
      + left; apply X_SeqErr; exact Herr.
      + destruct (IHc n2 Hlt2 s2 c (base + Cp.csize s1) y l x Hh2 Hr2 Hbp)
          as [Herr | [z [n3 [Hex2 [Hr3 Hlt3]]]]].
        * left; eapply X_Seq; [ apply exec_execE; exact Hex1 | exact Herr ].
        * right; exists z, n3; repeat split; [ eapply E_Seq; eassumption | | lia ].
          replace (base + Cp.csize (Seq s1 s2))
            with (base + Cp.csize s1 + Cp.csize s2) by (simpl; lia). exact Hr3.
    (* If *)
    - assert (Hif := Hh); apply Cp.holds_if in Hif as [Hbr [Hh1 [Hck1 [Hh2 Hck2]]]].
      destruct (Cp.run_cases G n c base a l x Hr)
        as [[Hz [Hl Hb]] | [k1 [k2 [mm [yy [Hn [Hs Hrest]]]]]]].
      + subst; exfalso; eapply badpoint_br; eassumption.
      + pose proof (Cp.step_cases G k1 c base a mm yy Hs) as Hsc;
          rewrite Hbr in Hsc; simpl in Hsc;
          destruct Hsc as [Hk1 [Hx [[Hg Hm] | [Hg Hm]]]]; subst.
        (* then-branch *)
        * destruct (IHc k2 (ltac:(lia)) s1 c (S base) a l x Hh1 Hrest Hbp)
            as [Herr | [y [n3 [Hex [Hr3 Hlt3]]]]].
          -- left; eapply X_IfTBodyErr; [ exact Hg | exact Herr ].
          -- destruct (Cp.run_cases G n3 c (S base + Cp.csize s1) y l x Hr3)
               as [[Hz' [Hl' Hb']] | [q1 [q2 [m1 [y1 [Hq [Hs1' Hrest1]]]]]]].
             ++ rewrite Hl', Hb' in Hbp; left; eapply X_IfTExitErr;
                  [ exact Hg | apply exec_execE; exact Hex | ].
                destruct (P.gtest g2 y) eqn:Hgy; [ | reflexivity ].
                exfalso; eapply (badpoint_chk c (S base + Cp.csize s1) g2 true
                                   (base + (Cp.csize s1 + Cp.csize s2 + 3)) y Hck1 Hbp).
                exact Hgy.
             ++ pose proof (Cp.step_cases G q1 c (S base + Cp.csize s1) y m1 y1 Hs1')
                  as Hsc1; rewrite Hck1 in Hsc1; simpl in Hsc1;
                  destruct Hsc1 as [Hq1 [Hm1 [Hy1 Hg2]]]; subst.
                right; exists y, q2; repeat split;
                  [ eapply E_IfT; eassumption | | lia ].
                replace (base + Cp.csize (If g1 s1 s2 g2))
                  with (base + (Cp.csize s1 + Cp.csize s2 + 3)) by (simpl; lia).
                exact Hrest1.
        (* else-branch *)
        * destruct (IHc k2 (ltac:(lia)) s2 c (S base + Cp.csize s1 + 1) a l x
                        Hh2 Hrest Hbp)
            as [Herr | [y [n3 [Hex [Hr3 Hlt3]]]]].
          -- left; eapply X_IfFBodyErr; [ exact Hg | exact Herr ].
          -- destruct (Cp.run_cases G n3 c (S base + Cp.csize s1 + 1 + Cp.csize s2)
                         y l x Hr3)
               as [[Hz' [Hl' Hb']] | [q1 [q2 [m1 [y1 [Hq [Hs1' Hrest1]]]]]]].
             ++ rewrite Hl', Hb' in Hbp; left; eapply X_IfFExitErr;
                  [ exact Hg | apply exec_execE; exact Hex | ].
                destruct (P.gtest g2 y) eqn:Hgy; [ reflexivity | ].
                exfalso; eapply (badpoint_chk c
                                   (S base + Cp.csize s1 + 1 + Cp.csize s2) g2 false
                                   (base + (Cp.csize s1 + Cp.csize s2 + 3)) y Hck2 Hbp).
                exact Hgy.
             ++ pose proof (Cp.step_cases G q1 c
                              (S base + Cp.csize s1 + 1 + Cp.csize s2) y m1 y1 Hs1')
                  as Hsc1; rewrite Hck2 in Hsc1; simpl in Hsc1;
                  destruct Hsc1 as [Hq1 [Hm1 [Hy1 Hg2]]]; subst.
                right; exists y, q2; repeat split;
                  [ eapply E_IfF; eassumption | | lia ].
                replace (base + Cp.csize (If g1 s1 s2 g2))
                  with (base + (Cp.csize s1 + Cp.csize s2 + 3)) by (simpl; lia).
                exact Hrest1.
    (* Loop *)
    - assert (Hlo := Hh); apply Cp.holds_loop in Hlo as [Hck [_ [_ [_ _]]]].
      destruct (Cp.run_cases G n c base a l x Hr)
        as [[Hz [Hl Hb]] | [k1 [k2 [mm [yy [Hn [Hs Hrest]]]]]]].
      + rewrite Hl, Hb in Hbp; left; apply X_LoopEntryErr.
        destruct (P.gtest g1 a) eqn:Hga; [ | reflexivity ].
        exfalso; eapply (badpoint_chk c base g1 true (S base) a Hck Hbp); exact Hga.
      + pose proof (Cp.step_cases G k1 c base a mm yy Hs) as Hsc;
          rewrite Hck in Hsc; simpl in Hsc;
          destruct Hsc as [Hk1 [Hm [Hx Hg]]]; subst.
        destruct (IHl k2 (ltac:(lia)) g1 s1 s2 g2 c base a l x Hh Hrest Hbp)
          as [Herr | [y [n3 [Hlp [Hr3 Hlt3]]]]].
        * left; eapply X_Loop; [ exact Hg | exact Herr ].
        * right; exists y, n3; repeat split; [ eapply E_Loop; eassumption | | lia ].
          exact Hr3.
    (* Call *)
    - simpl in Hh; apply Cp.holds_cons in Hh as [Hi _].
      destruct (Cp.run_cases G n c base a l x Hr)
        as [[Hz [Hl Hb]] | [k1 [k2 [mm [yy [Hn [Hs Hrest]]]]]]].
      + subst; left; apply X_Call; eapply badpoint_call; eassumption.
      + pose proof (Cp.step_cases G k1 c base a mm yy Hs) as Hsc;
          rewrite Hi in Hsc; simpl in Hsc;
          destruct Hsc as [Hm [k [Hk Hsub]]]; subst.
        right; exists yy, k2; repeat split; [ | | lia ].
        * apply E_Call; eapply Cp.crun_complete; exists k; exact Hsub.
        * replace (base + Cp.csize (Call p)) with (S base) by (simpl; lia).
          exact Hrest.
    (* Uncall *)
    - simpl in Hh; apply Cp.holds_cons in Hh as [Hi _].
      destruct (Cp.run_cases G n c base a l x Hr)
        as [[Hz [Hl Hb]] | [k1 [k2 [mm [yy [Hn [Hs Hrest]]]]]]].
      + subst; left; apply X_Uncall; eapply badpoint_uncall; eassumption.
      + pose proof (Cp.step_cases G k1 c base a mm yy Hs) as Hsc;
          rewrite Hi in Hsc; simpl in Hsc;
          destruct Hsc as [Hm [k [Hk Hsub]]]; subst.
        right; exists yy, k2; repeat split; [ | | lia ].
        * apply E_Uncall; eapply Cp.crun_complete; exists k; exact Hsub.
        * replace (base + Cp.csize (Uncall p)) with (S base) by (simpl; lia).
          exact Hrest. }
  split; [ exact Hc | ].
  unfold Rlp; intros g1 s1 s2 g2 c base a l x Hh Hr Hbp.
  assert (Hlo := Hh); apply Cp.holds_loop in Hlo as [_ [Hh1 [Hbr [Hh2 Hck]]]].
  destruct (Hc s1 c (S base) a l x Hh1 Hr Hbp) as [Herr | [y [n2 [Hex1 [Hr2 Hlt2]]]]].
  - left; apply LE_doErr; exact Herr.
  - destruct (Cp.run_cases G n2 c (S base + Cp.csize s1) y l x Hr2)
      as [[Hz [Hl Hb]] | [k1 [k2 [mm [yy [Hn [Hs Hrest]]]]]]].
    + subst; exfalso; eapply badpoint_br; eassumption.
    + pose proof (Cp.step_cases G k1 c (S base + Cp.csize s1) y mm yy Hs) as Hsc;
        rewrite Hbr in Hsc; simpl in Hsc;
        destruct Hsc as [Hk1 [Hy [[Hg Hm] | [Hg Hm]]]]; subst.
      (* exit on this round *)
      * right; exists y, k2; repeat split;
          [ apply L_one; assumption | | lia ].
        replace (base + Cp.csize (Loop g1 s1 s2 g2))
          with (base + (Cp.csize s1 + Cp.csize s2 + 3)) by (simpl; lia). exact Hrest.
      (* another round *)
      * destruct (IHc k2 (ltac:(lia)) s2 c (S base + Cp.csize s1 + 1) y l x
                      Hh2 Hrest Hbp)
          as [Herr | [z [n4 [Hex2 [Hr4 Hlt4]]]]].
        -- left; eapply LE_loopErr;
             [ apply exec_execE; exact Hex1 | exact Hg | exact Herr ].
        -- destruct (Cp.run_cases G n4 c
                       (S base + Cp.csize s1 + 1 + Cp.csize s2) z l x Hr4)
             as [[Hz' [Hl' Hb']] | [q1 [q2 [m1 [z1 [Hq [Hs1' Hrest1]]]]]]].
           ++ rewrite Hl', Hb' in Hbp; left; eapply LE_backErr;
                [ apply exec_execE; exact Hex1 | exact Hg
                | apply exec_execE; exact Hex2 | ].
              destruct (P.gtest g1 z) eqn:Hgz; [ reflexivity | ].
              exfalso; eapply (badpoint_chk c
                                 (S base + Cp.csize s1 + 1 + Cp.csize s2) g1 false
                                 (S base) z Hck Hbp); exact Hgz.
           ++ pose proof (Cp.step_cases G q1 c
                            (S base + Cp.csize s1 + 1 + Cp.csize s2) z m1 z1 Hs1')
                as Hsc1; rewrite Hck in Hsc1; simpl in Hsc1;
                destruct Hsc1 as [Hq1 [Hm1 [Hz1 Hg1']]]; subst.
              destruct (IHl q2 (ltac:(lia)) g1 s1 s2 g2 c base z l x Hh Hrest1 Hbp)
                as [Herr | [w [n6 [Hlp [Hr6 Hlt6]]]]].
              ** left; eapply LE_more;
                   [ apply exec_execE; exact Hex1 | exact Hg
                   | apply exec_execE; exact Hex2 | exact Hg1' | exact Herr ].
              ** right; exists w, n6; repeat split; [ | | lia ].
                 --- eapply L_more; eassumption.
                 --- exact Hr6.
Qed.

(** The converse of [fail_sound], and with it the correspondence. *)
Lemma failsP_execE : forall s a, failsP s a -> execE s a Err.
Proof.
  intros s a H; induction H as
    [ s a l x Hr Hlt Hls | s a l x p nxt Hr Hlt Hi Hf IH
    | s a l x p nxt Hr Hlt Hi Hf IH ];
    destruct Hr as [n Hr];
    [ assert (Hbp : badpoint (Cp.entry_code s) l x) by (left; exact Hls)
    | assert (Hbp : badpoint (Cp.entry_code s) l x)
        by (right; left; exists p, nxt; split; [ exact Hi | exact IH ])
    | assert (Hbp : badpoint (Cp.entry_code s) l x)
        by (right; right; exists p, nxt; split; [ exact Hi | exact IH ]) ];
    (destruct (proj1 (reach_bad n) s (Cp.entry_code s) 0 a l x
                 (Cp.holds_entry s) Hr Hbp) as [Herr | [y [n2 [Hex [Hr2 _]]]]];
     [ exact Herr | ];
     rewrite Nat.add_0_l in Hr2;
     destruct (Cp.halt_run_refl G n2 (Cp.entry_code s) (Cp.csize s) y l x
                 (Cp.entry_halt s) Hr2) as [Hl _]; lia).
Qed.

(** **The** correspondence: the compiled program fails exactly when the source
    fails an assertion.  This is what makes a proof of [ERR]-unreachability mean
    "no assertion can fail", in both directions — no missed failure, and no false
    alarm. *)
Theorem fail_iff : forall s a, execE s a Err <-> failsP s a.
Proof.
  intros s a; split; intro H.
  - apply fails_of_execE; exact H.
  - apply failsP_execE; exact H.
Qed.

Corollary no_fail_no_error : forall s a, ~ failsP s a -> ~ execE s a Err.
Proof. intros s a Hno He; apply Hno, fails_of_execE; exact He. Qed.

End Sem.
End ErrSem.
