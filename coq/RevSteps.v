(** * RevSteps.v — what compilation costs, and what running backwards costs

    [RevCompile.v] proves the compiled code computes the same relation as the
    source ([crun_iff]).  It says nothing about **how long** it takes, and its
    machine is already counted — [mstepn]/[mrunn] carry the number of
    instructions executed, including the ones inside nested calls.  What was
    missing was a count on the *source* side to compare it against.

    This file supplies one.  [execn n s a b] is the big-step semantics with a
    step count that charges exactly the run-time actions a Janus program
    performs:

      - one for each primitive executed, and one for [Skip];
      - one for each **guard test** and one for each **exit assertion** (so a
        conditional costs its branch plus two, and each loop turn costs its body
        plus the tests it makes);
      - one for each call or uncall instruction, *plus* the cost of the callee;
      - **nothing** for sequencing, which is not a run-time action.

    Two results follow, and the second is the one specific to reversible
    computing.

    - [compilation_is_step_exact_iff] : [execn n s a b] **iff** the compiled code
      runs from [a] to the exit in exactly [n] steps.  Flattening structured
      control flow into indexed jumps costs nothing: the factor is 1, not a
      constant greater than 1.  That is not automatic — a compiler with implicit
      fall-through, or one that emits a jump to join the arms of a conditional,
      would pay for it.  Here instructions carry their successor label
      explicitly, [Seq] emits no glue, and each test/assertion of the big-step
      rules becomes exactly one [IBr] or [IChk].

      The forward half is about a *derivation*; the converse says no other run
      of the same code reaches the exit in a different count, and needs the
      machine to be deterministic ([mstepn_det], [mrunn_det_halt]).  It is what
      makes the count a property of the program rather than of the derivation
      that happened to be written down.

    - [execn_rev] : [execn n s a b -> execn n (invert s) b a].  **Running a
      reversible program backwards costs exactly as much as running it
      forwards.**  [RevCore.exec_rev] gives the relation; this gives the cost,
      and it is not obvious from the relation, because [invert] rebuilds the
      control flow — it swaps the entry test of an [If] with its exit assertion,
      swaps the two guards of a [Loop], and reverses the order of the loop's
      rounds.  The count comes out equal because the multiset of actions is
      preserved even though their order is not.

    Together with [csize_invert] -- the inverted program occupies the *same
    number of labels* -- they give [inverse_costs_the_same]: the compiled inverse runs in
    the same number of machine steps as the compiled program, in the same amount
    of code.  That is the quantitative content of "an inverse interpreter is not
    an approximation" — [RevSemantics.inv] is not merely the same relation as
    [big], it is the same relation at the same cost.

    As everywhere in this development, the language instance is *projected out*
    of the one chain [RevSmallStep -> RevDenote -> RevFix -> RevCompile]: applying
    [RevLang] twice yields two distinct inductive types, and none of the theorems
    below would typecheck across them. *)

From Stdlib Require Import Arith Lia.
Require Import RevCore RevSmallStep RevDenote RevFix RevCompile.

Module Steps (P : REV_PRIM).

Module Cp := RevCompile.Compile P.
Module L := Cp.L.

Section WithEnv.
Variable G : L.pname -> L.stmt.

(* ===================================================================== *)
(** ** The counted big-step semantics.

    Rule for rule [RevCore.exec], with a count added.  Read the count as "how
    many run-time actions this derivation performs": [Seq] is free because
    sequencing is not an action, while a conditional's entry test and exit
    assertion are two, and they are exactly the two instructions [comp] emits
    around the branch. *)

Inductive execn : nat -> L.stmt -> P.state -> P.state -> Prop :=
| X_Skip : forall a, execn 1 L.Skip a a
| X_Prim : forall p a b, P.pstep p a b -> execn 1 (L.Prim p) a b
| X_Seq  : forall n1 n2 s1 s2 a m b,
    execn n1 s1 a m -> execn n2 s2 m b -> execn (n1 + n2) (L.Seq s1 s2) a b
| X_IfT  : forall n g1 s1 s2 g2 a b,
    P.gtest g1 a = true -> execn n s1 a b -> P.gtest g2 b = true ->
    execn (1 + n + 1) (L.If g1 s1 s2 g2) a b
| X_IfF  : forall n g1 s1 s2 g2 a b,
    P.gtest g1 a = false -> execn n s2 a b -> P.gtest g2 b = false ->
    execn (1 + n + 1) (L.If g1 s1 s2 g2) a b
| X_Loop : forall k g1 s1 s2 g2 a b,
    P.gtest g1 a = true -> lpn k g1 s1 s2 g2 a b ->
    execn (1 + k) (L.Loop g1 s1 s2 g2) a b
| X_Call : forall n p a b, execn n (G p) a b -> execn (1 + n) (L.Call p) a b
| X_Uncall : forall n p a b,
    execn n (L.invert (G p)) a b -> execn (1 + n) (L.Uncall p) a b

with lpn : nat -> P.guard -> L.stmt -> L.stmt -> P.guard -> P.state -> P.state -> Prop :=
| Xl_one : forall n1 g1 s1 s2 g2 a b,
    execn n1 s1 a b -> P.gtest g2 b = true -> lpn (n1 + 1) g1 s1 s2 g2 a b
| Xl_more : forall n1 n2 k g1 s1 s2 g2 a a1 a2 b,
    execn n1 s1 a a1 -> P.gtest g2 a1 = false ->
    execn n2 s2 a1 a2 -> P.gtest g1 a2 = false ->
    lpn k g1 s1 s2 g2 a2 b ->
    lpn (n1 + 1 + n2 + 1 + k) g1 s1 s2 g2 a b.

Scheme execn_mut := Induction for execn Sort Prop
  with lpn_mut   := Induction for lpn   Sort Prop.

(** Counting does not change the relation: erasing the count gives [exec], and
    every [exec] derivation carries one. *)

Lemma execn_exec : forall n s a b, execn n s a b -> L.exec G s a b.
Proof.
  intros n s a b H.
  induction H using execn_mut
    with (P0 := fun k g1 s1 s2 g2 a b (_ : lpn k g1 s1 s2 g2 a b) =>
                  L.lp G g1 s1 s2 g2 a b).
  - apply L.E_Skip.
  - apply L.E_Prim; assumption.
  - eapply L.E_Seq; eassumption.
  - apply L.E_IfT; assumption.
  - apply L.E_IfF; assumption.
  - eapply L.E_Loop; eassumption.
  - apply L.E_Call; assumption.
  - apply L.E_Uncall; assumption.
  - apply L.L_one; assumption.
  - eapply L.L_more; eassumption.
Qed.

Lemma exec_execn : forall s a b, L.exec G s a b -> exists n, execn n s a b.
Proof.
  intros s a b H.
  induction H using L.exec_mut
    with (P0 := fun g1 s1 s2 g2 a b (_ : L.lp G g1 s1 s2 g2 a b) =>
                  exists k, lpn k g1 s1 s2 g2 a b).
  - exists 1; apply X_Skip.
  - exists 1; apply X_Prim; assumption.
  - destruct IHexec1 as [n1 H1]; destruct IHexec2 as [n2 H2].
    exists (n1 + n2); eapply X_Seq; eassumption.
  - destruct IHexec as [n Hn]; exists (1 + n + 1); apply X_IfT; assumption.
  - destruct IHexec as [n Hn]; exists (1 + n + 1); apply X_IfF; assumption.
  - destruct IHexec as [k Hk]; exists (1 + k); eapply X_Loop; eassumption.
  - destruct IHexec as [n Hn]; exists (1 + n); apply X_Call; assumption.
  - destruct IHexec as [n Hn]; exists (1 + n); apply X_Uncall; assumption.
  - destruct IHexec as [n1 H1]; exists (n1 + 1); apply Xl_one; assumption.
  - destruct IHexec1 as [n1 H1]; destruct IHexec2 as [n2 H2];
      destruct IHexec3 as [k Hk].
    exists (n1 + 1 + n2 + 1 + k); eapply Xl_more; eassumption.
Qed.

(* ===================================================================== *)
(** ** The compiled code performs exactly that many steps.

    Two casts do all the arithmetic bookkeeping: the count of a composite run is
    assembled from its parts and then shown equal to the count the rule charges.
    Taking the equation as the *last* goal is what lets [lia] see the parts. *)

Lemma step_then : forall n1 n2 n c l a m x l' b,
  Cp.mstepn G n1 c l a m x -> Cp.mrunn G n2 c m x l' b -> n1 + n2 = n ->
  Cp.mrunn G n c l a l' b.
Proof. intros; subst; eapply Cp.NR_step; eassumption. Qed.

Lemma run_then : forall n1 n2 n c l a m x l' b,
  Cp.mrunn G n1 c l a m x -> Cp.mrunn G n2 c m x l' b -> n1 + n2 = n ->
  Cp.mrunn G n c l a l' b.
Proof. intros; subst; eapply Cp.mrunn_trans; eassumption. Qed.

Definition Pcost (n : nat) (s : L.stmt) (a b : P.state) : Prop :=
  forall c base, Cp.holds c base (Cp.comp s base) ->
    Cp.mrunn G n c base a (base + Cp.csize s) b.

Definition Qcost (k : nat) (g1 : P.guard) (s1 s2 : L.stmt) (g2 : P.guard)
                 (a b : P.state) : Prop :=
  forall c base, Cp.holds c base (Cp.comp (L.Loop g1 s1 s2 g2) base) ->
    Cp.mrunn G k c (S base) a (base + Cp.csize (L.Loop g1 s1 s2 g2)) b.

Theorem comp_cost : forall n s a b, execn n s a b -> Pcost n s a b.
Proof.
  intros n s a b H.
  induction H using execn_mut
    with (P0 := fun k g1 s1 s2 g2 a b (_ : lpn k g1 s1 s2 g2 a b) =>
                  Qcost k g1 s1 s2 g2 a b);
    red; intros c base Hh.
  (* Skip *)
  - simpl in Hh; apply Cp.holds_cons in Hh as [Hi _].
    replace (base + Cp.csize L.Skip) with (S base) by (simpl; lia).
    eapply step_then with (n1 := 1) (n2 := 0);
      [ eapply Cp.N_Nop; exact Hi | apply Cp.NR_refl | lia ].
  (* Prim *)
  - simpl in Hh; apply Cp.holds_cons in Hh as [Hi _].
    replace (base + Cp.csize (L.Prim p)) with (S base) by (simpl; lia).
    eapply step_then with (n1 := 1) (n2 := 0);
      [ eapply Cp.N_Prim; [ exact Hi | eassumption ] | apply Cp.NR_refl | lia ].
  (* Seq: the counts add, and no glue instruction is emitted *)
  - simpl in Hh; apply Cp.holds_app in Hh as [Hh1 Hh2]; rewrite Cp.comp_length in Hh2.
    replace (base + Cp.csize (L.Seq s1 s2)) with (base + Cp.csize s1 + Cp.csize s2)
      by (simpl; lia).
    eapply run_then with (n1 := n1) (n2 := n2);
      [ apply (IHexecn1 c base Hh1)
      | apply (IHexecn2 c (base + Cp.csize s1) Hh2) | lia ].
  (* If, then-branch: one IBr in, one IChk out *)
  - apply Cp.holds_if in Hh as [Hbr [Hh1 [Hchk1 [_ _]]]].
    replace (base + Cp.csize (L.If g1 s1 s2 g2))
      with (base + (Cp.csize s1 + Cp.csize s2 + 3)) by (simpl; lia).
    eapply step_then with (n1 := 1) (n2 := n + 1);
      [ eapply Cp.N_BrT; [ exact Hbr | eassumption ] | | lia ].
    eapply run_then with (n1 := n) (n2 := 1);
      [ apply (IHexecn c (S base) Hh1) | | lia ].
    eapply step_then with (n1 := 1) (n2 := 0);
      [ eapply Cp.N_Chk; [ exact Hchk1 | eassumption ] | apply Cp.NR_refl | lia ].
  (* If, else-branch *)
  - apply Cp.holds_if in Hh as [Hbr [_ [_ [Hh2 Hchk2]]]].
    replace (base + Cp.csize (L.If g1 s1 s2 g2))
      with (base + (Cp.csize s1 + Cp.csize s2 + 3)) by (simpl; lia).
    eapply step_then with (n1 := 1) (n2 := n + 1);
      [ eapply Cp.N_BrF; [ exact Hbr | eassumption ] | | lia ].
    eapply run_then with (n1 := n) (n2 := 1);
      [ apply (IHexecn c (S base + Cp.csize s1 + 1) Hh2) | | lia ].
    eapply step_then with (n1 := 1) (n2 := 0);
      [ eapply Cp.N_Chk; [ exact Hchk2 | eassumption ] | apply Cp.NR_refl | lia ].
  (* Loop: the entry assertion, then the rounds *)
  - assert (Hh' := Hh); apply Cp.holds_loop in Hh as [Hchk [_ [_ [_ _]]]].
    eapply step_then with (n1 := 1) (n2 := k);
      [ eapply Cp.N_Chk; [ exact Hchk | eassumption ]
      | apply (IHexecn c base Hh') | lia ].
  (* Call: the instruction, plus the callee's own count *)
  - simpl in Hh; apply Cp.holds_cons in Hh as [Hi _].
    replace (base + Cp.csize (L.Call p)) with (S base) by (simpl; lia).
    eapply step_then with (n1 := S n) (n2 := 0);
      [ eapply Cp.N_Call; [ exact Hi | ] | apply Cp.NR_refl | lia ].
    specialize (IHexecn (Cp.entry_code (G p)) 0 (Cp.holds_entry (G p))).
    rewrite Nat.add_0_l in IHexecn; exact IHexecn.
  (* Uncall *)
  - simpl in Hh; apply Cp.holds_cons in Hh as [Hi _].
    replace (base + Cp.csize (L.Uncall p)) with (S base) by (simpl; lia).
    eapply step_then with (n1 := S n) (n2 := 0);
      [ eapply Cp.N_Uncall; [ exact Hi | ] | apply Cp.NR_refl | lia ].
    specialize (IHexecn (Cp.entry_code (L.invert (G p))) 0
                  (Cp.holds_entry (L.invert (G p)))).
    rewrite Nat.add_0_l in IHexecn; exact IHexecn.
  (* lp: the exit test holds, so this was the last round *)
  - apply Cp.holds_loop in Hh as [_ [Hh1 [Hbr [_ _]]]].
    replace (base + Cp.csize (L.Loop g1 s1 s2 g2))
      with (base + (Cp.csize s1 + Cp.csize s2 + 3)) by (simpl; lia).
    eapply run_then with (n1 := n1) (n2 := 1);
      [ apply (IHexecn c (S base) Hh1) | | lia ].
    eapply step_then with (n1 := 1) (n2 := 0);
      [ eapply Cp.N_BrT; [ exact Hbr | eassumption ] | apply Cp.NR_refl | lia ].
  (* lp: one more round -- body, exit test, second body, entry assertion *)
  - assert (Hh' := Hh); apply Cp.holds_loop in Hh as [_ [Hh1 [Hbr [Hh2 Hchk]]]].
    eapply run_then with (n1 := n1) (n2 := 1 + n2 + 1 + k);
      [ apply (IHexecn1 c (S base) Hh1) | | lia ].
    eapply step_then with (n1 := 1) (n2 := n2 + 1 + k);
      [ eapply Cp.N_BrF; [ exact Hbr | eassumption ] | | lia ].
    eapply run_then with (n1 := n2) (n2 := 1 + k);
      [ apply (IHexecn2 c (S base + Cp.csize s1 + 1) Hh2) | | lia ].
    eapply step_then with (n1 := 1) (n2 := k);
      [ eapply Cp.N_Chk; [ exact Hchk | eassumption ]
      | apply (IHexecn3 c base Hh') | lia ].
Qed.

(** **The** cost theorem: compiling costs nothing.  A source derivation charging
    [n] run-time actions becomes a machine run of exactly [n] instructions --
    including the instructions executed inside nested calls, which is what
    [mrunn]'s count measures. *)
Theorem compilation_is_step_exact : forall n s a b,
  execn n s a b -> Cp.mrunn G n (Cp.entry_code s) 0 a (Cp.csize s) b.
Proof.
  intros n s a b H.
  specialize (comp_cost n s a b H (Cp.entry_code s) 0 (Cp.holds_entry s)) as Hr.
  rewrite Nat.add_0_l in Hr; exact Hr.
Qed.

(** ...and the uncounted [crun] is recovered, so this really is a refinement of
    [crun_sound] rather than a different statement. *)
Corollary compilation_is_step_exact_crun : forall n s a b,
  execn n s a b -> Cp.crun G s a b.
Proof. intros n s a b H; exists n; apply compilation_is_step_exact; exact H. Qed.

(* ===================================================================== *)
(** ** The converse: the machine cannot take a different number of steps.

    [compilation_is_step_exact] is a statement about a *derivation*: charge the
    source [n] and the machine performs [n] instructions.  On its own that leaves
    open whether some *other* run of the same compiled code could reach the exit
    in a different count — so "the compiler adds no overhead" would be only half
    proved.

    It cannot: the machine is deterministic.  [pstep_det] is a [REV_PRIM] law and
    [gtest] is a function, so an instruction determines its successor, its state
    *and its cost*; the only instruction whose cost is not 1 is a call, and its
    cost is the callee's run, which is deterministic by the same induction.
    Reaching the exit pins the count down because [entry_halt] puts an [IHalt]
    there, so a run that arrives has to stop. *)

(** [Cp.step_cases] loses the exact count at a call ([k < n] rather than
    [n = S k]), which is all its callers needed.  This is the same case analysis
    keeping the equation. *)
Lemma step_cases_exact : forall n c l a m x, Cp.mstepn G n c l a m x ->
  match Cp.get c l with
  | Cp.INop nxt => n = 1 /\ m = nxt /\ x = a
  | Cp.IPrim p nxt => n = 1 /\ m = nxt /\ P.pstep p a x
  | Cp.IBr g lt lf => n = 1 /\ x = a
      /\ ((P.gtest g a = true /\ m = lt) \/ (P.gtest g a = false /\ m = lf))
  | Cp.IChk g v nxt => n = 1 /\ m = nxt /\ x = a /\ P.gtest g a = v
  | Cp.ICall p nxt => m = nxt
      /\ exists k, n = S k
           /\ Cp.mrunn G k (Cp.entry_code (G p)) 0 a (Cp.csize (G p)) x
  | Cp.IUncall p nxt => m = nxt
      /\ exists k, n = S k
           /\ Cp.mrunn G k (Cp.entry_code (L.invert (G p))) 0 a
                (Cp.csize (L.invert (G p))) x
  | Cp.IHalt => False
  end.
Proof.
  intros n c l a m x H; inversion H; subst;
    match goal with Hi : Cp.get _ _ = _ |- _ => rewrite Hi end; simpl.
  - repeat split.
  - repeat split; assumption.
  - repeat split; left; split; [ assumption | reflexivity ].
  - repeat split; right; split; [ assumption | reflexivity ].
  - repeat split; assumption.
  - split; [ reflexivity | eexists; split; [ reflexivity | eassumption ] ].
  - split; [ reflexivity | eexists; split; [ reflexivity | eassumption ] ].
Qed.

(** A run that starts at a halt is the empty run — count included. *)
Lemma halt_run_refl_count : forall n c l a l' b,
  Cp.get c l = Cp.IHalt -> Cp.mrunn G n c l a l' b -> n = 0 /\ l' = l /\ b = a.
Proof.
  intros n c l a l' b Hh H; inversion H; subst.
  - repeat split.
  - exfalso; eapply Cp.halt_no_step; eassumption.
Qed.

Definition Pdet (n : nat) (c : Cp.code) (l : nat) (a : P.state)
                (m : nat) (x : P.state) : Prop :=
  forall n' m' x', Cp.mstepn G n' c l a m' x' -> n = n' /\ m = m' /\ x = x'.

(** For a *run* the count is only pinned down once the endpoint is a halt: a
    prefix of a run is also a run, so without that there is nothing to determine.
    [entry_halt] supplies it at every exit this development cares about. *)
Definition Qdet (n : nat) (c : Cp.code) (l : nat) (a : P.state)
                (l1 : nat) (b1 : P.state) : Prop :=
  Cp.get c l1 = Cp.IHalt ->
  forall n' l2 b2, Cp.mrunn G n' c l a l2 b2 -> Cp.get c l2 = Cp.IHalt ->
    n = n' /\ l1 = l2 /\ b1 = b2.

Lemma machine_det : forall n c l a m x, Cp.mstepn G n c l a m x -> Pdet n c l a m x.
Proof.
  intros n c l a m x H.
  induction H using Cp.mstepn_mut
    with (P0 := fun k c0 l0 a0 l1 b1 (_ : Cp.mrunn G k c0 l0 a0 l1 b1) =>
                  Qdet k c0 l0 a0 l1 b1);
    red.
  (* --- one instruction --- *)
  - (* INop *) intros n' m' x' H'; pose proof (step_cases_exact _ _ _ _ _ _ H') as Hc;
      match goal with Hi : Cp.get _ _ = _ |- _ => rewrite Hi in Hc end;
      simpl in Hc; destruct Hc as [? [? ?]]; subst; repeat split.
  - (* IPrim *) intros n' m' x' H'; pose proof (step_cases_exact _ _ _ _ _ _ H') as Hc;
      match goal with Hi : Cp.get _ _ = _ |- _ => rewrite Hi in Hc end;
      simpl in Hc; destruct Hc as [? [? Hp]]; subst; repeat split.
    eapply P.pstep_det; eassumption.
  - (* IBr, taken *) intros n' m' x' H'; pose proof (step_cases_exact _ _ _ _ _ _ H') as Hc;
      match goal with Hi : Cp.get _ _ = _ |- _ => rewrite Hi in Hc end;
      simpl in Hc; destruct Hc as [? [? [[Hg ?] | [Hg ?]]]]; subst;
      repeat split; congruence.
  - (* IBr, not taken *) intros n' m' x' H'; pose proof (step_cases_exact _ _ _ _ _ _ H') as Hc;
      match goal with Hi : Cp.get _ _ = _ |- _ => rewrite Hi in Hc end;
      simpl in Hc; destruct Hc as [? [? [[Hg ?] | [Hg ?]]]]; subst;
      repeat split; congruence.
  - (* IChk *) intros n' m' x' H'; pose proof (step_cases_exact _ _ _ _ _ _ H') as Hc;
      match goal with Hi : Cp.get _ _ = _ |- _ => rewrite Hi in Hc end;
      simpl in Hc; destruct Hc as [? [? [? ?]]]; subst; repeat split.
  - (* ICall: the cost is the callee's run, determined by the inner hypothesis *)
    intros n' m' x' H'; pose proof (step_cases_exact _ _ _ _ _ _ H') as Hc;
      match goal with Hi : Cp.get _ _ = _ |- _ => rewrite Hi in Hc end;
      simpl in Hc; destruct Hc as [? [k [Hk Hr]]]; subst.
    destruct (IHmstepn (Cp.entry_halt _) k _ _ Hr (Cp.entry_halt _))
      as [Hn [_ Hb]]; subst; repeat split.
  - (* IUncall *)
    intros n' m' x' H'; pose proof (step_cases_exact _ _ _ _ _ _ H') as Hc;
      match goal with Hi : Cp.get _ _ = _ |- _ => rewrite Hi in Hc end;
      simpl in Hc; destruct Hc as [? [k [Hk Hr]]]; subst.
    destruct (IHmstepn (Cp.entry_halt _) k _ _ Hr (Cp.entry_halt _))
      as [Hn [_ Hb]]; subst; repeat split.
  (* --- a run --- *)
  - (* NR_refl: the run is empty, so the other one is too *)
    intros Hh n' l2 b2 H' _.
    destruct (halt_run_refl_count n' _ _ _ _ _ Hh H') as [? [? ?]]; subst; repeat split.
  - (* NR_step *)
    intros Hh n' l2 b2 H' Hh2.
    destruct (Cp.run_cases G n' _ _ _ _ _ H')
      as [[Hz [Hl Hb]] | [k1 [k2 [m2 [x2 [Hn [Hs2 Hr2]]]]]]].
    + (* the other run is empty, but this one steps: impossible at a halt *)
      exfalso; subst.
      match goal with
      | Hh : Cp.get ?c0 ?l0 = Cp.IHalt, Hst : Cp.mstepn G _ ?c0 ?l0 _ _ _ |- _ =>
          exact (Cp.halt_no_step G _ c0 l0 _ _ _ Hh Hst)
      end.
    + destruct (IHmstepn k1 m2 x2 Hs2) as [? [? ?]]; subst.
      destruct (IHmstepn0 Hh k2 l2 b2 Hr2 Hh2) as [? [? ?]]; subst; repeat split.
Qed.

Corollary mstepn_det : forall n n' c l a m x m' x',
  Cp.mstepn G n c l a m x -> Cp.mstepn G n' c l a m' x' ->
  n = n' /\ m = m' /\ x = x'.
Proof. intros n n' c l a m x m' x' H1 H2; apply (machine_det _ _ _ _ _ _ H1 _ _ _ H2). Qed.

(** Two runs from one configuration that both stop at a halt are the same run. *)
Theorem mrunn_det_halt : forall n n' c l a l1 b1 l2 b2,
  Cp.mrunn G n c l a l1 b1 -> Cp.mrunn G n' c l a l2 b2 ->
  Cp.get c l1 = Cp.IHalt -> Cp.get c l2 = Cp.IHalt ->
  n = n' /\ l1 = l2 /\ b1 = b2.
Proof.
  intros n n' c l a l1 b1 l2 b2 H1 H2 Hh1 Hh2.
  (* the run-level statement is the [P0] of the same induction *)
  revert n' l2 b2 H2 Hh2 Hh1; induction H1 as [ c0 l0 a0 | k1 k2 c0 l0 a0 m0 x0 le b0 Hs Hr IH ];
    intros n' l2 b2 H2 Hh2 Hh1.
  - destruct (halt_run_refl_count n' _ _ _ _ _ Hh1 H2) as [? [? ?]]; subst; repeat split.
  - destruct (Cp.run_cases G n' _ _ _ _ _ H2)
      as [[Hz [Hl Hb]] | [q1 [q2 [m2 [x2 [Hn [Hs2 Hr2]]]]]]].
    + exfalso; subst.
      match goal with
      | Hh : Cp.get ?c0 ?l0 = Cp.IHalt, Hst : Cp.mstepn G _ ?c0 ?l0 _ _ _ |- _ =>
          exact (Cp.halt_no_step G _ c0 l0 _ _ _ Hh Hst)
      end.
    + destruct (mstepn_det _ _ _ _ _ _ _ _ _ Hs Hs2) as [? [? ?]]; subst.
      destruct (IH q2 l2 b2 Hr2 Hh2 Hh1) as [? [? ?]]; subst; repeat split.
Qed.

(** Hence the count is a property of the *program*, not of the derivation that
    happened to be written down: whatever run the compiled code performs from
    [a] to the exit, it takes exactly the number of steps the source charges. *)
Theorem crun_cost_complete : forall m s a b,
  Cp.mrunn G m (Cp.entry_code s) 0 a (Cp.csize s) b -> execn m s a b.
Proof.
  intros m s a b Hr.
  assert (Hex : L.exec G s a b) by (apply Cp.crun_complete; exists m; exact Hr).
  destruct (exec_execn s a b Hex) as [n Hn].
  assert (Hr' := compilation_is_step_exact n s a b Hn).
  destruct (mrunn_det_halt n m _ _ _ _ _ _ _ Hr' Hr
              (Cp.entry_halt s) (Cp.entry_halt s)) as [Heq [_ _]]; subst.
  exact Hn.
Qed.

(** The count is unique: a program, a starting state and a final state determine
    it.  (Two derivations compile to two runs reaching the same halt, and
    [mrunn_det_halt] identifies them.) *)
Corollary execn_unique : forall n1 n2 s a b,
  execn n1 s a b -> execn n2 s a b -> n1 = n2.
Proof.
  intros n1 n2 s a b H1 H2.
  destruct (mrunn_det_halt n1 n2 _ _ _ _ _ _ _
              (compilation_is_step_exact n1 s a b H1)
              (compilation_is_step_exact n2 s a b H2)
              (Cp.entry_halt s) (Cp.entry_halt s)) as [Heq [_ _]]; exact Heq.
Qed.

(** **The** cost theorem, both ways. *)
Theorem compilation_is_step_exact_iff : forall n s a b,
  execn n s a b <-> Cp.mrunn G n (Cp.entry_code s) 0 a (Cp.csize s) b.
Proof.
  intros n s a b; split;
    [ apply compilation_is_step_exact | apply crun_cost_complete ].
Qed.

(* ===================================================================== *)
(** ** Inversion preserves the count.

    The inverted program occupies the same number of labels and performs the same
    number of actions.  Neither is forced by [exec_rev]: [invert] swaps an [If]'s
    entry test with its exit assertion, swaps a [Loop]'s two guards, and reverses
    the order of the loop's rounds and of a [Seq]'s two halves.  What survives is
    the *multiset* of actions, and the count only sees that. *)

Lemma csize_invert : forall s, Cp.csize (L.invert s) = Cp.csize s.
Proof.
  induction s; simpl; try reflexivity; lia.
Qed.

(** Open iteration, counted -- the counterpart of [RevCore.opn], which is how the
    reversal of a loop is assembled: the reversed run is a chain of *continuing*
    rounds followed by one final body. *)
Inductive opnn (g1 : P.guard) (s1 s2 : L.stmt) (g2 : P.guard)
  : nat -> P.state -> P.state -> Prop :=
| Xo_nil  : forall a, opnn g1 s1 s2 g2 0 a a
| Xo_cons : forall n1 n2 k a a1 a2 b,
    execn n1 s1 a a1 -> P.gtest g2 a1 = false ->
    execn n2 s2 a1 a2 -> P.gtest g1 a2 = false ->
    opnn g1 s1 s2 g2 k a2 b ->
    opnn g1 s1 s2 g2 (n1 + 1 + n2 + 1 + k) a b.

Lemma opnn_snoc : forall g1 s1 s2 g2 k n1 n2 a m m1 m2,
  opnn g1 s1 s2 g2 k a m ->
  execn n1 s1 m m1 -> P.gtest g2 m1 = false ->
  execn n2 s2 m1 m2 -> P.gtest g1 m2 = false ->
  opnn g1 s1 s2 g2 (k + (n1 + 1 + n2 + 1)) a m2.
Proof.
  intros g1 s1 s2 g2 k n1 n2 a m m1 m2 H; revert n1 n2 m1 m2.
  induction H as [ a0 | p1 p2 k0 a0 b1 b2 c0 He1 Hg2 He2 Hg1 Hop IH ];
    intros q1 q2 m1 m2 Hs1 He He2' He1'.
  - replace (0 + (q1 + 1 + q2 + 1)) with (q1 + 1 + q2 + 1 + 0) by lia.
    eapply Xo_cons; try eassumption; apply Xo_nil.
  - replace (p1 + 1 + p2 + 1 + k0 + (q1 + 1 + q2 + 1))
      with (p1 + 1 + p2 + 1 + (k0 + (q1 + 1 + q2 + 1))) by lia.
    eapply Xo_cons; try eassumption.
    eapply IH; eassumption.
Qed.

Lemma opnn_to_lpn : forall g1 s1 s2 g2 k n1 a m b,
  opnn g1 s1 s2 g2 k a m -> execn n1 s1 m b -> P.gtest g2 b = true ->
  lpn (k + (n1 + 1)) g1 s1 s2 g2 a b.
Proof.
  intros g1 s1 s2 g2 k n1 a m b H; revert n1 b.
  induction H as [ a0 | p1 p2 k0 a0 b1 b2 c0 He1 Hg2 He2 Hg1 Hop IH ];
    intros q1 bb Hs1 Hex.
  - replace (0 + (q1 + 1)) with (q1 + 1) by lia. apply Xl_one; assumption.
  - replace (p1 + 1 + p2 + 1 + k0 + (q1 + 1))
      with (p1 + 1 + p2 + 1 + (k0 + (q1 + 1))) by lia.
    eapply Xl_more; try eassumption.
    eapply IH; eassumption.
Qed.

(** The exit assertion of a loop holds at its final state, with the count
    irrelevant -- needed to start the reversed loop. *)
Lemma lpn_exit_true : forall k g1 s1 s2 g2 a b,
  lpn k g1 s1 s2 g2 a b -> P.gtest g2 b = true.
Proof. intros until b; intro H; induction H; assumption. Qed.

(** **The** reversibility theorem with a cost: running backwards is exactly as
    expensive as running forwards. *)
Theorem execn_rev : forall n s a b, execn n s a b -> execn n (L.invert s) b a.
Proof.
  intros n s a b H.
  induction H using execn_mut
    with (P0 := fun k g1 s1 s2 g2 a b (_ : lpn k g1 s1 s2 g2 a b) =>
      exists q k1 m1, opnn g2 (L.invert s1) (L.invert s2) g1 k1 b q
                      /\ execn m1 (L.invert s1) q a
                      /\ k = k1 + (m1 + 1)).
  - (* Skip *) apply X_Skip.
  - (* Prim *) cbn [L.invert]. apply X_Prim, P.pstep_rev; assumption.
  - (* Seq: the two halves swap, the counts commute *)
    cbn [L.invert].
    replace (n1 + n2) with (n2 + n1) by lia.
    eapply X_Seq; eassumption.
  - (* If, then: the entry test and the exit assertion swap *)
    cbn [L.invert]. apply X_IfT; assumption.
  - (* If, else *)
    cbn [L.invert]. apply X_IfF; assumption.
  - (* Loop: reassembled from the open iteration, in the reverse order *)
    cbn [L.invert].
    destruct IHexecn as [q [k1 [m1 [Hopn [Hq Hk]]]]].
    subst k.
    apply X_Loop with (k := k1 + (m1 + 1)).
    + eapply lpn_exit_true; eassumption.
    + eapply opnn_to_lpn; [ exact Hopn | exact Hq | assumption ].
  - (* Call *) cbn [L.invert]. apply X_Uncall; assumption.
  - (* Uncall *) cbn [L.invert]. apply X_Call.
    rewrite L.invert_invol in IHexecn; assumption.
  - (* lp, last round: the reversed loop starts here, with no rounds behind it *)
    (* [repeat split] also discharges the count equation, by [eq_refl] *)
    exists b, 0, n1; repeat split; [ apply Xo_nil | assumption ].
  - (* lp, one more round: the reversed run gains a round at its end *)
    destruct IHexecn3 as [q [k1 [m1 [Hopn [Hq Hk]]]]].
    exists a1, (k1 + (m1 + 1 + n2 + 1)), n1; repeat split.
    + eapply opnn_snoc; eassumption.
    + assumption.
    + lia.
Qed.

(** The two together: the compiled inverse runs the same number of instructions,
    out of the same number of labels. *)
Corollary inverse_costs_the_same : forall n s a b,
  execn n s a b ->
  Cp.mrunn G n (Cp.entry_code (L.invert s)) 0 b (Cp.csize s) a.
Proof.
  intros n s a b H.
  rewrite <- (csize_invert s).
  apply compilation_is_step_exact, execn_rev; exact H.
Qed.

(** ...and inverting twice is free, count included. *)
Corollary execn_iff : forall n s a b, execn n s a b <-> execn n (L.invert s) b a.
Proof.
  intros n s a b; split; intro H.
  - apply execn_rev; exact H.
  - apply execn_rev in H; rewrite L.invert_invol in H; exact H.
Qed.

(* ===================================================================== *)
(** ** Fuel and steps.

    A fuel-bounded interpreter is the shape every executable core in this
    development takes ([RevExtract.v], [RevExtractAr.v], [RevExtractFrame.v],
    [RevExtractMod.v]).  None of them can be named alongside [execn], because
    each targets a core outside the [RevSmallStep -> RevDenote -> RevFix ->
    RevCompile] chain, or a separate application of [RevLang]; the generativity
    of functor application makes even the statement ill-typed.

    Putting one *inside* the chain runs into the framework's own design:
    [REV_PRIM.pstep] is a **relation**, deliberately — [RevStack.v] notes that a
    pop on a too-short stack simply has no step, which a function into [state]
    could not express.  So there is nothing to run.

    Extending [REV_PRIM] with a computable step is not the answer either: its
    three obligations are the framework's headline, and [RevNecessity.v] proves
    them *tight*.  Adding a fourth would be an interface decision, not a lemma.

    What costs nothing is to take the functional refinement as a **parameter**.
    Any instance that has one supplies it; instances whose primitives are
    genuinely relational simply do not get an interpreter.  The shape below is
    the development's own: [RevExtractMod.v] defines exactly this [pstep_fn] and
    proves exactly this [pstep_fn_sound]. *)

Section WithFn.

Variable pstep_fn : P.prim -> P.state -> option P.state.
Hypothesis pstep_fn_sound : forall p a b, pstep_fn p a = Some b -> P.pstep p a b.
Hypothesis pstep_fn_complete : forall p a b, P.pstep p a b -> pstep_fn p a = Some b.

Fixpoint runn (f : nat) (s : L.stmt) (a : P.state) {struct f} : option P.state :=
  match f with
  | O => None
  | S f' =>
      match s with
      | L.Skip => Some a
      | L.Prim p => pstep_fn p a
      | L.Seq s1 s2 =>
          match runn f' s1 a with Some m => runn f' s2 m | None => None end
      | L.If g1 s1 s2 g2 =>
          if P.gtest g1 a
          then match runn f' s1 a with
               | Some b => if P.gtest g2 b then Some b else None
               | None => None end
          else match runn f' s2 a with
               | Some b => if P.gtest g2 b then None else Some b
               | None => None end
      | L.Loop g1 s1 s2 g2 =>
          if P.gtest g1 a then loopn f' g1 s1 s2 g2 a else None
      | L.Call p => runn f' (G p) a
      | L.Uncall p => runn f' (L.invert (G p)) a
      end
  end
with loopn (f : nat) (g1 : P.guard) (s1 s2 : L.stmt) (g2 : P.guard) (a : P.state)
  {struct f} : option P.state :=
  match f with
  | O => None
  | S f' =>
      match runn f' s1 a with
      | None => None
      | Some a1 =>
          if P.gtest g2 a1 then Some a1
          else match runn f' s2 a1 with
               | None => None
               | Some a2 =>
                   if P.gtest g1 a2 then None else loopn f' g1 s1 s2 g2 a2
               end
      end
  end.

(** Soundness: whatever it returns is a real run. *)
Lemma runn_sound_mut : forall f,
  (forall s a b, runn f s a = Some b -> L.exec G s a b)
  /\ (forall g1 s1 s2 g2 a b,
        loopn f g1 s1 s2 g2 a = Some b -> L.lp G g1 s1 s2 g2 a b).
Proof.
  induction f as [ | f [IHr IHl] ]; split;
    [ intros s a b H; discriminate | intros g1 s1 s2 g2 a b H; discriminate | | ].
  - intros [ | p | s1 s2 | g1 s1 s2 g2 | g1 s1 s2 g2 | p | p ] a b H; simpl in H.
    + injection H as <-; apply L.E_Skip.
    + apply L.E_Prim, pstep_fn_sound; exact H.
    + destruct (runn f s1 a) as [m|] eqn:E1; [ | discriminate ].
      eapply L.E_Seq; [ apply IHr; exact E1 | apply IHr; exact H ].
    + destruct (P.gtest g1 a) eqn:Eg1.
      * destruct (runn f s1 a) as [x|] eqn:E1; [ | discriminate ].
        destruct (P.gtest g2 x) eqn:Eg2; [ | discriminate ].
        injection H as <-; apply L.E_IfT; [ exact Eg1 | apply IHr; exact E1 | exact Eg2 ].
      * destruct (runn f s2 a) as [x|] eqn:E2; [ | discriminate ].
        destruct (P.gtest g2 x) eqn:Eg2; [ discriminate | ].
        injection H as <-; apply L.E_IfF; [ exact Eg1 | apply IHr; exact E2 | exact Eg2 ].
    + destruct (P.gtest g1 a) eqn:Eg1; [ | discriminate ].
      apply L.E_Loop; [ exact Eg1 | apply IHl; exact H ].
    + apply L.E_Call, IHr; exact H.
    + apply L.E_Uncall, IHr; exact H.
  - intros g1 s1 s2 g2 a b H; simpl in H.
    destruct (runn f s1 a) as [a1|] eqn:E1; [ | discriminate ].
    destruct (P.gtest g2 a1) eqn:Eg2.
    + injection H as <-; apply L.L_one; [ apply IHr; exact E1 | exact Eg2 ].
    + destruct (runn f s2 a1) as [a2|] eqn:E2; [ | discriminate ].
      destruct (P.gtest g1 a2) eqn:Eg1; [ discriminate | ].
      eapply L.L_more;
        [ apply IHr; exact E1 | exact Eg2 | apply IHr; exact E2 | exact Eg1
        | apply IHl; exact H ].
Qed.

Corollary runn_sound : forall f s a b, runn f s a = Some b -> L.exec G s a b.
Proof. intros f; apply (proj1 (runn_sound_mut f)). Qed.

(** Every derivation charges at least one action, which is what makes the fuel
    arithmetic below go through: a [Seq] can hand each half all but one unit. *)
Lemma execn_pos : forall n s a b, execn n s a b -> 1 <= n.
Proof.
  intros n s a b H.
  induction H using execn_mut
    with (P0 := fun k g1 s1 s2 g2 a b (_ : lpn k g1 s1 s2 g2 a b) => 1 <= k);
    lia.
Qed.

(** **The** link: the step count *is* a fuel bound.  [n] units of fuel suffice
    for a run the source charges [n] — so the count is a resource claim about the
    interpreter, not only about the compiled machine. *)
Theorem execn_runn : forall n s a b,
  execn n s a b -> forall f, n <= f -> runn f s a = Some b.
Proof.
  intros n s a b H.
  induction H using execn_mut
    with (P0 := fun k g1 s1 s2 g2 a b (_ : lpn k g1 s1 s2 g2 a b) =>
                  forall f, k <= f -> loopn f g1 s1 s2 g2 a = Some b);
    intros f Hf.
  - (* Skip *) destruct f as [ | f' ]; [ lia | reflexivity ].
  - (* Prim *) destruct f as [ | f' ]; [ lia | ]. simpl; apply pstep_fn_complete; assumption.
  - (* Seq *)
    pose proof (execn_pos _ _ _ _ H) as Hp1; pose proof (execn_pos _ _ _ _ H0) as Hp2.
    destruct f as [ | f' ]; [ lia | ]; simpl.
    rewrite (IHexecn1 f') by lia; apply IHexecn2; lia.
  - (* IfT *) destruct f as [ | f' ]; [ lia | ]; simpl.
    rewrite e, (IHexecn f') by lia; rewrite e0; reflexivity.
  - (* IfF *) destruct f as [ | f' ]; [ lia | ]; simpl.
    rewrite e, (IHexecn f') by lia; rewrite e0; reflexivity.
  - (* Loop *) destruct f as [ | f' ]; [ lia | ]; simpl.
    rewrite e; apply IHexecn; lia.
  - (* Call *) destruct f as [ | f' ]; [ lia | ]; simpl; apply IHexecn; lia.
  - (* Uncall *) destruct f as [ | f' ]; [ lia | ]; simpl; apply IHexecn; lia.
  - (* lp, last round *)
    destruct f as [ | f' ]; [ lia | ]; simpl.
    rewrite (IHexecn f') by lia; rewrite e; reflexivity.
  - (* lp, one more round *)
    pose proof (execn_pos _ _ _ _ H) as Hp1; pose proof (execn_pos _ _ _ _ H0) as Hp2.
    destruct f as [ | f' ]; [ lia | ]; simpl.
    rewrite (IHexecn1 f') by lia; rewrite e.
    rewrite (IHexecn2 f') by lia; rewrite e0.
    apply IHexecn3; lia.
Qed.

(** The bound is **sufficient, not least**.  Fuel measures the *depth* of the
    recursion while the count measures *actions*, and a wide, shallow statement
    separates them: four [Skip]s in a balanced [Seq] charge 4 but run on 3.
    Recording it here so the bound is not "strengthened" into something false. *)
Example the_fuel_bound_is_not_tight : forall a,
  execn 4 (L.Seq (L.Seq L.Skip L.Skip) (L.Seq L.Skip L.Skip)) a a
  /\ runn 3 (L.Seq (L.Seq L.Skip L.Skip) (L.Seq L.Skip L.Skip)) a = Some a.
Proof.
  intro a; split; [ | reflexivity ].
  change 4 with (2 + 2); apply X_Seq with (m := a);
    (change 2 with (1 + 1); apply X_Seq with (m := a); apply X_Skip).
Qed.

End WithFn.

(* ===================================================================== *)
(** ** What the count charges, spelled out.

    These fix the accounting so it cannot drift: a conditional costs its taken
    branch plus two (the entry test and the exit assertion), a call costs its
    callee plus one, and sequencing is free. *)

Example an_if_costs_its_branch_plus_two : forall n g1 s1 s2 g2 a b,
  P.gtest g1 a = true -> execn n s1 a b -> P.gtest g2 b = true ->
  execn (n + 2) (L.If g1 s1 s2 g2) a b.
Proof.
  intros n g1 s1 s2 g2 a b H1 H2 H3.
  replace (n + 2) with (1 + n + 1) by lia.
  apply X_IfT; assumption.
Qed.

Example a_call_costs_its_callee_plus_one : forall n p a b,
  execn n (G p) a b -> execn (S n) (L.Call p) a b.
Proof. intros n p a b H; replace (S n) with (1 + n) by lia; apply X_Call; exact H. Qed.

Example sequencing_is_free : forall n1 n2 s1 s2 a m b,
  execn n1 s1 a m -> execn n2 s2 m b -> execn (n1 + n2) (L.Seq s1 s2) a b.
Proof. intros; eapply X_Seq; eassumption. Qed.

(** A loop that runs [Skip] once and exits costs 3: the entry assertion, the
    body, and the exit test.  The compiled form occupies [csize Skip + csize Skip
    + 3 = 5] labels, so the step count is *not* the code size -- the two are
    different measures that the theorem above relates only through the
    derivation. *)
Example a_one_round_skip_loop_costs_three : forall g1 g2 a,
  P.gtest g1 a = true -> P.gtest g2 a = true ->
  execn 3 (L.Loop g1 L.Skip L.Skip g2) a a.
Proof.
  intros g1 g2 a H1 H2.
  replace 3 with (1 + (1 + 1)) by lia.
  apply X_Loop with (k := 1 + 1); [ exact H1 | ].
  replace (1 + 1) with (1 + 1) by lia.
  apply Xl_one; [ apply X_Skip | exact H2 ].
Qed.

End WithEnv.
End Steps.
