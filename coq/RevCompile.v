(** * RevCompile.v — the compiler-mediated semantics

    The fifth semantics of the framework language: **erase the structured control
    flow into labelled code and run a machine on it**.  Unlike the big-step,
    small-step and denotational semantics, this one never sees the syntax tree —
    a conditional becomes a branch instruction, a loop becomes a backward jump,
    and the only thing left of the structure is the arithmetic of labels.

    Instructions carry their successor label explicitly (no implicit
    fall-through), so a fragment is self-contained: [comp s base] occupies the
    labels [base .. base + csize s - 1] and leaves via [base + csize s].
    Procedure calls stay as instructions whose step runs the *compiled* body,
    which is what a compiler plus a linker gives and avoids modelling a return
    stack; the flattening being verified here is the intraprocedural control
    flow, which is where the structure is actually lost.

    [RevSemantics.v] is where this semantics is placed alongside the other four
    and every pair is proved to agree. *)

From Stdlib Require Import List Bool Arith Lia Wf_nat.
Import ListNotations.
Require Import RevCore RevSmallStep RevDenote RevFix.

Module Compile (P : REV_PRIM).

(* Reuse the one language instance shared along
   [RevSmallStep] -> [RevDenote] -> [RevFix]; see the note in [RevDenote.v]. *)
Module Fxx := RevFix.DenoteFix P.
Module L := Fxx.L.
Import L.

(* ===================================================================== *)
(** ** Target: labelled code. *)

Inductive instr :=
| INop   (nxt : nat)
| IPrim  (p : P.prim) (nxt : nat)
| IBr    (g : P.guard) (lt lf : nat)            (** branch on [gtest g] *)
| IChk   (g : P.guard) (v : bool) (nxt : nat)   (** assert [gtest g = v] *)
| ICall  (p : pname) (nxt : nat)
| IUncall (p : pname) (nxt : nat)
| IHalt.

Definition code := list instr.
Definition get (c : code) (l : nat) : instr := nth l c IHalt.

(** The size of a fragment, i.e. how many labels it occupies. *)
Fixpoint csize (s : stmt) : nat :=
  match s with
  | Skip | Prim _ | Call _ | Uncall _ => 1
  | Seq s1 s2 => csize s1 + csize s2
  | If _ s1 s2 _ => csize s1 + csize s2 + 3
  | Loop _ s1 s2 _ => csize s1 + csize s2 + 3
  end.

Lemma csize_pos : forall s, 0 < csize s.
Proof. induction s; simpl; lia. Qed.

(** The compiler.  [comp s base] is the code for [s] laid out at [base]; it is
    entered at [base] and leaves by jumping to [base + csize s]. *)
Fixpoint comp (s : stmt) (base : nat) : code :=
  match s with
  | Skip => [INop (S base)]
  | Prim p => [IPrim p (S base)]
  | Call p => [ICall p (S base)]
  | Uncall p => [IUncall p (S base)]
  | Seq s1 s2 => comp s1 base ++ comp s2 (base + csize s1)
  | If g1 s1 s2 g2 =>
      IBr g1 (S base) (S base + csize s1 + 1)
        :: comp s1 (S base)
        ++ IChk g2 true (base + (csize s1 + csize s2 + 3))
        :: comp s2 (S base + csize s1 + 1)
        ++ [IChk g2 false (base + (csize s1 + csize s2 + 3))]
  | Loop g1 s1 s2 g2 =>
      IChk g1 true (S base)
        :: comp s1 (S base)
        ++ IBr g2 (base + (csize s1 + csize s2 + 3)) (S base + csize s1 + 1)
        :: comp s2 (S base + csize s1 + 1)
        ++ [IChk g1 false (S base)]
  end.

Lemma comp_length : forall s base, length (comp s base) = csize s.
Proof.
  induction s; intros base; simpl; try reflexivity.
  - rewrite length_app, IHs1, IHs2; reflexivity.
  - rewrite length_app, length_cons, length_app, IHs1, IHs2; simpl; lia.
  - rewrite length_app, length_cons, length_app, IHs1, IHs2; simpl; lia.
Qed.

(* ===================================================================== *)
(** ** The machine.

    [mstep] is one instruction; [mrun] is its reflexive-transitive closure,
    tracking the label it starts and ends at.  A call step runs the compiled
    body of the procedure — mutually inductive with [mrun], which is why the two
    are declared together. *)

(** The entry layout: the fragment, then a halt.  The halt matters for the
    *completeness* direction — without it a run could pass through the exit
    label, wander into whatever follows and come back in a different state, so
    "reaches the exit" would not pin the final state down. *)
Definition entry_code (s : stmt) : code := comp s 0 ++ [IHalt].

(** The machine, counted.  A call step costs one plus the steps of the run it
    performs, so the count measures the *whole* execution including nested calls;
    that is what makes the induction for completeness go through. *)
Inductive mstepn (G : pname -> stmt) : nat -> code -> nat -> P.state -> nat -> P.state -> Prop :=
| N_Nop : forall c l nxt a,
    get c l = INop nxt -> mstepn G 1 c l a nxt a
| N_Prim : forall c l p nxt a b,
    get c l = IPrim p nxt -> P.pstep p a b -> mstepn G 1 c l a nxt b
| N_BrT : forall c l g lt lf a,
    get c l = IBr g lt lf -> P.gtest g a = true -> mstepn G 1 c l a lt a
| N_BrF : forall c l g lt lf a,
    get c l = IBr g lt lf -> P.gtest g a = false -> mstepn G 1 c l a lf a
| N_Chk : forall c l g v nxt a,
    get c l = IChk g v nxt -> P.gtest g a = v -> mstepn G 1 c l a nxt a
| N_Call : forall n c l p nxt a b,
    get c l = ICall p nxt ->
    mrunn G n (entry_code (G p)) 0 a (csize (G p)) b ->
    mstepn G (S n) c l a nxt b
| N_Uncall : forall n c l p nxt a b,
    get c l = IUncall p nxt ->
    mrunn G n (entry_code (invert (G p))) 0 a (csize (invert (G p))) b ->
    mstepn G (S n) c l a nxt b

with mrunn (G : pname -> stmt) : nat -> code -> nat -> P.state -> nat -> P.state -> Prop :=
| NR_refl : forall c l a, mrunn G 0 c l a l a
| NR_step : forall n1 n2 c l a m x n b,
    mstepn G n1 c l a m x -> mrunn G n2 c m x n b -> mrunn G (n1 + n2) c l a n b.

Scheme mstepn_mut := Induction for mstepn Sort Prop
  with mrunn_mut  := Induction for mrunn  Sort Prop.

Lemma mstepn_pos : forall G n c l a m x, mstepn G n c l a m x -> 1 <= n.
Proof. intros G n c l a m x H; inversion H; lia. Qed.

(** Nothing can happen at a halt. *)
Lemma halt_no_step : forall G n c l a m x,
  get c l = IHalt -> mstepn G n c l a m x -> False.
Proof. intros G n c l a m x Hh H; inversion H; congruence. Qed.

Lemma halt_run_refl : forall G n c l a l' b,
  get c l = IHalt -> mrunn G n c l a l' b -> l' = l /\ b = a.
Proof.
  intros G n c l a l' b Hh H; inversion H; subst.
  - split; reflexivity.
  - exfalso; eapply halt_no_step; eassumption.
Qed.

(** The uncounted machine, as an existential over the counted one.  The
    lemmas below are stated so that everything downstream reads exactly as if
    [mstep]/[mrun] were the primitive inductives. *)
Definition mstep (G : pname -> stmt) (c : code) (l : nat) (a : P.state)
                 (m : nat) (x : P.state) : Prop := exists n, mstepn G n c l a m x.
Definition mrun (G : pname -> stmt) (c : code) (l : nat) (a : P.state)
                (l' : nat) (b : P.state) : Prop := exists n, mrunn G n c l a l' b.

Lemma M_Nop : forall G c l nxt a, get c l = INop nxt -> mstep G c l a nxt a.
Proof. intros; exists 1; apply N_Nop; assumption. Qed.
Lemma M_Prim : forall G c l p nxt a b,
  get c l = IPrim p nxt -> P.pstep p a b -> mstep G c l a nxt b.
Proof. intros; exists 1; eapply N_Prim; eassumption. Qed.
Lemma M_BrT : forall G c l g lt lf a,
  get c l = IBr g lt lf -> P.gtest g a = true -> mstep G c l a lt a.
Proof. intros; exists 1; eapply N_BrT; eassumption. Qed.
Lemma M_BrF : forall G c l g lt lf a,
  get c l = IBr g lt lf -> P.gtest g a = false -> mstep G c l a lf a.
Proof. intros; exists 1; eapply N_BrF; eassumption. Qed.
Lemma M_Chk : forall G c l g v nxt a,
  get c l = IChk g v nxt -> P.gtest g a = v -> mstep G c l a nxt a.
Proof. intros; exists 1; eapply N_Chk; eassumption. Qed.
Lemma M_Call : forall G c l p nxt a b,
  get c l = ICall p nxt -> mrun G (entry_code (G p)) 0 a (csize (G p)) b ->
  mstep G c l a nxt b.
Proof. intros G c l p nxt a b Hi [n Hr]; exists (S n); eapply N_Call; eassumption. Qed.
Lemma M_Uncall : forall G c l p nxt a b,
  get c l = IUncall p nxt ->
  mrun G (entry_code (invert (G p))) 0 a (csize (invert (G p))) b ->
  mstep G c l a nxt b.
Proof. intros G c l p nxt a b Hi [n Hr]; exists (S n); eapply N_Uncall; eassumption. Qed.

Lemma MR_refl : forall G c l a, mrun G c l a l a.
Proof. intros; exists 0; apply NR_refl. Qed.
Lemma MR_step : forall G c l a m x n b,
  mstep G c l a m x -> mrun G c m x n b -> mrun G c l a n b.
Proof.
  intros G c l a m x n b [n1 H1] [n2 H2]; exists (n1 + n2); eapply NR_step; eassumption.
Qed.

Lemma mrunn_trans : forall G n1 c l a m x n2 n b,
  mrunn G n1 c l a m x -> mrunn G n2 c m x n b -> mrunn G (n1 + n2) c l a n b.
Proof.
  intros G n1 c l a m x n2 n b H; revert n2 n b; induction H as [| p1 p2 c0 l0 a0 m0 x0 n0 b0 Hs Hr IH];
    intros n2' n' b' H2.
  - simpl; exact H2.
  - replace (p1 + p2 + n2') with (p1 + (p2 + n2')) by lia.
    eapply NR_step; [ exact Hs | apply IH; exact H2 ].
Qed.

Lemma mrun_trans : forall G c l a m x n b,
  mrun G c l a m x -> mrun G c m x n b -> mrun G c l a n b.
Proof.
  intros G c l a m x n b [n1 H1] [n2 H2]; exists (n1 + n2); eapply mrunn_trans; eassumption.
Qed.

(** The semantics: compile the statement at label 0 and run to the exit. *)
Definition crun (G : pname -> stmt) (s : stmt) (a b : P.state) : Prop :=
  mrun G (entry_code s) 0 a (csize s) b.

(* ===================================================================== *)
(** ** Framing: a fragment behaves the same wherever it is placed.

    [holds c base f] says the code [c] contains the fragment [f] at [base].
    Since instructions carry absolute successor labels, [comp s base] is already
    the right code for position [base]; all that is needed is to read it out of
    a larger [c]. *)

Definition holds (c : code) (base : nat) (f : code) : Prop :=
  forall k, k < length f -> get c (base + k) = get f k.

Lemma holds_entry : forall s, holds (entry_code s) 0 (comp s 0).
Proof.
  intros s k Hk; unfold entry_code, holds, get.
  apply app_nth1; exact Hk.
Qed.

Lemma holds_cons : forall c base x f,
  holds c base (x :: f) -> get c base = x /\ holds c (S base) f.
Proof.
  intros c base x f H; unfold holds, get in *; split.
  - specialize (H 0 (Nat.lt_0_succ _)); rewrite Nat.add_0_r in H; simpl in H; exact H.
  - intros k Hk. specialize (H (S k) (proj1 (Nat.succ_lt_mono _ _) Hk)).
    replace (S base + k) with (base + S k) by lia. simpl in H; exact H.
Qed.

Lemma holds_app : forall c base f1 f2,
  holds c base (f1 ++ f2) -> holds c base f1 /\ holds c (base + length f1) f2.
Proof.
  intros c base f1 f2 H; unfold holds, get in *; split.
  - intros k Hk. rewrite <- (app_nth1 f1 f2 IHalt Hk). apply H.
    rewrite length_app; lia.
  - intros k Hk.
    replace (base + length f1 + k) with (base + (length f1 + k)) by lia.
    rewrite H by (rewrite length_app; lia).
    rewrite app_nth2 by lia. f_equal; lia.
Qed.

(** The five instruction facts and two sub-fragments of a compiled [If]. *)
Lemma holds_if : forall c base g1 s1 s2 g2,
  holds c base (comp (If g1 s1 s2 g2) base) ->
  get c base = IBr g1 (S base) (S base + csize s1 + 1)
  /\ holds c (S base) (comp s1 (S base))
  /\ get c (S base + csize s1) = IChk g2 true (base + (csize s1 + csize s2 + 3))
  /\ holds c (S base + csize s1 + 1) (comp s2 (S base + csize s1 + 1))
  /\ get c (S base + csize s1 + 1 + csize s2)
       = IChk g2 false (base + (csize s1 + csize s2 + 3)).
Proof.
  intros c base g1 s1 s2 g2 H; simpl in H.
  apply holds_cons in H as [Hbr H].
  apply holds_app in H as [H1 H]; rewrite comp_length in H.
  apply holds_cons in H as [Hchk H].
  replace (S (S base + csize s1)) with (S base + csize s1 + 1) in H by lia.
  apply holds_app in H as [H2 H3]; rewrite comp_length in H3.
  repeat split; try assumption.
  specialize (H3 0 (Nat.lt_0_succ _)); rewrite Nat.add_0_r in H3; exact H3.
Qed.

(** ...and of a compiled [Loop]. *)
Lemma holds_loop : forall c base g1 s1 s2 g2,
  holds c base (comp (Loop g1 s1 s2 g2) base) ->
  get c base = IChk g1 true (S base)
  /\ holds c (S base) (comp s1 (S base))
  /\ get c (S base + csize s1)
       = IBr g2 (base + (csize s1 + csize s2 + 3)) (S base + csize s1 + 1)
  /\ holds c (S base + csize s1 + 1) (comp s2 (S base + csize s1 + 1))
  /\ get c (S base + csize s1 + 1 + csize s2) = IChk g1 false (S base).
Proof.
  intros c base g1 s1 s2 g2 H; simpl in H.
  apply holds_cons in H as [Hchk H].
  apply holds_app in H as [H1 H]; rewrite comp_length in H.
  apply holds_cons in H as [Hbr H].
  replace (S (S base + csize s1)) with (S base + csize s1 + 1) in H by lia.
  apply holds_app in H as [H2 H3]; rewrite comp_length in H3.
  repeat split; try assumption.
  specialize (H3 0 (Nat.lt_0_succ _)); rewrite Nat.add_0_r in H3; exact H3.
Qed.

(* ===================================================================== *)
(** ** Soundness: everything the source does, the compiled code does. *)

Section Sound.
Variable G : pname -> stmt.

Definition Psound (s : stmt) (a b : P.state) : Prop :=
  forall c base, holds c base (comp s base) -> mrun G c base a (base + csize s) b.

Definition Qsound (g1 : P.guard) (s1 s2 : stmt) (g2 : P.guard) (a b : P.state) : Prop :=
  forall c base, holds c base (comp (Loop g1 s1 s2 g2) base) ->
    mrun G c (S base) a (base + csize (Loop g1 s1 s2 g2)) b.

Lemma comp_sound : forall s a b, exec G s a b -> Psound s a b.
Proof.
  intros s a b H.
  induction H using L.exec_mut
    with (P0 := fun g1 s1 s2 g2 a b (_ : lp G g1 s1 s2 g2 a b) =>
                  Qsound g1 s1 s2 g2 a b);
    red; intros c base Hh.
  (* Skip *)
  - simpl in Hh; apply holds_cons in Hh as [Hi _].
    eapply MR_step; [ eapply M_Nop; exact Hi | ].
    replace (base + csize Skip) with (S base) by (simpl; lia). apply MR_refl.
  (* Prim *)
  - simpl in Hh; apply holds_cons in Hh as [Hi _].
    eapply MR_step; [ eapply M_Prim; [ exact Hi | eassumption ] | ].
    replace (base + csize (Prim p)) with (S base) by (simpl; lia). apply MR_refl.
  (* Seq *)
  - simpl in Hh; apply holds_app in Hh as [Hh1 Hh2]; rewrite comp_length in Hh2.
    eapply mrun_trans; [ apply (IHexec1 c base Hh1) | ].
    replace (base + csize (Seq s1 s2)) with (base + csize s1 + csize s2)
      by (simpl; lia).
    apply (IHexec2 c (base + csize s1) Hh2).
  (* If, then-branch *)
  - apply holds_if in Hh as [Hbr [Hh1 [Hchk1 [_ _]]]].
    eapply MR_step; [ eapply M_BrT; [ exact Hbr | eassumption ] | ].
    eapply mrun_trans; [ apply (IHexec c (S base) Hh1) | ].
    eapply MR_step; [ eapply M_Chk; [ exact Hchk1 | eassumption ] | ].
    replace (base + csize (If g1 s1 s2 g2))
      with (base + (csize s1 + csize s2 + 3)) by (simpl; lia).
    apply MR_refl.
  (* If, else-branch *)
  - apply holds_if in Hh as [Hbr [_ [_ [Hh2 Hchk2]]]].
    eapply MR_step; [ eapply M_BrF; [ exact Hbr | eassumption ] | ].
    eapply mrun_trans; [ apply (IHexec c (S base + csize s1 + 1) Hh2) | ].
    eapply MR_step; [ eapply M_Chk; [ exact Hchk2 | eassumption ] | ].
    replace (base + csize (If g1 s1 s2 g2))
      with (base + (csize s1 + csize s2 + 3)) by (simpl; lia).
    apply MR_refl.
  (* Loop: the entry assertion, then the iteration *)
  - assert (Hh' := Hh); apply holds_loop in Hh as [Hchk [_ [_ [_ _]]]].
    eapply MR_step; [ eapply M_Chk; [ exact Hchk | eassumption ] | ].
    apply (IHexec c base Hh').
  (* Call *)
  - simpl in Hh; apply holds_cons in Hh as [Hi _].
    eapply MR_step; [ eapply M_Call; [ exact Hi | ] | ].
    + specialize (IHexec (entry_code (G p)) 0 (holds_entry (G p))).
      rewrite Nat.add_0_l in IHexec; exact IHexec.
    + replace (base + csize (Call p)) with (S base) by (simpl; lia).
      apply MR_refl.
  (* Uncall *)
  - simpl in Hh; apply holds_cons in Hh as [Hi _].
    eapply MR_step; [ eapply M_Uncall; [ exact Hi | ] | ].
    + specialize (IHexec (entry_code (invert (G p))) 0 (holds_entry (invert (G p)))).
      rewrite Nat.add_0_l in IHexec; exact IHexec.
    + replace (base + csize (Uncall p)) with (S base) by (simpl; lia).
      apply MR_refl.
  (* lp: exit on this round *)
  - apply holds_loop in Hh as [_ [Hh1 [Hbr [_ _]]]].
    eapply mrun_trans; [ apply (IHexec c (S base) Hh1) | ].
    eapply MR_step; [ eapply M_BrT; [ exact Hbr | eassumption ] | ].
    replace (base + csize (Loop g1 s1 s2 g2))
      with (base + (csize s1 + csize s2 + 3)) by (simpl; lia).
    apply MR_refl.
  (* lp: one more round *)
  - assert (Hh' := Hh); apply holds_loop in Hh as [_ [Hh1 [Hbr [Hh2 Hchk]]]].
    eapply mrun_trans; [ apply (IHexec1 c (S base) Hh1) | ].
    eapply MR_step; [ eapply M_BrF; [ exact Hbr | exact e ] | ].
    eapply mrun_trans; [ apply (IHexec2 c (S base + csize s1 + 1) Hh2) | ].
    eapply MR_step; [ eapply M_Chk; [ exact Hchk | exact e0 ] | ].
    apply (IHexec3 c base Hh').
Qed.

(** Instantiated at the top-level layout: the compiled program does whatever the
    source does. *)
Corollary crun_sound : forall s a b, exec G s a b -> crun G s a b.
Proof.
  intros s a b H; unfold crun.
  specialize (comp_sound s a b H (entry_code s) 0 (holds_entry s)) as Hr.
  rewrite Nat.add_0_l in Hr; exact Hr.
Qed.

End Sound.

(* ===================================================================== *)
(** ** Confinement: a compiled fragment only jumps inside itself.

    Every instruction of [comp s base] targets a label in
    [base .. base + csize s], so a run that enters the fragment cannot escape
    except through the exit label at the top.  Stated over the list with [Forall]
    rather than by index arithmetic, which makes the induction on [s] routine. *)

Definition tw (lo sz : nat) (i : instr) : Prop :=
  match i with
  | INop n => lo <= n <= lo + sz
  | IPrim _ n => lo <= n <= lo + sz
  | IChk _ _ n => lo <= n <= lo + sz
  | ICall _ n => lo <= n <= lo + sz
  | IUncall _ n => lo <= n <= lo + sz
  | IBr _ lt lf => (lo <= lt <= lo + sz) /\ (lo <= lf <= lo + sz)
  | IHalt => True
  end.

Lemma tw_widen : forall lo sz lo' sz' i,
  lo <= lo' -> lo' + sz' <= lo + sz -> tw lo' sz' i -> tw lo sz i.
Proof.
  intros lo sz lo' sz' i H1 H2 H; destruct i; simpl in *;
    solve [ exact I | lia | destruct H; lia ].
Qed.

Ltac widen H := eapply Forall_impl; [ intros ? ?; eapply tw_widen; [ | | eassumption ] | apply H ].

Lemma comp_within : forall s base, Forall (tw base (csize s)) (comp s base).
Proof.
  induction s; intros base; simpl.
  - repeat constructor; simpl; lia.
  - repeat constructor; simpl; lia.
  - apply Forall_app; split.
    + widen (IHs1 base); lia.
    + widen (IHs2 (base + csize s1)); lia.
  - constructor; [ simpl; lia | ]. apply Forall_app; split.
    + widen (IHs1 (S base)); lia.
    + constructor; [ simpl; lia | ]. apply Forall_app; split.
      * widen (IHs2 (S base + csize s1 + 1)); lia.
      * repeat constructor; simpl; lia.
  - constructor; [ simpl; lia | ]. apply Forall_app; split.
    + widen (IHs1 (S base)); lia.
    + constructor; [ simpl; lia | ]. apply Forall_app; split.
      * widen (IHs2 (S base + csize s1 + 1)); lia.
      * repeat constructor; simpl; lia.
  - repeat constructor; simpl; lia.
  - repeat constructor; simpl; lia.
Qed.

Lemma within_get : forall s base k, k < csize s -> tw base (csize s) (get (comp s base) k).
Proof.
  intros s base k Hk; unfold get.
  apply (proj1 (Forall_forall _ _) (comp_within s base)).
  apply nth_In; rewrite comp_length; exact Hk.
Qed.

Lemma confined : forall c base s,
  holds c base (comp s base) ->
  forall k, k < csize s -> tw base (csize s) (get c (base + k)).
Proof.
  intros c base s Hh k Hk.
  rewrite (Hh k) by (rewrite comp_length; exact Hk).
  apply within_get; exact Hk.
Qed.

(* ===================================================================== *)
(** ** Splitting a run at its first exit from a confined region.

    If the code in [lo .. lo + sz - 1] only targets [lo .. lo + sz], then a run
    starting inside the region and ending outside it must pass through
    [lo + sz], and the prefix produced below is the run *up to the first time it
    gets there* — which is what lets the [Seq]/[If]/[Loop] cases of completeness
    recurse on a strictly smaller step count. *)

Lemma run_split : forall G n c l a l' b, mrunn G n c l a l' b ->
  forall lo sz,
    (forall k, k < sz -> tw lo sz (get c (lo + k))) ->
    lo <= l -> l < lo + sz -> (l' < lo \/ lo + sz <= l') ->
    exists j x n2, 1 <= j /\ j + n2 = n /\
      mrunn G j c l a (lo + sz) x /\ mrunn G n2 c (lo + sz) x l' b.
Proof.
  intros G n c l a l' b H.
  induction H as [ c0 l0 a0 | p1 p2 c0 l0 a0 m x le b0 Hs Hr IH ];
    intros lo sz Hconf Hlo Hhi Hout.
  - lia.
  - assert (Htw : tw lo sz (get c0 l0)).
    { replace l0 with (lo + (l0 - lo)) by lia. apply Hconf; lia. }
    assert (Hm : lo <= m <= lo + sz).
    { inversion Hs; subst;
        match goal with Hi : get c0 l0 = _ |- _ => rewrite Hi in Htw end;
        simpl in Htw; solve [ lia | destruct Htw; lia ]. }
    destruct (Nat.eq_dec m (lo + sz)) as [Heq | Hne].
    + subst m. exists p1, x, p2; repeat split.
      (* `repeat split` discharges the count equation by [eq_refl] itself. *)
      * eapply mstepn_pos; eassumption.
      * replace p1 with (p1 + 0) by lia.
        eapply NR_step; [ exact Hs | apply NR_refl ].
      * exact Hr.
    + destruct (IH lo sz Hconf) as [j [y [n2' [Hj [Hsum [Hpre Hpost]]]]]];
        try lia; try exact Hout.
      exists (p1 + j), y, n2'; repeat split.
      * lia.
      * lia.
      * eapply NR_step; [ exact Hs | exact Hpre ].
      * exact Hpost.
Qed.

(* ===================================================================== *)
(** ** Reading a single step off the instruction at the label.

    One inversion lemma, dispatching on [get c l].  Because the conclusion is a
    [match] on the instruction, rewriting the caller's own
    [get c l = <instruction>] into it reduces the whole thing to exactly the
    facts that case needs — and the caller never has to guess a name that
    [inversion] invented. *)

Lemma step_cases : forall G n c l a m x, mstepn G n c l a m x ->
  match get c l with
  | INop nxt => n = 1 /\ m = nxt /\ x = a
  | IPrim p nxt => n = 1 /\ m = nxt /\ P.pstep p a x
  | IBr g lt lf => n = 1 /\ x = a
      /\ ((P.gtest g a = true /\ m = lt) \/ (P.gtest g a = false /\ m = lf))
  | IChk g v nxt => n = 1 /\ m = nxt /\ x = a /\ P.gtest g a = v
  | ICall p nxt => m = nxt
      /\ exists k, k < n /\ mrunn G k (entry_code (G p)) 0 a (csize (G p)) x
  | IUncall p nxt => m = nxt
      /\ exists k, k < n
           /\ mrunn G k (entry_code (invert (G p))) 0 a (csize (invert (G p))) x
  | IHalt => False
  end.
Proof.
  intros G n c l a m x H; inversion H; subst;
    match goal with Hi : get _ _ = _ |- _ => rewrite Hi end; simpl.
  - repeat split.
  - repeat split; assumption.
  - repeat split; left; split; [ assumption | reflexivity ].
  - repeat split; right; split; [ assumption | reflexivity ].
  - repeat split; assumption.
  - repeat split; eexists; split; [ | eassumption ]; lia.
  - repeat split; eexists; split; [ | eassumption ]; lia.
Qed.

(** ...and the same for a run: either it is empty, or it is a step followed by a
    run.  Returning this as a disjunction lets the caller choose its own names. *)
Lemma run_cases : forall G n c l a l' b, mrunn G n c l a l' b ->
  (n = 0 /\ l' = l /\ b = a)
  \/ (exists k1 k2 m x, n = k1 + k2
        /\ mstepn G k1 c l a m x /\ mrunn G k2 c m x l' b).
Proof.
  intros G n c l a l' b H; inversion H; subst.
  - left; repeat split.
  - right; exists n1, n2, m, x; repeat split; assumption.
Qed.

Lemma entry_halt : forall s, get (entry_code s) (csize s) = IHalt.
Proof.
  intros s; unfold entry_code, get.
  rewrite app_nth2 by (rewrite comp_length; lia).
  rewrite comp_length, Nat.sub_diag; reflexivity.
Qed.

(* ===================================================================== *)
(** ** Completeness: the compiled code invents nothing.

    [Qc n] is the statement "a run of [n] steps entering a compiled fragment
    performs the fragment's job and then continues from its exit"; [Qlp n] is the
    same for the body of a loop, whose meaning is [lp] rather than [exec].
    Existentially quantifying the state at the exit is what removes the need to
    talk about *first* arrivals: [run_split] hands over the prefix up to the
    first exit, and the leftover run is returned to the caller.

    Every case consumes at least one step before recursing, so the leftover count
    is strictly smaller; [Seq] is the only case that recurses at the same count,
    and there the recursion is on a structurally smaller statement. *)

Section Complete.
Variable G : pname -> stmt.

Definition Qc (n : nat) : Prop :=
  forall s c base a l' b,
    holds c base (comp s base) ->
    mrunn G n c base a l' b ->
    (l' < base \/ base + csize s <= l') ->
    exists x n2, exec G s a x
      /\ mrunn G n2 c (base + csize s) x l' b /\ n2 < n.

Definition Qlp (n : nat) : Prop :=
  forall g1 s1 s2 g2 c base a l' b,
    holds c base (comp (Loop g1 s1 s2 g2) base) ->
    mrunn G n c (S base) a l' b ->
    (l' < base \/ base + csize (Loop g1 s1 s2 g2) <= l') ->
    exists x n2, lp G g1 s1 s2 g2 a x
      /\ mrunn G n2 c (base + csize (Loop g1 s1 s2 g2)) x l' b /\ n2 < n.

Lemma complete_all : forall n, Qc n /\ Qlp n.
Proof.
  intro n; induction n as [n IH] using (well_founded_induction lt_wf).
  assert (IHc : forall m, m < n -> Qc m) by (intros m Hm; apply (IH m Hm)).
  assert (IHl : forall m, m < n -> Qlp m) by (intros m Hm; apply (IH m Hm)).
  clear IH.
  (* --- the statement-indexed part, by induction on the statement --- *)
  assert (Hc : Qc n).
  { unfold Qc; induction s; intros c base a l' b Hh Hr Hout.
    (* Skip *)
    - simpl in Hh; apply holds_cons in Hh as [Hi _].
      destruct (run_cases G n c base a l' b Hr)
        as [[Hz [Hl Hb]] | [k1 [k2 [mm [xx [Hn [Hs Hrest]]]]]]].
      + subst; simpl in Hout; lia.
      + pose proof (step_cases G k1 c base a mm xx Hs) as Hsc;
          rewrite Hi in Hsc; simpl in Hsc; destruct Hsc as [Hk1 [Hm Hx]]; subst.
        exists a, k2; repeat split.
        * apply E_Skip.
        * replace (base + csize Skip) with (S base) by (simpl; lia). exact Hrest.
        * lia.
    (* Prim *)
    - simpl in Hh; apply holds_cons in Hh as [Hi _].
      destruct (run_cases G n c base a l' b Hr)
        as [[Hz [Hl Hb]] | [k1 [k2 [mm [xx [Hn [Hs Hrest]]]]]]].
      + subst; simpl in Hout; lia.
      + pose proof (step_cases G k1 c base a mm xx Hs) as Hsc;
          rewrite Hi in Hsc; simpl in Hsc; destruct Hsc as [Hk1 [Hm Hps]]; subst.
        exists xx, k2; repeat split.
        * apply E_Prim; exact Hps.
        * replace (base + csize (Prim p)) with (S base) by (simpl; lia). exact Hrest.
        * lia.
    (* Seq: the one case recursing at the same count, on a smaller statement *)
    - simpl in Hh; apply holds_app in Hh as [Hh1 Hh2]; rewrite comp_length in Hh2.
      destruct (IHs1 c base a l' b Hh1 Hr) as [x [n2 [Hex1 [Hr2 Hlt2]]]];
        [ simpl in Hout; lia | ].
      destruct (IHc n2 Hlt2 s2 c (base + csize s1) x l' b Hh2 Hr2)
        as [y [n3 [Hex2 [Hr3 Hlt3]]]]; [ simpl in Hout; lia | ].
      exists y, n3; repeat split.
      + eapply E_Seq; eassumption.
      + replace (base + csize (Seq s1 s2)) with (base + csize s1 + csize s2)
          by (simpl; lia). exact Hr3.
      + lia.
    (* If *)
    - assert (Hif := Hh); apply holds_if in Hif as [Hbr [Hh1 [Hck1 [Hh2 Hck2]]]].
      destruct (run_cases G n c base a l' b Hr)
        as [[Hz [Hl Hb]] | [k1 [k2 [mm [xx [Hn [Hs Hrest]]]]]]].
      + subst; simpl in Hout; lia.
      + pose proof (step_cases G k1 c base a mm xx Hs) as Hsc;
          rewrite Hbr in Hsc; simpl in Hsc;
          destruct Hsc as [Hk1 [Hx [[Hg Hm] | [Hg Hm]]]]; subst.
        (* then-branch *)
        * destruct (IHc k2 (ltac:(lia)) s1 c (S base) a l' b Hh1 Hrest)
            as [y [n3 [Hex [Hr3 Hlt3]]]]; [ simpl in Hout; lia | ].
          destruct (run_cases G n3 c (S base + csize s1) y l' b Hr3)
            as [[Hz' [Hl' Hb']] | [q1 [q2 [m1 [y1 [Hq [Hs1' Hrest1]]]]]]].
          { subst; simpl in Hout; lia. }
          pose proof (step_cases G q1 c (S base + csize s1) y m1 y1 Hs1') as Hsc1;
            rewrite Hck1 in Hsc1; simpl in Hsc1;
            destruct Hsc1 as [Hq1 [Hm1 [Hy1 Hg2]]]; subst.
          exists y, q2; repeat split.
          -- eapply E_IfT; eassumption.
          -- replace (base + csize (If g1 s1 s2 g2))
               with (base + (csize s1 + csize s2 + 3)) by (simpl; lia). exact Hrest1.
          -- lia.
        (* else-branch *)
        * destruct (IHc k2 (ltac:(lia)) s2 c (S base + csize s1 + 1) a l' b Hh2 Hrest)
            as [y [n3 [Hex [Hr3 Hlt3]]]]; [ simpl in Hout; lia | ].
          destruct (run_cases G n3 c (S base + csize s1 + 1 + csize s2) y l' b Hr3)
            as [[Hz' [Hl' Hb']] | [q1 [q2 [m1 [y1 [Hq [Hs1' Hrest1]]]]]]].
          { subst; simpl in Hout; lia. }
          pose proof (step_cases G q1 c (S base + csize s1 + 1 + csize s2) y m1 y1 Hs1')
            as Hsc1; rewrite Hck2 in Hsc1; simpl in Hsc1;
            destruct Hsc1 as [Hq1 [Hm1 [Hy1 Hg2]]]; subst.
          exists y, q2; repeat split.
          -- eapply E_IfF; eassumption.
          -- replace (base + csize (If g1 s1 s2 g2))
               with (base + (csize s1 + csize s2 + 3)) by (simpl; lia). exact Hrest1.
          -- lia.
    (* Loop: the entry assertion, then the iteration via the outer hypothesis *)
    - assert (Hlo := Hh); apply holds_loop in Hlo as [Hck [_ [_ [_ _]]]].
      destruct (run_cases G n c base a l' b Hr)
        as [[Hz [Hl Hb]] | [k1 [k2 [mm [xx [Hn [Hs Hrest]]]]]]].
      + subst; simpl in Hout; lia.
      + pose proof (step_cases G k1 c base a mm xx Hs) as Hsc;
          rewrite Hck in Hsc; simpl in Hsc;
          destruct Hsc as [Hk1 [Hm [Hx Hg]]]; subst.
        destruct (IHl k2 (ltac:(lia)) g1 s1 s2 g2 c base a l' b Hh Hrest Hout)
          as [y [n3 [Hlp [Hr3 Hlt3]]]].
        exists y, n3; repeat split.
        * eapply E_Loop; eassumption.
        * exact Hr3.
        * lia.
    (* Call *)
    - simpl in Hh; apply holds_cons in Hh as [Hi _].
      destruct (run_cases G n c base a l' b Hr)
        as [[Hz [Hl Hb]] | [k1 [k2 [mm [xx [Hn [Hs Hrest]]]]]]].
      + subst; simpl in Hout; lia.
      + pose proof (step_cases G k1 c base a mm xx Hs) as Hsc;
          rewrite Hi in Hsc; simpl in Hsc;
          destruct Hsc as [Hm [k [Hk Hsub]]]; subst.
        destruct (IHc k (ltac:(lia)) (G p) (entry_code (G p)) 0 a (csize (G p)) xx
                      (holds_entry (G p)) Hsub (ltac:(lia)))
          as [y [n3 [Hex [Hr3 _]]]].
        rewrite Nat.add_0_l in Hr3.
        destruct (halt_run_refl G n3 (entry_code (G p)) (csize (G p)) y
                    (csize (G p)) xx (entry_halt (G p)) Hr3) as [_ Hxy]; subst xx.
        exists y, k2; repeat split.
        * apply E_Call; exact Hex.
        * replace (base + csize (Call p)) with (S base) by (simpl; lia). exact Hrest.
        * lia.
    (* Uncall *)
    - simpl in Hh; apply holds_cons in Hh as [Hi _].
      destruct (run_cases G n c base a l' b Hr)
        as [[Hz [Hl Hb]] | [k1 [k2 [mm [xx [Hn [Hs Hrest]]]]]]].
      + subst; simpl in Hout; lia.
      + pose proof (step_cases G k1 c base a mm xx Hs) as Hsc;
          rewrite Hi in Hsc; simpl in Hsc;
          destruct Hsc as [Hm [k [Hk Hsub]]]; subst.
        destruct (IHc k (ltac:(lia)) (invert (G p)) (entry_code (invert (G p))) 0 a
                      (csize (invert (G p))) xx
                      (holds_entry (invert (G p))) Hsub (ltac:(lia)))
          as [y [n3 [Hex [Hr3 _]]]].
        rewrite Nat.add_0_l in Hr3.
        destruct (halt_run_refl G n3 (entry_code (invert (G p))) (csize (invert (G p)))
                    y (csize (invert (G p))) xx (entry_halt (invert (G p))) Hr3)
          as [_ Hxy]; subst xx.
        exists y, k2; repeat split.
        * apply E_Uncall; exact Hex.
        * replace (base + csize (Uncall p)) with (S base) by (simpl; lia). exact Hrest.
        * lia. }
  split; [ exact Hc | ].
  (* --- the loop body, using Hc at the same count --- *)
  unfold Qlp; intros g1 s1 s2 g2 c base a l' b Hh Hr Hout.
  assert (Hlo := Hh); apply holds_loop in Hlo as [_ [Hh1 [Hbr [Hh2 Hck]]]].
  destruct (Hc s1 c (S base) a l' b Hh1 Hr) as [x [n2 [Hex1 [Hr2 Hlt2]]]];
    [ simpl in Hout; lia | ].
  destruct (run_cases G n2 c (S base + csize s1) x l' b Hr2)
    as [[Hz [Hl Hb]] | [k1 [k2 [mm [xx [Hn [Hs Hrest]]]]]]].
  { subst; simpl in Hout; lia. }
  pose proof (step_cases G k1 c (S base + csize s1) x mm xx Hs) as Hsc;
    rewrite Hbr in Hsc; simpl in Hsc;
    destruct Hsc as [Hk1 [Hx [[Hg Hm] | [Hg Hm]]]]; subst.
  - (* the exit test holds: this was the last round *)
    exists x, k2; repeat split.
    + apply L_one; assumption.
    + replace (base + csize (Loop g1 s1 s2 g2))
        with (base + (csize s1 + csize s2 + 3)) by (simpl; lia). exact Hrest.
    + lia.
  - (* another round: run s2, assert ~g1, iterate *)
    destruct (IHc k2 (ltac:(lia)) s2 c (S base + csize s1 + 1) x l' b Hh2 Hrest)
      as [y [n4 [Hex2 [Hr4 Hlt4]]]]; [ simpl in Hout; lia | ].
    destruct (run_cases G n4 c (S base + csize s1 + 1 + csize s2) y l' b Hr4)
      as [[Hz' [Hl' Hb']] | [q1 [q2 [m1 [y1 [Hq [Hs1' Hrest1]]]]]]].
    { subst; simpl in Hout; lia. }
    pose proof (step_cases G q1 c (S base + csize s1 + 1 + csize s2) y m1 y1 Hs1')
      as Hsc1; rewrite Hck in Hsc1; simpl in Hsc1;
      destruct Hsc1 as [Hq1 [Hm1 [Hy1 Hg1']]]; subst.
    destruct (IHl q2 (ltac:(lia)) g1 s1 s2 g2 c base y l' b Hh Hrest1 Hout)
      as [z [n6 [Hlp [Hr6 Hlt6]]]].
    exists z, n6; repeat split.
    + eapply L_more; eassumption.
    + exact Hr6.
    + lia.
Qed.

Corollary crun_complete : forall s a b, crun G s a b -> exec G s a b.
Proof.
  intros s a b [n Hr]; unfold crun in *.
  destruct (proj1 (complete_all n) s (entry_code s) 0 a (csize s) b
              (holds_entry s) Hr (ltac:(lia))) as [x [n2 [Hex [Hr2 _]]]].
  rewrite Nat.add_0_l in Hr2.
  destruct (halt_run_refl G n2 (entry_code s) (csize s) x (csize s) b
              (entry_halt s) Hr2) as [_ Hxb]; subst b.
  exact Hex.
Qed.

End Complete.

(** **The** theorem: the compiler-mediated semantics is the big-step semantics. *)
Theorem crun_iff : forall G s a b, exec G s a b <-> crun G s a b.
Proof.
  intros G s a b; split; intro H.
  - apply crun_sound; exact H.
  - eapply crun_complete; exact H.
Qed.

(* ===================================================================== *)
(** ** Note on what made completeness work.

    [mrun G c l a l' b] says *some* run from [l] reaches [l'], not that [l'] is
    where the run first arrives, and the code outside a fragment is arbitrary —
    so a run could pass through a fragment's exit, wander off and come back in a
    different state.  Three things remove that:

      - the entry layout ends in [IHalt] ([entry_halt]), so at the top level and
        at every procedure's exit no step is possible and "reaches the exit"
        does pin the final state down;
      - [comp_within] / [confined]: every instruction of [comp s base] targets a
        label in [base .. base + csize s], so a run entering a fragment stays
        inside until it leaves through the top;
      - [run_split]: a run leaving a confined region is cut at its *first* exit,
        and the statement [Qc] hands the leftover run back to the caller instead
        of asserting anything about first arrivals.

    The step count includes nested calls ([N_Call] costs [S n]), which is what
    lets the [Call] case appeal to the induction hypothesis at all. *)

End Compile.
