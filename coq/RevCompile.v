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

From Stdlib Require Import List Bool Arith Lia.
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

Definition entry_code (s : stmt) : code := comp s 0.

Inductive mstep (G : pname -> stmt) : code -> nat -> P.state -> nat -> P.state -> Prop :=
| M_Nop : forall c l nxt a,
    get c l = INop nxt -> mstep G c l a nxt a
| M_Prim : forall c l p nxt a b,
    get c l = IPrim p nxt -> P.pstep p a b -> mstep G c l a nxt b
| M_BrT : forall c l g lt lf a,
    get c l = IBr g lt lf -> P.gtest g a = true -> mstep G c l a lt a
| M_BrF : forall c l g lt lf a,
    get c l = IBr g lt lf -> P.gtest g a = false -> mstep G c l a lf a
| M_Chk : forall c l g v nxt a,
    get c l = IChk g v nxt -> P.gtest g a = v -> mstep G c l a nxt a
| M_Call : forall c l p nxt a b,
    get c l = ICall p nxt ->
    mrun G (entry_code (G p)) 0 a (csize (G p)) b ->
    mstep G c l a nxt b
| M_Uncall : forall c l p nxt a b,
    get c l = IUncall p nxt ->
    mrun G (entry_code (invert (G p))) 0 a (csize (invert (G p))) b ->
    mstep G c l a nxt b

with mrun (G : pname -> stmt) : code -> nat -> P.state -> nat -> P.state -> Prop :=
| MR_refl : forall c l a, mrun G c l a l a
| MR_step : forall c l a m x n b,
    mstep G c l a m x -> mrun G c m x n b -> mrun G c l a n b.

Scheme mstep_mut := Induction for mstep Sort Prop
  with mrun_mut  := Induction for mrun  Sort Prop.

Lemma mrun_trans : forall G c l a m x n b,
  mrun G c l a m x -> mrun G c m x n b -> mrun G c l a n b.
Proof.
  intros G c l a m x n b H; revert n b; induction H; intros n' b' H2.
  - exact H2.
  - eapply MR_step; [ eassumption | apply IHmrun; exact H2 ].
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
Proof. intros s k _; reflexivity. Qed.

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
    + specialize (IHexec (comp (G p) 0) 0 (holds_entry (G p))).
      rewrite Nat.add_0_l in IHexec; exact IHexec.
    + replace (base + csize (Call p)) with (S base) by (simpl; lia).
      apply MR_refl.
  (* Uncall *)
  - simpl in Hh; apply holds_cons in Hh as [Hi _].
    eapply MR_step; [ eapply M_Uncall; [ exact Hi | ] | ].
    + specialize (IHexec (comp (invert (G p)) 0) 0 (holds_entry (invert (G p)))).
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
  specialize (comp_sound s a b H (comp s 0) 0 (holds_entry s)) as Hr.
  rewrite Nat.add_0_l in Hr; exact Hr.
Qed.

End Sound.

(* ===================================================================== *)
(** ** The open half: completeness.

    [crun_sound] says the compiler loses nothing.  The converse — the machine
    invents nothing, [crun G s a b -> exec G s a b] — is **not proved here**, and
    the reason is worth writing down because it is not a gap in the compiler.

    [mrun G c l a l' b] says *some* run from [l] reaches [l'], not that [l'] is
    where the run first arrives.  Since the code outside a fragment is arbitrary,
    a run may pass through a fragment's exit label, wander off and come back with
    a different state, so [mrun c base a (base + csize s) b] alone does not pin
    [b] down.  Closing the converse therefore needs

      - **confinement**: every instruction of [comp s base] targets a label in
        [base .. base + csize s], so a run entering the fragment stays inside
        until it leaves through the top (provable by induction on [s]);
      - **first arrival**: a step-counted run relation and a splitting lemma
        giving, for a run that leaves a sub-region, the *earliest* run to the
        region's exit — which is what lets the [Seq]/[If]/[Loop] cases recurse;
      - a step count that includes nested procedure calls, since [M_Call] runs an
        unbounded sub-run and induction on the outer count would not cover it.

    That is a development in its own right, and none of it is needed for
    [crun_sound].  [RevSemantics.v] keeps the distinction visible by naming the
    compiler pairs [*_sound] rather than [*_iff]. *)

End Compile.
