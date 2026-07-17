(** * RevIO.v — reversible input/output as a RevCore instance

    The verified frame core ([RevFrame.v]) and its extracted interpreter model a
    Janus program as a *pure store transformer*: there is no I/O.  The dialect
    [jana2014_in_out] adds two statements — [read x] and [write x] — that PyJanus
    runs reversibly against an input/output stream, but which [vjanus] can only
    refuse (it lowers them to an "unsupported" exit).  This file closes that gap
    *semantically*: it exhibits reversible I/O as a first-class [REV_PRIM]
    instance, so the reversibility of read/write is a theorem, not an assertion.

    The state is a register store together with an input and an output stream:

        state := (nat -> Z) * list Z * list Z      (* store, input, output *)

    The primitives are the two I/O moves and their *stream-level* inverses.  The
    key modelling point is that at the primitive level [read] and [write] are NOT
    each other's inverse — [read] consumes the input, so its inverse must *put a
    value back onto the input* (an "unread"); likewise [write]'s inverse pops the
    output.  This is exactly the reversible-I/O convention (running a program
    backward reads the reversed output and writes the reversed input):

        Read i   : input head -> register i   (register i must be 0)
        Unread i : register i -> input head, register i := 0     (inverse of Read)
        Write i  : register i -> output head, register i := 0
        Unwrite i: output head -> register i  (register i must be 0) (inv of Write)

    Supplying the three local laws ([pinv_invol], [pstep_det], [pstep_rev]) makes
    [RevLang] hand back [exec_rev], [exec_iff], [exec_det] and [exec_injective]
    for a genuinely I/O-effectful language — reversibility for free. *)

From Stdlib Require Import ZArith List Lia.
From Stdlib Require Import FunctionalExtensionality.
Require Import RevCore.
Import ListNotations.
Open Scope Z_scope.

(** A register store and its pointwise update. *)
Definition store := nat -> Z.
Definition upd (i : nat) (v : Z) (s : store) : store :=
  fun j => if Nat.eqb i j then v else s j.

Lemma upd_upd : forall i v w s, upd i v (upd i w s) = upd i v s.
Proof.
  intros; apply functional_extensionality; intro j.
  unfold upd; destruct (Nat.eqb i j); reflexivity.
Qed.

Lemma upd_same : forall i s, upd i (s i) s = s.
Proof.
  intros; apply functional_extensionality; intro j.
  unfold upd; destruct (Nat.eqb i j) eqn:E; [ | reflexivity ].
  apply Nat.eqb_eq in E; subst j; reflexivity.
Qed.

Lemma upd_get : forall i v s, upd i v s i = v.
Proof. intros; unfold upd; rewrite Nat.eqb_refl; reflexivity. Qed.

(** From [s i = 0], erasing register i is the identity. *)
Lemma upd_erase_zero : forall i s, s i = 0 -> upd i 0 s = s.
Proof. intros i s H. rewrite <- H at 1. apply upd_same. Qed.

Module IOPrim <: REV_PRIM.
  Definition state := (store * list Z * list Z)%type.

  (** Guards may test the whole state (e.g. "register i equals k"). *)
  Definition guard := state -> bool.
  Definition gtest (g : guard) (a : state) : bool := g a.

  Inductive prim_ : Type :=
  | Read    (i : nat)
  | Unread  (i : nat)
  | Write   (i : nat)
  | Unwrite (i : nat).
  Definition prim := prim_.

  Definition pstep (p : prim) (a b : state) : Prop :=
    let '(s, inp, out) := a in
    match p with
    | Read i    => exists v inp', inp = v :: inp' /\ s i = 0
                                  /\ b = (upd i v s, inp', out)
    | Unread i  => b = (upd i 0 s, s i :: inp, out)
    | Write i   => b = (upd i 0 s, inp, s i :: out)
    | Unwrite i => exists v out', out = v :: out' /\ s i = 0
                                  /\ b = (upd i v s, inp, out')
    end.

  Definition pinv (p : prim) : prim :=
    match p with
    | Read i    => Unread i
    | Unread i  => Read i
    | Write i   => Unwrite i
    | Unwrite i => Write i
    end.

  Lemma pinv_invol : forall p, pinv (pinv p) = p.
  Proof. destruct p; reflexivity. Qed.

  Lemma pstep_det : forall p a b b', pstep p a b -> pstep p a b' -> b = b'.
  Proof.
    destruct p; intros [[s inp] out] b b'; simpl.
    - (* Read *) intros [v [inp' [Hin [Hz Hb]]]] [v0 [inp0 [Hin0 [Hz0 Hb0]]]].
      subst. inversion Hin0. subst. reflexivity.
    - (* Unread *) intros Hb Hb'; subst; reflexivity.
    - (* Write *)  intros Hb Hb'; subst; reflexivity.
    - (* Unwrite *) intros [v [out' [Ho [Hz Hb]]]] [v0 [out0 [Ho0 [Hz0 Hb0]]]].
      subst. inversion Ho0. subst. reflexivity.
  Qed.

  Lemma pstep_rev : forall p a b, pstep p a b -> pstep (pinv p) b a.
  Proof.
    destruct p; intros [[s inp] out] b; simpl.
    - (* Read -> Unread *)
      intros [v [inp' [Hin [Hz Hb]]]]; subst; simpl.
      rewrite upd_get, upd_upd, upd_erase_zero by assumption. reflexivity.
    - (* Unread -> Read *)
      intros Hb; subst; simpl.
      exists (s i), inp. split; [reflexivity | split].
      + apply upd_get.
      + rewrite upd_upd, upd_same. reflexivity.
    - (* Write -> Unwrite *)
      intros Hb; subst; simpl.
      exists (s i), out. split; [reflexivity | split].
      + apply upd_get.
      + rewrite upd_upd, upd_same. reflexivity.
    - (* Unwrite -> Write *)
      intros [v [out' [Ho [Hz Hb]]]]; subst; simpl.
      rewrite upd_get, upd_upd, upd_erase_zero by assumption. reflexivity.
  Qed.
End IOPrim.

Module IO := RevLang IOPrim.

(** Reversibility of the reversible-I/O language, inherited verbatim from the
    generic functor: a final (store, input, output) determines the initial one. *)
Theorem io_reversible :
  forall (Γ : IO.pname -> IO.stmt) (s : IO.stmt) (a a' b : IOPrim.state),
    IO.exec Γ s a b -> IO.exec Γ s a' b -> a = a'.
Proof. exact IO.exec_injective. Qed.

(** Inverting a program swaps read/write for their stream duals and reverses
    time, again for free. *)
Theorem io_iff :
  forall (Γ : IO.pname -> IO.stmt) (s : IO.stmt) (a b : IOPrim.state),
    IO.exec Γ s a b <-> IO.exec Γ (IO.invert s) b a.
Proof. intros; apply IO.exec_iff. Qed.

(** ** Concrete checks (the "tests" for this formalization). *)

Definition z0 : store := fun _ => 0.
Definition Γ0 : IO.pname -> IO.stmt := fun _ => IO.Skip.

Lemma upd_idem_zero : forall i, upd i 0 z0 = z0.
Proof. intro i. apply upd_erase_zero. reflexivity. Qed.

(** [write 0] emits register 0 and clears it: (r0=5, in=[], out=[]) -> (0,[],[5]). *)
Example write_emits :
  IO.exec Γ0 (IO.Prim (IOPrim.Write 0)) (upd 0 5 z0, [], []) (z0, [], [5]).
Proof.
  apply IO.E_Prim. simpl. rewrite upd_get, upd_upd, upd_idem_zero. reflexivity.
Qed.

(** [read 0] consumes an input value into the (zero) register 0:
    (r0=0, in=[7], out=[]) -> (r0=7, in=[], out=[]). *)
Example read_consumes :
  IO.exec Γ0 (IO.Prim (IOPrim.Read 0)) (z0, [7], []) (upd 0 7 z0, [], []).
Proof.
  apply IO.E_Prim. simpl. exists 7, (@nil Z). repeat split.
Qed.

(** Running [read 0] backward is [write]-to-input: it recovers the input stream
    and re-zeroes the register — reversibility, concretely. *)
Example read_backward :
  IO.exec Γ0 (IO.invert (IO.Prim (IOPrim.Read 0))) (upd 0 7 z0, [], []) (z0, [7], []).
Proof.
  apply IO.exec_rev. apply read_consumes.
Qed.
