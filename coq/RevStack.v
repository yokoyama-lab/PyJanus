(** * RevStack.v — a third instance: a reversible stack machine

    A second demonstration that [RevCore.v] is not Janus-specific.  Here the
    state is a *stack* (a [list Z]) rather than a store-as-function, and the
    primitives are stack operations.  Reversibility of structured programs over
    these primitives is again obtained *for free* from the generic
    [exec_injective]; all we supply are the three local laws.

    The primitives illustrate the two ways an atom can be reversible:

      - a *mutually-inverse pair* — [Push v] / [Pop v] (push a known constant /
        pop and assert it), [AddNext] / [SubNext] (top += / -= the element below
        it, which is preserved and so recoverable);
      - a *self-inverse* atom — [Neg] (negate the top), [SwapTop] (swap the top
        two).

    Note [Pop v], [Neg], [AddNext], … are *partial*: they are undefined on a
    too-short stack.  [pstep] being a relation (not a function) accommodates this
    directly, and partiality is no obstacle to reversibility. *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Require Import RevCore.
Open Scope Z_scope.

Module StackPrim <: REV_PRIM.

  Definition state := list Z.

  (** *** Guards: test emptiness, the top value, or the depth. *)
  Inductive guard_ := GEmpty | GTopEq (k : Z) | GDepth (n : nat).
  Definition guard := guard_.
  Definition gtest (g : guard) (s : state) : bool :=
    match g with
    | GEmpty    => match s with [] => true | _ => false end
    | GTopEq k  => match s with x :: _ => Z.eqb x k | [] => false end
    | GDepth n  => Nat.eqb (length s) n
    end.

  (** *** Primitives. *)
  Inductive prim_ :=
  | Push (v : Z)        (* push a known constant *)
  | Pop  (v : Z)        (* pop and assert the popped value is [v] *)
  | Neg                 (* negate the top *)
  | AddNext             (* top += second-from-top *)
  | SubNext             (* top -= second-from-top *)
  | SwapTop.            (* swap the top two *)
  Definition prim := prim_.

  Definition pstep (p : prim) (a b : state) : Prop :=
    match p with
    | Push v  => b = v :: a
    | Pop v   => a = v :: b
    | Neg     => match a with x :: r => b = (- x) :: r | [] => False end
    | AddNext => match a with x :: y :: r => b = (x + y) :: y :: r | _ => False end
    | SubNext => match a with x :: y :: r => b = (x - y) :: y :: r | _ => False end
    | SwapTop => match a with x :: y :: r => b = y :: x :: r | _ => False end
    end.

  Definition pinv (p : prim) : prim :=
    match p with
    | Push v  => Pop v
    | Pop v   => Push v
    | Neg     => Neg
    | AddNext => SubNext
    | SubNext => AddNext
    | SwapTop => SwapTop
    end.

  Lemma pinv_invol : forall p, pinv (pinv p) = p.
  Proof. destruct p; reflexivity. Qed.

  Lemma pstep_det : forall p a b b', pstep p a b -> pstep p a b' -> b = b'.
  Proof.
    destruct p; simpl; intros a b b' H1 H2;
      try (destruct a as [|x [|y r]]); try contradiction; congruence.
  Qed.

  Lemma pstep_rev : forall p a b, pstep p a b -> pstep (pinv p) b a.
  Proof.
    destruct p; simpl; intros a b H.
    - (* Push v -> Pop v *) exact H.
    - (* Pop v -> Push v *) exact H.
    - (* Neg (self-inverse) *)
      destruct a as [|x r]; [contradiction|]. subst b; simpl.
      rewrite Z.opp_involutive; reflexivity.
    - (* AddNext -> SubNext *)
      destruct a as [|x [|y r]]; try contradiction. subst b; simpl.
      replace (x + y - y) with x by lia; reflexivity.
    - (* SubNext -> AddNext *)
      destruct a as [|x [|y r]]; try contradiction. subst b; simpl.
      replace (x - y + y) with x by lia; reflexivity.
    - (* SwapTop (self-inverse) *)
      destruct a as [|x [|y r]]; try contradiction. subst b; reflexivity.
  Qed.

End StackPrim.

Import StackPrim.
Module Stk := RevLang StackPrim.

(** ** Reversibility of stack-machine programs — straight from the framework. *)
Theorem stack_reversible :
  forall (Γ : Stk.pname -> Stk.stmt) (s : Stk.stmt) (a a' b : state),
    Stk.exec Γ s a b -> Stk.exec Γ s a' b -> a = a'.
Proof. exact Stk.exec_injective. Qed.

(** Syntactic inversion is semantically correct here too. *)
Theorem stack_invert_correct :
  forall (Γ : Stk.pname -> Stk.stmt) (s : Stk.stmt) (a b : state),
    Stk.exec Γ s a b <-> Stk.exec Γ (Stk.invert s) b a.
Proof. exact Stk.exec_iff. Qed.

(** A concrete demo: [push 3 ; addnext] inverts to [subnext ; pop 3].
    The generic inverter mirrors the sequence and replaces each atom by its
    inverse — by computation, no proof effort. *)
Example invert_stack_demo :
  Stk.invert (Stk.Seq (Stk.Prim (Push 3)) (Stk.Prim AddNext))
  = Stk.Seq (Stk.Prim SubNext) (Stk.Prim (Pop 3)).
Proof. reflexivity. Qed.

(** And it really runs: [push 3 ; addnext] takes [5;7;…] (via [3;5;7;…])
    to [8;5;7;…]. *)
Example run_stack_demo :
  forall Γ rest,
    Stk.exec Γ (Stk.Seq (Stk.Prim (Push 3)) (Stk.Prim AddNext))
             (5 :: 7 :: rest) (8 :: 5 :: 7 :: rest).
Proof.
  intros Γ rest.
  eapply Stk.E_Seq.
  - apply Stk.E_Prim. reflexivity.            (* Push 3:  3 :: 5 :: 7 :: rest *)
  - apply Stk.E_Prim. simpl. reflexivity.     (* AddNext: 8 :: 5 :: 7 :: rest *)
Qed.
