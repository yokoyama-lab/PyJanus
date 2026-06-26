(** * RevCA.v — a fourth instance: a reversible cellular automaton

    A genuinely different kind of reversible language: a *second-order*
    cellular automaton.  This stresses [RevCore.v] along a new axis — the state
    is an infinite object (a pair of bi-infinite binary configurations), and
    reversibility comes not from an arithmetic inverse but from the involutivity
    of XOR.

    A second-order CA keeps two generations [(cur, prev)] and steps by

        next i = rule(cur) i  XOR  prev i,        result = (next, cur).

    Because XOR is its own inverse, [prev i = rule(cur) i XOR next i], so the
    step is a *bijection* on states; the backward step recovers the older
    generation.  We package the forward and backward steps as a mutually-inverse
    pair of primitives [Fwd]/[Bwd].  The concrete local [rule] below is the
    "rule 90" neighbourhood [c(i-1) XOR c(i+1)]; nothing in the reversibility
    argument depends on which local rule is chosen — *every* local rule yields a
    reversible second-order CA, which is exactly the point of factoring through
    [REV_PRIM].  Reversibility of structured CA programs (sequencing,
    assertion-guarded conditionals/loops, call/uncall) then comes *for free*
    from the generic [exec_injective]. *)

From Stdlib Require Import ZArith Bool FunctionalExtensionality.
Require Import RevCore.
Open Scope Z_scope.

Module CAPrim <: REV_PRIM.

  (** A configuration assigns a bit to every (integer-indexed) cell. *)
  Definition config := Z -> bool.

  (** The local rule (here: rule 90, [c(i-1) XOR c(i+1)]).  Arbitrary. *)
  Definition rule (c : config) (i : Z) : bool := xorb (c (i - 1)) (c (i + 1)).

  (** A state carries two generations: [(current, previous)]. *)
  Definition state := (config * config)%type.

  (** One forward step of the second-order CA, and its inverse. *)
  Definition step (st : state) : state :=
    (fun i => xorb (rule (fst st) i) (snd st i), fst st).
  Definition unstep (st : state) : state :=
    (snd st, fun i => xorb (rule (snd st) i) (fst st i)).

  Lemma unstep_step : forall st, unstep (step st) = st.
  Proof.
    intros [c1 c0]; unfold step, unstep; cbn [fst snd]; f_equal.
    apply functional_extensionality; intro i.
    destruct (rule c1 i); destruct (c0 i); reflexivity.
  Qed.

  Lemma step_unstep : forall st, step (unstep st) = st.
  Proof.
    intros [c2 c1]; unfold step, unstep; cbn [fst snd]; f_equal.
    apply functional_extensionality; intro i.
    destruct (rule c1 i); destruct (c2 i); reflexivity.
  Qed.

  (** *** Guards: test whether cell [k] of the current generation is on. *)
  Definition guard := Z.
  Definition gtest (k : Z) (st : state) : bool := fst st k.

  (** *** Primitives: step forward or backward. *)
  Inductive prim_ := Fwd | Bwd.
  Definition prim := prim_.

  Definition pstep (p : prim) (a b : state) : Prop :=
    match p with Fwd => b = step a | Bwd => b = unstep a end.

  Definition pinv (p : prim) : prim :=
    match p with Fwd => Bwd | Bwd => Fwd end.

  Lemma pinv_invol : forall p, pinv (pinv p) = p.
  Proof. destruct p; reflexivity. Qed.

  Lemma pstep_det : forall p a b b', pstep p a b -> pstep p a b' -> b = b'.
  Proof. destruct p; simpl; intros a b b' H1 H2; congruence. Qed.

  Lemma pstep_rev : forall p a b, pstep p a b -> pstep (pinv p) b a.
  Proof.
    destruct p; simpl; intros a b H; subst b.
    - rewrite unstep_step; reflexivity.
    - rewrite step_unstep; reflexivity.
  Qed.

End CAPrim.

Import CAPrim.
Module CA := RevLang CAPrim.

(** ** Reversibility of CA programs — straight from the framework. *)
Theorem ca_reversible :
  forall (Γ : CA.pname -> CA.stmt) (s : CA.stmt) (a a' b : state),
    CA.exec Γ s a b -> CA.exec Γ s a' b -> a = a'.
Proof. exact CA.exec_injective. Qed.

Theorem ca_invert_correct :
  forall (Γ : CA.pname -> CA.stmt) (s : CA.stmt) (a b : state),
    CA.exec Γ s a b <-> CA.exec Γ (CA.invert s) b a.
Proof. exact CA.exec_iff. Qed.

(** A demo: two forward steps invert to two backward steps. *)
Example invert_ca_demo :
  CA.invert (CA.Seq (CA.Prim Fwd) (CA.Prim Fwd))
  = CA.Seq (CA.Prim Bwd) (CA.Prim Bwd).
Proof. reflexivity. Qed.
