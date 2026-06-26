(** * RevToy.v — a second, unrelated instance: a reversible counter over Z

    To show the framework is not Janus-specific, we instantiate it with a
    completely different state space ([Z], a single counter), different
    primitives ([Inc]/[Dec]), and different guards ("the counter equals k").
    The reversibility theorem for this language is obtained *for free* from
    the same generic [exec_injective] — the three local laws are one-liners
    closed by [lia]. *)

From Stdlib Require Import ZArith Lia.
Require Import RevCore.
Open Scope Z_scope.

Module ToyPrim <: REV_PRIM.
  Definition state := Z.
  Definition guard := Z.
  Definition gtest (k : Z) (a : Z) : bool := Z.eqb a k.

  Inductive prim_ : Type := Inc | Dec.
  Definition prim := prim_.

  Definition pstep (p : prim) (a b : Z) : Prop :=
    match p with Inc => b = a + 1 | Dec => b = a - 1 end.

  Definition pinv (p : prim) : prim :=
    match p with Inc => Dec | Dec => Inc end.

  Lemma pinv_invol : forall p, pinv (pinv p) = p.
  Proof. destruct p; reflexivity. Qed.

  Lemma pstep_det : forall p a b b', pstep p a b -> pstep p a b' -> b = b'.
  Proof. destruct p; simpl; intros a b b' H1 H2; subst; reflexivity. Qed.

  Lemma pstep_rev : forall p a b, pstep p a b -> pstep (pinv p) b a.
  Proof. destruct p; simpl; intros a b H; subst; lia. Qed.
End ToyPrim.

Module Toy := RevLang ToyPrim.

(** Reversibility of the toy counter language, for free. *)
Theorem toy_reversible :
  forall (Γ : Toy.pname -> Toy.stmt) (s : Toy.stmt) (a a' b : Z),
    Toy.exec Γ s a b -> Toy.exec Γ s a' b -> a = a'.
Proof. exact Toy.exec_injective. Qed.
