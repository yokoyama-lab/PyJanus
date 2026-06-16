(** * RevJanus.v — core Janus as an instance of the generic framework

    We instantiate [RevCore.RevLang] with the Janus atoms (reversible
    assignment [x op= e] with side condition [~ occurs x e], and swap
    [x <=> y]) and Janus guards (an expression is "true" when nonzero).
    The three local laws are discharged by reusing the algebraic lemmas
    already proved in [Janus.v].  The headline reversibility theorem then
    falls out as a *corollary of the generic [exec_injective]* — no
    Janus-specific reversibility argument is repeated. *)

From Stdlib Require Import ZArith.
Require Import RevCore.
Require Import Janus.   (* reuse store, expr, eval, occurs, aop, adenote, ainv, sw + lemmas *)
Open Scope Z_scope.

Module JanusPrim <: REV_PRIM.
  Definition state := store.
  Definition guard := expr.
  Definition gtest (e : expr) (s : store) : bool := negb (Z.eqb (eval s e) 0).

  Inductive prim_ : Type :=
  | PAssign (x : var) (o : aop) (e : expr)   (* x op= e , needs ~ occurs x e *)
  | PSwap   (x y : var).                      (* x <=> y *)
  Definition prim := prim_.

  Definition pstep (p : prim) (a b : state) : Prop :=
    match p with
    | PAssign x o e => occurs x e = false /\ b = update a x (adenote o (a x) (eval a e))
    | PSwap x y => b = sw a x y
    end.

  Definition pinv (p : prim) : prim :=
    match p with
    | PAssign x o e => PAssign x (ainv o) e
    | PSwap x y => PSwap x y
    end.

  Lemma pinv_invol : forall p, pinv (pinv p) = p.
  Proof. destruct p; simpl; try reflexivity. rewrite ainv_invol; reflexivity. Qed.

  Lemma pstep_det : forall p a b b', pstep p a b -> pstep p a b' -> b = b'.
  Proof.
    destruct p; simpl; intros a b b' H1 H2.
    - destruct H1 as [_ ->]; destruct H2 as [_ ->]; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma pstep_rev : forall p a b, pstep p a b -> pstep (pinv p) b a.
  Proof.
    destruct p; simpl; intros a b H.
    - destruct H as [Hocc ->]. split; [ exact Hocc | ].
      rewrite update_eq.
      rewrite (eval_update_notin x (adenote o (a x) (eval a e)) a e Hocc).
      rewrite ainv_correct, update_shadow, update_same; reflexivity.
    - subst. rewrite sw_invol; reflexivity.
  Qed.
End JanusPrim.

Module JR := RevLang JanusPrim.

(** Core Janus is reversible — obtained purely as an instance of the generic
    framework's [exec_injective]. *)
Theorem janus_reversible :
  forall (Γ : JR.pname -> JR.stmt) (s : JR.stmt) (a a' b : store),
    JR.exec Γ s a b -> JR.exec Γ s a' b -> a = a'.
Proof. exact JR.exec_injective. Qed.

(** And the inverse program computes the inverse run. *)
Theorem janus_invert_correct :
  forall (Γ : JR.pname -> JR.stmt) (s : JR.stmt) (a b : store),
    JR.exec Γ s a b <-> JR.exec Γ (JR.invert s) b a.
Proof. exact JR.exec_iff. Qed.
