(** * RevMul.v — reversible multiplicative assignment: the *= and /= operators

    The verified frame core ([RevFrame.v]) offers only the *total* reversible
    updates [OAdd | OSub | OXor] (`+= -= ^=`); [vjanus] therefore reports Janus's
    multiplicative updates `*=` / `/=` as unsupported.  The reason is not that
    they are irreversible but that their reversibility is *conditional and
    partial*, so they do not fit a total apply-function:

      - `x *= k` is injective in [x] exactly when [k <> 0]; and
      - its inverse `x /= k` is a *partial* operation — defined only when
        [k] divides the current value of [x].

    A [REV_PRIM] primitive is a *relation* [pstep], not a total function, so it
    accommodates both facts directly.  We model a single Z register and

        pstep (Mul k) a b := k <> 0 /\ b = k * a        (* x *= k *)
        pstep (Div k) a b := k <> 0 /\ a = k * b        (* x /= k, i.e. b = a/k *)

    where [Div k]'s relation simply *has no [b]* unless [k] divides [a] — that is
    exactly the partiality of `/=`.  The three local laws hold (determinism of
    [Div] is left-cancellation of a nonzero factor), so [RevLang] yields
    [exec_rev] / [exec_iff] / [exec_det] / [exec_injective] for a language whose
    atoms are `*=` and `/=` — a machine-checked account of why those operators
    are reversible, and under exactly which side condition. *)

From Stdlib Require Import ZArith Lia.
Require Import RevCore.
Open Scope Z_scope.

Module MulPrim <: REV_PRIM.
  Definition state := Z.
  Definition guard := Z.
  Definition gtest (k : Z) (a : Z) : bool := Z.eqb a k.

  Inductive prim_ : Type := Mul (k : Z) | Div (k : Z).
  Definition prim := prim_.

  Definition pstep (p : prim) (a b : Z) : Prop :=
    match p with
    | Mul k => k <> 0 /\ b = k * a
    | Div k => k <> 0 /\ a = k * b
    end.

  Definition pinv (p : prim) : prim :=
    match p with Mul k => Div k | Div k => Mul k end.

  Lemma pinv_invol : forall p, pinv (pinv p) = p.
  Proof. destruct p; reflexivity. Qed.

  Lemma pstep_det : forall p a b b', pstep p a b -> pstep p a b' -> b = b'.
  Proof.
    destruct p as [k | k]; simpl; intros a b b' [Hk Hb] [_ Hb'].
    - (* Mul: b = k*a = b' *) subst; reflexivity.
    - (* Div: a = k*b = k*b', cancel the nonzero k *)
      apply (Z.mul_reg_l b b' k Hk). rewrite <- Hb, <- Hb'. reflexivity.
  Qed.

  Lemma pstep_rev : forall p a b, pstep p a b -> pstep (pinv p) b a.
  Proof.
    destruct p as [k | k]; simpl; intros a b [Hk He]; split; assumption.
  Qed.
End MulPrim.

Module Mul := RevLang MulPrim.

(** Reversibility of the multiplicative-update language, for free: a final value
    determines the initial one (given the nonzero-factor side conditions carried
    by each step). *)
Theorem mul_reversible :
  forall (Γ : Mul.pname -> Mul.stmt) (s : Mul.stmt) (a a' b : Z),
    Mul.exec Γ s a b -> Mul.exec Γ s a' b -> a = a'.
Proof. exact Mul.exec_injective. Qed.

(** ** Concrete checks. *)

Definition Γ0 : Mul.pname -> Mul.stmt := fun _ => Mul.Skip.

(** `x *= 3` on x=5 gives 15. *)
Example mul_forward : Mul.exec Γ0 (Mul.Prim (MulPrim.Mul 3)) 5 15.
Proof. apply Mul.E_Prim. simpl. split; [ discriminate | reflexivity ]. Qed.

(** Its inverse `x /= 3` recovers 5 from 15 — reversibility, concretely.  Note
    [Div 3] relates 15 to 5 precisely because 3 divides 15; on a non-multiple it
    relates to nothing (the partiality of `/=`). *)
Example div_backward :
  Mul.exec Γ0 (Mul.invert (Mul.Prim (MulPrim.Mul 3))) 15 5.
Proof. apply Mul.exec_rev. apply mul_forward. Qed.

(** [Div 3] directly: 15 /= 3 = 5 (since 15 = 3*5). *)
Example div_forward : Mul.exec Γ0 (Mul.Prim (MulPrim.Div 3)) 15 5.
Proof. apply Mul.E_Prim. simpl. split; [ discriminate | reflexivity ]. Qed.
