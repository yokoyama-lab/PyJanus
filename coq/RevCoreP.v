(** * RevCoreP.v — parameterized procedures in the generic framework

    [RevCore.v] handles parameterless procedures.  Here the *generic* framework
    is extended with parameter passing, abstractly: the interface gains an
    opaque type [ren] of renamings acting on primitives and guards
    ([rprim]/[rguard]), subject to the single law that renaming commutes with
    the primitive inverter,

        pinv (rprim r p) = rprim r (pinv p).

    A call [Call p r] runs the body of [p] renamed by [r] (the formals->actuals
    binding).  Reversibility goes through exactly as for [RevProc.v]'s concrete
    version, via [rename_invert].  This shows parameter passing is part of the
    *generic* reversibility story, not a per-language afterthought. *)

Module Type REV_PRIM_P.
  Parameter state : Type.
  Parameter prim  : Type.
  Parameter guard : Type.
  Parameter gtest : guard -> state -> bool.
  Parameter pstep : prim -> state -> state -> Prop.
  Parameter pinv  : prim -> prim.
  Axiom pinv_invol : forall p, pinv (pinv p) = p.
  Axiom pstep_det  : forall p a b b', pstep p a b -> pstep p a b' -> b = b'.
  Axiom pstep_rev  : forall p a b, pstep p a b -> pstep (pinv p) b a.
  (** Renamings (parameter bindings). *)
  Parameter ren    : Type.
  Parameter rcomp  : ren -> ren -> ren.
  Parameter rprim  : ren -> prim -> prim.
  Parameter rguard : ren -> guard -> guard.
  Axiom rprim_pinv : forall r p, pinv (rprim r p) = rprim r (pinv p).
End REV_PRIM_P.

Module RevLangP (P : REV_PRIM_P).
Import P.

Definition pname := nat.

Inductive stmt :=
| Skip
| Prim   (p : prim)
| Seq    (s1 s2 : stmt)
| If     (g1 : guard) (s1 s2 : stmt) (g2 : guard)
| Loop   (g1 : guard) (s1 s2 : stmt) (g2 : guard)
| Call   (p : pname) (r : ren)
| Uncall (p : pname) (r : ren).

(** Apply a renaming throughout a statement (composing into inner calls). *)
Fixpoint rename (r : ren) (s : stmt) : stmt :=
  match s with
  | Skip => Skip
  | Prim p => Prim (rprim r p)
  | Seq s1 s2 => Seq (rename r s1) (rename r s2)
  | If g1 s1 s2 g2 => If (rguard r g1) (rename r s1) (rename r s2) (rguard r g2)
  | Loop g1 s1 s2 g2 => Loop (rguard r g1) (rename r s1) (rename r s2) (rguard r g2)
  | Call p r' => Call p (rcomp r r')
  | Uncall p r' => Uncall p (rcomp r r')
  end.

Fixpoint invert (s : stmt) : stmt :=
  match s with
  | Skip => Skip
  | Prim p => Prim (pinv p)
  | Seq s1 s2 => Seq (invert s2) (invert s1)
  | If g1 s1 s2 g2 => If g2 (invert s1) (invert s2) g1
  | Loop g1 s1 s2 g2 => Loop g2 (invert s1) (invert s2) g1
  | Call p r => Uncall p r
  | Uncall p r => Call p r
  end.

Lemma invert_invol : forall s, invert (invert s) = s.
Proof.
  induction s; simpl; try reflexivity.
  - rewrite pinv_invol; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
Qed.

(** The one new ingredient: renaming commutes with inversion. *)
Lemma rename_invert : forall r s, invert (rename r s) = rename r (invert s).
Proof.
  intros r s; induction s; simpl; try reflexivity.
  - rewrite rprim_pinv; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
Qed.

Section Sem.
Variable Γ : pname -> stmt.   (* procedure bodies (over their formals) *)

Inductive exec : stmt -> state -> state -> Prop :=
| E_Skip : forall a, exec Skip a a
| E_Prim : forall p a b, pstep p a b -> exec (Prim p) a b
| E_Seq  : forall s1 s2 a m b, exec s1 a m -> exec s2 m b -> exec (Seq s1 s2) a b
| E_IfT  : forall g1 s1 s2 g2 a b,
    gtest g1 a = true  -> exec s1 a b -> gtest g2 b = true  -> exec (If g1 s1 s2 g2) a b
| E_IfF  : forall g1 s1 s2 g2 a b,
    gtest g1 a = false -> exec s2 a b -> gtest g2 b = false -> exec (If g1 s1 s2 g2) a b
| E_Loop : forall g1 s1 s2 g2 a b,
    gtest g1 a = true -> lp g1 s1 s2 g2 a b -> exec (Loop g1 s1 s2 g2) a b
| E_Call : forall p r a b,
    exec (rename r (Γ p)) a b -> exec (Call p r) a b
| E_Uncall : forall p r a b,
    exec (rename r (invert (Γ p))) a b -> exec (Uncall p r) a b

with lp : guard -> stmt -> stmt -> guard -> state -> state -> Prop :=
| L_one  : forall g1 s1 s2 g2 a b,
    exec s1 a b -> gtest g2 b = true -> lp g1 s1 s2 g2 a b
| L_more : forall g1 s1 s2 g2 a a1 a2 b,
    exec s1 a a1 -> gtest g2 a1 = false ->
    exec s2 a1 a2 -> gtest g1 a2 = false ->
    lp g1 s1 s2 g2 a2 b -> lp g1 s1 s2 g2 a b.

Scheme exec_mut := Induction for exec Sort Prop
  with lp_mut   := Induction for lp   Sort Prop.

Lemma lp_exit_true :
  forall g1 s1 s2 g2 a b, lp g1 s1 s2 g2 a b -> gtest g2 b = true.
Proof. intros until b; intro H; induction H; assumption. Qed.

Inductive opn (g1 : guard) (s1 s2 : stmt) (g2 : guard) : state -> state -> Prop :=
| O_nil  : forall a, opn g1 s1 s2 g2 a a
| O_cons : forall a a1 a2 b,
    exec s1 a a1 -> gtest g2 a1 = false ->
    exec s2 a1 a2 -> gtest g1 a2 = false ->
    opn g1 s1 s2 g2 a2 b -> opn g1 s1 s2 g2 a b.

Lemma opn_snoc :
  forall g1 s1 s2 g2 a m m1 m2,
    opn g1 s1 s2 g2 a m ->
    exec s1 m m1 -> gtest g2 m1 = false ->
    exec s2 m1 m2 -> gtest g1 m2 = false ->
    opn g1 s1 s2 g2 a m2.
Proof.
  intros g1 s1 s2 g2 a m m1 m2 H. revert m1 m2.
  induction H; intros m1 m2 Hr He Hs Hg.
  - eapply O_cons; eauto. apply O_nil.
  - eapply O_cons; eauto.
Qed.

Lemma opn_to_lp :
  forall g1 s1 s2 g2 a m b,
    opn g1 s1 s2 g2 a m -> exec s1 m b -> gtest g2 b = true ->
    lp g1 s1 s2 g2 a b.
Proof.
  intros g1 s1 s2 g2 a m b H. induction H; intros Hs1 Hex.
  - apply L_one; assumption.
  - eapply L_more; eauto.
Qed.

Theorem exec_rev : forall s a b, exec s a b -> exec (invert s) b a.
Proof.
  intros s a b H.
  induction H using exec_mut
    with (P0 := fun g1 s1 s2 g2 a b (_ : lp g1 s1 s2 g2 a b) =>
      exists q, opn g2 (invert s1) (invert s2) g1 b q /\ exec (invert s1) q a).
  - apply E_Skip.
  - cbn [invert]. apply E_Prim. apply pstep_rev. assumption.
  - cbn [invert]. eapply E_Seq; [ exact IHexec2 | exact IHexec1 ].
  - cbn [invert]. apply E_IfT; assumption.
  - cbn [invert]. apply E_IfF; assumption.
  - cbn [invert].
    destruct IHexec as [q [Hopn Hq]].
    apply E_Loop.
    + eapply lp_exit_true; eassumption.
    + eapply opn_to_lp; [ exact Hopn | exact Hq | eassumption ].
  - (* Call -> Uncall *)
    cbn [invert]. apply E_Uncall. rewrite <- rename_invert. exact IHexec.
  - (* Uncall -> Call *)
    cbn [invert]. apply E_Call.
    rewrite <- rename_invert, invert_invol in IHexec. exact IHexec.
  - exists b. split; [ apply O_nil | assumption ].
  - match goal with H : exists _, _ |- _ => destruct H as [q [Hopn Hq]] end.
    exists a1. split.
    + eapply opn_snoc; eauto.
    + assumption.
Qed.

Corollary exec_iff : forall s a b, exec s a b <-> exec (invert s) b a.
Proof.
  intros; split; intro H.
  - apply exec_rev; assumption.
  - apply exec_rev in H; rewrite invert_invol in H; assumption.
Qed.

Theorem exec_det : forall s a b, exec s a b -> forall b', exec s a b' -> b = b'.
Proof.
  intros s a b H.
  induction H using exec_mut
    with (P0 := fun g1 s1 s2 g2 a b (_ : lp g1 s1 s2 g2 a b) =>
      forall b', lp g1 s1 s2 g2 a b' -> b = b').
  - intros b' Hb'; inversion Hb'; subst; reflexivity.
  - intros b' Hb'; inversion Hb'; subst. eapply pstep_det; eassumption.
  - intros b' Hb'; inversion Hb'; subst.
    match goal with
    | He2 : exec s2 ?mid b' |- _ =>
        assert (Em : m = mid) by (apply IHexec1; assumption);
        apply IHexec2; rewrite Em; exact He2
    end.
  - intros b' Hb'; inversion Hb'; subst; [ apply IHexec; assumption | congruence ].
  - intros b' Hb'; inversion Hb'; subst; [ congruence | apply IHexec; assumption ].
  - intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - intros b' Hb'; inversion Hb'; subst.
    + apply IHexec; assumption.
    + match goal with He : gtest g2 ?aa = false |- _ =>
        match goal with Hx : exec s1 a aa |- _ => apply IHexec in Hx; subst end
      end; congruence.
  - intros b' Hb'; inversion Hb'; subst.
    + match goal with Hx : exec s1 a b' |- _ => apply IHexec1 in Hx; subst end;
      congruence.
    + match goal with
      | Hi3 : lp g1 s1 s2 g2 ?aa2 b' |- _ =>
        match goal with
        | Hi2 : exec s2 ?aa1 aa2 |- _ =>
          match goal with
          | Hi1 : exec s1 a aa1 |- _ =>
              apply IHexec1 in Hi1; subst;
              apply IHexec2 in Hi2; subst;
              apply IHexec3 in Hi3; exact Hi3
          end
        end
      end.
Qed.

Corollary exec_injective :
  forall s a a' b, exec s a b -> exec s a' b -> a = a'.
Proof.
  intros s a a' b H1 H2.
  apply exec_rev in H1. apply exec_rev in H2.
  eapply exec_det; eauto.
Qed.

End Sem.
End RevLangP.

(* ===================================================================== *)
(** ** A concrete instance: Janus atoms with variable renaming.

    [ren := var -> var]; renaming an assignment/swap renames its variables and
    expression.  This recovers parameterized reference procedures (cf.
    [RevProc.v]) as an *instance of the generic functor*. *)
From Stdlib Require Import ZArith Lia Bool FunctionalExtensionality.
Open Scope Z_scope.

Module JanusP <: REV_PRIM_P.
  Definition var := nat.
  Definition state := var -> Z.

  Definition update (s : state) (x : var) (v : Z) : state :=
    fun y => if Nat.eqb x y then v else s y.
  Lemma update_eq : forall s x v, update s x v x = v.
  Proof. intros; unfold update; rewrite Nat.eqb_refl; reflexivity. Qed.

  Inductive aop := AAdd | ASub | AXor.
  Definition adenote (o : aop) (a b : Z) : Z :=
    match o with AAdd => a + b | ASub => a - b | AXor => Z.lxor a b end.
  Definition ainv (o : aop) : aop :=
    match o with AAdd => ASub | ASub => AAdd | AXor => AXor end.

  Inductive expr := Cst (n : Z) | EVar (x : var) | Bin (o : aop) (e1 e2 : expr).
  Fixpoint eval (s : state) (e : expr) : Z :=
    match e with Cst n => n | EVar x => s x | Bin o e1 e2 => adenote o (eval s e1) (eval s e2) end.
  Fixpoint occurs (x : var) (e : expr) : bool :=
    match e with Cst _ => false | EVar y => Nat.eqb x y
               | Bin _ e1 e2 => orb (occurs x e1) (occurs x e2) end.
  Fixpoint rexpr (σ : var -> var) (e : expr) : expr :=
    match e with Cst n => Cst n | EVar x => EVar (σ x)
               | Bin o e1 e2 => Bin o (rexpr σ e1) (rexpr σ e2) end.

  Inductive prim_ := PAssign (x : var) (o : aop) (e : expr) | PSwap (x y : var).
  Definition prim := prim_.
  Definition sw (s : state) (x y : var) : state :=
    update (update s x (s y)) y (s x).
  Definition pstep (p : prim) (a b : state) : Prop :=
    match p with
    | PAssign x o e => occurs x e = false /\ b = update a x (adenote o (a x) (eval a e))
    | PSwap x y => b = sw a x y
    end.
  Definition pinv (p : prim) : prim :=
    match p with PAssign x o e => PAssign x (ainv o) e | PSwap x y => PSwap x y end.

  Definition guard := expr.
  Definition gtest (e : expr) (s : state) : bool := negb (Z.eqb (eval s e) 0).

  Definition ren := var -> var.
  Definition rcomp (r r' : ren) : ren := fun v => r (r' v).
  Definition rprim (σ : ren) (p : prim) : prim :=
    match p with
    | PAssign x o e => PAssign (σ x) o (rexpr σ e)
    | PSwap x y => PSwap (σ x) (σ y)
    end.
  Definition rguard (σ : ren) (g : guard) : guard := rexpr σ g.

  (* the three reversibility laws and the renaming law *)
  Lemma pinv_invol : forall p, pinv (pinv p) = p.
  Proof. destruct p; simpl; try reflexivity. destruct o; reflexivity. Qed.

  Lemma pstep_det : forall p a b b', pstep p a b -> pstep p a b' -> b = b'.
  Proof.
    destruct p; simpl; intros a b b' H1 H2.
    - destruct H1 as [_ ->]; destruct H2 as [_ ->]; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma update_neq : forall s x v y, x <> y -> update s x v y = s y.
  Proof.
    intros s x v y H; unfold update.
    destruct (Nat.eqb x y) eqn:E; [ apply Nat.eqb_eq in E; contradiction | reflexivity ].
  Qed.
  Lemma eval_update_notin :
    forall x v s e, occurs x e = false -> eval (update s x v) e = eval s e.
  Proof.
    intros x v s e; induction e; intro H; simpl in H |- *.
    - reflexivity.
    - unfold update; rewrite H; reflexivity.
    - apply Bool.orb_false_iff in H; destruct H as [H1 H2].
      rewrite IHe1 by assumption; rewrite IHe2 by assumption; reflexivity.
  Qed.
  Lemma ainv_correct : forall o a b, adenote (ainv o) (adenote o a b) b = a.
  Proof.
    destruct o; intros a b; simpl; try lia.
    rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r; reflexivity.
  Qed.
  Lemma update_shadow : forall s x a b, update (update s x a) x b = update s x b.
  Proof.
    intros; apply functional_extensionality; intro z; unfold update.
    destruct (Nat.eqb x z); reflexivity.
  Qed.
  Lemma update_same : forall s x, update s x (s x) = s.
  Proof.
    intros; apply functional_extensionality; intro z; unfold update.
    destruct (Nat.eqb x z) eqn:E; [ apply Nat.eqb_eq in E; subst; reflexivity | reflexivity ].
  Qed.
  Lemma sw_invol : forall s x y, sw (sw s x y) x y = s.
  Proof.
    intros s x y; apply functional_extensionality; intro z; unfold sw, update.
    destruct (Nat.eqb y z) eqn:Hyz.
    - apply Nat.eqb_eq in Hyz; subst z.
      destruct (Nat.eqb y x) eqn:Hyx.
      + apply Nat.eqb_eq in Hyx; subst x; reflexivity.
      + rewrite Nat.eqb_refl; reflexivity.
    - destruct (Nat.eqb x z) eqn:Hxz.
      + rewrite Nat.eqb_refl. apply Nat.eqb_eq in Hxz; subst x; reflexivity.
      + reflexivity.
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

  Lemma rprim_pinv : forall r p, pinv (rprim r p) = rprim r (pinv p).
  Proof. destruct p; simpl; reflexivity. Qed.
End JanusP.

Module JP := RevLangP JanusP.

(** Parameterized reference procedures, reversible — straight from the functor. *)
Theorem janusP_reversible :
  forall (Γ : JP.pname -> JP.stmt) (s : JP.stmt) (a a' b : JanusP.state),
    JP.exec Γ s a b -> JP.exec Γ s a' b -> a = a'.
Proof. exact JP.exec_injective. Qed.
