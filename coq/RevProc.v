(** * RevProc.v — Janus with parameterized (reference) procedures

    The remaining gap between the core and *real* Janus is procedures that take
    parameters.  Janus passes parameters by reference: a call [call p(a1..an)]
    runs the body of [p] with the formal parameters standing for the actual
    variables [a1..an].  We model this faithfully as a *variable renaming* of the
    body (formals |-> actuals).

    The reversibility argument carries over with one new ingredient: renaming
    commutes with the inverter ([rename_invert]).  Then [call]/[uncall] are
    reversed exactly as the parameterless versions were.

    Lesson made precise ([alias_blocks]): parameter *aliasing* does not break the
    reversibility theorem — if two actuals coincide, the renamed body's update
    [x op= e] can violate its side condition [~ occurs x e], so that call simply
    has no execution.  Reversibility holds for the executions that do exist. *)

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
Import ListNotations.
Open Scope Z_scope.

(* ************************************************************************* *)
(** ** Stores, expressions, reversible operators (as in [Janus.v]). *)
Definition var := nat.
Definition store := var -> Z.

Definition update (s : store) (x : var) (v : Z) : store :=
  fun y => if Nat.eqb x y then v else s y.
Lemma update_eq : forall s x v, update s x v x = v.
Proof. intros; unfold update; rewrite Nat.eqb_refl; reflexivity. Qed.
Lemma update_neq : forall s x v y, x <> y -> update s x v y = s y.
Proof.
  intros s x v y H; unfold update.
  destruct (Nat.eqb x y) eqn:E; [apply Nat.eqb_eq in E; contradiction | reflexivity].
Qed.
Lemma update_shadow : forall s x a b, update (update s x a) x b = update s x b.
Proof.
  intros; apply functional_extensionality; intro z; unfold update.
  destruct (Nat.eqb x z); reflexivity.
Qed.
Lemma update_same : forall s x, update s x (s x) = s.
Proof.
  intros; apply functional_extensionality; intro z; unfold update.
  destruct (Nat.eqb x z) eqn:E; [apply Nat.eqb_eq in E; subst; reflexivity | reflexivity].
Qed.

Definition sw (s : store) (x y : var) : store :=
  update (update s x (s y)) y (s x).
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

Inductive binop := OAdd | OSub | OMul | OEq | OLt.
Definition denote (o : binop) (a b : Z) : Z :=
  match o with
  | OAdd => a + b | OSub => a - b | OMul => a * b
  | OEq => if Z.eqb a b then 1 else 0
  | OLt => if Z.ltb a b then 1 else 0
  end.
Inductive expr := Cst (n : Z) | Var (x : var) | Bin (o : binop) (e1 e2 : expr).
Fixpoint eval (s : store) (e : expr) : Z :=
  match e with
  | Cst n => n | Var x => s x | Bin o e1 e2 => denote o (eval s e1) (eval s e2)
  end.
Fixpoint occurs (x : var) (e : expr) : bool :=
  match e with
  | Cst _ => false | Var y => Nat.eqb x y
  | Bin _ e1 e2 => orb (occurs x e1) (occurs x e2)
  end.
Lemma eval_update_notin :
  forall x v s e, occurs x e = false -> eval (update s x v) e = eval s e.
Proof.
  intros x v s e; induction e; intro H; simpl in H |- *.
  - reflexivity.
  - unfold update; rewrite H; reflexivity.
  - apply orb_false_iff in H; destruct H as [H1 H2].
    rewrite IHe1 by assumption; rewrite IHe2 by assumption; reflexivity.
Qed.

Inductive aop := AAdd | ASub | AXor.
Definition adenote (o : aop) (a b : Z) : Z :=
  match o with AAdd => a + b | ASub => a - b | AXor => Z.lxor a b end.
Definition ainv (o : aop) : aop :=
  match o with AAdd => ASub | ASub => AAdd | AXor => AXor end.
Lemma ainv_invol : forall o, ainv (ainv o) = o.
Proof. destruct o; reflexivity. Qed.
Lemma ainv_correct : forall o a b, adenote (ainv o) (adenote o a b) b = a.
Proof.
  destruct o; intros a b; simpl; try lia.
  rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r; reflexivity.
Qed.

(* ************************************************************************* *)
(** ** Syntax: now with parameterized [Call]/[Uncall]. *)
Definition pname := nat.

Inductive stmt :=
| Skip
| Assign (x : var) (o : aop) (e : expr)
| Swap   (x y : var)
| Seq    (s1 s2 : stmt)
| If     (e1 : expr) (s1 s2 : stmt) (e2 : expr)
| Loop   (e1 : expr) (s1 s2 : stmt) (e2 : expr)
| Call   (p : pname) (args : list var)
| Uncall (p : pname) (args : list var).

(** Apply a variable renaming throughout an expression / statement. *)
Fixpoint rexpr (σ : var -> var) (e : expr) : expr :=
  match e with
  | Cst n => Cst n | Var x => Var (σ x)
  | Bin o e1 e2 => Bin o (rexpr σ e1) (rexpr σ e2)
  end.

Fixpoint rename (σ : var -> var) (s : stmt) : stmt :=
  match s with
  | Skip => Skip
  | Assign x o e => Assign (σ x) o (rexpr σ e)
  | Swap x y => Swap (σ x) (σ y)
  | Seq s1 s2 => Seq (rename σ s1) (rename σ s2)
  | If e1 s1 s2 e2 => If (rexpr σ e1) (rename σ s1) (rename σ s2) (rexpr σ e2)
  | Loop e1 s1 s2 e2 => Loop (rexpr σ e1) (rename σ s1) (rename σ s2) (rexpr σ e2)
  | Call p args => Call p (map σ args)
  | Uncall p args => Uncall p (map σ args)
  end.

Fixpoint invert (s : stmt) : stmt :=
  match s with
  | Skip => Skip
  | Assign x o e => Assign x (ainv o) e
  | Swap x y => Swap x y
  | Seq s1 s2 => Seq (invert s2) (invert s1)
  | If e1 s1 s2 e2 => If e2 (invert s1) (invert s2) e1
  | Loop e1 s1 s2 e2 => Loop e2 (invert s1) (invert s2) e1
  | Call p args => Uncall p args
  | Uncall p args => Call p args
  end.

Lemma invert_invol : forall s, invert (invert s) = s.
Proof.
  induction s; simpl; try reflexivity.
  - rewrite ainv_invol; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
Qed.

(** The key new fact: renaming commutes with inversion. *)
Lemma rename_invert : forall σ s, invert (rename σ s) = rename σ (invert s).
Proof.
  intros σ s; induction s; simpl; try reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
Qed.

(* ************************************************************************* *)
(** ** Big-step semantics with a parameter-passing procedure environment. *)
Section Sem.

(** Each procedure has formal parameters and a body. *)
Variable Γ : pname -> (list var * stmt).

(** Bind formals to actuals: [pbind p args] maps the i-th formal to the i-th
    actual (identity elsewhere). *)
Fixpoint argsubst (fs args : list var) (v : var) : var :=
  match fs, args with
  | f :: fs', a :: args' => if Nat.eqb v f then a else argsubst fs' args' v
  | _, _ => v
  end.
Definition pbind (p : pname) (args : list var) : var -> var :=
  argsubst (fst (Γ p)) args.
Definition pbody (p : pname) : stmt := snd (Γ p).

Inductive exec : stmt -> store -> store -> Prop :=
| E_Skip   : forall s, exec Skip s s
| E_Assign : forall x o e s,
    occurs x e = false ->
    exec (Assign x o e) s (update s x (adenote o (s x) (eval s e)))
| E_Swap   : forall x y s, exec (Swap x y) s (sw s x y)
| E_Seq    : forall s1 s2 a m b, exec s1 a m -> exec s2 m b -> exec (Seq s1 s2) a b
| E_IfT    : forall e1 s1 s2 e2 a b,
    eval a e1 <> 0 -> exec s1 a b -> eval b e2 <> 0 -> exec (If e1 s1 s2 e2) a b
| E_IfF    : forall e1 s1 s2 e2 a b,
    eval a e1 =  0 -> exec s2 a b -> eval b e2 =  0 -> exec (If e1 s1 s2 e2) a b
| E_Loop   : forall e1 s1 s2 e2 a b,
    eval a e1 <> 0 -> lp e1 s1 s2 e2 a b -> exec (Loop e1 s1 s2 e2) a b
| E_Call   : forall p args a b,
    exec (rename (pbind p args) (pbody p)) a b -> exec (Call p args) a b
| E_Uncall : forall p args a b,
    exec (rename (pbind p args) (invert (pbody p))) a b -> exec (Uncall p args) a b

with lp : expr -> stmt -> stmt -> expr -> store -> store -> Prop :=
| L_one  : forall e1 s1 s2 e2 a b,
    exec s1 a b -> eval b e2 <> 0 -> lp e1 s1 s2 e2 a b
| L_more : forall e1 s1 s2 e2 a a1 a2 b,
    exec s1 a a1 -> eval a1 e2 = 0 ->
    exec s2 a1 a2 -> eval a2 e1 = 0 ->
    lp e1 s1 s2 e2 a2 b -> lp e1 s1 s2 e2 a b.

Scheme exec_mut := Induction for exec Sort Prop
  with lp_mut   := Induction for lp   Sort Prop.

Lemma lp_exit_true : forall e1 s1 s2 e2 a b, lp e1 s1 s2 e2 a b -> eval b e2 <> 0.
Proof. intros until b; intro H; induction H; assumption. Qed.

Inductive opn (e1 : expr) (s1 s2 : stmt) (e2 : expr) : store -> store -> Prop :=
| O_nil  : forall a, opn e1 s1 s2 e2 a a
| O_cons : forall a a1 a2 b,
    exec s1 a a1 -> eval a1 e2 = 0 ->
    exec s2 a1 a2 -> eval a2 e1 = 0 ->
    opn e1 s1 s2 e2 a2 b -> opn e1 s1 s2 e2 a b.

Lemma opn_snoc :
  forall e1 s1 s2 e2 a m m1 m2,
    opn e1 s1 s2 e2 a m ->
    exec s1 m m1 -> eval m1 e2 = 0 ->
    exec s2 m1 m2 -> eval m2 e1 = 0 ->
    opn e1 s1 s2 e2 a m2.
Proof.
  intros e1 s1 s2 e2 a m m1 m2 H. revert m1 m2.
  induction H; intros m1 m2 Hs1 He2 Hs2 He1.
  - eapply O_cons; eauto. apply O_nil.
  - eapply O_cons; eauto.
Qed.

Lemma opn_to_lp :
  forall e1 s1 s2 e2 a m b,
    opn e1 s1 s2 e2 a m -> exec s1 m b -> eval b e2 <> 0 ->
    lp e1 s1 s2 e2 a b.
Proof.
  intros e1 s1 s2 e2 a m b H. induction H; intros Hs1 Hex.
  - apply L_one; assumption.
  - eapply L_more; eauto.
Qed.

Lemma assign_inv_ok :
  forall s x o e, occurs x e = false ->
    exec (Assign x (ainv o) e) (update s x (adenote o (s x) (eval s e))) s.
Proof.
  intros s x o e Hocc.
  pose proof (E_Assign x (ainv o) e (update s x (adenote o (s x) (eval s e))) Hocc) as Hg.
  rewrite update_eq in Hg.
  rewrite (eval_update_notin x (adenote o (s x) (eval s e)) s e Hocc) in Hg.
  rewrite ainv_correct in Hg.
  rewrite update_shadow in Hg.
  rewrite update_same in Hg.
  exact Hg.
Qed.

(** ** Reversibility, including the parameterized call/uncall. *)
Theorem exec_rev : forall s a b, exec s a b -> exec (invert s) b a.
Proof.
  intros s a b H.
  induction H using exec_mut
    with (P0 := fun e1 s1 s2 e2 a b (_ : lp e1 s1 s2 e2 a b) =>
      exists q, opn e2 (invert s1) (invert s2) e1 b q /\ exec (invert s1) q a).
  - apply E_Skip.
  - cbn [invert]. apply assign_inv_ok; assumption.
  - cbn [invert]. rewrite <- (sw_invol s x y) at 2. apply E_Swap.
  - cbn [invert]. eapply E_Seq; [ exact IHexec2 | exact IHexec1 ].
  - cbn [invert]. apply E_IfT; assumption.
  - cbn [invert]. apply E_IfF; assumption.
  - cbn [invert].
    destruct IHexec as [q [Hopn Hq]].
    apply E_Loop.
    + eapply lp_exit_true; eassumption.
    + eapply opn_to_lp; [ exact Hopn | exact Hq | eassumption ].
  - (* Call -> Uncall: use rename/invert commutation *)
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
    with (P0 := fun e1 s1 s2 e2 a b (_ : lp e1 s1 s2 e2 a b) =>
      forall b', lp e1 s1 s2 e2 a b' -> b = b').
  - intros b' Hb'; inversion Hb'; subst; reflexivity.
  - intros b' Hb'; inversion Hb'; subst; reflexivity.
  - intros b' Hb'; inversion Hb'; subst; reflexivity.
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
    + match goal with He : eval ?aa e2 = 0 |- _ =>
        match goal with Hx : exec s1 a aa |- _ => apply IHexec in Hx; subst end
      end; congruence.
  - intros b' Hb'; inversion Hb'; subst.
    + match goal with Hx : exec s1 a b' |- _ => apply IHexec1 in Hx; subst end;
      congruence.
    + match goal with
      | Hi3 : lp e1 s1 s2 e2 ?aa2 b' |- _ =>
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

(** *** Aliasing is captured by the side condition, not by an extra hypothesis.

    If a call aliases two actuals so that a renamed update [x op= e] has [x]
    occurring in [e], that update — hence that call — has no execution.  (Here a
    one-statement body [Assign f o e] whose two distinct formals [f] and a
    variable of [e] are bound to the same actual.) *)
Lemma alias_blocks :
  forall x o e s t, occurs x e = true -> ~ exec (Assign x o e) s t.
Proof.
  intros x o e s t Hocc Hexec; inversion Hexec; subst; congruence.
Qed.

End Sem.
