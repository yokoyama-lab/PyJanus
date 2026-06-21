(** * Janus.v — Mechanized reversibility of core Janus (Rocq/Coq)

    This development formalizes the *reversibility* of the core fragment of
    Janus, the reversible imperative language (Lutz & Derby 1986; Yokoyama &
    Glück 2007).  The semantics here is the big-step semantics whose
    reversibility is the property that the small-step paper

        "A Small-Step Semantics for Janus", RC 2024 (hal-04610285)

    takes as its reference point (its small-step semantics is proved equivalent
    to this big-step one).

    Main results (Section [Sem], parametric in a procedure environment [Γ]):

      - [exec_rev]       : exec s a b  ->  exec (invert s) b a
      - [exec_iff]       : exec s a b  <-> exec (invert s) b a
      - [exec_det]       : forward determinism of [exec]
      - [exec_injective] : exec s a b -> exec s a' b -> a = a'   (backward
                           determinism = local invertibility = reversibility)

    The conceptual heart is [invert] (the program inverter) together with the
    loop case, handled through the open iteration relation [opn] and the tail
    append lemma [opn_snoc], which absorbs the structural "off-by-one" between a
    forward loop  s1 (s2 s1)^n  and its reverse  (invs1 invs2)^n invs1. *)

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
Open Scope Z_scope.

(* ************************************************************************* *)
(** ** Stores *)

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

(** Value swap of two cells (the meaning of [x <=> y]). *)
Definition sw (s : store) (x y : var) : store :=
  update (update s x (s y)) y (s x).

Lemma sw_invol : forall s x y, sw (sw s x y) x y = s.
Proof.
  intros s x y; apply functional_extensionality; intro z.
  unfold sw, update.
  destruct (Nat.eqb y z) eqn:Hyz.
  - apply Nat.eqb_eq in Hyz; subst z.
    destruct (Nat.eqb y x) eqn:Hyx.
    + apply Nat.eqb_eq in Hyx; subst x; reflexivity.
    + rewrite Nat.eqb_refl; reflexivity.
  - destruct (Nat.eqb x z) eqn:Hxz.
    + rewrite Nat.eqb_refl. apply Nat.eqb_eq in Hxz; subst x; reflexivity.
    + reflexivity.
Qed.

(* ************************************************************************* *)
(** ** Expressions *)

Inductive binop := OAdd | OSub | OMul | OEq | OLt | ODiv | OMod.

(** [denote] is a *total* read-only function on values.  Adding [ODiv]/[OMod]
    keeps it total ([Z.div a 0 = 0], [Z.modulo a 0 = a]) and does NOT affect
    reversibility: [binop] only appears inside [eval] (expressions are pure and
    are never inverted by [invert]).  The reversibility of an update [x op= e]
    rests solely on the [aop] inverse and the [occurs x e = false] side
    condition (see [eval_update_notin]), which hold for any expression [e]
    regardless of which [binop]s it contains.  Cf. [RevArr.v] which already
    uses the same [ODiv]/[OMod] denotation. *)
Definition denote (o : binop) (a b : Z) : Z :=
  match o with
  | OAdd => a + b
  | OSub => a - b
  | OMul => a * b
  | OEq  => if Z.eqb a b then 1 else 0
  | OLt  => if Z.ltb a b then 1 else 0
  | ODiv => Z.div a b
  | OMod => Z.modulo a b
  end.

Inductive expr :=
| Cst (n : Z)
| Var (x : var)
| Bin (o : binop) (e1 e2 : expr).

Fixpoint eval (s : store) (e : expr) : Z :=
  match e with
  | Cst n => n
  | Var x => s x
  | Bin o e1 e2 => denote o (eval s e1) (eval s e2)
  end.

Fixpoint occurs (x : var) (e : expr) : bool :=
  match e with
  | Cst _ => false
  | Var y => Nat.eqb x y
  | Bin _ e1 e2 => orb (occurs x e1) (occurs x e2)
  end.

(** If [x] does not occur in [e], updating [x] cannot change [e]'s value.
    This is exactly the syntactic side condition that makes the reversible
    update [x op= e] reversible. *)
Lemma eval_update_notin :
  forall x v s e, occurs x e = false -> eval (update s x v) e = eval s e.
Proof.
  intros x v s e; induction e; intro H; simpl in H |- *.
  - reflexivity.
  - unfold update; rewrite H; reflexivity.
  - apply orb_false_iff in H; destruct H as [H1 H2].
    rewrite IHe1 by assumption; rewrite IHe2 by assumption; reflexivity.
Qed.

(** *** Tests for the [ODiv]/[OMod] additions (computational sanity). *)
Example denote_div_ex  : denote ODiv 17 5 = 3.  Proof. reflexivity. Qed.
Example denote_mod_ex  : denote OMod 17 5 = 2.  Proof. reflexivity. Qed.
Example denote_div0_ex : denote ODiv 17 0 = 0.  Proof. reflexivity. Qed.  (* total *)
Example denote_mod0_ex : denote OMod 17 0 = 17. Proof. reflexivity. Qed.  (* total *)
(* divmod identity used by the consume pattern: for d>0, d*(n/d) + n mod d = n. *)
Example divmod_recovers : forall n d, d > 0 -> d * (n / d) + n mod d = n.
Proof. intros n d Hd. symmetry. apply Z.div_mod. lia. Qed.
(* a [binop] with [ODiv] inside an expression still satisfies the side condition
   that makes [x op= e] reversible (occurs-check is structural, op-agnostic). *)
Example occurs_div_ex :
  occurs 2%nat (Bin OAdd (Bin ODiv (Var 0%nat) (Var 1%nat)) (Var 0%nat)) = false.
Proof. reflexivity. Qed.

(* ************************************************************************* *)
(** ** Reversible update operators *)

Inductive aop := AAdd | ASub | AXor.

Definition adenote (o : aop) (a b : Z) : Z :=
  match o with
  | AAdd => a + b
  | ASub => a - b
  | AXor => Z.lxor a b
  end.

Definition ainv (o : aop) : aop :=
  match o with AAdd => ASub | ASub => AAdd | AXor => AXor end.

Lemma ainv_invol : forall o, ainv (ainv o) = o.
Proof. destruct o; reflexivity. Qed.

(** The defining property: applying the inverse operator with the same right
    operand cancels the original update. *)
Lemma ainv_correct : forall o a b, adenote (ainv o) (adenote o a b) b = a.
Proof.
  destruct o; intros a b; simpl.
  - lia.
  - lia.
  - rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r; reflexivity.
Qed.

(* ************************************************************************* *)
(** ** Syntax of statements *)

Definition pname := nat.

Inductive stmt :=
| Skip
| Assign (x : var) (o : aop) (e : expr)          (* x op= e , needs ~ occurs x e *)
| Swap   (x y : var)                              (* x <=> y *)
| Seq    (s1 s2 : stmt)                           (* s1 ; s2 *)
| If     (e1 : expr) (s1 s2 : stmt) (e2 : expr)   (* if e1 then s1 else s2 fi e2 *)
| Loop   (e1 : expr) (s1 s2 : stmt) (e2 : expr)   (* from e1 do s1 loop s2 until e2 *)
| Call   (p : pname)
| Uncall (p : pname).

(** The program inverter.  [invert] is the syntactic heart of reversibility:
    each statement form names its own inverse. *)
Fixpoint invert (s : stmt) : stmt :=
  match s with
  | Skip            => Skip
  | Assign x o e    => Assign x (ainv o) e
  | Swap x y        => Swap x y
  | Seq s1 s2       => Seq (invert s2) (invert s1)
  | If e1 s1 s2 e2  => If e2 (invert s1) (invert s2) e1
  | Loop e1 s1 s2 e2 => Loop e2 (invert s1) (invert s2) e1
  | Call p          => Uncall p
  | Uncall p        => Call p
  end.

Lemma invert_invol : forall s, invert (invert s) = s.
Proof.
  induction s; simpl; try reflexivity.
  - rewrite ainv_invol; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
Qed.

(* ************************************************************************* *)
(** ** Big-step semantics, parametric in a procedure environment *)

Section Sem.

Variable Γ : pname -> stmt.   (* body of each (parameterless, global-store) procedure *)

(** [exec s a b]: running [s] in store [a] terminates in store [b].
    [lp e1 s1 s2 e2 a b]: the loop body  s1 (s2 s1)^n  starting in [a] and
    exiting in [b] (i.e. with the exit test [e2] true at [b]); the entry
    assertion [e1] is checked by [E_Loop], not by [lp]. *)
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
| E_Call   : forall p a b, exec (Γ p) a b -> exec (Call p) a b
| E_Uncall : forall p a b, exec (invert (Γ p)) a b -> exec (Uncall p) a b

with lp : expr -> stmt -> stmt -> expr -> store -> store -> Prop :=
| L_one  : forall e1 s1 s2 e2 a b,
    exec s1 a b -> eval b e2 <> 0 -> lp e1 s1 s2 e2 a b
| L_more : forall e1 s1 s2 e2 a a1 a2 b,
    exec s1 a a1 -> eval a1 e2 = 0 ->
    exec s2 a1 a2 -> eval a2 e1 = 0 ->
    lp e1 s1 s2 e2 a2 b ->
    lp e1 s1 s2 e2 a b.

Scheme exec_mut := Induction for exec Sort Prop
  with lp_mut   := Induction for lp   Sort Prop.

(** The loop always exits with [e2] true. *)
Lemma lp_exit_true : forall e1 s1 s2 e2 a b, lp e1 s1 s2 e2 a b -> eval b e2 <> 0.
Proof. intros until b; intro H; induction H; assumption. Qed.

(** Open iteration: zero or more *continuing* rounds [s1 ; s2]
    (no exit baked in).  Built front-first; [opn_snoc] appends at the tail. *)
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

(** Closing an open iteration with the final exit [s1] yields a loop body. *)
Lemma opn_to_lp :
  forall e1 s1 s2 e2 a m b,
    opn e1 s1 s2 e2 a m -> exec s1 m b -> eval b e2 <> 0 ->
    lp e1 s1 s2 e2 a b.
Proof.
  intros e1 s1 s2 e2 a m b H. induction H; intros Hs1 Hex.
  - apply L_one; assumption.
  - eapply L_more; eauto.
Qed.

(** *** Assignment is reversible. *)
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

(* --------------------------------------------------------------------- *)
(** ** Main theorem: reversibility *)

Theorem exec_rev : forall s a b, exec s a b -> exec (invert s) b a.
Proof.
  intros s a b H.
  induction H using exec_mut
    with (P0 := fun e1 s1 s2 e2 a b (_ : lp e1 s1 s2 e2 a b) =>
      exists q, opn e2 (invert s1) (invert s2) e1 b q /\ exec (invert s1) q a).
  - (* E_Skip *) apply E_Skip.
  - (* E_Assign *) cbn [invert]. apply assign_inv_ok; assumption.
  - (* E_Swap *) cbn [invert]. rewrite <- (sw_invol s x y) at 2. apply E_Swap.
  - (* E_Seq *) cbn [invert]. eapply E_Seq; [ exact IHexec2 | exact IHexec1 ].
  - (* E_IfT *) cbn [invert]. apply E_IfT; assumption.
  - (* E_IfF *) cbn [invert]. apply E_IfF; assumption.
  - (* E_Loop *)
    cbn [invert].
    destruct IHexec as [q [Hopn Hq]].
    apply E_Loop.
    + (* entry assertion of the inverse loop = forward exit test *)
      eapply lp_exit_true; eassumption.
    + (* lp for the inverse loop, from b back to a *)
      eapply opn_to_lp; [ exact Hopn | exact Hq | eassumption ].
  - (* E_Call *) cbn [invert]. apply E_Uncall; assumption.
  - (* E_Uncall *) cbn [invert]. apply E_Call. rewrite invert_invol in IHexec. assumption.
  - (* L_one : base of P0 *)
    exists b. split.
    + apply O_nil.
    + assumption.
  - (* L_more : inductive step of P0 *)
    match goal with H : exists _, _ |- _ => destruct H as [q [Hopn Hq]] end.
    exists a1. split.
    + (* append one inverse round (invs1 ; invs2) at the tail *)
      eapply opn_snoc; eauto.
    + assumption.
Qed.

(** Inverse characterization. *)
Corollary exec_iff : forall s a b, exec s a b <-> exec (invert s) b a.
Proof.
  intros; split; intro H.
  - apply exec_rev; assumption.
  - apply exec_rev in H; rewrite invert_invol in H; assumption.
Qed.

(* --------------------------------------------------------------------- *)
(** ** Forward determinism and, hence, backward determinism (reversibility) *)

Theorem exec_det : forall s a b, exec s a b -> forall b', exec s a b' -> b = b'.
Proof.
  intros s a b H.
  induction H using exec_mut
    with (P0 := fun e1 s1 s2 e2 a b (_ : lp e1 s1 s2 e2 a b) =>
      forall b', lp e1 s1 s2 e2 a b' -> b = b').
  - (* Skip *) intros b' Hb'; inversion Hb'; subst; reflexivity.
  - (* Assign *) intros b' Hb'; inversion Hb'; subst; reflexivity.
  - (* Swap *) intros b' Hb'; inversion Hb'; subst; reflexivity.
  - (* Seq *) intros b' Hb'; inversion Hb'; subst.
    (* match the inverted run's premise by shape (it concludes in [b']),
       which uniquely distinguishes it from the original premises. *)
    match goal with
    | He2 : exec s2 ?mid b' |- _ =>
        assert (Em : m = mid) by (apply IHexec1; assumption);
        apply IHexec2; rewrite Em; exact He2
    end.
  - (* IfT *) intros b' Hb'; inversion Hb'; subst.
    + apply IHexec; assumption.
    + congruence.
  - (* IfF *) intros b' Hb'; inversion Hb'; subst.
    + congruence.
    + apply IHexec; assumption.
  - (* Loop *) intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - (* Call *) intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - (* Uncall *) intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - (* L_one *) intros b' Hb'; inversion Hb'; subst.
    + apply IHexec; assumption.
    + (* inverted loop took another round: its first leg has [eval _ e2 = 0],
         contradicting the exit test [eval b e2 <> 0] of this single round. *)
      match goal with He : eval ?aa e2 = 0 |- _ =>
        match goal with Hx : exec s1 a aa |- _ => apply IHexec in Hx; subst end
      end; congruence.
  - (* L_more *) intros b' Hb'; inversion Hb'; subst.
    + (* inverted loop exited immediately: contradicts our continuing round. *)
      match goal with Hx : exec s1 a b' |- _ => apply IHexec1 in Hx; subst end;
      congruence.
    + (* inverted loop also continued: chain the three IHs, matching the
         inverted premises by their (b'-reaching) shape. *)
      match goal with
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

(** Backward determinism: a final store determines the initial store.
    This is the formal statement that a Janus statement denotes an *injective*
    (partial) function — i.e. it is reversible. *)
Corollary exec_injective :
  forall s a a' b, exec s a b -> exec s a' b -> a = a'.
Proof.
  intros s a a' b H1 H2.
  apply exec_rev in H1. apply exec_rev in H2.
  eapply exec_det; eauto.
Qed.

End Sem.
