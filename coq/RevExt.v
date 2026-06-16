(** * RevExt.v — extending the framework with arrays and local/delocal

    This is the stress test for [RevCore.v]: features usually thought of as
    *language extensions* — arrays and reversible local-variable blocks
    ([local x = e ... delocal x = e']) — are absorbed as a single new
    *instance*, with the generic core left **completely unchanged**.

    Two ideas:

    1. **Arrays are just more locations.**  We index the store by a location
       type [loc] that covers scalars ([Scal]), array cells ([Cell a i]), and
       local cells ([LVar n]).  Array-cell update/swap are then the very same
       reversible atoms as scalar update/swap — only the location differs.

    2. **[local]/[delocal] needs no new combinator.**  It is two reversible
       atoms — [PEnter] (initialize a dead cell) and [PExit] (assert-and-clear
       it) — composed with [Seq].  Because they are genuine inverses, the
       *generic* [invert] automatically turns
           local x = e ; S ; delocal x = e'
       into
           local x = e' ; invert S ; delocal x = e
       (see [invert_LocalBlock]), and the generic [exec_injective] gives
       reversibility of array/local programs for free ([ext_reversible]). *)

From Stdlib Require Import ZArith Lia Bool FunctionalExtensionality.
Require Import RevCore.
Open Scope Z_scope.

Module ExtPrim <: REV_PRIM.

  (** *** Reversible update operators (self-contained copy of the algebra). *)
  Inductive binop := OAdd | OSub | OMul | OEq | OLt.
  Definition denote (o : binop) (a b : Z) : Z :=
    match o with
    | OAdd => a + b | OSub => a - b | OMul => a * b
    | OEq => if Z.eqb a b then 1 else 0
    | OLt => if Z.ltb a b then 1 else 0
    end.

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

  (** *** Locations: scalars, array cells, and local cells — all in one store. *)
  Inductive loc := Scal (n : nat) | Cell (a : nat) (i : Z) | LVar (n : nat).

  Definition loc_eq_dec (x y : loc) : {x = y} + {x <> y}.
  Proof. decide equality; (apply Z.eq_dec || apply Nat.eq_dec). Defined.

  Definition loceqb (l m : loc) : bool := if loc_eq_dec l m then true else false.
  Lemma loceqb_refl : forall l, loceqb l l = true.
  Proof. intro l; unfold loceqb; destruct (loc_eq_dec l l); [reflexivity | contradiction]. Qed.
  Lemma loceqb_true : forall l m, loceqb l m = true -> l = m.
  Proof. intros l m; unfold loceqb; destruct (loc_eq_dec l m); [auto | discriminate]. Qed.

  Definition state := loc -> Z.
  Definition store := state.

  Definition update (s : store) (l : loc) (v : Z) : store :=
    fun m => if loceqb l m then v else s m.

  Lemma update_eq : forall s l v, update s l v l = v.
  Proof. intros; unfold update; rewrite loceqb_refl; reflexivity. Qed.
  Lemma update_neq : forall s l v m, l <> m -> update s l v m = s m.
  Proof.
    intros s l v m H; unfold update.
    destruct (loceqb l m) eqn:E; [apply loceqb_true in E; contradiction | reflexivity].
  Qed.
  Lemma update_shadow : forall s l a b, update (update s l a) l b = update s l b.
  Proof.
    intros; apply functional_extensionality; intro m; unfold update.
    destruct (loceqb l m); reflexivity.
  Qed.
  Lemma update_same : forall s l, update s l (s l) = s.
  Proof.
    intros; apply functional_extensionality; intro m; unfold update.
    destruct (loceqb l m) eqn:E; [apply loceqb_true in E; subst; reflexivity | reflexivity].
  Qed.

  Definition sw (s : store) (l1 l2 : loc) : store :=
    update (update s l1 (s l2)) l2 (s l1).
  Lemma sw_invol : forall s l1 l2, sw (sw s l1 l2) l1 l2 = s.
  Proof.
    intros s l1 l2; apply functional_extensionality; intro m.
    unfold sw, update.
    destruct (loceqb l2 m) eqn:H2.
    - apply loceqb_true in H2; subst m.
      destruct (loceqb l2 l1) eqn:H21.
      + apply loceqb_true in H21; subst l1; reflexivity.
      + rewrite loceqb_refl; reflexivity.
    - destruct (loceqb l1 m) eqn:H1.
      + rewrite loceqb_refl. apply loceqb_true in H1; subst l1; reflexivity.
      + reflexivity.
  Qed.

  (** *** Expressions read any location (so guards/updates may mention cells). *)
  Inductive expr := Cst (z : Z) | Var (l : loc) | Bin (o : binop) (e1 e2 : expr).
  Fixpoint eval (s : store) (e : expr) : Z :=
    match e with
    | Cst z => z | Var l => s l
    | Bin o e1 e2 => denote o (eval s e1) (eval s e2)
    end.
  Fixpoint occurs (k : loc) (e : expr) : bool :=
    match e with
    | Cst _ => false | Var l => loceqb k l
    | Bin _ e1 e2 => orb (occurs k e1) (occurs k e2)
    end.
  Lemma eval_update_notin :
    forall k v s e, occurs k e = false -> eval (update s k v) e = eval s e.
  Proof.
    intros k v s e; induction e; intro H; simpl in H |- *.
    - reflexivity.
    - unfold update; rewrite H; reflexivity.
    - apply orb_false_iff in H; destruct H as [H1 H2].
      rewrite IHe1 by assumption; rewrite IHe2 by assumption; reflexivity.
  Qed.

  (** *** Guards: an expression is "true" when it is nonzero. *)
  Definition guard := expr.
  Definition gtest (e : expr) (s : store) : bool := negb (Z.eqb (eval s e) 0).

  (** *** Primitives.
      [PUpd]/[PSwap] act on any location (scalar OR array cell).
      [PEnter]/[PExit] are the two halves of a [local]/[delocal] block over a
      *dead* local cell ([LVar n] is conventionally 0 outside its block). *)
  Inductive prim_ : Type :=
  | PUpd  (l : loc) (o : aop) (e : expr)   (* l op= e , needs ~ occurs l e *)
  | PSwap (l1 l2 : loc)                     (* l1 <=> l2 *)
  | PEnter (n : nat) (e : expr)             (* local x = e   (x = LVar n) *)
  | PExit  (n : nat) (e : expr).            (* delocal x = e *)
  Definition prim := prim_.

  Definition pstep (p : prim) (a b : state) : Prop :=
    match p with
    | PUpd l o e => occurs l e = false /\ b = update a l (adenote o (a l) (eval a e))
    | PSwap l1 l2 => b = sw a l1 l2
    | PEnter n e =>
        a (LVar n) = 0 /\ occurs (LVar n) e = false /\
        b = update a (LVar n) (eval a e)
    | PExit n e =>
        occurs (LVar n) e = false /\ b = update a (LVar n) 0 /\
        a (LVar n) = eval b e
    end.

  Definition pinv (p : prim) : prim :=
    match p with
    | PUpd l o e => PUpd l (ainv o) e
    | PSwap l1 l2 => PSwap l1 l2
    | PEnter n e => PExit n e
    | PExit n e => PEnter n e
    end.

  Lemma pinv_invol : forall p, pinv (pinv p) = p.
  Proof. destruct p; simpl; try reflexivity. rewrite ainv_invol; reflexivity. Qed.

  Lemma pstep_det : forall p a b b', pstep p a b -> pstep p a b' -> b = b'.
  Proof.
    destruct p; simpl; intros a b b' H1 H2.
    - destruct H1 as [_ ->]; destruct H2 as [_ ->]; reflexivity.
    - subst; reflexivity.
    - destruct H1 as [_ [_ ->]]; destruct H2 as [_ [_ ->]]; reflexivity.
    - destruct H1 as [_ [-> _]]; destruct H2 as [_ [-> _]]; reflexivity.
  Qed.

  Lemma pstep_rev : forall p a b, pstep p a b -> pstep (pinv p) b a.
  Proof.
    destruct p; simpl; intros a b H.
    - (* PUpd: same reversal as scalar assignment *)
      destruct H as [Hocc ->]. split; [ exact Hocc | ].
      rewrite update_eq.
      rewrite (eval_update_notin l (adenote o (a l) (eval a e)) a e Hocc).
      rewrite ainv_correct, update_shadow, update_same; reflexivity.
    - (* PSwap *)
      subst. rewrite sw_invol; reflexivity.
    - (* PEnter -> PExit *)
      destruct H as [Hz [Hocc ->]]. split; [ exact Hocc | split ].
      + rewrite update_shadow, <- Hz, update_same; reflexivity.
      + rewrite update_eq; reflexivity.
    - (* PExit -> PEnter *)
      destruct H as [Hocc [-> Hval]]. split; [ rewrite update_eq; reflexivity | split ].
      + exact Hocc.
      + rewrite update_shadow, <- Hval, update_same; reflexivity.
  Qed.

End ExtPrim.

Import ExtPrim.
Module EX := RevLang ExtPrim.

(** ** Reversibility of array/local programs — straight from the framework. *)
Theorem ext_reversible :
  forall (Γ : EX.pname -> EX.stmt) (s : EX.stmt) (a a' b : store),
    EX.exec Γ s a b -> EX.exec Γ s a' b -> a = a'.
Proof. exact EX.exec_injective. Qed.

Theorem ext_invert_correct :
  forall (Γ : EX.pname -> EX.stmt) (s : EX.stmt) (a b : store),
    EX.exec Γ s a b <-> EX.exec Γ (EX.invert s) b a.
Proof. exact EX.exec_iff. Qed.

(** ** [local]/[delocal] is derived: just two atoms wrapped around the body. *)
Definition LBlockR (n : nat) (e : expr) (s : EX.stmt) (e' : expr) : EX.stmt :=
  EX.Seq (EX.Prim (PEnter n e)) (EX.Seq s (EX.Prim (PExit n e'))).
Definition LBlockL (n : nat) (e : expr) (s : EX.stmt) (e' : expr) : EX.stmt :=
  EX.Seq (EX.Seq (EX.Prim (PEnter n e)) s) (EX.Prim (PExit n e')).

(** The generic inverter turns  [local x=e; S; delocal x=e']  into
    [local x=e'; invert S; delocal x=e]  — by computation, no proof effort.
    (The two sides differ only in the parenthesisation of [;], which [exec]
    does not distinguish; see [seq_assoc] below.) *)
Theorem invert_LocalBlock :
  forall n e s e', EX.invert (LBlockR n e s e') = LBlockL n e' (EX.invert s) e.
Proof. reflexivity. Qed.

(** Sequencing is associative for [exec], so the two bracketings above are
    interchangeable as programs. *)
Lemma seq_assoc :
  forall Γ A B C a b,
    EX.exec Γ (EX.Seq (EX.Seq A B) C) a b <-> EX.exec Γ (EX.Seq A (EX.Seq B C)) a b.
Proof.
  intros Γ A B C a b; split; intro H.
  - inversion H; subst.
    match goal with
    | HAB : EX.exec ?g (EX.Seq A B) ?a0 ?m, HC : EX.exec ?g C ?m ?b0 |- _ =>
      inversion HAB; subst;
      match goal with
      | HA : EX.exec ?g A ?a0 ?m2, HB : EX.exec ?g B ?m2 ?m |- _ =>
        eapply EX.E_Seq; [ exact HA | eapply EX.E_Seq; [ exact HB | exact HC ] ]
      end
    end.
  - inversion H; subst.
    match goal with
    | HA : EX.exec ?g A ?a0 ?m, HBC : EX.exec ?g (EX.Seq B C) ?m ?b0 |- _ =>
      inversion HBC; subst;
      match goal with
      | HB : EX.exec ?g B ?m ?m2, HC : EX.exec ?g C ?m2 ?b0 |- _ =>
        eapply EX.E_Seq; [ eapply EX.E_Seq; [ exact HA | exact HB ] | exact HC ]
      end
    end.
Qed.

(** A concrete array example: the inverter mirrors and reverses two array
    updates (note [^=] is its own inverse, [+=] flips to [-=]). *)
Example invert_array_demo :
  EX.invert (EX.Seq (EX.Prim (PUpd (Cell 0 0) AAdd (Var (Scal 1))))
                    (EX.Prim (PUpd (Cell 1 1) AXor (Var (Scal 2)))))
  = EX.Seq (EX.Prim (PUpd (Cell 1 1) AXor (Var (Scal 2))))
           (EX.Prim (PUpd (Cell 0 0) ASub (Var (Scal 1)))).
Proof. reflexivity. Qed.
