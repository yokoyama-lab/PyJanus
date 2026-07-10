(** * RevExtMod.v — a modular (bounded-integer) reversible core, via RevCore

    [RevExt.v] is a [RevCore] instance with a store over scalars, array cells and
    local cells, and unbounded [Z] arithmetic.  This file is its *modular*
    sibling: every register carries a fixed modulus [M = 2^bits], so an
    assignment wraps.  It is the verified target a modular frame core (the one
    [vjanus] would extract to run Janus's sized integer types [i8]/[i16]/… and
    the [-m bits] mode) commits to.

    Two modelling points, matching PyJanus exactly:

    1. **Only stores wrap; expression intermediates stay unbounded.**  [eval] is
       plain [Z] arithmetic (as in PyJanus, where a binary op result is
       [UNBOUND]); the wrap [mod M] happens on the *assignment* [l op= e] and on
       a local's initial value.

    2. **Reversibility needs canonicity.**  Wrapping a [Z] cell is a bijection
       only within one residue window, so [pstep] for an update carries the guard
       [0 <= a l < M] on the cell it touches — exactly what a [Z/M] cell type
       enforces structurally.  Each update's result is [_ mod M], hence canonical,
       so the guard is preserved.

    Supplying the three [REV_PRIM] local laws makes [RevLang] hand back
    [exec_rev]/[exec_iff]/[exec_det]/[exec_injective] for the modular language —
    reversibility of bounded-int array/local programs, for free. *)

From Stdlib Require Import ZArith Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
Require Import RevCore.
Open Scope Z_scope.

Module Type MODULUS.
  Parameter M : Z.
  Axiom M_pos : 0 < M.
End MODULUS.

Module ExtModPrim (Import Mod : MODULUS) <: REV_PRIM.

  (** *** Locations: scalars, array cells, and local cells — one store. *)
  Inductive loc := Scal (n : nat) | Cell (a : nat) (i : Z) | LVar (n : nat).
  Definition loc_eq_dec : forall x y : loc, {x = y} + {x <> y}.
  Proof. decide equality; (apply Nat.eq_dec || apply Z.eq_dec). Defined.
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
    intros; apply functional_extensionality; intro m.
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

  (** *** Modular update algebra: [+=]/[-=] wrap mod M. *)
  Inductive aop := OAdd | OSub.
  Definition adenote (o : aop) (a b : Z) : Z :=
    match o with OAdd => (a + b) mod M | OSub => (a - b) mod M end.
  Definition ainv (o : aop) : aop := match o with OAdd => OSub | OSub => OAdd end.
  Lemma ainv_invol : forall o, ainv (ainv o) = o. Proof. destruct o; reflexivity. Qed.

  Lemma adenote_canon : forall o a b, 0 <= adenote o a b < M.
  Proof. intros; destruct o; apply Z.mod_pos_bound; apply M_pos. Qed.

  (* the reversal law, valid exactly when the left operand is canonical *)
  Lemma adenote_rev : forall o x v, 0 <= x < M -> adenote (ainv o) (adenote o x v) v = x.
  Proof.
    intros o x v Hx; destruct o; simpl.
    - rewrite Zminus_mod_idemp_l. replace (x + v - v) with x by ring.
      apply Z.mod_small; assumption.
    - rewrite Zplus_mod_idemp_l. replace (x - v + v) with x by ring.
      apply Z.mod_small; assumption.
  Qed.

  (** *** Expressions: unbounded (only assignments wrap), as in PyJanus. *)
  Inductive binop := BAdd | BSub | BMul | BEq | BLt | BDiv | BMod | BXor | BAnd | BOr.
  Definition denote (o : binop) (a b : Z) : Z :=
    match o with
    | BAdd => a + b | BSub => a - b | BMul => a * b
    | BEq => if Z.eqb a b then 1 else 0 | BLt => if Z.ltb a b then 1 else 0
    | BDiv => Z.div a b | BMod => Z.modulo a b
    | BXor => Z.lxor a b | BAnd => Z.land a b | BOr => Z.lor a b
    end.
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

  (** *** Guards: an expression is "true" when nonzero. *)
  Definition guard := expr.
  Definition gtest (e : expr) (s : store) : bool := negb (Z.eqb (eval s e) 0).

  (** *** Primitives. *)
  Inductive prim_ : Type :=
  | PUpd  (l : loc) (o : aop) (e : expr)   (* l op= e (mod M), needs ~ occurs l e *)
  | PSwap (l1 l2 : loc)                     (* l1 <=> l2 *)
  | PEnter (n : nat) (e : expr)             (* local x = e  (stored mod M) *)
  | PExit  (n : nat) (e : expr).            (* delocal x = e *)
  Definition prim := prim_.

  Definition pstep (p : prim) (a b : state) : Prop :=
    match p with
    | PUpd l o e =>
        occurs l e = false /\ 0 <= a l < M /\
        b = update a l (adenote o (a l) (eval a e))
    | PSwap l1 l2 => b = sw a l1 l2
    | PEnter n e =>
        a (LVar n) = 0 /\ occurs (LVar n) e = false /\
        b = update a (LVar n) ((eval a e) mod M)
    | PExit n e =>
        occurs (LVar n) e = false /\ b = update a (LVar n) 0 /\
        a (LVar n) = (eval b e) mod M
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
    - destruct H1 as [_ [_ ->]]; destruct H2 as [_ [_ ->]]; reflexivity.
    - subst; reflexivity.
    - destruct H1 as [_ [_ ->]]; destruct H2 as [_ [_ ->]]; reflexivity.
    - destruct H1 as [_ [-> _]]; destruct H2 as [_ [-> _]]; reflexivity.
  Qed.

  Lemma pstep_rev : forall p a b, pstep p a b -> pstep (pinv p) b a.
  Proof.
    destruct p; simpl; intros a b H.
    - (* PUpd: modular reversal, using canonicity of [a l] *)
      destruct H as [Hocc [Hcan ->]]. split; [ exact Hocc | split ].
      + rewrite update_eq. apply adenote_canon.
      + rewrite update_eq.
        rewrite (eval_update_notin l (adenote o (a l) (eval a e)) a e Hocc).
        rewrite (adenote_rev o (a l) (eval a e) Hcan).
        rewrite update_shadow, update_same; reflexivity.
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

End ExtModPrim.

(** Reversibility of a modular (bounded-int) reversible language, for free. *)
Module ExtModFacts (Mod : MODULUS).
  Module P := ExtModPrim Mod.
  Module L := RevLang P.
  Theorem extmod_reversible :
    forall (Γ : L.pname -> L.stmt) (s : L.stmt) (a a' b : P.state),
      L.exec Γ s a b -> L.exec Γ s a' b -> a = a'.
  Proof. exact L.exec_injective. Qed.
  Theorem extmod_iff :
    forall (Γ : L.pname -> L.stmt) (s : L.stmt) (a b : P.state),
      L.exec Γ s a b <-> L.exec Γ (L.invert s) b a.
  Proof. intros; apply L.exec_iff. Qed.
End ExtModFacts.

(** ** Concrete check: an i8 store (M = 256), array cell wraps and is reversible. *)

Module M256 <: MODULUS.
  Definition M := 256.
  Lemma M_pos : 0 < M. Proof. unfold M; lia. Qed.
End M256.

Module P8 := ExtModPrim M256.
Module I8 := RevLang P8.
Definition Γ0 : I8.pname -> I8.stmt := fun _ => I8.Skip.

Definition s0 : P8.store := fun _ => 0.

(** Array cell [Cell 0 0] holding 250, then [+= 10], wraps to 4 (mod 256). *)
Example i8_cell_wraps :
  I8.exec Γ0 (I8.Prim (P8.PUpd (P8.Cell 0 0) P8.OAdd (P8.Cst 10)))
          (P8.update s0 (P8.Cell 0 0) 250)
          (P8.update s0 (P8.Cell 0 0) 4).
Proof.
  apply I8.E_Prim. unfold P8.pstep. split; [ reflexivity | split ].
  - rewrite P8.update_eq. unfold M256.M; lia.
  - rewrite P8.update_eq, P8.update_shadow. reflexivity.
Qed.

(** And it is reversible: running the wrapping update backward recovers 250. *)
Example i8_cell_reversible :
  I8.exec Γ0 (I8.invert (I8.Prim (P8.PUpd (P8.Cell 0 0) P8.OAdd (P8.Cst 10))))
          (P8.update s0 (P8.Cell 0 0) 4)
          (P8.update s0 (P8.Cell 0 0) 250).
Proof. apply I8.exec_rev. apply i8_cell_wraps. Qed.
