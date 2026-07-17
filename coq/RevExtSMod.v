(** * RevExtSMod.v — the signed-modular store core (the [-m bits] mode)

    [RevExtMod.v] wraps only the *store* (each register canonical in [0, M));
    expression intermediates stay unbounded — the right model for Janus's
    per-variable sized types ([i8]/[i16]/…), matching PyJanus's
    [_normalize_int(value, int_type)] calls at assignment sites.

    PyJanus's *global* [-m bits] mode is different: [_eval_bin] normalizes
    **every** binary-operator result through the signed wrap [norm] (see
    [RevSMod.v]), not just assignments — because under [-m bits] with no
    per-variable sized type, [_normalize_int] falls through to the [mod_bits]
    branch unconditionally.  So a `-m`-faithful core must wrap [eval] itself,
    not only [PUpd]/[PEnter]/[PExit].  This file is that core: [RevExtMod.v]'s
    store (scalars, array cells, local cells) with [RevSMod.v]'s signed [norm]
    threaded through both evaluation and assignment.

    Reversibility is recovered the same way as [RevSMod.v]: with every register
    held canonical in the signed window [[-half, half)], the wrapping updates
    are mutually inverse bijections — [RevLang] gives [extsmod_reversible] for
    free once the three [REV_PRIM] local laws are discharged. *)

From Stdlib Require Import ZArith Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
Require Import RevCore RevSMod.
Open Scope Z_scope.

Module ExtSModPrim (Import B : BITS) <: REV_PRIM.
  Module N := SModPrim B.
  Import N.  (* M, half, norm, norm_range, norm_id, norm_absorb, norm_add_rev, norm_sub_rev *)

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

  (** *** Update algebra: [+=]/[-=], wrapping via the signed [norm]. *)
  Inductive aop := OAdd | OSub.
  Definition adenote (o : aop) (a b : Z) : Z :=
    match o with OAdd => norm (a + b) | OSub => norm (a - b) end.
  Definition ainv (o : aop) : aop := match o with OAdd => OSub | OSub => OAdd end.
  Lemma ainv_invol : forall o, ainv (ainv o) = o. Proof. destruct o; reflexivity. Qed.

  (* the reversal law, valid exactly when the left operand is canonical *)
  Lemma adenote_rev : forall o x v, -half <= x < half ->
    adenote (ainv o) (adenote o x v) v = x.
  Proof.
    intros o x v Hx; destruct o; simpl.
    - apply norm_add_rev; exact Hx.
    - apply norm_sub_rev; exact Hx.
  Qed.

  (** *** Expressions: EVERY binop result wraps via [norm] — the [-m bits]
      semantics (PyJanus's [_eval_bin] normalizes unconditionally when no
      per-variable sized type overrides it). *)
  Inductive binop := BAdd | BSub | BMul | BEq | BLt | BDiv | BMod | BXor | BAnd | BOr.
  Definition denote0 (o : binop) (a b : Z) : Z :=
    match o with
    | BAdd => a + b | BSub => a - b | BMul => a * b
    | BEq => if Z.eqb a b then 1 else 0 | BLt => if Z.ltb a b then 1 else 0
    | BDiv => Z.div a b | BMod => Z.modulo a b
    | BXor => Z.lxor a b | BAnd => Z.land a b | BOr => Z.lor a b
    end.
  Definition denote (o : binop) (a b : Z) : Z := norm (denote0 o a b).

  Inductive expr := Cst (z : Z) | Var (l : loc) | Bin (o : binop) (e1 e2 : expr).
  Fixpoint eval (s : store) (e : expr) : Z :=
    match e with
    | Cst z => norm z | Var l => s l
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

  (* every evaluated expression is canonical, since [Cst]/[Bin] both wrap and a
     [Var] reads a canonical cell (an invariant [PUpd]/[PEnter] preserve) *)
  Definition canon_store (s : store) : Prop := forall l, -half <= s l < half.
  Lemma eval_canon : forall s e, canon_store s -> -half <= eval s e < half.
  Proof.
    intros s e Hs; induction e; simpl.
    - apply norm_range.
    - apply Hs.
    - apply norm_range.
  Qed.

  (** *** Guards: an expression is "true" when nonzero. *)
  Definition guard := expr.
  Definition gtest (e : expr) (s : store) : bool := negb (Z.eqb (eval s e) 0).

  (** *** Primitives. *)
  Inductive prim_ : Type :=
  | PUpd  (l : loc) (o : aop) (e : expr)   (* l op= e, signed-wraps *)
  | PSwap (l1 l2 : loc)                     (* l1 <=> l2 *)
  | PEnter (n : nat) (e : expr)             (* local x = e (stored signed-wrapped) *)
  | PExit  (n : nat) (e : expr).            (* delocal x = e *)
  Definition prim := prim_.

  Definition pstep (p : prim) (a b : state) : Prop :=
    match p with
    | PUpd l o e =>
        occurs l e = false /\ -half <= a l < half /\
        b = update a l (adenote o (a l) (eval a e))
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
    - destruct H1 as [_ [_ ->]]; destruct H2 as [_ [_ ->]]; reflexivity.
    - subst; reflexivity.
    - destruct H1 as [_ [_ ->]]; destruct H2 as [_ [_ ->]]; reflexivity.
    - destruct H1 as [_ [-> _]]; destruct H2 as [_ [-> _]]; reflexivity.
  Qed.

  Lemma pstep_rev : forall p a b, pstep p a b -> pstep (pinv p) b a.
  Proof.
    destruct p; simpl; intros a b H.
    - (* PUpd: signed-modular reversal, using canonicity of [a l] *)
      destruct H as [Hocc [Hcan ->]]. split; [ exact Hocc | split ].
      + rewrite update_eq. unfold adenote. destruct o; apply norm_range.
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
End ExtSModPrim.

(** Reversibility of the signed-modular ([-m bits]) language, for free. *)
Module ExtSModFacts (B : BITS).
  Module P := ExtSModPrim B.
  Module L := RevLang P.
  Theorem extsmod_reversible :
    forall (Γ : L.pname -> L.stmt) (s : L.stmt) (a a' b : P.state),
      L.exec Γ s a b -> L.exec Γ s a' b -> a = a'.
  Proof. exact L.exec_injective. Qed.
  Theorem extsmod_iff :
    forall (Γ : L.pname -> L.stmt) (s : L.stmt) (a b : P.state),
      L.exec Γ s a b <-> L.exec Γ (L.invert s) b a.
  Proof. intros; apply L.exec_iff. Qed.
End ExtSModFacts.

(** ** Concrete check: an 8-bit signed store — array cell wraps, reversibly, and
    an expression intermediate wraps mid-computation (unlike RevExtMod). *)

Module B8 <: BITS.
  Definition bits := 8%nat.
  Lemma bits_pos : (1 <= bits)%nat. Proof. unfold bits; lia. Qed.
End B8.

Module P8 := ExtSModPrim B8.
Module I8 := RevLang P8.
Definition Γ0 : I8.pname -> I8.stmt := fun _ => I8.Skip.

Definition s0 : P8.store := fun _ => 0.

(** Array cell [Cell 0 0] holding 100, [+= 50], wraps to -106 (signed 8-bit),
    exactly PyJanus's `-m 8` (verified against the interpreter in RevSMod.v). *)
Example i8_cell_swraps :
  I8.exec Γ0 (I8.Prim (P8.PUpd (P8.Cell 0 0) P8.OAdd (P8.Cst 50)))
          (P8.update s0 (P8.Cell 0 0) 100)
          (P8.update s0 (P8.Cell 0 0) (-106)).
Proof.
  apply I8.E_Prim. unfold P8.pstep. split; [ reflexivity | split ].
  - rewrite P8.update_eq. unfold P8.N.half, P8.N.M, B8.bits. cbn; lia.
  - rewrite P8.update_eq. unfold P8.adenote, P8.N.norm, P8.N.half, P8.N.M, B8.bits.
    cbn. rewrite P8.update_shadow. reflexivity.
Qed.

(** And it is reversible: running the update backward recovers 100. *)
Example i8_cell_sreversible :
  I8.exec Γ0 (I8.invert (I8.Prim (P8.PUpd (P8.Cell 0 0) P8.OAdd (P8.Cst 50))))
          (P8.update s0 (P8.Cell 0 0) (-106))
          (P8.update s0 (P8.Cell 0 0) 100).
Proof. apply I8.exec_rev. apply i8_cell_swraps. Qed.

(** An expression intermediate wraps mid-computation: (100 + 50) - 90, evaluated
    left-to-right, wraps once at the inner sum ((100+50) -> -106) and again at
    the outer difference (-106 - 90 = -196 -> 60) — matching PyJanus's -m 8,
    where a binary op's result is ALWAYS normalized, not just at assignment
    (unlike RevExtMod, whose intermediates stay unbounded). *)
Example expr_wraps_mid_computation :
  P8.eval s0 (P8.Bin P8.BSub (P8.Bin P8.BAdd (P8.Cst 100) (P8.Cst 50)) (P8.Cst 90)) = 60.
Proof. reflexivity. Qed.
