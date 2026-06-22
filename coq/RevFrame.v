(** * RevFrame.v — design spike for Phase 2a: frame-stacked locals.

    A minimal reversible language with GLOBAL slots and DEPTH-INDEXED LOCAL slots,
    plus by-reference procedure calls and recursion.  Its purpose is to validate
    — on a small core, before touching RevArr.v — that giving each activation a
    fresh local frame keeps the language reversible and admits a sound fuel
    interpreter.

    Locations: [G n] global slot, [L d x] local slot [x] at frame depth [d].
    A procedure body references variables through [ref]:
      [RG n] a global, [RL x] one of *its own* locals (resolved at the current
      depth), [RF i] the i-th formal (replaced at call time by the actual's
      absolute name), [RN nm] an already-resolved absolute name.
    [Call] runs the callee body at depth [S d] after substituting formals by the
    actuals resolved at the caller's depth [d] — so a caller-local passed by
    reference stays pinned to the caller's frame while the callee's own locals
    live one frame deeper. *)

From Stdlib Require Import ZArith Bool List Lia FunctionalExtensionality.
Import ListNotations.
Open Scope Z_scope.

(* ---------- locations and store ---------- *)

(* scalar slots G/L, and array cells GA/LA (global / depth-d local), ahead of the
   array layer that will read and assign them. *)
Inductive loc :=
| G  (n : nat)
| L  (d : nat) (x : nat)
| GA (a : nat) (i : Z)
| LA (d : nat) (a : nat) (i : Z).

Definition loceqb (a b : loc) : bool :=
  match a, b with
  | G m, G n => Nat.eqb m n
  | L d x, L e y => Nat.eqb d e && Nat.eqb x y
  | GA m i, GA n j => Nat.eqb m n && Z.eqb i j
  | LA d m i, LA e n j => Nat.eqb d e && Nat.eqb m n && Z.eqb i j
  | _, _ => false
  end.

Lemma loceqb_refl : forall l, loceqb l l = true.
Proof.
  destruct l; simpl.
  - now rewrite Nat.eqb_refl.
  - now rewrite !Nat.eqb_refl.
  - now rewrite Nat.eqb_refl, Z.eqb_refl.
  - now rewrite !Nat.eqb_refl, Z.eqb_refl.
Qed.

Lemma loceqb_true : forall a b, loceqb a b = true -> a = b.
Proof.
  destruct a, b; simpl; try discriminate.
  - now intro H; apply Nat.eqb_eq in H; subst.
  - intro H; apply andb_true_iff in H as [H1 H2];
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2; subst; reflexivity.
  - intro H; apply andb_true_iff in H as [H1 H2];
    apply Nat.eqb_eq in H1; apply Z.eqb_eq in H2; subst; reflexivity.
  - intro H; apply andb_true_iff in H as [H12 H3]; apply andb_true_iff in H12 as [H1 H2];
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2; apply Z.eqb_eq in H3; subst; reflexivity.
Qed.

Lemma loceqb_sym : forall a b, loceqb a b = loceqb b a.
Proof.
  destruct a as [m|d x|m i|d m i], b as [n|e y|n j|e n j]; simpl; try reflexivity.
  - apply Nat.eqb_sym.
  - now rewrite (Nat.eqb_sym d e), (Nat.eqb_sym x y).
  - now rewrite (Nat.eqb_sym m n), (Z.eqb_sym i j).
  - now rewrite (Nat.eqb_sym d e), (Nat.eqb_sym m n), (Z.eqb_sym i j).
Qed.

Definition store := loc -> Z.
Definition update (s : store) (l : loc) (v : Z) : store :=
  fun m => if loceqb l m then v else s m.

Lemma update_eq : forall s l v, update s l v l = v.
Proof. intros; unfold update; rewrite loceqb_refl; reflexivity. Qed.
Lemma update_neq : forall s l m v, loceqb l m = false -> update s l v m = s m.
Proof. intros; unfold update; now rewrite H. Qed.
Lemma update_shadow : forall s l a b, update (update s l a) l b = update s l b.
Proof. intros; apply functional_extensionality; intro m; unfold update;
  destruct (loceqb l m); reflexivity. Qed.
Lemma update_same : forall s l, update s l (s l) = s.
Proof. intros; apply functional_extensionality; intro m; unfold update;
  destruct (loceqb l m) eqn:E; [apply loceqb_true in E; subst; reflexivity | reflexivity]. Qed.

(* ---------- syntax ---------- *)

Inductive nm := NG (n : nat) | NL (d : nat) (x : nat).
Inductive ref := RG (n : nat) | RL (x : nat) | RF (i : nat) | RN (a : nm).

(* resolve an array base [ref] + index to its cell, at the current depth *)
Definition acell (d : nat) (r : ref) (i : Z) : loc :=
  match r with
  | RG n => GA n i | RL x => LA d x i
  | RN (NG n) => GA n i | RN (NL e x) => LA e x i
  | RF k => GA k i  (* dummy; never reached post-subst *)
  end.

(* name-based test: is [l] some cell of the array that [r] denotes at depth [d]?
   (conservative — ignores the index, like RevArr's occ on array names). *)
Definition arr_hit (d : nat) (r : ref) (l : loc) : bool :=
  match l, r with
  | GA a _, RG n => Nat.eqb a n
  | GA a _, RN (NG n) => Nat.eqb a n
  | GA a _, RF k => Nat.eqb a k
  | LA e a _, RL x => Nat.eqb e d && Nat.eqb a x
  | LA e a _, RN (NL e' x) => Nat.eqb e e' && Nat.eqb a x
  | _, _ => false
  end.

(* if [l] is not in [r]'s array, it cannot be the specific cell [acell d r j]. *)
Lemma arr_miss : forall d r l j, arr_hit d r l = false -> loceqb (acell d r j) l = false.
Proof.
  intros d r l j H; destruct r as [n|x|k|[n|e x]], l as [m|e' y|m i|e' m i];
    simpl in H |- *; try reflexivity.
  - now rewrite (Nat.eqb_sym n m), H.
  - now rewrite (Nat.eqb_sym d e'), (Nat.eqb_sym x m), H.
  - now rewrite (Nat.eqb_sym k m), H.
  - now rewrite (Nat.eqb_sym n m), H.
  - now rewrite (Nat.eqb_sym e e'), (Nat.eqb_sym x m), H.
Qed.

(* invertible assignment operators (each [Asn]/[AAsn] must be undoable) *)
Inductive aop := OAdd | OSub | OXor.
Definition app (o : aop) (a b : Z) : Z :=
  match o with OAdd => a + b | OSub => a - b | OXor => Z.lxor a b end.
Definition ainv (o : aop) : aop :=
  match o with OAdd => OSub | OSub => OAdd | OXor => OXor end.
(* the key local law: applying the inverse op over the result, with the same
   right operand, restores the left operand (XOR is its own inverse). *)
Lemma app_ainv : forall o a b, app (ainv o) (app o a b) b = a.
Proof. destruct o; intros a b; simpl; try lia.
  rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r; reflexivity. Qed.

(* total binary operators for expressions (read-only; no inverse needed), at
   parity with RevArr's [binop]/[denote] so a frame program computes identically *)
Inductive binop := BAdd | BSub | BMul | BEq | BLt | BDiv | BMod.
Definition bden (o : binop) (a b : Z) : Z :=
  match o with BAdd => a + b | BSub => a - b | BMul => a * b
    | BEq => if Z.eqb a b then 1 else 0 | BLt => if Z.ltb a b then 1 else 0
    | BDiv => Z.div a b | BMod => Z.modulo a b end.

Inductive expr := Cst (z : Z) | Rd (r : ref) | ARd (r : ref) (idx : expr) | Bin (o : binop) (a b : expr).

Inductive stmt :=
| Skip
| Asn (r : ref) (o : aop) (e : expr)
| AAsn (r : ref) (idx : expr) (o : aop) (e : expr)   (* array cell: r[idx] op= e *)
| Seq (s1 s2 : stmt)
| If (e1 : expr) (s1 s2 : stmt) (e2 : expr)
| Loop (e1 : expr) (s1 s2 : stmt) (e2 : expr)
| Enter (x : nat) (e : expr)
| Exit  (x : nat) (e : expr)
| Call   (p : nat) (args : list ref)
| Uncall (p : nat) (args : list ref).

(* a ref, resolved against the current depth, denotes a location *)
Definition loc_of_nm (a : nm) : loc := match a with NG n => G n | NL d x => L d x end.
Definition loc_of_ref (d : nat) (r : ref) : loc :=
  match r with RG n => G n | RL x => L d x | RN a => loc_of_nm a | RF i => G i (* dummy; never reached post-subst *) end.

Fixpoint eval (d : nat) (s : store) (e : expr) : Z :=
  match e with
  | Cst z => z
  | Rd r => s (loc_of_ref d r)
  | ARd r idx => s (acell d r (eval d s idx))
  | Bin o a b => bden o (eval d s a) (eval d s b)
  end.

(* does [e] read location [l] at depth [d]?  Exact for scalars; conservative
   (name-based, index-agnostic) for array reads, via [arr_hit]. *)
Fixpoint reads (d : nat) (l : loc) (e : expr) : bool :=
  match e with
  | Cst _ => false
  | Rd r => loceqb (loc_of_ref d r) l
  | ARd r idx => arr_hit d r l || reads d l idx
  | Bin _ a b => reads d l a || reads d l b
  end.

Lemma eval_stable : forall d l v s e, reads d l e = false -> eval d (update s l v) e = eval d s e.
Proof.
  intros d l v s; induction e as [z | r | r idx IHidx | o e1 IH1 e2 IH2]; intro H; simpl in *.
  - reflexivity.
  - apply update_neq; rewrite loceqb_sym; exact H.
  - apply orb_false_iff in H as [Hhit Hidx]. rewrite (IHidx Hidx).
    apply update_neq; rewrite loceqb_sym; apply arr_miss; exact Hhit.
  - apply orb_false_iff in H as [H1 H2]; rewrite (IH1 H1), (IH2 H2); reflexivity.
Qed.

Definition wf_asn (d : nat) (r : ref) (e : expr) : bool := negb (reads d (loc_of_ref d r) e).

(* undoing an assignment: when [e] does not read the target, applying the inverse
   operator over the post-store returns the original store. *)
Lemma asn_inv_store : forall d r o e s, reads d (loc_of_ref d r) e = false ->
  update (update s (loc_of_ref d r) (app o (s (loc_of_ref d r)) (eval d s e)))
         (loc_of_ref d r)
         (app (ainv o)
              (update s (loc_of_ref d r) (app o (s (loc_of_ref d r)) (eval d s e)) (loc_of_ref d r))
              (eval d (update s (loc_of_ref d r) (app o (s (loc_of_ref d r)) (eval d s e))) e))
  = s.
Proof.
  intros d r o e s H. set (l := loc_of_ref d r) in *.
  rewrite update_eq, (eval_stable d l (app o (s l) (eval d s e)) s e H).
  replace (app (ainv o) (app o (s l) (eval d s e)) (eval d s e)) with (s l)
    by (symmetry; apply app_ainv).
  rewrite update_shadow, update_same; reflexivity.
Qed.

(* array assignment r[idx] op= e: admissible when the written cell is read by
   neither e nor the index idx.  Because [reads] is store-free (name-based on
   array ids), this condition is automatically stable under the update — no
   reads_cell_stable lemma needed. *)
Definition wf_aasn (d : nat) (s : store) (r : ref) (idx e : expr) : bool :=
  negb (reads d (acell d r (eval d s idx)) e) && negb (reads d (acell d r (eval d s idx)) idx).

Lemma aasn_inv_store : forall d s r idx o e,
  reads d (acell d r (eval d s idx)) e = false ->
  reads d (acell d r (eval d s idx)) idx = false ->
  update (update s (acell d r (eval d s idx)) (app o (s (acell d r (eval d s idx))) (eval d s e)))
    (acell d r (eval d (update s (acell d r (eval d s idx)) (app o (s (acell d r (eval d s idx))) (eval d s e))) idx))
    (app (ainv o)
      (update s (acell d r (eval d s idx)) (app o (s (acell d r (eval d s idx))) (eval d s e))
        (acell d r (eval d (update s (acell d r (eval d s idx)) (app o (s (acell d r (eval d s idx))) (eval d s e))) idx)))
      (eval d (update s (acell d r (eval d s idx)) (app o (s (acell d r (eval d s idx))) (eval d s e))) e))
  = s.
Proof.
  intros d s r idx o e He Hi.
  set (c := acell d r (eval d s idx)) in *.
  set (v0 := app o (s c) (eval d s e)).
  assert (Hc : acell d r (eval d (update s c v0) idx) = c) by (unfold c; f_equal; apply eval_stable; exact Hi).
  rewrite Hc, update_eq, (eval_stable d c v0 s e He).
  replace (app (ainv o) v0 (eval d s e)) with (s c) by (unfold v0; symmetry; apply app_ainv).
  rewrite update_shadow, update_same; reflexivity.
Qed.

(* ---------- inversion ---------- *)

Fixpoint invert (s : stmt) : stmt :=
  match s with
  | Skip => Skip
  | Asn r o e => Asn r (ainv o) e
  | AAsn r idx o e => AAsn r idx (ainv o) e
  | Seq a b => Seq (invert b) (invert a)
  | If e1 s1 s2 e2 => If e2 (invert s1) (invert s2) e1
  | Loop e1 s1 s2 e2 => Loop e2 (invert s1) (invert s2) e1
  | Enter x e => Exit x e
  | Exit x e => Enter x e
  | Call p a => Uncall p a
  | Uncall p a => Call p a
  end.

Lemma ainv_invol : forall o, ainv (ainv o) = o. Proof. now destruct o. Qed.

Lemma invert_invol : forall s, invert (invert s) = s.
Proof. induction s; simpl; try reflexivity;
  try (now rewrite IHs1, IHs2); now rewrite ainv_invol. Qed.

(* ---------- substitution of formals by resolved actual names ---------- *)

Definition resolve (d : nat) (r : ref) : nm :=
  match r with RG n => NG n | RL x => NL d x | RN a => a | RF i => NG i end.

Definition subst1 (nms : list nm) (r : ref) : ref :=
  match r with RF i => RN (nth i nms (NG 0)) | _ => r end.

Fixpoint sexpr (nms : list nm) (e : expr) : expr :=
  match e with
  | Cst z => Cst z | Rd r => Rd (subst1 nms r)
  | ARd r idx => ARd (subst1 nms r) (sexpr nms idx)
  | Bin o a b => Bin o (sexpr nms a) (sexpr nms b)
  end.

Fixpoint subst (nms : list nm) (s : stmt) : stmt :=
  match s with
  | Skip => Skip
  | Asn r o e => Asn (subst1 nms r) o (sexpr nms e)
  | AAsn r idx o e => AAsn (subst1 nms r) (sexpr nms idx) o (sexpr nms e)
  | Seq a b => Seq (subst nms a) (subst nms b)
  | If e1 s1 s2 e2 => If (sexpr nms e1) (subst nms s1) (subst nms s2) (sexpr nms e2)
  | Loop e1 s1 s2 e2 => Loop (sexpr nms e1) (subst nms s1) (subst nms s2) (sexpr nms e2)
  | Enter x e => Enter x (sexpr nms e)
  | Exit x e => Exit x (sexpr nms e)
  | Call p a => Call p (map (subst1 nms) a)
  | Uncall p a => Uncall p (map (subst1 nms) a)
  end.

Lemma subst_invert : forall nms s, subst nms (invert s) = invert (subst nms s).
Proof. induction s; simpl; try reflexivity; now rewrite IHs1, IHs2. Qed.

(* ---------- semantics ---------- *)

Section Sem.
Variable Γ : nat -> stmt.

Definition rargs (d : nat) (args : list ref) : list nm := map (resolve d) args.

Inductive exec : nat -> stmt -> store -> store -> Prop :=
| E_Skip : forall d s, exec d Skip s s
| E_Asn  : forall d r o e s, wf_asn d r e = true ->
    exec d (Asn r o e) s (update s (loc_of_ref d r) (app o (s (loc_of_ref d r)) (eval d s e)))
| E_AAsn : forall d r idx o e s, wf_aasn d s r idx e = true ->
    exec d (AAsn r idx o e) s
      (update s (acell d r (eval d s idx)) (app o (s (acell d r (eval d s idx))) (eval d s e)))
| E_Seq  : forall d s1 s2 a m b, exec d s1 a m -> exec d s2 m b -> exec d (Seq s1 s2) a b
| E_IfT  : forall d e1 s1 s2 e2 a b,
    eval d a e1 <> 0 -> exec d s1 a b -> eval d b e2 <> 0 -> exec d (If e1 s1 s2 e2) a b
| E_IfF  : forall d e1 s1 s2 e2 a b,
    eval d a e1 =  0 -> exec d s2 a b -> eval d b e2 =  0 -> exec d (If e1 s1 s2 e2) a b
| E_Loop : forall d e1 s1 s2 e2 a b,
    eval d a e1 <> 0 -> lp d e1 s1 s2 e2 a b -> exec d (Loop e1 s1 s2 e2) a b
| E_Enter : forall d x e s, s (L d x) = 0 -> reads d (L d x) e = false ->
    exec d (Enter x e) s (update s (L d x) (eval d s e))
| E_Exit  : forall d x e s, reads d (L d x) e = false -> s (L d x) = eval d (update s (L d x) 0) e ->
    exec d (Exit x e) s (update s (L d x) 0)
| E_Call  : forall d p args a b,
    exec (S d) (subst (rargs d args) (Γ p)) a b -> exec d (Call p args) a b
| E_Uncall : forall d p args a b,
    exec (S d) (subst (rargs d args) (invert (Γ p))) a b -> exec d (Uncall p args) a b

with lp : nat -> expr -> stmt -> stmt -> expr -> store -> store -> Prop :=
| L_one  : forall d e1 s1 s2 e2 a b,
    exec d s1 a b -> eval d b e2 <> 0 -> lp d e1 s1 s2 e2 a b
| L_more : forall d e1 s1 s2 e2 a a1 a2 b,
    exec d s1 a a1 -> eval d a1 e2 = 0 ->
    exec d s2 a1 a2 -> eval d a2 e1 = 0 ->
    lp d e1 s1 s2 e2 a2 b -> lp d e1 s1 s2 e2 a b.

Scheme exec_mut := Induction for exec Sort Prop
  with lp_mut   := Induction for lp   Sort Prop.

Lemma lp_exit_true : forall d e1 s1 s2 e2 a b, lp d e1 s1 s2 e2 a b -> eval d b e2 <> 0.
Proof. intros until b; intro H; induction H; assumption. Qed.

(* an "open" run of the loop body, used to reverse a [lp] derivation *)
Inductive opn (d : nat) (e1 : expr) (s1 s2 : stmt) (e2 : expr) : store -> store -> Prop :=
| O_nil  : forall a, opn d e1 s1 s2 e2 a a
| O_cons : forall a a1 a2 b,
    exec d s1 a a1 -> eval d a1 e2 = 0 -> exec d s2 a1 a2 -> eval d a2 e1 = 0 ->
    opn d e1 s1 s2 e2 a2 b -> opn d e1 s1 s2 e2 a b.

Lemma opn_snoc : forall d e1 s1 s2 e2 a m m1 m2,
  opn d e1 s1 s2 e2 a m -> exec d s1 m m1 -> eval d m1 e2 = 0 ->
  exec d s2 m1 m2 -> eval d m2 e1 = 0 -> opn d e1 s1 s2 e2 a m2.
Proof. intros d e1 s1 s2 e2 a m m1 m2 H; revert m1 m2.
  induction H; intros m1 m2 Hs1 He2 Hs2 He1.
  - eapply O_cons; eauto. apply O_nil.
  - eapply O_cons; eauto. Qed.

Lemma opn_to_lp : forall d e1 s1 s2 e2 a m b,
  opn d e1 s1 s2 e2 a m -> exec d s1 m b -> eval d b e2 <> 0 -> lp d e1 s1 s2 e2 a b.
Proof. intros d e1 s1 s2 e2 a m b H; induction H; intros Hs1 Hex.
  - apply L_one; assumption.
  - eapply L_more; eauto. Qed.

(* ---------- reversibility ---------- *)

(* per-statement reversibility, factored out so exec_rev's bullets stay robust. *)
Lemma asn_rev : forall d r o e s, wf_asn d r e = true ->
  exec d (Asn r (ainv o) e) (update s (loc_of_ref d r) (app o (s (loc_of_ref d r)) (eval d s e))) s.
Proof.
  intros d r o e s W. unfold wf_asn in W; apply negb_true_iff in W.
  cut (exec d (Asn r (ainv o) e) (update s (loc_of_ref d r) (app o (s (loc_of_ref d r)) (eval d s e)))
        (update (update s (loc_of_ref d r) (app o (s (loc_of_ref d r)) (eval d s e))) (loc_of_ref d r)
          (app (ainv o) (update s (loc_of_ref d r) (app o (s (loc_of_ref d r)) (eval d s e)) (loc_of_ref d r))
            (eval d (update s (loc_of_ref d r) (app o (s (loc_of_ref d r)) (eval d s e))) e)))).
  - intro Hc; rewrite (asn_inv_store d r o e s W) in Hc; exact Hc.
  - apply E_Asn; unfold wf_asn; now apply negb_true_iff.
Qed.

Lemma aasn_rev : forall d r idx o e s, wf_aasn d s r idx e = true ->
  exec d (AAsn r idx (ainv o) e)
    (update s (acell d r (eval d s idx)) (app o (s (acell d r (eval d s idx))) (eval d s e))) s.
Proof.
  intros d r idx o e s W. unfold wf_aasn in W; apply andb_true_iff in W as [He Hi];
    apply negb_true_iff in He; apply negb_true_iff in Hi.
  cut (exec d (AAsn r idx (ainv o) e)
        (update s (acell d r (eval d s idx)) (app o (s (acell d r (eval d s idx))) (eval d s e)))
        (update (update s (acell d r (eval d s idx)) (app o (s (acell d r (eval d s idx))) (eval d s e)))
          (acell d r (eval d (update s (acell d r (eval d s idx)) (app o (s (acell d r (eval d s idx))) (eval d s e))) idx))
          (app (ainv o)
            (update s (acell d r (eval d s idx)) (app o (s (acell d r (eval d s idx))) (eval d s e))
              (acell d r (eval d (update s (acell d r (eval d s idx)) (app o (s (acell d r (eval d s idx))) (eval d s e))) idx)))
            (eval d (update s (acell d r (eval d s idx)) (app o (s (acell d r (eval d s idx))) (eval d s e))) e)))).
  - intro Hc; rewrite (aasn_inv_store d s r idx o e He Hi) in Hc; exact Hc.
  - apply E_AAsn; unfold wf_aasn.
    assert (Hcell : acell d r (eval d (update s (acell d r (eval d s idx)) (app o (s (acell d r (eval d s idx))) (eval d s e))) idx)
                  = acell d r (eval d s idx)) by (f_equal; apply eval_stable; exact Hi).
    rewrite Hcell; apply andb_true_iff; split; apply negb_true_iff; assumption.
Qed.

Lemma enter_rev : forall d x e s, s (L d x) = 0 -> reads d (L d x) e = false ->
  exec d (Exit x e) (update s (L d x) (eval d s e)) s.
Proof.
  intros d x e s Hz Hr.
  cut (exec d (Exit x e) (update s (L d x) (eval d s e)) (update (update s (L d x) (eval d s e)) (L d x) 0)).
  - intro Hc; replace (update (update s (L d x) (eval d s e)) (L d x) 0) with s in Hc;
      [exact Hc | rewrite update_shadow, <- Hz, update_same; reflexivity].
  - apply E_Exit; [exact Hr|]. rewrite update_eq, update_shadow, (eval_stable d (L d x) 0 s e Hr); reflexivity.
Qed.

Lemma exit_rev : forall d x e s, reads d (L d x) e = false ->
  s (L d x) = eval d (update s (L d x) 0) e -> exec d (Enter x e) (update s (L d x) 0) s.
Proof.
  intros d x e s Hr Hv.
  cut (exec d (Enter x e) (update s (L d x) 0) (update (update s (L d x) 0) (L d x) (eval d (update s (L d x) 0) e))).
  - intro Hc; replace (update (update s (L d x) 0) (L d x) (eval d (update s (L d x) 0) e)) with s in Hc;
      [exact Hc | rewrite update_shadow, <- Hv, update_same; reflexivity].
  - apply E_Enter; [apply update_eq | exact Hr].
Qed.

Theorem exec_rev : forall d s a b, exec d s a b -> exec d (invert s) b a.
Proof.
  intros d s a b H.
  induction H using exec_mut
    with (P0 := fun d e1 s1 s2 e2 a b (_ : lp d e1 s1 s2 e2 a b) =>
      exists q, opn d e2 (invert s1) (invert s2) e1 b q /\ exec d (invert s1) q a).
  - apply E_Skip.
  - cbn [invert]. apply asn_rev; assumption.
  - cbn [invert]. apply aasn_rev; assumption.
  - cbn [invert]. eapply E_Seq; eassumption.
  - cbn [invert]. apply E_IfT; assumption.
  - cbn [invert]. apply E_IfF; assumption.
  - cbn [invert]. match goal with Hx : exists _, _ |- _ => destruct Hx as [q [Hopn Hq]] end.
    apply E_Loop; [ eapply lp_exit_true; eassumption
                  | eapply opn_to_lp; [exact Hopn | exact Hq | eassumption] ].
  - cbn [invert]. apply enter_rev; assumption.
  - cbn [invert]. apply exit_rev; assumption.
  - cbn [invert]. apply E_Uncall; rewrite subst_invert; assumption.
  - cbn [invert]. apply E_Call; rewrite subst_invert, invert_invol in IHexec; exact IHexec.
  - (* L_one *) exists b; split; [apply O_nil | assumption].
  - (* L_more *) match goal with Hx : exists _, _ |- _ => destruct Hx as [q [Hopn Hq]] end.
    exists a1; split; [eapply opn_snoc; eauto | assumption].
Qed.

Corollary exec_iff : forall d s a b, exec d s a b <-> exec d (invert s) b a.
Proof.
  split; intro H; [now apply exec_rev|].
  apply exec_rev in H; now rewrite invert_invol in H.
Qed.

(* ---------- determinism ---------- *)

Theorem exec_det : forall d s a b, exec d s a b -> forall b', exec d s a b' -> b = b'.
Proof.
  intros d s a b H.
  induction H using exec_mut
    with (P0 := fun d e1 s1 s2 e2 a b (_ : lp d e1 s1 s2 e2 a b) =>
      forall b', lp d e1 s1 s2 e2 a b' -> b = b').
  - intros b' Hb'; inversion Hb'; subst; reflexivity.
  - intros b' Hb'; inversion Hb'; subst; reflexivity.
  - intros b' Hb'; inversion Hb'; subst; reflexivity.
  - intros b' Hb'; inversion Hb'; subst.
    match goal with He2 : exec d s2 ?mid b' |- _ =>
      assert (Em : m = mid) by (apply IHexec1; assumption); apply IHexec2; rewrite Em; exact He2 end.
  - intros b' Hb'; inversion Hb'; subst; [ apply IHexec; assumption | congruence ].
  - intros b' Hb'; inversion Hb'; subst; [ congruence | apply IHexec; assumption ].
  - intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - intros b' Hb'; inversion Hb'; subst; reflexivity.
  - intros b' Hb'; inversion Hb'; subst; reflexivity.
  - intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - (* L_one *) intros b' Hb'; inversion Hb'; subst.
    + apply IHexec; assumption.
    + match goal with He : eval d ?aa e2 = 0 |- _ =>
        match goal with Hx : exec d s1 a aa |- _ => apply IHexec in Hx; subst end end; congruence.
  - (* L_more *) intros b' Hb'; inversion Hb'; subst.
    + match goal with Hx : exec d s1 a b' |- _ => apply IHexec1 in Hx; subst end; congruence.
    + match goal with
      | Hi3 : lp d e1 s1 s2 e2 ?aa2 b' |- _ =>
        match goal with Hi2 : exec d s2 ?aa1 aa2 |- _ =>
          match goal with Hi1 : exec d s1 a aa1 |- _ =>
            apply IHexec1 in Hi1; subst; apply IHexec2 in Hi2; subst; apply IHexec3 in Hi3; exact Hi3
          end end
      end.
Qed.

Corollary exec_injective : forall d s a a' b, exec d s a b -> exec d s a' b -> a = a'.
Proof.
  intros d s a a' b H1 H2. apply exec_rev in H1; apply exec_rev in H2.
  eapply exec_det; eassumption.
Qed.

(* ---------- a sound fuel interpreter ---------- *)

Fixpoint run (f d : nat) (s : stmt) (st : store) {struct f} : option store :=
  match f with
  | O => None
  | S f =>
    match s with
    | Skip => Some st
    | Asn r o e => if wf_asn d r e
                   then Some (update st (loc_of_ref d r) (app o (st (loc_of_ref d r)) (eval d st e)))
                   else None
    | AAsn r idx o e => if wf_aasn d st r idx e
                        then Some (update st (acell d r (eval d st idx)) (app o (st (acell d r (eval d st idx))) (eval d st e)))
                        else None
    | Seq a b => match run f d a st with Some m => run f d b m | None => None end
    | If e1 s1 s2 e2 =>
        if negb (Z.eqb (eval d st e1) 0)
        then match run f d s1 st with
             | Some b => if negb (Z.eqb (eval d b e2) 0) then Some b else None | None => None end
        else match run f d s2 st with
             | Some b => if Z.eqb (eval d b e2) 0 then Some b else None | None => None end
    | Loop e1 s1 s2 e2 => if negb (Z.eqb (eval d st e1) 0) then runloop f d e1 s1 s2 e2 st else None
    | Enter x e => if Z.eqb (st (L d x)) 0 && negb (reads d (L d x) e)
                   then Some (update st (L d x) (eval d st e)) else None
    | Exit x e => if negb (reads d (L d x) e) && Z.eqb (st (L d x)) (eval d (update st (L d x) 0) e)
                  then Some (update st (L d x) 0) else None
    | Call p args => run f (S d) (subst (rargs d args) (Γ p)) st
    | Uncall p args => run f (S d) (subst (rargs d args) (invert (Γ p))) st
    end
  end
with runloop (f d : nat) (e1 : expr) (s1 s2 : stmt) (e2 : expr) (st : store) {struct f} : option store :=
  match f with
  | O => None
  | S f =>
    match run f d s1 st with
    | None => None
    | Some a1 =>
        if negb (Z.eqb (eval d a1 e2) 0) then Some a1
        else match run f d s2 a1 with
             | None => None
             | Some a2 => if negb (Z.eqb (eval d a2 e1) 0) then None else runloop f d e1 s1 s2 e2 a2
             end
    end
  end.

Lemma run_sound_mut : forall f,
  (forall d s st st', run f d s st = Some st' -> exec d s st st') /\
  (forall d e1 s1 s2 e2 st st', runloop f d e1 s1 s2 e2 st = Some st' -> lp d e1 s1 s2 e2 st st').
Proof.
  induction f as [|f IH].
  - split; intros; simpl in *; discriminate.
  - destruct IH as [IHr IHl]. split.
    + intros d s st st' H; destruct s; simpl in H.
      * inversion H; subst; apply E_Skip.
      * destruct (wf_asn d r e) eqn:W; [|discriminate]. inversion H; subst. now apply E_Asn.
      * destruct (wf_aasn d st r idx e) eqn:W; [|discriminate]. inversion H; subst. now apply E_AAsn.
      * destruct (run f d s1 st) as [m|] eqn:R1; [|discriminate].
        eapply E_Seq; [apply IHr; exact R1 | apply IHr; exact H].
      * destruct (negb (Z.eqb (eval d st e1) 0)) eqn:G1.
        -- destruct (run f d s1 st) as [b|] eqn:R; [|discriminate].
           destruct (negb (Z.eqb (eval d b e2) 0)) eqn:G2; [|discriminate]. inversion H; subst.
           apply E_IfT; [apply negb_true_iff, Z.eqb_neq in G1; exact G1 | apply IHr; exact R
                        | apply negb_true_iff, Z.eqb_neq in G2; exact G2].
        -- destruct (run f d s2 st) as [b|] eqn:R; [|discriminate].
           destruct (Z.eqb (eval d b e2) 0) eqn:G2; [|discriminate]. inversion H; subst.
           apply E_IfF; [ apply negb_false_iff, Z.eqb_eq in G1; exact G1 | apply IHr; exact R
                        | apply Z.eqb_eq in G2; exact G2].
      * destruct (negb (Z.eqb (eval d st e1) 0)) eqn:G1; [|discriminate].
        apply E_Loop; [apply negb_true_iff, Z.eqb_neq in G1; exact G1 | apply IHl; exact H].
      * destruct (Z.eqb (st (L d x)) 0 && negb (reads d (L d x) e)) eqn:E; [|discriminate].
        apply andb_true_iff in E as [E1 E2]. inversion H; subst.
        apply E_Enter; [now apply Z.eqb_eq in E1 | now apply negb_true_iff in E2].
      * destruct (negb (reads d (L d x) e) && Z.eqb (st (L d x)) (eval d (update st (L d x) 0) e)) eqn:E; [|discriminate].
        apply andb_true_iff in E as [E1 E2]. inversion H; subst.
        apply E_Exit; [now apply negb_true_iff in E1 | now apply Z.eqb_eq in E2].
      * apply E_Call; apply IHr; exact H.
      * apply E_Uncall; apply IHr; exact H.
    + intros d e1 s1 s2 e2 st st' H; simpl in H.
      destruct (run f d s1 st) as [a1|] eqn:R1; [|discriminate].
      destruct (negb (Z.eqb (eval d a1 e2) 0)) eqn:Ex.
      * inversion H; subst. apply L_one; [apply IHr; exact R1 | apply negb_true_iff, Z.eqb_neq in Ex; exact Ex].
      * destruct (run f d s2 a1) as [a2|] eqn:R2; [|discriminate].
        destruct (negb (Z.eqb (eval d a2 e1) 0)) eqn:Ec; [discriminate|].
        eapply L_more;
          [ apply IHr; exact R1 | apply negb_false_iff, Z.eqb_eq in Ex; exact Ex
          | apply IHr; exact R2 | apply negb_false_iff, Z.eqb_eq in Ec; exact Ec | apply IHl; exact H ].
Qed.

Theorem run_sound : forall f d s st st', run f d s st = Some st' -> exec d s st st'.
Proof. intro f; apply (proj1 (run_sound_mut f)). Qed.

End Sem.

(* ---------- operational check: frames stop locals aliasing across a call ----

   [demo] enters local 0 at depth 0, then calls [g] which *also* enters local 0
   — at depth 1, a fresh slot.  In the old flat model both would hit the same
   [LS 0], so the inner [Enter]'s dead-cell precondition would fail and [run]
   would return [None].  With depth-indexed locals the inner local is [L 1 0]
   (fresh), so [run] succeeds and restores the store. *)

Definition demoΓ : nat -> stmt := fun _ => Seq (Enter 0 (Cst 5)) (Exit 0 (Cst 5)).
Definition demo : stmt := Seq (Enter 0 (Cst 3)) (Seq (Call 0 []) (Exit 0 (Cst 3))).

Example frames_avoid_local_alias :
  match run demoΓ 50 0 demo (fun _ => 0) with Some _ => True | None => False end.
Proof. exact I. Qed.

(* run is sound w.r.t. the relation, so this is a real [exec] derivation: *)
Example demo_runs : exists b, exec demoΓ 0 demo (fun _ => 0) b.
Proof. eexists. apply (run_sound demoΓ 50). vm_compute. reflexivity. Qed.
