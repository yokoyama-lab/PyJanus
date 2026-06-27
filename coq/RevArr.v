(** * RevArr.v — reversible Janus with arrays (and reference procedures)

    Extends [RevProc.v] with arrays.  The store is indexed by [loc] (a scalar
    [LS x] or an array cell [LA a i]); expressions may read array cells
    ([ARd a e]); an assignment targets an l-value [lv] (a scalar or a cell with a
    *dynamic* index).  Procedures still pass everything by reference via a single
    renaming [σ : nat -> nat] (scalar and array ids live in one namespace),
    reusing [RevProc]'s machinery unchanged.

    The reversibility side condition is the usual Janus one, made syntactic on
    *names*: [x op= e] / [A[i] op= e] is admissible when the written name does
    not occur in [e] (nor, for arrays, in the index [i]) — see [wf_assign].
    Under that condition the update does not disturb [e] or the index
    ([eval_upd]), so the inverse recovers the input.  (Swap is kept scalar-only
    to avoid index-stability bookkeeping; array-element swap is out of scope.) *)

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
Import ListNotations.
Open Scope Z_scope.

(* ************************************************************************* *)
(** ** Locations, names, store. *)
Definition var := nat.
Inductive loc := LS (x : var) | LA (a : var) (i : Z).
Inductive nm  := NS (x : var) | NA (a : var).

Definition loc_eq_dec (x y : loc) : {x = y} + {x <> y}.
Proof. decide equality; (apply Z.eq_dec || apply Nat.eq_dec). Defined.
Definition loceqb (l m : loc) : bool := if loc_eq_dec l m then true else false.
Lemma loceqb_refl : forall l, loceqb l l = true.
Proof. intro l; unfold loceqb; destruct (loc_eq_dec l l); [reflexivity | contradiction]. Qed.
Lemma loceqb_true : forall l m, loceqb l m = true -> l = m.
Proof. intros l m; unfold loceqb; destruct (loc_eq_dec l m); [auto | discriminate]. Qed.

Definition nameof (l : loc) : nm := match l with LS x => NS x | LA a _ => NA a end.

Definition store := loc -> Z.
Definition update (s : store) (l : loc) (v : Z) : store :=
  fun m => if loceqb l m then v else s m.
Lemma update_eq : forall s l v, update s l v l = v.
Proof. intros; unfold update; rewrite loceqb_refl; reflexivity. Qed.
Lemma update_shadow : forall s l a b, update (update s l a) l b = update s l b.
Proof. intros; apply functional_extensionality; intro m; unfold update;
  destruct (loceqb l m); reflexivity. Qed.
Lemma update_same : forall s l, update s l (s l) = s.
Proof. intros; apply functional_extensionality; intro m; unfold update;
  destruct (loceqb l m) eqn:E; [apply loceqb_true in E; subst; reflexivity | reflexivity]. Qed.

Definition sw (s : store) (l1 l2 : loc) : store :=
  update (update s l1 (s l2)) l2 (s l1).
Lemma sw_invol : forall s l1 l2, sw (sw s l1 l2) l1 l2 = s.
Proof.
  intros s l1 l2; apply functional_extensionality; intro m; unfold sw, update.
  destruct (loceqb l2 m) eqn:H2.
  - apply loceqb_true in H2; subst m.
    destruct (loceqb l2 l1) eqn:H21.
    + apply loceqb_true in H21; subst l1; reflexivity.
    + rewrite loceqb_refl; reflexivity.
  - destruct (loceqb l1 m) eqn:H1.
    + rewrite loceqb_refl. apply loceqb_true in H1; subst l1; reflexivity.
    + reflexivity.
Qed.

(* ************************************************************************* *)
(** ** Reversible operators (as before). *)
Inductive binop := OAdd | OSub | OMul | OEq | OLt | ODiv | OMod | OXor | OAnd | OOr.
Definition denote (o : binop) (a b : Z) : Z :=
  match o with OAdd => a + b | OSub => a - b | OMul => a * b
    | OEq => if Z.eqb a b then 1 else 0 | OLt => if Z.ltb a b then 1 else 0
    | ODiv => Z.div a b | OMod => Z.modulo a b
    | OXor => Z.lxor a b | OAnd => Z.land a b | OOr => Z.lor a b end.
(* bitwise operators denote like PyJanus's & | ^ : 12 (1100), 10 (1010) *)
Example denote_bitwise :
  denote OAnd 12 10 = 8 /\ denote OOr 12 10 = 14 /\ denote OXor 12 10 = 6.
Proof. repeat split; reflexivity. Qed.
Inductive aop := AAdd | ASub | AXor.
Definition adenote (o : aop) (a b : Z) : Z :=
  match o with AAdd => a + b | ASub => a - b | AXor => Z.lxor a b end.
Definition ainv (o : aop) : aop :=
  match o with AAdd => ASub | ASub => AAdd | AXor => AXor end.
Lemma ainv_invol : forall o, ainv (ainv o) = o.
Proof. destruct o; reflexivity. Qed.
Lemma ainv_correct : forall o a b, adenote (ainv o) (adenote o a b) b = a.
Proof. destruct o; intros a b; simpl; try lia.
  rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r; reflexivity. Qed.

(* ************************************************************************* *)
(** ** Expressions (with array reads) and l-values. *)
Inductive expr :=
| Cst (n : Z) | Var (x : var) | ARd (a : var) (idx : expr) | Bin (o : binop) (e1 e2 : expr).
Inductive lv := LVs (x : var) | LVa (a : var) (idx : expr).

Fixpoint eval (s : store) (e : expr) : Z :=
  match e with
  | Cst n => n
  | Var x => s (LS x)
  | ARd a idx => s (LA a (eval s idx))
  | Bin o e1 e2 => denote o (eval s e1) (eval s e2)
  end.
Definition lloc (s : store) (l : lv) : loc :=
  match l with LVs x => LS x | LVa a idx => LA a (eval s idx) end.
Definition base (l : lv) : nm := match l with LVs x => NS x | LVa a _ => NA a end.
Lemma nameof_lloc : forall s l, nameof (lloc s l) = base l.
Proof. intros s [x|a idx]; reflexivity. Qed.

Definition nmeqb (n m : nm) : bool :=
  match n, m with NS x, NS y => Nat.eqb x y | NA x, NA y => Nat.eqb x y | _, _ => false end.

Fixpoint occ (n : nm) (e : expr) : bool :=
  match e with
  | Cst _ => false
  | Var x => nmeqb n (NS x)
  | ARd a idx => nmeqb n (NA a) || occ n idx
  | Bin _ e1 e2 => occ n e1 || occ n e2
  end.

(** Updating a location whose name does not occur in [e] cannot change [e]. *)
Lemma eval_upd : forall l v s e, occ (nameof l) e = false -> eval (update s l v) e = eval s e.
Proof.
  intros l v s e; revert s;
    induction e as [n | x | a idx IHidx | o e1 IHe1 e2 IHe2]; intros s H; simpl in H |- *.
  - reflexivity.
  - unfold update; destruct (loceqb l (LS x)) eqn:E; [ | reflexivity ].
    apply loceqb_true in E; subst l; simpl in H; rewrite Nat.eqb_refl in H; discriminate.
  - apply orb_false_iff in H; destruct H as [Hn Hi].
    rewrite IHidx by exact Hi.
    unfold update; destruct (loceqb l (LA a (eval s idx))) eqn:E; [ | reflexivity ].
    apply loceqb_true in E; subst l; simpl in Hn; rewrite Nat.eqb_refl in Hn; discriminate.
  - apply orb_false_iff in H; destruct H as [H1 H2].
    rewrite IHe1 by assumption; rewrite IHe2 by assumption; reflexivity.
Qed.

(** Does [e] read the *cell* [c] (in store [s])?  This is the runtime aliasing
    test Janus uses: an array update [A[i] op= e] is reversible exactly when the
    written cell is not read by [e] (nor by the index) — which, with dynamic
    indices, is a property of the store, not of names. *)
Fixpoint reads_cell (s : store) (c : loc) (e : expr) : bool :=
  match e with
  | Cst _ => false
  | Var x => loceqb c (LS x)
  | ARd a idx => loceqb c (LA a (eval s idx)) || reads_cell s c idx
  | Bin _ e1 e2 => reads_cell s c e1 || reads_cell s c e2
  end.
Definition reads_idx (s : store) (c : loc) (l : lv) : bool :=
  match l with LVs _ => false | LVa _ idx => reads_cell s c idx end.

Lemma eval_ncell : forall c v s e,
  reads_cell s c e = false -> eval (update s c v) e = eval s e.
Proof.
  intros c v s e; induction e as [n | x | a idx IH | o e1 IH1 e2 IH2]; intro H; simpl in H |- *.
  - reflexivity.
  - unfold update; rewrite H; reflexivity.
  - apply orb_false_iff in H; destruct H as [Hc Hi].
    rewrite IH by exact Hi. unfold update; rewrite Hc; reflexivity.
  - apply orb_false_iff in H; destruct H as [H1 H2]; rewrite IH1, IH2 by assumption; reflexivity.
Qed.

Lemma reads_cell_stable : forall c v s e,
  reads_cell s c e = false -> reads_cell (update s c v) c e = false.
Proof.
  intros c v s e; induction e as [n | x | a idx IH | o e1 IH1 e2 IH2]; intro H; simpl in H |- *.
  - reflexivity.
  - exact H.
  - apply orb_false_iff in H; destruct H as [Hc Hi].
    rewrite (eval_ncell c v s idx Hi), Hc, (IH Hi); reflexivity.
  - apply orb_false_iff in H; destruct H as [H1 H2]; rewrite IH1, IH2 by assumption; reflexivity.
Qed.

Lemma lloc_ncell : forall c v s l,
  reads_idx s c l = false -> lloc (update s c v) l = lloc s l.
Proof.
  intros c v s [x | a idx] H; simpl in H |- *; [ reflexivity | ].
  rewrite (eval_ncell c v s idx H); reflexivity.
Qed.

(** Admissibility (runtime Janus side condition) of an assignment. *)
Definition wf_assign (s : store) (l : lv) (e : expr) : bool :=
  negb (reads_cell s (lloc s l) e) && negb (reads_idx s (lloc s l) l).

(** Swap of two l-values is reversible when neither index reads either swapped
    name (so the swap does not move the cells being indexed). *)
Definition idxocc (n : nm) (l : lv) : bool :=
  match l with LVs _ => false | LVa _ idx => occ n idx end.
Definition wf_swap (l1 l2 : lv) : bool :=
  negb (idxocc (base l1) l1) && negb (idxocc (base l2) l1) &&
  negb (idxocc (base l1) l2) && negb (idxocc (base l2) l2).

(* ************************************************************************* *)
(** ** Syntax, renaming, inversion. *)
Definition pname := nat.
Inductive stmt :=
| Skip
| Assign (l : lv) (o : aop) (e : expr)
| Swap   (l1 l2 : lv)
| Enter  (x : var) (e : expr)        (* local int x = e   *)
| Exit   (x : var) (e : expr)        (* delocal int x = e *)
| Seq    (s1 s2 : stmt)
| If     (e1 : expr) (s1 s2 : stmt) (e2 : expr)
| Loop   (e1 : expr) (s1 s2 : stmt) (e2 : expr)
| Call   (p : pname) (args : list var)
| Uncall (p : pname) (args : list var).

Fixpoint rexpr (σ : var -> var) (e : expr) : expr :=
  match e with
  | Cst n => Cst n | Var x => Var (σ x)
  | ARd a idx => ARd (σ a) (rexpr σ idx)
  | Bin o e1 e2 => Bin o (rexpr σ e1) (rexpr σ e2)
  end.
Definition rlv (σ : var -> var) (l : lv) : lv :=
  match l with LVs x => LVs (σ x) | LVa a idx => LVa (σ a) (rexpr σ idx) end.

Fixpoint rename (σ : var -> var) (s : stmt) : stmt :=
  match s with
  | Skip => Skip
  | Assign l o e => Assign (rlv σ l) o (rexpr σ e)
  | Swap l1 l2 => Swap (rlv σ l1) (rlv σ l2)
  | Enter x e => Enter (σ x) (rexpr σ e)
  | Exit x e => Exit (σ x) (rexpr σ e)
  | Seq s1 s2 => Seq (rename σ s1) (rename σ s2)
  | If e1 s1 s2 e2 => If (rexpr σ e1) (rename σ s1) (rename σ s2) (rexpr σ e2)
  | Loop e1 s1 s2 e2 => Loop (rexpr σ e1) (rename σ s1) (rename σ s2) (rexpr σ e2)
  | Call p args => Call p (map σ args)
  | Uncall p args => Uncall p (map σ args)
  end.

Fixpoint invert (s : stmt) : stmt :=
  match s with
  | Skip => Skip
  | Assign l o e => Assign l (ainv o) e
  | Swap l1 l2 => Swap l1 l2
  | Enter x e => Exit x e
  | Exit x e => Enter x e
  | Seq s1 s2 => Seq (invert s2) (invert s1)
  | If e1 s1 s2 e2 => If e2 (invert s1) (invert s2) e1
  | Loop e1 s1 s2 e2 => Loop e2 (invert s1) (invert s2) e1
  | Call p args => Uncall p args
  | Uncall p args => Call p args
  end.

Lemma invert_invol : forall s, invert (invert s) = s.
Proof. induction s; simpl; try reflexivity;
  try (rewrite ainv_invol; reflexivity);
  rewrite IHs1, IHs2; reflexivity. Qed.

Lemma rename_invert : forall σ s, invert (rename σ s) = rename σ (invert s).
Proof. intros σ s; induction s; simpl; try reflexivity;
  rewrite IHs1, IHs2; reflexivity. Qed.

(* ************************************************************************* *)
(** ** Big-step semantics. *)
Section Sem.
Variable Γ : pname -> (list var * stmt).

Fixpoint argsubst (fs args : list var) (v : var) : var :=
  match fs, args with
  | f :: fs', a :: args' => if Nat.eqb v f then a else argsubst fs' args' v
  | _, _ => v
  end.

Inductive exec : stmt -> store -> store -> Prop :=
| E_Skip   : forall s, exec Skip s s
| E_Assign : forall l o e s,
    wf_assign s l e = true ->
    exec (Assign l o e) s (update s (lloc s l) (adenote o (s (lloc s l)) (eval s e)))
| E_Swap   : forall l1 l2 s, wf_swap l1 l2 = true ->
    exec (Swap l1 l2) s (sw s (lloc s l1) (lloc s l2))
| E_Enter  : forall x e s,
    s (LS x) = 0 -> occ (NS x) e = false ->
    exec (Enter x e) s (update s (LS x) (eval s e))
| E_Exit   : forall x e s,
    occ (NS x) e = false -> s (LS x) = eval (update s (LS x) 0) e ->
    exec (Exit x e) s (update s (LS x) 0)
| E_Seq    : forall s1 s2 a m b, exec s1 a m -> exec s2 m b -> exec (Seq s1 s2) a b
| E_IfT    : forall e1 s1 s2 e2 a b,
    eval a e1 <> 0 -> exec s1 a b -> eval b e2 <> 0 -> exec (If e1 s1 s2 e2) a b
| E_IfF    : forall e1 s1 s2 e2 a b,
    eval a e1 =  0 -> exec s2 a b -> eval b e2 =  0 -> exec (If e1 s1 s2 e2) a b
| E_Loop   : forall e1 s1 s2 e2 a b,
    eval a e1 <> 0 -> lp e1 s1 s2 e2 a b -> exec (Loop e1 s1 s2 e2) a b
| E_Call   : forall p args a b,
    exec (rename (argsubst (fst (Γ p)) args) (snd (Γ p))) a b -> exec (Call p args) a b
| E_Uncall : forall p args a b,
    exec (rename (argsubst (fst (Γ p)) args) (invert (snd (Γ p)))) a b -> exec (Uncall p args) a b

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
    exec s1 a a1 -> eval a1 e2 = 0 -> exec s2 a1 a2 -> eval a2 e1 = 0 ->
    opn e1 s1 s2 e2 a2 b -> opn e1 s1 s2 e2 a b.

Lemma opn_snoc : forall e1 s1 s2 e2 a m m1 m2,
  opn e1 s1 s2 e2 a m -> exec s1 m m1 -> eval m1 e2 = 0 ->
  exec s2 m1 m2 -> eval m2 e1 = 0 -> opn e1 s1 s2 e2 a m2.
Proof. intros e1 s1 s2 e2 a m m1 m2 H. revert m1 m2.
  induction H; intros m1 m2 Hs1 He2 Hs2 He1.
  - eapply O_cons; eauto. apply O_nil.
  - eapply O_cons; eauto. Qed.

Lemma opn_to_lp : forall e1 s1 s2 e2 a m b,
  opn e1 s1 s2 e2 a m -> exec s1 m b -> eval b e2 <> 0 -> lp e1 s1 s2 e2 a b.
Proof. intros e1 s1 s2 e2 a m b H. induction H; intros Hs1 Hex.
  - apply L_one; assumption.
  - eapply L_more; eauto. Qed.

(** Assignment is reversible (the heart of the array case). *)
Lemma assign_inv_ok : forall s l o e, wf_assign s l e = true ->
  exec (Assign l (ainv o) e)
       (update s (lloc s l) (adenote o (s (lloc s l)) (eval s e))) s.
Proof.
  intros s l o e Hwf.
  unfold wf_assign in Hwf; apply andb_true_iff in Hwf; destruct Hwf as [Hce Hci].
  apply negb_true_iff in Hce, Hci.
  assert (Hll : lloc (update s (lloc s l) (adenote o (s (lloc s l)) (eval s e))) l = lloc s l)
    by (apply lloc_ncell; exact Hci).
  assert (Hev : eval (update s (lloc s l) (adenote o (s (lloc s l)) (eval s e))) e = eval s e)
    by (apply eval_ncell; exact Hce).
  (* the inverse assignment is itself well-formed in the updated store *)
  assert (Hwf' : wf_assign (update s (lloc s l) (adenote o (s (lloc s l)) (eval s e))) l e = true).
  { unfold wf_assign; rewrite Hll; apply andb_true_iff; split; apply negb_true_iff.
    - apply reads_cell_stable; exact Hce.
    - destruct l as [x | a idx]; simpl in Hci |- *; [ reflexivity | ].
      apply reads_cell_stable; exact Hci. }
  pose proof (E_Assign l (ainv o) e _ Hwf') as Hg.
  rewrite Hll, Hev, update_eq in Hg.
  rewrite ainv_correct, update_shadow, update_same in Hg.
  exact Hg.
Qed.

(** Swapping two l-values is its own inverse when their indices are stable. *)
Lemma eval_sw : forall l1 l2 s e,
  occ (nameof l1) e = false -> occ (nameof l2) e = false ->
  eval (sw s l1 l2) e = eval s e.
Proof.
  intros l1 l2 s e H1 H2; unfold sw.
  rewrite eval_upd by exact H2. rewrite eval_upd by exact H1. reflexivity.
Qed.

Lemma lloc_sw : forall s l1 l2 l,
  match l with LVs _ => True
    | LVa _ idx => occ (nameof (lloc s l1)) idx = false
                /\ occ (nameof (lloc s l2)) idx = false end ->
  lloc (sw s (lloc s l1) (lloc s l2)) l = lloc s l.
Proof.
  intros s l1 l2 [x | a idx] H; simpl; [ reflexivity | ].
  destruct H as [Ha Hb]. rewrite (eval_sw (lloc s l1) (lloc s l2) s idx Ha Hb); reflexivity.
Qed.

Lemma swap_inv_ok : forall s l1 l2, wf_swap l1 l2 = true ->
  exec (Swap l1 l2) (sw s (lloc s l1) (lloc s l2)) s.
Proof.
  intros s l1 l2 Hwf.
  pose proof (E_Swap l1 l2 (sw s (lloc s l1) (lloc s l2)) Hwf) as Hg.
  unfold wf_swap in Hwf.
  apply andb_true_iff in Hwf; destruct Hwf as [Hwf Hd].
  apply andb_true_iff in Hwf; destruct Hwf as [Hwf Hc].
  apply andb_true_iff in Hwf; destruct Hwf as [Ha Hb].
  apply negb_true_iff in Ha, Hb, Hc, Hd.
  assert (Hl1 : lloc (sw s (lloc s l1) (lloc s l2)) l1 = lloc s l1).
  { apply lloc_sw. destruct l1 as [x | a idx]; [ exact I | ].
    rewrite !nameof_lloc; split; assumption. }
  assert (Hl2 : lloc (sw s (lloc s l1) (lloc s l2)) l2 = lloc s l2).
  { apply lloc_sw. destruct l2 as [x | a idx]; [ exact I | ].
    rewrite !nameof_lloc; split; assumption. }
  rewrite Hl1, Hl2 in Hg. rewrite sw_invol in Hg. exact Hg.
Qed.

(** Entering then exiting a local cell are mutually inverse (dead-cell model). *)
Lemma enter_inv_ok : forall s x e, s (LS x) = 0 -> occ (NS x) e = false ->
  exec (Exit x e) (update s (LS x) (eval s e)) s.
Proof.
  intros s x e Hz Hocc.
  assert (Hpop : update (update s (LS x) (eval s e)) (LS x) 0 = s).
  { rewrite update_shadow; rewrite <- Hz; apply update_same. }
  assert (Has : update s (LS x) (eval s e) (LS x)
              = eval (update (update s (LS x) (eval s e)) (LS x) 0) e).
  { rewrite update_eq, Hpop; reflexivity. }
  pose proof (E_Exit x e (update s (LS x) (eval s e)) Hocc Has) as Hg.
  rewrite Hpop in Hg; exact Hg.
Qed.

Lemma exit_inv_ok : forall s x e, occ (NS x) e = false ->
  s (LS x) = eval (update s (LS x) 0) e ->
  exec (Enter x e) (update s (LS x) 0) s.
Proof.
  intros s x e Hocc Hval.
  assert (Hz0 : update s (LS x) 0 (LS x) = 0) by apply update_eq.
  assert (Hres : update (update s (LS x) 0) (LS x) (eval (update s (LS x) 0) e) = s).
  { rewrite update_shadow, <- Hval, update_same; reflexivity. }
  pose proof (E_Enter x e (update s (LS x) 0) Hz0 Hocc) as Hg.
  rewrite Hres in Hg; exact Hg.
Qed.

Theorem exec_rev : forall s a b, exec s a b -> exec (invert s) b a.
Proof.
  intros s a b H.
  induction H using exec_mut
    with (P0 := fun e1 s1 s2 e2 a b (_ : lp e1 s1 s2 e2 a b) =>
      exists q, opn e2 (invert s1) (invert s2) e1 b q /\ exec (invert s1) q a).
  - apply E_Skip.
  - cbn [invert]. apply assign_inv_ok; assumption.
  - cbn [invert]. apply swap_inv_ok; assumption.
  - cbn [invert]. apply enter_inv_ok; assumption.
  - cbn [invert]. apply exit_inv_ok; assumption.
  - cbn [invert]. eapply E_Seq; [ exact IHexec2 | exact IHexec1 ].
  - cbn [invert]. apply E_IfT; assumption.
  - cbn [invert]. apply E_IfF; assumption.
  - cbn [invert]. destruct IHexec as [q [Hopn Hq]]. apply E_Loop.
    + eapply lp_exit_true; eassumption.
    + eapply opn_to_lp; [ exact Hopn | exact Hq | eassumption ].
  - cbn [invert]. apply E_Uncall. rewrite <- rename_invert. exact IHexec.
  - cbn [invert]. apply E_Call. rewrite <- rename_invert, invert_invol in IHexec. exact IHexec.
  - exists b. split; [ apply O_nil | assumption ].
  - match goal with H : exists _, _ |- _ => destruct H as [q [Hopn Hq]] end.
    exists a1. split; [ eapply opn_snoc; eauto | assumption ].
Qed.

Corollary exec_iff : forall s a b, exec s a b <-> exec (invert s) b a.
Proof. intros; split; intro H.
  - apply exec_rev; assumption.
  - apply exec_rev in H; rewrite invert_invol in H; assumption. Qed.

Theorem exec_det : forall s a b, exec s a b -> forall b', exec s a b' -> b = b'.
Proof.
  intros s a b H.
  induction H using exec_mut
    with (P0 := fun e1 s1 s2 e2 a b (_ : lp e1 s1 s2 e2 a b) =>
      forall b', lp e1 s1 s2 e2 a b' -> b = b').
  - intros b' Hb'; inversion Hb'; subst; reflexivity.
  - intros b' Hb'; inversion Hb'; subst; reflexivity.
  - intros b' Hb'; inversion Hb'; subst; reflexivity.
  - intros b' Hb'; inversion Hb'; subst; reflexivity.
  - intros b' Hb'; inversion Hb'; subst; reflexivity.
  - intros b' Hb'; inversion Hb'; subst.
    match goal with He2 : exec s2 ?mid b' |- _ =>
      assert (Em : m = mid) by (apply IHexec1; assumption); apply IHexec2; rewrite Em; exact He2 end.
  - intros b' Hb'; inversion Hb'; subst; [ apply IHexec; assumption | congruence ].
  - intros b' Hb'; inversion Hb'; subst; [ congruence | apply IHexec; assumption ].
  - intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - intros b' Hb'; inversion Hb'; subst.
    + apply IHexec; assumption.
    + match goal with He : eval ?aa e2 = 0 |- _ =>
        match goal with Hx : exec s1 a aa |- _ => apply IHexec in Hx; subst end end; congruence.
  - intros b' Hb'; inversion Hb'; subst.
    + match goal with Hx : exec s1 a b' |- _ => apply IHexec1 in Hx; subst end; congruence.
    + match goal with
      | Hi3 : lp e1 s1 s2 e2 ?aa2 b' |- _ =>
        match goal with Hi2 : exec s2 ?aa1 aa2 |- _ =>
          match goal with Hi1 : exec s1 a aa1 |- _ =>
            apply IHexec1 in Hi1; subst; apply IHexec2 in Hi2; subst; apply IHexec3 in Hi3; exact Hi3
          end end
      end.
Qed.

Corollary exec_injective : forall s a a' b, exec s a b -> exec s a' b -> a = a'.
Proof. intros s a a' b H1 H2. apply exec_rev in H1. apply exec_rev in H2.
  eapply exec_det; eauto. Qed.

End Sem.
