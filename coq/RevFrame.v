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

Inductive aop := OAdd | OSub.
Definition app (o : aop) (a b : Z) : Z := match o with OAdd => a + b | OSub => a - b end.
Definition ainv (o : aop) : aop := match o with OAdd => OSub | OSub => OAdd end.

Inductive expr := Cst (z : Z) | Rd (r : ref) | Bin (o : aop) (a b : expr).

Inductive stmt :=
| Skip
| Asn (r : ref) (o : aop) (e : expr)
| Seq (s1 s2 : stmt)
| If (e1 : expr) (s1 s2 : stmt) (e2 : expr)
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
  | Bin o a b => app o (eval d s a) (eval d s b)
  end.

(* does [e] read location [l] at depth [d]? — exact occurrence check *)
Fixpoint reads (d : nat) (l : loc) (e : expr) : bool :=
  match e with
  | Cst _ => false
  | Rd r => loceqb (loc_of_ref d r) l
  | Bin _ a b => reads d l a || reads d l b
  end.

Lemma eval_stable : forall d l v s e, reads d l e = false -> eval d (update s l v) e = eval d s e.
Proof.
  intros d l v s; induction e as [z | r | o e1 IH1 e2 IH2]; intro H; simpl in *.
  - reflexivity.
  - apply update_neq; rewrite loceqb_sym; exact H.
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
    by (destruct o; simpl; lia).
  rewrite update_shadow, update_same; reflexivity.
Qed.

(* ---------- inversion ---------- *)

Fixpoint invert (s : stmt) : stmt :=
  match s with
  | Skip => Skip
  | Asn r o e => Asn r (ainv o) e
  | Seq a b => Seq (invert b) (invert a)
  | If e1 s1 s2 e2 => If e2 (invert s1) (invert s2) e1
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
  match e with Cst z => Cst z | Rd r => Rd (subst1 nms r) | Bin o a b => Bin o (sexpr nms a) (sexpr nms b) end.

Fixpoint subst (nms : list nm) (s : stmt) : stmt :=
  match s with
  | Skip => Skip
  | Asn r o e => Asn (subst1 nms r) o (sexpr nms e)
  | Seq a b => Seq (subst nms a) (subst nms b)
  | If e1 s1 s2 e2 => If (sexpr nms e1) (subst nms s1) (subst nms s2) (sexpr nms e2)
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
| E_Seq  : forall d s1 s2 a m b, exec d s1 a m -> exec d s2 m b -> exec d (Seq s1 s2) a b
| E_IfT  : forall d e1 s1 s2 e2 a b,
    eval d a e1 <> 0 -> exec d s1 a b -> eval d b e2 <> 0 -> exec d (If e1 s1 s2 e2) a b
| E_IfF  : forall d e1 s1 s2 e2 a b,
    eval d a e1 =  0 -> exec d s2 a b -> eval d b e2 =  0 -> exec d (If e1 s1 s2 e2) a b
| E_Enter : forall d x e s, s (L d x) = 0 -> reads d (L d x) e = false ->
    exec d (Enter x e) s (update s (L d x) (eval d s e))
| E_Exit  : forall d x e s, reads d (L d x) e = false -> s (L d x) = eval d (update s (L d x) 0) e ->
    exec d (Exit x e) s (update s (L d x) 0)
| E_Call  : forall d p args a b,
    exec (S d) (subst (rargs d args) (Γ p)) a b -> exec d (Call p args) a b
| E_Uncall : forall d p args a b,
    exec (S d) (subst (rargs d args) (invert (Γ p))) a b -> exec d (Uncall p args) a b.

(* ---------- reversibility ---------- *)

Theorem exec_rev : forall d s a b, exec d s a b -> exec d (invert s) b a.
Proof.
  intros d s a b H; induction H; simpl.
  - apply E_Skip.
  - (* Asn -> Asn with the inverse operator *)
    unfold wf_asn in H; apply negb_true_iff in H.
    cut (exec d (Asn r (ainv o) e)
          (update s (loc_of_ref d r) (app o (s (loc_of_ref d r)) (eval d s e)))
          (update (update s (loc_of_ref d r) (app o (s (loc_of_ref d r)) (eval d s e)))
                  (loc_of_ref d r)
                  (app (ainv o)
                       (update s (loc_of_ref d r) (app o (s (loc_of_ref d r)) (eval d s e)) (loc_of_ref d r))
                       (eval d (update s (loc_of_ref d r) (app o (s (loc_of_ref d r)) (eval d s e))) e)))).
    + intro Hc; rewrite (asn_inv_store d r o e s H) in Hc; exact Hc.
    + apply E_Asn; unfold wf_asn; now apply negb_true_iff.
  - eapply E_Seq; eassumption.
  - eapply E_IfT; eassumption.
  - eapply E_IfF; eassumption.
  - (* Enter -> Exit *)
    cut (exec d (Exit x e) (update s (L d x) (eval d s e))
           (update (update s (L d x) (eval d s e)) (L d x) 0)).
    + intro Hc.
      replace (update (update s (L d x) (eval d s e)) (L d x) 0) with s in Hc;
        [exact Hc | rewrite update_shadow, <- H, update_same; reflexivity].
    + apply E_Exit; [exact H0|].
      rewrite update_eq, update_shadow, (eval_stable d (L d x) 0 s e H0); reflexivity.
  - (* Exit -> Enter *)
    cut (exec d (Enter x e) (update s (L d x) 0)
           (update (update s (L d x) 0) (L d x) (eval d (update s (L d x) 0) e))).
    + intro Hc.
      replace (update (update s (L d x) 0) (L d x) (eval d (update s (L d x) 0) e)) with s in Hc;
        [exact Hc | rewrite update_shadow, <- H0, update_same; reflexivity].
    + apply E_Enter; [apply update_eq | exact H].
  - apply E_Uncall; rewrite subst_invert; exact IHexec.
  - apply E_Call; rewrite subst_invert, invert_invol in IHexec; exact IHexec.
Qed.

Corollary exec_iff : forall d s a b, exec d s a b <-> exec d (invert s) b a.
Proof.
  split; intro H; [now apply exec_rev|].
  apply exec_rev in H; now rewrite invert_invol in H.
Qed.

(* ---------- determinism ---------- *)

Theorem exec_det : forall d s a b, exec d s a b -> forall b', exec d s a b' -> b = b'.
Proof.
  intros d s a b H; induction H; intros b' H'; inversion H'; subst;
    try reflexivity;
    try (exfalso; congruence);
    try (now apply IHexec).
  - (* Seq *) assert (m = m0) by (apply IHexec1; assumption); subst; now apply IHexec2.
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
    | Seq a b => match run f d a st with Some m => run f d b m | None => None end
    | If e1 s1 s2 e2 =>
        if negb (Z.eqb (eval d st e1) 0)
        then match run f d s1 st with
             | Some b => if negb (Z.eqb (eval d b e2) 0) then Some b else None | None => None end
        else match run f d s2 st with
             | Some b => if Z.eqb (eval d b e2) 0 then Some b else None | None => None end
    | Enter x e => if Z.eqb (st (L d x)) 0 && negb (reads d (L d x) e)
                   then Some (update st (L d x) (eval d st e)) else None
    | Exit x e => if negb (reads d (L d x) e) && Z.eqb (st (L d x)) (eval d (update st (L d x) 0) e)
                  then Some (update st (L d x) 0) else None
    | Call p args => run f (S d) (subst (rargs d args) (Γ p)) st
    | Uncall p args => run f (S d) (subst (rargs d args) (invert (Γ p))) st
    end
  end.

Theorem run_sound : forall f d s st st', run f d s st = Some st' -> exec d s st st'.
Proof.
  induction f as [|f IH]; intros d s st st' H; [discriminate|].
  destruct s; simpl in H.
  - inversion H; subst; apply E_Skip.
  - destruct (wf_asn d r e) eqn:W; [|discriminate]. inversion H; subst. now apply E_Asn.
  - destruct (run f d s1 st) as [m|] eqn:R1; [|discriminate].
    eapply E_Seq; [apply IH; exact R1 | apply IH; exact H].
  - destruct (negb (Z.eqb (eval d st e1) 0)) eqn:G1.
    + destruct (run f d s1 st) as [b|] eqn:R; [|discriminate].
      destruct (negb (Z.eqb (eval d b e2) 0)) eqn:G2; [|discriminate]. inversion H; subst.
      apply E_IfT; [apply negb_true_iff, Z.eqb_neq in G1; exact G1 | apply IH; exact R
                   | apply negb_true_iff, Z.eqb_neq in G2; exact G2].
    + destruct (run f d s2 st) as [b|] eqn:R; [|discriminate].
      destruct (Z.eqb (eval d b e2) 0) eqn:G2; [|discriminate]. inversion H; subst.
      apply E_IfF; [ apply negb_false_iff, Z.eqb_eq in G1; exact G1 | apply IH; exact R
                   | apply Z.eqb_eq in G2; exact G2].
  - destruct (Z.eqb (st (L d x)) 0 && negb (reads d (L d x) e)) eqn:E; [|discriminate].
    apply andb_true_iff in E as [E1 E2]. inversion H; subst.
    apply E_Enter; [now apply Z.eqb_eq in E1 | now apply negb_true_iff in E2].
  - destruct (negb (reads d (L d x) e) && Z.eqb (st (L d x)) (eval d (update st (L d x) 0) e)) eqn:E; [|discriminate].
    apply andb_true_iff in E as [E1 E2]. inversion H; subst.
    apply E_Exit; [now apply negb_true_iff in E1 | now apply Z.eqb_eq in E2].
  - apply E_Call; apply IH; exact H.
  - apply E_Uncall; apply IH; exact H.
Qed.

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
