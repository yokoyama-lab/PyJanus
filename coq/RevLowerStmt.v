(** * RevLowerStmt.v — the statement lowering, and the simulation skeleton

    Increment 3 of `docs/vjanus-lowering-soundness.md`: take a source *statement*
    language end to end against a Coq reference semantics, so the remaining forms
    have a skeleton to slot into.  [RevLowerExpr.v] did the expressions; this
    file adds statements over the same scalar store:

      [lower_stmt_sound : sexec s g h -> exec 0 (lower_stmt s) (enc g) (enc h)]

    -- a **forward simulation**.  Combined with the core's [exec_det] it gives
    what vjanus actually needs ([lower_stmt_correct]): if the source semantics
    says the answer is [h], the core cannot produce anything else.

    The interesting case is the one where the lowering is *not* one-to-one.  The
    frame core has no swap primitive, so [x <=> y] becomes the XOR triple
    [x ^= y; y ^= x; x ^= y].  [RevLowering.v] proves that triple correct in
    isolation, on an abstract store; here it has to be discharged against
    [RevFrame.exec] itself, which also forces its side condition into the open:
    the triple zeroes the cell when [x = y], so the source semantics may only
    admit [x <> y].  Both implementations already agree on that (PyJanus reports
    "Identifiers `x' and `x' are aliases"; vjanus's [wf_asn] makes [x ^= x] have
    no step), and now the proof records *why* it is needed rather than leaving it
    to the aliasing checker.

    The source semantics again follows PyJanus:

      - an assignment [x op= e] requires [x] not to occur in [e] (the aliasing
        rule), [e] to have a value, and the operator to be admissible ([aok]) --
        [RevLowerExpr]'s [seval] supplies the first two;
      - a guard is true when its value is **nonzero** ([Runtime] applies
        [bool(value)] to it, so any nonzero counts -- no boolean requirement,
        unlike [&&]/[||]);
      - [if]/[fi] and [from]/[until] carry the exit assertions.

    Out of scope, as in the expression slice: arrays, structs, stacks, locals,
    procedure call/uncall.  Those need the ref-classification model, which is the
    next increment. *)

From Stdlib Require Import ZArith Bool Lia FunctionalExtensionality.
Require Import RevFrame RevLowerExpr.
Import RevFrame.
Import RevLowerExpr.
Open Scope Z_scope.

(* ===================================================================== *)
(** ** Source statements over a scalar store. *)

Definition sstore := nat -> Z.
Definition supd (g : sstore) (x : nat) (v : Z) : sstore :=
  fun n => if Nat.eqb n x then v else g n.

Lemma supd_eq : forall g x v, supd g x v x = v.
Proof. intros; unfold supd; now rewrite Nat.eqb_refl. Qed.
Lemma supd_neq : forall g x y v, x <> y -> supd g y v x = g x.
Proof.
  intros g x y v H; unfold supd.
  destruct (Nat.eqb x y) eqn:E; [ apply Nat.eqb_eq in E; contradiction | reflexivity ].
Qed.

(** Which variables an expression reads. *)
Fixpoint soccurs (x : nat) (e : sexpr) : bool :=
  match e with
  | SNum _ => false
  | SVar n => Nat.eqb x n
  | SNot e1 => soccurs x e1
  | SBin _ a b => soccurs x a || soccurs x b
  end.

Inductive sstmt :=
| TSkip
| TAsn  (x : nat) (o : aop) (e : sexpr)
| TSwap (x y : nat)
| TSeq  (a b : sstmt)
| TIf   (e1 : sexpr) (a b : sstmt) (e2 : sexpr)
| TLoop (e1 : sexpr) (a b : sstmt) (e2 : sexpr).

(** The reference semantics. *)
Inductive sexec : sstmt -> sstore -> sstore -> Prop :=
| S_Skip : forall g, sexec TSkip g g
| S_Asn  : forall g x o e v,
    soccurs x e = false -> wf e = true -> seval g e = Some v -> aok o (g x) v = true ->
    sexec (TAsn x o e) g (supd g x (app o (g x) v))
| S_Swap : forall g x y, x <> y ->
    sexec (TSwap x y) g (supd (supd g x (g y)) y (g x))
| S_Seq  : forall g m h a b, sexec a g m -> sexec b m h -> sexec (TSeq a b) g h
| S_IfT  : forall g h e1 a b e2 v1 v2,
    wf e1 = true -> seval g e1 = Some v1 -> v1 <> 0 -> sexec a g h ->
    wf e2 = true -> seval h e2 = Some v2 -> v2 <> 0 -> sexec (TIf e1 a b e2) g h
| S_IfF  : forall g h e1 a b e2 v1 v2,
    wf e1 = true -> seval g e1 = Some v1 -> v1 = 0 -> sexec b g h ->
    wf e2 = true -> seval h e2 = Some v2 -> v2 = 0 -> sexec (TIf e1 a b e2) g h
| S_Loop : forall g h e1 a b e2 v1,
    wf e1 = true -> seval g e1 = Some v1 -> v1 <> 0 -> slp e1 a b e2 g h ->
    sexec (TLoop e1 a b e2) g h

with slp : sexpr -> sstmt -> sstmt -> sexpr -> sstore -> sstore -> Prop :=
| SL_one  : forall e1 a b e2 g h v2,
    sexec a g h -> wf e2 = true -> seval h e2 = Some v2 -> v2 <> 0 ->
    slp e1 a b e2 g h
| SL_more : forall e1 a b e2 g g1 g2 h v2 v1,
    sexec a g g1 -> wf e2 = true -> seval g1 e2 = Some v2 -> v2 = 0 ->
    sexec b g1 g2 -> wf e1 = true -> seval g2 e1 = Some v1 -> v1 = 0 ->
    slp e1 a b e2 g2 h -> slp e1 a b e2 g h.

Scheme sexec_mut := Induction for sexec Sort Prop
  with slp_mut   := Induction for slp   Sort Prop.

(* ===================================================================== *)
(** ** The lowering, transcribed from [lower.ml]. *)

(** The frame core has no swap, so [x <=> y] is the XOR triple. *)
Definition lower_swap (x y : nat) : stmt :=
  Seq (Asn (RG x) OXor (Rd (RG y)))
      (Seq (Asn (RG y) OXor (Rd (RG x)))
           (Asn (RG x) OXor (Rd (RG y)))).

Fixpoint lower_stmt (s : sstmt) : stmt :=
  match s with
  | TSkip => Skip
  | TAsn x o e => Asn (RG x) o (lower e)
  | TSwap x y => lower_swap x y
  | TSeq a b => Seq (lower_stmt a) (lower_stmt b)
  | TIf e1 a b e2 => If (lower e1) (lower_stmt a) (lower_stmt b) (lower e2)
  | TLoop e1 a b e2 => Loop (lower e1) (lower_stmt a) (lower_stmt b) (lower e2)
  end.

(* ===================================================================== *)
(** ** The encoding commutes with an update. *)

Lemma enc_supd : forall g x v, update (enc g) (G x) v = enc (supd g x v).
Proof.
  intros g x v; apply functional_extensionality; intro l.
  unfold update, enc, supd; destruct l as [n|d n|a i|d a i]; simpl; try reflexivity.
  destruct (Nat.eqb x n) eqn:E.
  - apply Nat.eqb_eq in E; subst; now rewrite Nat.eqb_refl.
  - rewrite Nat.eqb_sym in E; now rewrite E.
Qed.

Lemma enc_get : forall g x, enc g (G x) = g x.
Proof. reflexivity. Qed.

(** Reading a scalar cell of the lowered expression is the source occurrence
    check -- so the core's runtime aliasing test and PyJanus's static one agree
    on this fragment. *)
Lemma reads_lower : forall g x e, reads 0 (enc g) (G x) (lower e) = soccurs x e.
Proof.
  intros g x e; induction e as [z | n | e1 IH1 | o a IHa b IHb]; simpl.
  - reflexivity.
  - reflexivity.
  - now rewrite IH1, orb_false_r.
  - destruct o; simpl; rewrite ?IHa, ?IHb;
      destruct (soccurs x a), (soccurs x b); reflexivity.
Qed.

(* ===================================================================== *)
(** ** The XOR triple realises the swap. *)

Lemma xor_cancel_l : forall a b, Z.lxor b (Z.lxor a b) = a.
Proof.
  intros a b; rewrite (Z.lxor_comm a b), <- Z.lxor_assoc,
    Z.lxor_nilpotent; reflexivity.
Qed.

Lemma xor_cancel_r : forall a b, Z.lxor (Z.lxor a b) a = b.
Proof.
  intros a b; rewrite Z.lxor_comm, <- Z.lxor_assoc, Z.lxor_nilpotent; reflexivity.
Qed.

Lemma swap_lowering : forall Γ g x y, x <> y ->
  exec Γ 0 (lower_swap x y) (enc g) (enc (supd (supd g x (g y)) y (g x))).
Proof.
  intros Γ g x y Hxy.
  assert (Hne : Nat.eqb x y = false) by (apply Nat.eqb_neq; exact Hxy).
  assert (Hne' : Nat.eqb y x = false) by (apply Nat.eqb_neq; congruence).
  (* the two intermediate source stores *)
  set (g1 := supd g x (Z.lxor (g x) (g y))).
  set (g2 := supd g1 y (g x)).
  assert (W1 : wf_asn 0 (enc g) (RG x) OXor (Rd (RG y)) = true).
  { unfold wf_asn; simpl; rewrite Hne; reflexivity. }
  eapply E_Seq with (m := enc g1).
  { assert (E := E_Asn Γ 0 (RG x) OXor (Rd (RG y)) (enc g) W1).
    simpl in E; rewrite enc_supd in E; exact E. }
  assert (Hg1x : g1 x = Z.lxor (g x) (g y)) by apply supd_eq.
  assert (Hg1y : g1 y = g y) by (apply supd_neq; congruence).
  assert (W2 : wf_asn 0 (enc g1) (RG y) OXor (Rd (RG x)) = true).
  { unfold wf_asn; simpl; rewrite Hne'; reflexivity. }
  eapply E_Seq with (m := enc g2).
  { assert (E := E_Asn Γ 0 (RG y) OXor (Rd (RG x)) (enc g1) W2).
    simpl in E; rewrite enc_supd in E.
    replace (Z.lxor (g1 y) (g1 x)) with (g x) in E; [ exact E | ].
    rewrite Hg1x, Hg1y; symmetry; apply xor_cancel_l. }
  assert (Hg2x : g2 x = Z.lxor (g x) (g y))
    by (unfold g2; rewrite supd_neq; [ exact Hg1x | congruence ]).
  assert (Hg2y : g2 y = g x) by apply supd_eq.
  assert (W3 : wf_asn 0 (enc g2) (RG x) OXor (Rd (RG y)) = true).
  { unfold wf_asn; simpl; rewrite Hne; reflexivity. }
  assert (E := E_Asn Γ 0 (RG x) OXor (Rd (RG y)) (enc g2) W3).
  simpl in E; rewrite enc_supd in E.
  replace (Z.lxor (g2 x) (g2 y)) with (g y) in E.
  - (* the resulting source store is the swap *)
    replace (supd g2 x (g y)) with (supd (supd g x (g y)) y (g x)) in E;
      [ exact E | ].
    apply functional_extensionality; intro n.
    unfold g2, g1, supd; destruct (Nat.eqb n x) eqn:Ex; destruct (Nat.eqb n y) eqn:Ey;
      try reflexivity.
    apply Nat.eqb_eq in Ex; apply Nat.eqb_eq in Ey; subst; contradiction.
  - rewrite Hg2x, Hg2y; symmetry; apply xor_cancel_r.
Qed.

(* ===================================================================== *)
(** ** Forward simulation. *)

(* discharge a lowered guard from the source's [seval] premise *)
Ltac eval_guard :=
  match goal with
  | W : wf ?E = true, H : seval ?G ?E = Some ?V
    |- context[eval 0 (enc ?G) (lower ?E)] =>
      rewrite (lower_expr_sound G E V W H)
  end.

Theorem lower_stmt_sound : forall Γ s g h,
  sexec s g h -> exec Γ 0 (lower_stmt s) (enc g) (enc h).
Proof.
  intros Γ s g h H.
  induction H using sexec_mut with
    (P0 := fun e1 a b e2 g h (_ : slp e1 a b e2 g h) =>
      lp Γ 0 (lower e1) (lower_stmt a) (lower_stmt b) (lower e2) (enc g) (enc h)).
  - (* S_Skip *) apply E_Skip.
  - (* S_Asn *)
    simpl.
    assert (Hv : eval 0 (enc g) (lower e) = v)
      by (apply lower_expr_sound; assumption).
    assert (W : wf_asn 0 (enc g) (RG x) o (lower e) = true).
    { unfold wf_asn; apply andb_true_iff; split;
        [ apply andb_true_iff; split | ].
      - apply negb_true_iff; cbn [loc_of_ref]; rewrite reads_lower; assumption.
      - eapply lower_expr_safe; eassumption.
      - cbn [loc_of_ref]; rewrite enc_get, Hv; assumption. }
    assert (E := E_Asn Γ 0 (RG x) o (lower e) (enc g) W).
    cbn [loc_of_ref] in E; rewrite enc_get, Hv, enc_supd in E; exact E.
  - (* S_Swap *) apply swap_lowering; assumption.
  - (* S_Seq *) simpl; eapply E_Seq; eassumption.
  - (* S_IfT *)
    simpl; apply E_IfT.
    + eapply lower_expr_safe; eassumption.
    + eval_guard; assumption.
    + assumption.
    + eapply lower_expr_safe; eassumption.
    + eval_guard; assumption.
  - (* S_IfF *)
    simpl; apply E_IfF.
    + eapply lower_expr_safe; eassumption.
    + eval_guard; assumption.
    + assumption.
    + eapply lower_expr_safe; eassumption.
    + eval_guard; assumption.
  - (* S_Loop *)
    simpl; apply E_Loop.
    + eapply lower_expr_safe; eassumption.
    + eval_guard; assumption.
    + assumption.
  - (* SL_one *)
    apply L_one.
    + assumption.
    + eapply lower_expr_safe; eassumption.
    + eval_guard; assumption.
  - (* SL_more *)
    eapply L_more.
    + eassumption.
    + eapply lower_expr_safe; eassumption.
    + eval_guard; assumption.
    + eassumption.
    + eapply lower_expr_safe; eassumption.
    + eval_guard; assumption.
    + assumption.
Qed.

(* ===================================================================== *)
(** ** What vjanus needs: it cannot compute a different answer.

    Forward simulation plus the core's determinism.  If the reference semantics
    says the program takes [g] to [h], then whatever store the core reaches from
    [enc g] *is* [enc h] -- the translation cannot silently compute something
    else.  The converse is [lower_stmt_complete] below. *)

Corollary lower_stmt_correct : forall Γ s g h t,
  sexec s g h -> exec Γ 0 (lower_stmt s) (enc g) t -> t = enc h.
Proof.
  intros Γ s g h t Hs Hc.
  apply (exec_det Γ 0 (lower_stmt s) (enc g) t Hc).
  apply lower_stmt_sound; exact Hs.
Qed.

(** And the lowered program is reversible, for free, from the core. *)
Corollary lower_stmt_reversible : forall Γ s g h,
  sexec s g h -> exec Γ 0 (invert (lower_stmt s)) (enc h) (enc g).
Proof.
  intros Γ s g h H; apply exec_rev, lower_stmt_sound; exact H.
Qed.

(* ===================================================================== *)
(** ** The side condition the swap encoding forces.

    [x <=> x] is harmless in the source (it is the identity), but the XOR triple
    zeroes the cell.  The source semantics above therefore admits [TSwap x y]
    only for [x <> y], and both implementations agree: PyJanus rejects it as an
    alias, and the core's [wf_asn] gives [x ^= x] no step.  This example pins the
    encoding's failure mode so the side condition cannot be dropped by mistake. *)

Example self_swap_would_zero : forall g x,
  eval 0 (enc g) (Rd (RG x)) = g x /\
  app OXor (g x) (g x) = 0.
Proof. intros; split; [ reflexivity | apply Z.lxor_nilpotent ]. Qed.

Example self_swap_has_no_step : forall g x,
  wf_asn 0 (enc g) (RG x) OXor (Rd (RG x)) = false.
Proof.
  intros g x; unfold wf_asn; simpl; rewrite Nat.eqb_refl; reflexivity.
Qed.

(* ===================================================================== *)
(** ** The other direction: the core cannot run what the source cannot.

    [lower_stmt_sound] says a source run is realised by the core.  Its converse
    rules out the opposite failure -- vjanus *accepting* a program the reference
    semantics rejects -- and it is not automatic, because the core sees only the
    translated form.  Anything the source checks and the translation erases has
    to be recovered, and getting this direction to go through is exactly what
    exposed the two lowering bugs:

      - a zero divisor is recovered from [RevFrame.safe], which the core carries
        only because of the first fix (before it, [BDiv] was total and the core
        simply ran where the source errored);
      - the boolean restriction on [&&]/[||]/[!] is **not recoverable at all**:
        the lowering erases it ([&&] becomes [BMul]).  So it has to be a
        hypothesis, [wfs s] -- and `lower.ml` now enforces exactly that check
        statically, which is the second fix. *)

Fixpoint wfs (s : sstmt) : bool :=
  match s with
  | TSkip => true
  | TAsn _ _ e => wf e
  | TSwap _ _ => true
  | TSeq a b => wfs a && wfs b
  | TIf e1 a b e2 => wf e1 && wf e2 && wfs a && wfs b
  | TLoop e1 a b e2 => wf e1 && wf e2 && wfs a && wfs b
  end.

(** The core's safety guard is the source's definedness: an expression the core
    is willing to evaluate is one the source gives a value to.  (With the
    syntactic boolean rule, division is [seval]'s only way to fail.) *)
Lemma seval_defined : forall g e,
  wf e = true -> safe 0 (enc g) (lower e) = true -> exists v, seval g e = Some v.
Proof.
  intros g e; induction e as [z | n | e1 IH1 | o a IHa b IHb]; intros Hw Hs.
  - exists z; reflexivity.
  - exists (g n); reflexivity.
  - simpl in Hw; apply andb_true_iff in Hw as [_ Hw].
    simpl in Hs; rewrite ?andb_true_r in Hs.
    destruct (IH1 Hw Hs) as [v1 E1].
    exists (b2z (Z.eqb v1 0)); simpl; now rewrite E1.
  - simpl in Hw; apply andb_true_iff in Hw as [Hw Hwb];
      apply andb_true_iff in Hw as [_ Hwa].
    assert (Hab : safe 0 (enc g) (lower a) = true /\ safe 0 (enc g) (lower b) = true).
    { destruct o; simpl in Hs;
        repeat (apply andb_true_iff in Hs as [Hs ?]); split; assumption. }
    destruct Hab as [Sa Sb].
    destruct (IHa Hwa Sa) as [va Ea]; destruct (IHb Hwb Sb) as [vb Eb].
    assert (Vb : eval 0 (enc g) (lower b) = vb)
      by (apply lower_expr_sound; assumption).
    destruct o; simpl; rewrite Ea, Eb; simpl;
      try (eexists; reflexivity).
    + (* SDiv *) simpl in Hs; rewrite Vb in Hs.
      repeat (apply andb_true_iff in Hs as [_ Hs]).
      apply negb_true_iff in Hs; rewrite Hs; eexists; reflexivity.
    + (* SMod *) simpl in Hs; rewrite Vb in Hs.
      repeat (apply andb_true_iff in Hs as [_ Hs]).
      apply negb_true_iff in Hs; rewrite Hs; eexists; reflexivity.
Qed.

(** One turn of the loop, generalised so the induction on the core derivation
    keeps its indices abstract. *)
Lemma lp_complete : forall Γ d E1 A B E2 u t,
  lp Γ d E1 A B E2 u t ->
  forall e1 a b e2 g,
    d = 0%nat ->
    E1 = lower e1 -> A = lower_stmt a -> B = lower_stmt b -> E2 = lower e2 ->
    u = enc g -> wf e1 = true -> wf e2 = true ->
    (forall g' t', exec Γ 0 (lower_stmt a) (enc g') t' ->
                   exists h, t' = enc h /\ sexec a g' h) ->
    (forall g' t', exec Γ 0 (lower_stmt b) (enc g') t' ->
                   exists h, t' = enc h /\ sexec b g' h) ->
    exists h, t = enc h /\ slp e1 a b e2 g h.
Proof.
  intros Γ d E1 A B E2 u t H.
  induction H; intros f1 sa sb f2 gg Hd HE1 HA HB HE2 Hu W1 W2 IHa IHb; subst.
  - (* L_one *)
    destruct (IHa gg b H) as [h [Hb Hsa]]; subst b.
    match goal with S : safe 0 (enc h) (lower f2) = true |- _ =>
      destruct (seval_defined h f2 W2 S) as [v2 E2v] end.
    exists h; split; [ reflexivity | ].
    eapply SL_one; [ exact Hsa | exact W2 | exact E2v | ].
    rewrite <- (lower_expr_sound h f2 v2 W2 E2v); assumption.
  - (* L_more *)
    match goal with HA : exec Γ 0 (lower_stmt sa) (enc gg) ?m |- _ =>
      destruct (IHa gg m HA) as [h1 [Hb1 Hsa]]; subst m end.
    match goal with S : safe 0 (enc h1) (lower f2) = true |- _ =>
      destruct (seval_defined h1 f2 W2 S) as [v2 E2v] end.
    match goal with HB : exec Γ 0 (lower_stmt sb) (enc h1) ?m |- _ =>
      destruct (IHb h1 m HB) as [h2 [Hb2 Hsb]]; subst m end.
    match goal with S : safe 0 (enc h2) (lower f1) = true |- _ =>
      destruct (seval_defined h2 f1 W1 S) as [v1 E1v] end.
    destruct (IHlp f1 sa sb f2 h2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                W1 W2 IHa IHb) as [h [Hbt Hrest]]; subst.
    exists h; split; [ reflexivity | ].
    eapply SL_more with (g1 := h1) (g2 := h2) (v2 := v2) (v1 := v1).
    + exact Hsa.
    + exact W2.
    + exact E2v.
    + rewrite <- (lower_expr_sound h1 f2 v2 W2 E2v); assumption.
    + exact Hsb.
    + exact W1.
    + exact E1v.
    + rewrite <- (lower_expr_sound h2 f1 v1 W1 E1v); assumption.
    + exact Hrest.
Qed.

Theorem lower_stmt_complete : forall Γ s g t,
  wfs s = true -> exec Γ 0 (lower_stmt s) (enc g) t ->
  exists h, t = enc h /\ sexec s g h.
Proof.
  intros Γ s; induction s as [ | x o e | x y | a IHa b IHb
                             | e1 a IHa b IHb e2 | e1 a IHa b IHb e2 ];
    intros g t Hw Hex; simpl in Hw, Hex.
  - (* TSkip *) inversion Hex; subst; exists g; split; [reflexivity | apply S_Skip].
  - (* TAsn *)
    inversion Hex; subst.
    match goal with W : wf_asn _ _ _ _ _ = true |- _ =>
      rename W into Wa end.
    assert (Wa' := Wa); unfold wf_asn in Wa'.
    apply andb_true_iff in Wa' as [Wa' Hok]; apply andb_true_iff in Wa' as [Wr Hsf].
    cbn [loc_of_ref] in Wr, Hsf, Hok.
    apply negb_true_iff in Wr; rewrite reads_lower in Wr.
    destruct (seval_defined g e Hw Hsf) as [v Ev].
    assert (Hv : eval 0 (enc g) (lower e) = v) by (apply lower_expr_sound; assumption).
    rewrite Hv, enc_get in Hok.
    exists (supd g x (app o (g x) v)); split.
    + cbn [loc_of_ref]; rewrite Hv, enc_get, enc_supd; reflexivity.
    + apply S_Asn; assumption.
  - (* TSwap *)
    assert (Hxy : x <> y).
    { inversion Hex; subst.
      match goal with HA : exec _ _ (Asn _ _ _) _ _ |- _ => inversion HA; subst end.
      match goal with W : wf_asn _ _ _ _ _ = true |- _ =>
        unfold wf_asn in W; cbn [loc_of_ref reads loceqb] in W;
        apply andb_true_iff in W as [W _]; apply andb_true_iff in W as [W _];
        apply negb_true_iff, Nat.eqb_neq in W; exact W end. }
    exists (supd (supd g x (g y)) y (g x)); split.
    + eapply exec_det; [ exact Hex | apply swap_lowering; exact Hxy ].
    + apply S_Swap; exact Hxy.
  - (* TSeq *)
    apply andb_true_iff in Hw as [Hwa Hwb].
    inversion Hex; subst.
    match goal with H1 : exec _ _ (lower_stmt a) _ ?m |- _ =>
      destruct (IHa g m Hwa H1) as [h1 [-> Hsa]] end.
    match goal with H2 : exec _ _ (lower_stmt b) _ t |- _ =>
      destruct (IHb h1 t Hwb H2) as [h [-> Hsb]] end.
    exists h; split; [ reflexivity | eapply S_Seq; eassumption ].
  - (* TIf *)
    apply andb_true_iff in Hw as [Hw Hwb]; apply andb_true_iff in Hw as [Hw Hwa];
      apply andb_true_iff in Hw as [W1 W2].
    inversion Hex; subst.
    + (* took the then-branch *)
      match goal with H1 : exec _ _ (lower_stmt a) _ t |- _ =>
        destruct (IHa g t Hwa H1) as [h [-> Hsa]] end.
      destruct (seval_defined g e1 W1 ltac:(assumption)) as [v1 E1v].
      destruct (seval_defined h e2 W2 ltac:(assumption)) as [v2 E2v].
      exists h; split; [ reflexivity | ].
      eapply S_IfT; [ exact W1 | exact E1v | | exact Hsa | exact W2 | exact E2v | ].
      * rewrite <- (lower_expr_sound g e1 v1 W1 E1v); assumption.
      * rewrite <- (lower_expr_sound h e2 v2 W2 E2v); assumption.
    + (* took the else-branch *)
      match goal with H1 : exec _ _ (lower_stmt b) _ t |- _ =>
        destruct (IHb g t Hwb H1) as [h [-> Hsb]] end.
      destruct (seval_defined g e1 W1 ltac:(assumption)) as [v1 E1v].
      destruct (seval_defined h e2 W2 ltac:(assumption)) as [v2 E2v].
      exists h; split; [ reflexivity | ].
      eapply S_IfF; [ exact W1 | exact E1v | | exact Hsb | exact W2 | exact E2v | ].
      * rewrite <- (lower_expr_sound g e1 v1 W1 E1v); assumption.
      * rewrite <- (lower_expr_sound h e2 v2 W2 E2v); assumption.
  - (* TLoop *)
    apply andb_true_iff in Hw as [Hw Hwb]; apply andb_true_iff in Hw as [Hw Hwa];
      apply andb_true_iff in Hw as [W1 W2].
    inversion Hex; subst.
    destruct (seval_defined g e1 W1 ltac:(assumption)) as [v1 E1v].
    match goal with Hl : lp _ _ _ _ _ _ _ t |- _ =>
      destruct (lp_complete _ _ _ _ _ _ _ _ Hl e1 a b e2 g
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl W1 W2
                  (fun g' t' H => IHa g' t' Hwa H)
                  (fun g' t' H => IHb g' t' Hwb H)) as [h [-> Hsl]] end.
    exists h; split; [ reflexivity | ].
    eapply S_Loop; [ exact W1 | exact E1v | | exact Hsl ].
    rewrite <- (lower_expr_sound g e1 v1 W1 E1v); assumption.
Qed.

(** The two directions together: on the well-formed scalar fragment, the source
    semantics and the lowered core agree exactly. *)
Corollary lower_stmt_iff : forall Γ s g h,
  wfs s = true ->
  (sexec s g h <-> exec Γ 0 (lower_stmt s) (enc g) (enc h)).
Proof.
  intros Γ s g h Hw; split; intro H.
  - apply lower_stmt_sound; exact H.
  - destruct (lower_stmt_complete Γ s g (enc h) Hw H) as [h' [Heq Hs]].
    (* [enc] is injective on stores, so the two source stores coincide *)
    assert (h = h') as ->; [ | exact Hs ].
    apply functional_extensionality; intro n.
    change (enc h (G n) = enc h' (G n)); rewrite Heq; reflexivity.
Qed.
