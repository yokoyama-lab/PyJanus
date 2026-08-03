(** * RevSmvBlock.v — the large-block encoding of the totality checker, verified

    `docs/totality-checking.md` §5.4 records the one change that moved the
    checker's decision rate: **large-block encoding**.  A statement does not get
    its own program location; straight-line code is executed *symbolically* into
    a pending map (variable -> an expression over the values at the block's
    entry) plus a path condition, and a location is cut only where control
    actually branches.  Cutting the location count from 36 to 8 on `fall.ja`
    turned 2/8 proved into 5/8, with the same solver and the same time limit.

    That made it the largest unverified part of the encoding, and §8.4 said why
    it could not be verified where the rest was: what can go wrong in a
    large-block encoding is

      - the **composition order** of the accumulated updates -- after `v += g`,
        does `h -= v` subtract the entry value of [v] or the accumulated one? --
        and
      - the **state a path condition is evaluated in** -- a guard met halfway
        through a block is emitted as a term over the block's *entry* values,

    and neither is expressible while [prim] and [guard] are abstract.  Both are
    expressible over [RevLowerStmt.v]'s concrete [sstmt] / [sexec], which is what
    this file uses.

    The result is that one transition carrying |vars| simultaneous updates
    denotes the same relation as the sequential source semantics of the whole
    block:

      [block_sound] : sexec s g h -> forall x, seval g (p' x) = Some (h x)

    where [p'] is the pending map [sx] accumulates.  The guard question is
    [guard_at_entry]: substituting the pending map and evaluating at the entry
    store is evaluating at the current store.

    **Scope.**  This is the straight-line fragment -- [TSkip], [TAsn], [TSwap],
    [TSeq] -- which is exactly what [smv.py] accumulates into one transition;
    where it cuts a location ([_if], [_from], [_seal]) the block ends and the
    ordinary control-flow encoding takes over, which is [RevError.v]'s subject.
    The per-statement *obligations* ([aok] for `*=` and `/=`, a nonzero divisor)
    are emitted as separate ERR edges, not as part of the update, so they are
    §8/§9's subject too; here they appear as hypotheses of [sexec].

    [tests/verify/test_smv_block.py] pins [smv.py]'s emitted updates to the
    shapes proved here. *)

From Stdlib Require Import ZArith Bool Lia.
Require Import RevFrame RevLowerExpr RevLowerStmt RevSmvAlias.
Open Scope Z_scope.

(* ===================================================================== *)
(** ** The pending map.

    [smv.py]'s [self.pending] maps an SMV variable to the expression giving its
    value *at this point in the block* in terms of the values at block entry;
    [_val] reads it, defaulting to the variable itself for an entry not yet
    written. *)

Definition pmap := nat -> sexpr.
Definition pid : pmap := fun n => SVar n.
Definition pupd (p : pmap) (x : nat) (e : sexpr) : pmap :=
  fun n => if Nat.eqb n x then e else p n.

Lemma pupd_eq : forall p x e, pupd p x e x = e.
Proof. intros; unfold pupd; now rewrite Nat.eqb_refl. Qed.
Lemma pupd_neq : forall p x y e, x <> y -> pupd p y e x = p x.
Proof.
  intros p x y e H; unfold pupd.
  destruct (Nat.eqb x y) eqn:E; [ apply Nat.eqb_eq in E; contradiction | reflexivity ].
Qed.

(** [_iexpr] translating a variable emits [_val(name)], i.e. it *reads* the
    pending map -- which is why sequential composition happens as the expressions
    are built and no substitution pass over generated text is ever needed. *)
Fixpoint subst (p : pmap) (e : sexpr) : sexpr :=
  match e with
  | SNum z => SNum z
  | SVar n => p n
  | SNot e1 => SNot (subst p e1)
  | SBin o a b => SBin o (subst p a) (subst p b)
  end.

(** The four update operators [_assign] handles.  `^=` is refused
    ("assignment operator outside the fragment"), so it has no image. *)
Definition op2bin (o : aop) : option sbin :=
  match o with
  | OAdd => Some SAdd | OSub => Some SSub
  | OMul => Some SMul | ODiv => Some SDiv
  | OXor => None
  end.

(** Symbolic execution of straight-line code, transcribed from [_stmt].

    [None] is "the block compiler does not emit an ordinary transition here",
    which covers both refusals ([SmvUnsupported]: `^=`, and any statement that
    cuts a location) and the aliasing flags of [RevSmvAlias.v] (an unconditional
    edge to ERR, after which the continuation is unreachable). *)
Fixpoint sx (p : pmap) (s : sstmt) : option pmap :=
  match s with
  | TSkip => Some p
  | TAsn x o e =>
      if soccurs x e then None                      (* the aliasing flag *)
      else match op2bin o with
           | Some bo => Some (pupd p x (SBin bo (p x) (subst p e)))
           | None => None
           end
  | TSwap x y =>
      if Nat.eqb x y then None                      (* the aliasing flag *)
      else Some (pupd (pupd p x (p y)) y (p x))
  | TSeq a b => match sx p a with Some p1 => sx p1 b | None => None end
  | TIf _ _ _ _ | TLoop _ _ _ _ => None             (* the block is cut here *)
  end.

(** The block's exit edge writes every changed entry **simultaneously**
    ([_edge] collects [(n, e)] for [e <> n] and the renderer emits one
    [next(n) := e] per variable).  [describes g0 p g] says the pending map [p]
    denotes the store [g] when read at the entry store [g0]. *)
Definition describes (g0 : sstore) (p : pmap) (g : sstore) : Prop :=
  forall x, seval g0 (p x) = Some (g x).

Lemma describes_pid : forall g, describes g pid g.
Proof. intros g x; reflexivity. Qed.

(* ===================================================================== *)
(** ** The substitution lemma.

    Everything below rests on this: reading an expression through the pending
    map at the entry store is reading it at the current store.  Note it is an
    equality of [option]s, so it also transports *undefinedness* -- a division by
    zero is a division by zero either way, which is what lets the obligations be
    emitted as separate edges over entry values. *)

Lemma seval_subst : forall g0 p g e,
  describes g0 p g -> seval g0 (subst p e) = seval g e.
Proof.
  intros g0 p g e H; induction e as [z | n | e1 IH1 | o a IHa b IHb]; simpl.
  - reflexivity.
  - apply H.
  - rewrite IH1; reflexivity.
  - rewrite IHa, IHb; reflexivity.
Qed.

(** The path-condition question of §8.4, answered: a guard met halfway through a
    block may be emitted as a term over the block's entry values, because
    substituting the pending map into it and evaluating there is evaluating it in
    the store the source semantics has reached. *)
Theorem guard_at_entry : forall g0 p g c,
  describes g0 p g -> seval g0 (subst p c) = seval g c.
Proof. intros; apply seval_subst; assumption. Qed.

(* ===================================================================== *)
(** ** Soundness: the accumulated updates compose in the right order.

    Stated relative to an arbitrary entry store [g0] and an arbitrary incoming
    pending map, which is what makes the [TSeq] induction go through: the second
    statement starts from the map the first left. *)

Theorem block_sound : forall s p p' g0 g h,
  sx p s = Some p' -> describes g0 p g -> sexec s g h -> describes g0 p' h.
Proof.
  induction s as [ | x o e | x y | a IHa b IHb | | ];
    intros p p' g0 g h Hsx Hd Hex; simpl in Hsx.
  - (* TSkip *)
    injection Hsx as <-; inversion Hex; subst; exact Hd.
  - (* TAsn *)
    destruct (soccurs x e) eqn:Hoc; [ discriminate | ].
    destruct (op2bin o) as [bo|] eqn:Hbo; [ | discriminate ].
    injection Hsx as <-.
    inversion Hex; subst.
    match goal with Hv : seval g e = Some ?v |- _ => rename Hv into Hval end.
    intro n.
    destruct (Nat.eq_dec n x) as [Hnx | Hnx].
    + (* the written cell: [(pending x) op (e read through the pending map)] *)
      subst n; rewrite pupd_eq, supd_eq.
      simpl; rewrite (Hd x), (seval_subst g0 p g e Hd), Hval; simpl.
      destruct o; simpl in Hbo; try discriminate;
        injection Hbo as Hbo; subst bo; simpl; try reflexivity.
      (* ODiv: [aok] supplies the nonzero divisor [sbin_den] asks for *)
      match goal with Hk : aok ODiv _ _ = true |- _ =>
        simpl in Hk; apply andb_true_iff in Hk as [Hk _];
        apply negb_true_iff in Hk; rewrite Hk end.
      reflexivity.
    + rewrite (pupd_neq _ n x _ Hnx), (supd_neq _ n x _ Hnx); apply Hd.
  - (* TSwap: the two entries are exchanged simultaneously *)
    destruct (Nat.eqb x y) eqn:Exy; [ discriminate | ].
    apply Nat.eqb_neq in Exy.
    injection Hsx as <-.
    inversion Hex; subst.
    intro n.
    destruct (Nat.eq_dec n y) as [Hny | Hny].
    + subst n; rewrite pupd_eq, supd_eq; apply Hd.
    + rewrite (pupd_neq _ n y _ Hny), (supd_neq _ n y _ Hny).
      destruct (Nat.eq_dec n x) as [Hnx | Hnx].
      * subst n; rewrite pupd_eq, supd_eq; apply Hd.
      * rewrite (pupd_neq _ n x _ Hnx), (supd_neq _ n x _ Hnx); apply Hd.
  - (* TSeq *)
    destruct (sx p a) as [p1|] eqn:Ha; [ | discriminate ].
    inversion Hex; subst.
    match goal with Hm : sexec a g ?m |- _ =>
      apply (IHb p1 p' g0 m h Hsx (IHa p p1 g0 g m Ha Hd Hm)) end;
      assumption.
  - (* TIf: the block is cut, nothing to prove *) discriminate.
  - (* TLoop: likewise *) discriminate.
Qed.

(** At the block's entry the pending map is the identity, so the theorem reads:
    the single transition [next(x) := p' x], with every [p' x] evaluated in the
    store the block starts from, produces exactly the store the source semantics
    reaches after running the whole block statement by statement. *)
Corollary block_from_entry : forall s p' g h,
  sx pid s = Some p' -> sexec s g h -> forall x, seval g (p' x) = Some (h x).
Proof.
  intros s p' g h Hsx Hex; apply (block_sound s pid p' g g h Hsx (describes_pid g) Hex).
Qed.

(** ...and the block cannot compute a *different* store, since [seval] is a
    function: two source runs of one block agree, so the transition is
    well defined.  (Determinism of [sexec] itself comes from the core through
    [RevLowerStmt.lower_stmt_correct]; this is the statement the model needs.) *)
Corollary block_is_functional : forall s p' g h h',
  sx pid s = Some p' -> sexec s g h -> sexec s g h' -> forall x, h x = h' x.
Proof.
  intros s p' g h h' Hsx H1 H2 x.
  pose proof (block_from_entry s p' g h Hsx H1 x) as E1.
  pose proof (block_from_entry s p' g h' Hsx H2 x) as E2.
  rewrite E1 in E2; injection E2 as <-; reflexivity.
Qed.

(* ===================================================================== *)
(** ** The two traps the encoding has to avoid.

    Both are about *how* the pending map is updated, and both are invisible in a
    one-location-per-statement encoding, where each update is written against the
    real store. *)

(** **Composition order.**  The documented block

      [v += g   h -= v   h += halfg   t += 1]

    (variables [v=0], [g=1], [h=2], [halfg=3], [t=4]) accumulates for [h] the
    term `((h - (v + g)) + halfg)` -- [h] is decreased by the *accumulated* [v],
    not by its entry value.  This is the exact string `docs/totality-checking.md`
    §2 quotes. *)
Definition documented_block : sstmt :=
  TSeq (TAsn 0 OAdd (SVar 1))
    (TSeq (TAsn 2 OSub (SVar 0))
      (TSeq (TAsn 2 OAdd (SVar 3)) (TAsn 4 OAdd (SNum 1)))).

Example documented_block_accumulates :
  match sx pid documented_block with
  | Some p =>
      (* h reads the accumulated v, not the entry v *)
      p 2%nat = SBin SAdd (SBin SSub (SVar 2) (SBin SAdd (SVar 0) (SVar 1))) (SVar 3)
      (* the counter is its own one-line update *)
      /\ p 4%nat = SBin SAdd (SVar 4) (SNum 1)
      (* and the variables the block never writes stay identities, which is what
         lets [_edge] drop them and the [TRUE] default absorb their frames *)
      /\ p 1%nat = SVar 1 /\ p 3%nat = SVar 3
  | None => False
  end.
Proof. repeat split. Qed.

(** Reading the *entry* value of [v] instead would be a different term -- and a
    different program.  Evaluated at [v = g = h = 1, halfg = 0] the accumulating
    form gives [-1] and the entry-reading form [0]. *)
Example composition_order_is_observable :
  let acc := SBin SSub (SVar 2) (SBin SAdd (SVar 0) (SVar 1)) in
  let naive := SBin SSub (SVar 2) (SVar 0) in
  let g := fun n => if Nat.eqb n 3 then 0 else 1 in
  seval g acc = Some (-1) /\ seval g naive = Some 0.
Proof. split; reflexivity. Qed.

(** **Simultaneity.**  A swap exchanges the two pending entries at once
    (`self.pending[left], self.pending[right] = before_right, before_left`
    evaluates the right-hand tuple first).  Writing the two updates one after the
    other, with the second reading the map the first left, loses the value:
    both entries end up holding [y]. *)
Definition swap_sequentially (p : pmap) (x y : nat) : pmap :=
  let p1 := pupd p x (p y) in pupd p1 y (p1 x).

Example a_swap_must_be_simultaneous :
  match sx pid (TSwap 0 1) with
  | Some p => p 0%nat = SVar 1 /\ p 1%nat = SVar 0    (* correct: exchanged *)
  | None => False
  end
  /\ swap_sequentially pid 0 1 0%nat = SVar 1
  /\ swap_sequentially pid 0 1 1%nat = SVar 1.        (* wrong: [x]'s value is gone *)
Proof. repeat split. Qed.

(** The sequential form is not merely different, it is not even injective -- it
    maps every store to one where both cells hold the same value, which no
    reversible program does. *)
Example the_sequential_swap_is_not_reversible : forall g : sstore,
  seval g (swap_sequentially pid 0 1 0%nat) = seval g (swap_sequentially pid 0 1 1%nat).
Proof. intros g; reflexivity. Qed.

(** **The unsoundness [RevSmvAlias.v] found, stated where it can be stated.**

    Before the fix, [smv.py]'s swap case had no aliasing test: it exchanged the
    two pending entries unconditionally.  [swap_unchecked] is that code.  When
    both sides resolve to one slot the exchange is a *no-op* -- the pending map
    comes back unchanged, so [_edge] emits no update and no ERR edge, and nuXmv
    proves [INVARSPEC pc != ERR].  Meanwhile the source has no run at all.  A
    model with a transition where the source has none is exactly a proof that is
    a lie. *)
Definition swap_unchecked (p : pmap) (x y : nat) : pmap :=
  pupd (pupd p x (p y)) y (p x).

Example the_unchecked_swap_is_the_identity : forall p x n,
  swap_unchecked p x x n = p n.
Proof.
  intros p x n; unfold swap_unchecked, pupd.
  destruct (Nat.eqb n x) eqn:E; [ apply Nat.eqb_eq in E; now subst | reflexivity ].
Qed.

Example the_unchecked_swap_models_a_run_the_source_has_not : forall x g,
  (* the emitted transition would take the store to itself ... *)
  (forall n, seval g (swap_unchecked pid x x n) = Some (g n))
  (* ... while the source semantics has no run whatsoever *)
  /\ (forall h, ~ sexec (TSwap x x) g h)
  (* ... which is why [sx] must refuse it, as it now does *)
  /\ sx pid (TSwap x x) = None.
Proof.
  intros x g; repeat split.
  - intro n; rewrite the_unchecked_swap_is_the_identity; reflexivity.
  - intros h H; inversion H; congruence.
  - simpl; now rewrite Nat.eqb_refl.
Qed.

(* ===================================================================== *)
(** ** Where the block stops.

    [sx] returns [None] exactly at the points [smv.py] leaves the accumulation:
    a flagged alias (an unconditional edge to ERR -- [RevSmvAlias.alias_ok]), an
    operator outside the fragment, or a statement that cuts a location.  The
    aliasing cases agree with the previous file's decision, so a block that
    accumulates is one whose statements all pass the check. *)

Lemma sx_atomic_alias : forall p x o e,
  sx p (TAsn x o e) = None -> op2bin o <> None -> alias_ok (fun n => n) (TAsn x o e) = false.
Proof.
  intros p x o e H Hop; simpl in H |- *.
  destruct (soccurs x e) eqn:Hoc.
  - rewrite aoccurs_rn; simpl.
    replace (rn (fun n : nat => n) e) with e; [ now rewrite Hoc | ].
    clear; induction e as [z | n | e1 IH1 | o' a IHa b IHb]; simpl;
      [ reflexivity | reflexivity | now rewrite <- IH1 | now rewrite <- IHa, <- IHb ].
  - destruct (op2bin o); [ discriminate | contradiction ].
Qed.

Lemma sx_swap_alias : forall p x y,
  sx p (TSwap x y) = None -> alias_ok (fun n => n) (TSwap x y) = false.
Proof.
  intros p x y H; simpl in H |- *.
  destruct (Nat.eqb x y) eqn:E; [ reflexivity | discriminate ].
Qed.

(** And a block that does accumulate never hides an aliasing violation: by
    [block_sound] the transition it emits denotes the source relation, whose
    every step carries [RevSmvAlias.step_alias_ok]. *)
Corollary accumulated_block_is_alias_free : forall x o e g h,
  sexec (TAsn x o e) g h -> alias_ok (fun n => n) (TAsn x o e) = true.
Proof.
  intros x o e g h H; apply (step_alias_ok (fun n => n) (TAsn x o e) g h).
  replace (rn_stmt (fun n : nat => n) (TAsn x o e)) with (TAsn x o e); [ exact H | ].
  simpl; f_equal.
  clear; induction e as [z | n | e1 IH1 | o' a IHa b IHb]; simpl;
    [ reflexivity | reflexivity | now rewrite <- IH1 | now rewrite <- IHa, <- IHb ].
Qed.
