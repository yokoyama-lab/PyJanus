(** * RevSmvAlias.v — the aliasing check of the totality checker, verified

    [RevError.v] proved the checker's *control-flow* encoding right: reaching ERR
    and failing a source assertion are the same thing.  [RevSmvExpr.v] did the
    same for the *expression* traps (floor division, sort confusion).  The third
    trap of `docs/totality-checking.md` §3 — **aliasing is a run-time check, not
    a static one** — was still unwired, and it is the one the document calls the
    most dangerous: naively translating [x += x] to [next(x) = x + x] models a
    program PyJanus *rejects* as a safe one, so [INVARSPEC pc != ERR] is proved
    of a program that fails.

    What makes the check statable at all is that [smv.py] **inlines** calls, so
    by the time a statement is emitted every name has been resolved to an SMV
    variable through the environment [env].  Aliasing — two source names denoting
    one slot — is then syntactic.  That resolution is a *renaming*, and this file
    is about the one square it induces:

      [aoccurs env t e]  (what [smv.py] computes, on the un-renamed expression)
        =
      [soccurs t (rn env e)]  (the side condition [sexec] imposes, on the inlined
                               program)
        =
      [reads _ _ (sloc _ t) (lower _ (rn env e))]  (the frame core's run-time test)

    Everything else follows: the two directions the checker needs, in the shape
    [RevError.fail_iff] fixed — no missed alias (else a `proved` verdict is a
    lie) and no false alarm (else a `refuted` verdict is).

    Mechanizing it found two real gaps in [smv.py], both recorded below as
    examples rather than prose:

      - [self_swap_gap] — the swap case had **no** aliasing check at all.
        [x <=> x] was symbolically executed as a simultaneous exchange, which for
        one variable is the identity, so the model had no ERR edge while PyJanus
        raises "Identifiers `x' and `x' are aliases".  That is exactly the §3.3
        unsoundness, still present for swaps after being fixed for assignments.
      - [double_binding_is_not_itself_an_error] — the call site rejected *any*
        two parameters bound to the same variable, whether or not a statement in
        the body ever aliases them.  Sound but imprecise: a false alarm on a
        program PyJanus runs happily.

    The reference for the source side is PyJanus's [_check_alias_assign] /
    [_check_alias_swap] (`jana_py/runtime.py`), which compare *resolved* keys at
    the moment the statement executes — hence per-statement, hence a violation on
    an unreachable path is not an error.  [smv.py] matches that by making the
    flagged statement an unconditional edge to ERR rather than a global refusal.

    [tests/verify/test_smv_alias.py] pins [smv.py]'s emitted edges to what is
    proved here, the way [tests/verify/test_smv_expr.py] does for the division
    macro. *)

From Stdlib Require Import ZArith Bool Lia.
Require Import RevFrame RevLowerExpr RevLowerStmt.
Open Scope Z_scope.

(* ===================================================================== *)
(** ** Inlining, as a renaming.

    [smv.py] carries a dictionary [env] from source names to SMV variables and
    resolves every l-value and every variable read through it ([_lookup],
    [_lval_name]).  A procedure call extends it with the actuals
    ([inner[param] = resolved]), which is where two names can come to denote one
    slot.  Here that dictionary is a total function [renv]; the fragment where it
    is partial is exactly where [smv.py] raises [SmvUnsupported]. *)

Definition renv := nat -> nat.

(** [_occurs]: does the SMV variable [t] occur in [e] after resolution? *)
Fixpoint aoccurs (env : renv) (t : nat) (e : sexpr) : bool :=
  match e with
  | SNum _ => false
  | SVar n => Nat.eqb (env n) t
  | SNot e1 => aoccurs env t e1
  | SBin _ a b => aoccurs env t a || aoccurs env t b
  end.

(** The program the inlined model is *about*: every name replaced by its slot. *)
Fixpoint rn (env : renv) (e : sexpr) : sexpr :=
  match e with
  | SNum z => SNum z
  | SVar n => SVar (env n)
  | SNot e1 => SNot (rn env e1)
  | SBin o a b => SBin o (rn env a) (rn env b)
  end.

Fixpoint rn_stmt (env : renv) (s : sstmt) : sstmt :=
  match s with
  | TSkip => TSkip
  | TAsn x o e => TAsn (env x) o (rn env e)
  | TSwap x y => TSwap (env x) (env y)
  | TSeq a b => TSeq (rn_stmt env a) (rn_stmt env b)
  | TIf e1 a b e2 => TIf (rn env e1) (rn_stmt env a) (rn_stmt env b) (rn env e2)
  | TLoop e1 a b e2 => TLoop (rn env e1) (rn_stmt env a) (rn_stmt env b) (rn env e2)
  end.

(** The checker's per-statement decision.  [true] means "emit the statement";
    [false] means "emit an unconditional edge to ERR, the continuation is
    unreachable".  The two atomic forms are the two PyJanus checks at run time:
    [_check_alias_assign] (the target occurs in the right-hand side) and
    [_check_alias_swap] (the two sides are one slot). *)
Definition alias_ok (env : renv) (s : sstmt) : bool :=
  match s with
  | TAsn x _ e => negb (aoccurs env (env x) e)
  | TSwap x y => negb (Nat.eqb (env x) (env y))
  | _ => true
  end.

(** Renaming does not disturb what an expression *means* under a store that has
    already been renamed -- the model's variables are the slots. *)
Lemma seval_rn : forall env g e, seval (fun n => g (env n)) e = seval g (rn env e).
Proof.
  intros env g e; induction e as [z | n | e1 IH1 | o a IHa b IHb]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1; reflexivity.
  - rewrite IHa, IHb; reflexivity.
Qed.

(** Nor whether it is well formed: the boolean discipline is on the shape. *)
Lemma wf_rn : forall env e, wf (rn env e) = wf e.
Proof.
  intros env e; induction e as [z | n | e1 IH1 | o a IHa b IHb]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1; f_equal; destruct e1; reflexivity.
  - rewrite IHa, IHb; f_equal; f_equal.
    destruct o; try reflexivity; simpl; destruct a, b; reflexivity.
Qed.

(* ===================================================================== *)
(** ** The bridge: the checker's test *is* the source's side condition.

    [smv.py] tests the *un-renamed* expression against the *resolved* target,
    because that is the form it has in hand; [sexec] imposes [soccurs] on the
    inlined program.  They are the same predicate. *)

Theorem aoccurs_rn : forall env t e, aoccurs env t e = soccurs t (rn env e).
Proof.
  intros env t e; induction e as [z | n | e1 IH1 | o a IHa b IHb]; simpl.
  - reflexivity.
  - apply Nat.eqb_sym.
  - exact IH1.
  - rewrite IHa, IHb; reflexivity.
Qed.

(** ...and both are the frame core's *run-time* aliasing test on the lowered
    expression ([reads_lower]).  Three notions of "the target is read by the
    right-hand side" — one in the model checker's front end, one in the reference
    semantics, one in the verified core — and they coincide. *)
Theorem alias_three_ways : forall env lv g x e,
  aoccurs env (env x) e = soccurs (env x) (rn env e)
  /\ soccurs (env x) (rn env e)
     = reads 0 (enc lv g) (sloc lv (env x)) (lower lv (rn env e)).
Proof.
  intros env lv g x e; split.
  - apply aoccurs_rn.
  - symmetry; apply reads_lower.
Qed.

(* ===================================================================== *)
(** ** No missed alias: a statement that runs is one the checker lets through.

    This is the half a `proved` verdict rests on.  If the source can take a step
    then the checker did *not* flag it, so a program the model runs to completion
    is one the reference semantics also runs -- no aliasing violation is being
    silently modelled as an ordinary update. *)

Theorem step_alias_ok : forall env s g h,
  sexec (rn_stmt env s) g h -> alias_ok env s = true.
Proof.
  intros env [ | x o e | x y | a b | e1 a b e2 | e1 a b e2 ] g h H;
    simpl in H |- *; try reflexivity.
  - (* TAsn: [S_Asn] carries [soccurs = false] *)
    inversion H; subst.
    apply negb_true_iff; rewrite aoccurs_rn; assumption.
  - (* TSwap: [S_Swap] carries [x <> y] *)
    inversion H; subst.
    apply negb_true_iff, Nat.eqb_neq; assumption.
Qed.

(* ===================================================================== *)
(** ** No false alarm: a flagged statement really has no step.

    This is the half a `refuted` verdict rests on.  The checker turns a flagged
    statement into an unconditional edge to ERR; for that to be honest, reaching
    the statement must genuinely be a failure. *)

Theorem alias_flagged_no_step : forall env s g h,
  alias_ok env s = false -> ~ sexec (rn_stmt env s) g h.
Proof.
  intros env s g h Hbad Hstep.
  rewrite (step_alias_ok env s g h Hstep) in Hbad; discriminate.
Qed.

(** The two together, in the shape [RevError.fail_iff] takes for assertions: the
    checker's aliasing decision is exactly the reference semantics' -- it flags a
    statement iff the statement cannot run. *)
Corollary alias_check_is_exact : forall env s g h,
  (alias_ok env s = false -> ~ sexec (rn_stmt env s) g h)
  /\ (sexec (rn_stmt env s) g h -> alias_ok env s = true).
Proof.
  intros env s g h; split;
    [ apply alias_flagged_no_step | apply (step_alias_ok env s g h) ].
Qed.

(** For the swap the correspondence is an outright equivalence, because aliasing
    is a swap's *only* way to fail: it is flagged exactly when it is stuck. *)
Theorem swap_alias_iff : forall env x y,
  alias_ok env (TSwap x y) = false <-> (forall g h, ~ sexec (rn_stmt env (TSwap x y)) g h).
Proof.
  intros env x y; split.
  - intros Hbad g h; apply alias_flagged_no_step; exact Hbad.
  - intros Hno; simpl; apply negb_false_iff, Nat.eqb_eq.
    destruct (Nat.eq_dec (env x) (env y)) as [Heq | Hne]; [ exact Heq | ].
    exfalso; apply (Hno (fun _ => 0)
      (supd (supd (fun _ => 0) (env x) 0) (env y) 0)).
    simpl; apply S_Swap; exact Hne.
Qed.

(* ===================================================================== *)
(** ** The first gap: the swap had no check.

    [smv.py] executed [x <=> y] symbolically as a simultaneous exchange of the
    two pending entries.  When both sides resolve to one slot that is the
    *identity* -- the model gets an edge with no update and no ERR, while
    PyJanus raises.  So the model checker would prove [INVARSPEC pc != ERR] of a
    program that fails: the §3.3 unsoundness, unfixed for swaps.

    The source semantics is unambiguous here, and so is the core: [S_Swap]
    requires [x <> y] because the XOR triple that implements the swap zeroes the
    cell otherwise ([RevLowerStmt.self_swap_would_zero],
    [RevLowerStmt.self_swap_has_no_step]).

    That the unchecked symbolic execution really does produce the identity -- so
    the model had a run where the source has none -- is
    [RevSmvBlock.the_unchecked_swap_is_the_identity], which needs the pending
    map to state. *)

Example self_swap_has_no_run : forall x g h, ~ sexec (TSwap x x) g h.
Proof. intros x g h H; inversion H; congruence. Qed.

Example self_swap_gap : forall x env,
  (* the source cannot run it ... *)
  (forall g h, ~ sexec (TSwap x x) g h)
  (* ... so the checker must flag it, under any resolution *)
  /\ alias_ok env (TSwap x x) = false.
Proof.
  intros x env; split.
  - intros g h; apply self_swap_has_no_run.
  - simpl; now rewrite Nat.eqb_refl.
Qed.

(** And the same through a call, which is how it arises in practice
    (`call swapit(x, x)` with body `a <=> b`): the resolution makes two distinct
    source names one slot. *)
Example self_swap_through_parameters :
  let env := fun _ : nat => 7%nat in       (* both formals bound to slot 7 *)
  alias_ok env (TSwap 0 1) = false
  /\ (forall g h, ~ sexec (rn_stmt env (TSwap 0 1)) g h).
Proof.
  simpl; split; [ reflexivity | ].
  intros g h; apply self_swap_has_no_run.
Qed.

(* ===================================================================== *)
(** ** The second gap: a double binding is not itself an error.

    [smv.py]'s call site refused *any* two parameters resolving to one variable.
    PyJanus does not: it checks each statement as it reaches it, so a body that
    never brings the two together runs fine.  The blanket rule is sound but
    imprecise -- it yields a counterexample for a program that cannot fail --
    and the per-statement rule above is both sound and exact.

    (`a += 1` under a resolution collapsing both formals onto slot 0.) *)

Example double_binding_is_not_itself_an_error :
  let env := fun _ : nat => 0%nat in
  alias_ok env (TAsn 1 OAdd (SNum 1)) = true
  /\ sexec (rn_stmt env (TAsn 1 OAdd (SNum 1)))
       (fun _ => 0) (supd (fun _ => 0) 0 1).
Proof.
  simpl; split; [ reflexivity | ].
  apply (S_Asn (fun _ => 0) 0 OAdd (SNum 1) 1); reflexivity.
Qed.

(** Whereas bringing them together in the same statement *is* one, and the
    per-statement rule catches it -- this is `alias-1.ja`'s shape
    (`call foo(x,x)` -> `call bar(x,y)` -> `a += b`) after inlining. *)
Example the_body_that_does_alias_is_caught :
  let env := fun _ : nat => 0%nat in
  alias_ok env (TAsn 1 OAdd (SVar 2)) = false
  /\ (forall g h, ~ sexec (rn_stmt env (TAsn 1 OAdd (SVar 2))) g h).
Proof.
  cbv zeta; split; [ reflexivity | ].
  intros g h; apply alias_flagged_no_step; reflexivity.
Qed.

(* ===================================================================== *)
(** ** Why the check must run *before* the pending substitution.

    [smv.py] tests [_occurs] against the statement's own source expression, not
    against the expression after the block's pending map has been substituted
    into it.  That is not an accident of the implementation: the substituted form
    mentions the *entry* values, so after `x += y` the pending entry for [x] is
    `x + y`, and a later `y += x` reads a term in which [x] occurs -- while the
    statement is perfectly legal.  Testing the substituted form would reject it.

    Here the two forms are [rn env e] (renamed, not substituted) and its image
    under a pending map; the example exhibits a statement the substituted test
    would reject and the reference semantics accepts. *)

Example the_check_is_on_the_source_expression :
  (* after `x += y`, the pending value of x (slot 0) is `x + y` *)
  let pend := SBin SAdd (SVar 0) (SVar 1) in
  (* `y += x` is legal: the target, slot 1, does not occur in `x` *)
  soccurs 1 (SVar 0) = false
  (* but slot 1 *does* occur in x's pending expression *)
  /\ soccurs 1 pend = true.
Proof. split; reflexivity. Qed.
