(** * JanusCost.v — A cost semantics for core Janus, with machine-checked
      resource laws (Rocq/Coq)

    RC-03 ("可逆プログラムは何を払っているか", the Janus resource atlas) measures
    three resource quantities per run — [steps] (executed statements),
    [stack_peak] (peak total depth of all Janus [stack] variables) and
    [call_depth_peak] — and observes, on 6 input sizes each, that

      * for gcd on consecutive Fibonacci arguments the stack peak equals the
        number of Euclidean divisions, and
      * for bubble sort the stack peak equals the number of comparisons
        n(n-1)/2,

    adding "these equalities are 6-point agreements, not proofs".  This file
    turns them (and three soundness theorems for syntactic resource checks)
    into theorems.

    Design (kept deliberately close to [Janus.v]):

      - State: an integer store [vars : nat -> Z], arrays [arrs : nat -> Z -> Z]
        (unbounded, index in Z), Janus stack variables [stks : nat -> list Z]
        of which the first [nstk] are declared.  The current total stack size
        [ssize st] is a function of the state; the peak is the maximum over
        all intermediate states of a run.
      - Statements: [x op= e], [a[i] op= e], sequencing, [if e1 then s1 else s2
        fi e2], [from e1 do s1 loop s2 until e2] (Janus semantics, exactly as
        [Janus.v]/[RevCore.v]), [local x = e1 s delocal x = e2] (modelled as a
        plain store variable that must be 0 on entry, is initialised, asserted
        and re-zeroed on exit), [push(x,s)] (x is pushed and zeroed) and
        [pop(x,s)] (x must be 0), [call p]/[uncall p] with a procedure
        environment [Γ : pname -> stmt].  Procedure parameters are modelled by
        global variables, as in [Janus.v].
      - Cost: [exec s a b c] is a big-step relation instrumented with a
        [cost] record {steps; stack_peak; call_depth_peak; total_calls}.
        Statement counting follows [jana_py/pebble.py]: every executed
        statement counts 1, compound statements (if/loop/local/call/uncall)
        count 1 plus their children; [Skip] models the *empty block* and
        costs 0 (this reproduces pebble's totals: gcd.ja = 16, bubble_sort.ja
        = 247).

    Headline theorems:

      - [exec_det]                     : final state and cost are determined
      - [exec_cost_rev]                : exec s a b c -> exec (invert s) b a c
                                         (reversal preserves *all* costs exactly)
      - [gcd_stack_eq_divisions]       : gcd (a,b), a,b>0: log length =
                                         stack_peak = sub_steps a b,
                                         steps = 2 + 4 sub_steps a b
      - [gcd_fib_stack]                : (F(k+2),F(k+1)): stack_peak = k
      - [sub_steps_quotients]          : sub_steps a b + 1 = Σ Euclidean quotients
      - [bsort_stack_eq_comparisons]   : bubble sort on any n-array:
                                         stack_peak = n(n-1)/2, steps in
                                         [3+3n+4C, 3+3n+8C], C = n(n-1)/2
      - [no_push_stack_zero]           : no push/pop reachable => peak = entry size
      - [acyclic_depth_bound]          : ranked call graph => depth <= bound
      - [no_call_in_loop_bounded_calls]: no call in loops + acyclic =>
                                         total_calls <= syntactic bound *)

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
Import ListNotations.
Open Scope Z_scope.

(* ************************************************************************* *)
(** ** States *)

Definition var   := nat.
Definition aname := nat.
Definition sname := nat.
Definition pname := nat.

Definition update (f : var -> Z) (x : var) (v : Z) : var -> Z :=
  fun y => if Nat.eqb x y then v else f y.

Definition aupd (f : aname -> Z -> Z) (a : aname) (i v : Z) : aname -> Z -> Z :=
  fun a' i' => if andb (Nat.eqb a a') (Z.eqb i i') then v else f a' i'.
Arguments aupd : simpl never.

Definition supd (f : sname -> list Z) (k : sname) (l : list Z) : sname -> list Z :=
  fun k' => if Nat.eqb k k' then l else f k'.

Record state := mkst {
  vars : var -> Z;            (* integer variables *)
  arrs : aname -> Z -> Z;     (* arrays, indexed by Z *)
  stks : sname -> list Z;     (* Janus stack variables *)
  nstk : nat                  (* number of declared stack variables *)
}.

Definition setv (st : state) (x : var) (v : Z) : state :=
  mkst (update (vars st) x v) (arrs st) (stks st) (nstk st).
Definition seta (st : state) (a : aname) (i v : Z) : state :=
  mkst (vars st) (aupd (arrs st) a i v) (stks st) (nstk st).
Definition sets (st : state) (k : sname) (l : list Z) : state :=
  mkst (vars st) (arrs st) (supd (stks st) k l) (nstk st).

(** Total number of values held in the declared stacks [0..n-1]. *)
Fixpoint ssum (n : nat) (f : sname -> list Z) : nat :=
  match n with
  | O => O
  | S n' => (ssum n' f + length (f n'))%nat
  end.
Notation ssize st := (ssum (nstk st) (stks st)).

Lemma update_eq : forall f x v, update f x v x = v.
Proof. intros; unfold update; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma update_neq : forall f x v y, x <> y -> update f x v y = f y.
Proof.
  intros f x v y H; unfold update.
  destruct (Nat.eqb x y) eqn:E; [apply Nat.eqb_eq in E; contradiction | reflexivity].
Qed.

Lemma update_shadow : forall f x a b, update (update f x a) x b = update f x b.
Proof.
  intros; apply functional_extensionality; intro z; unfold update.
  destruct (Nat.eqb x z); reflexivity.
Qed.

Lemma update_same : forall f x, update f x (f x) = f.
Proof.
  intros; apply functional_extensionality; intro z; unfold update.
  destruct (Nat.eqb x z) eqn:E; [apply Nat.eqb_eq in E; subst; reflexivity | reflexivity].
Qed.

Lemma aupd_eq : forall f a i v, aupd f a i v a i = v.
Proof. intros; unfold aupd; rewrite Nat.eqb_refl, Z.eqb_refl; reflexivity. Qed.

Lemma aupd_neq_i : forall f a i v a' i', i <> i' -> aupd f a i v a' i' = f a' i'.
Proof.
  intros f a i v a' i' H; unfold aupd.
  destruct (Z.eqb i i') eqn:E; [apply Z.eqb_eq in E; contradiction |].
  rewrite andb_false_r; reflexivity.
Qed.

Lemma aupd_neq_a : forall f a i v a' i', a <> a' -> aupd f a i v a' i' = f a' i'.
Proof.
  intros f a i v a' i' H; unfold aupd.
  destruct (Nat.eqb a a') eqn:E; [apply Nat.eqb_eq in E; contradiction | reflexivity].
Qed.

Lemma aupd_shadow : forall f a i v w, aupd (aupd f a i v) a i w = aupd f a i w.
Proof.
  intros; apply functional_extensionality; intro a'; apply functional_extensionality; intro i'.
  unfold aupd. destruct (andb (Nat.eqb a a') (Z.eqb i i')); reflexivity.
Qed.

Lemma aupd_same : forall f a i, aupd f a i (f a i) = f.
Proof.
  intros; apply functional_extensionality; intro a'; apply functional_extensionality; intro i'.
  unfold aupd. destruct (Nat.eqb a a') eqn:Ea; destruct (Z.eqb i i') eqn:Ei; simpl; try reflexivity.
  apply Nat.eqb_eq in Ea; apply Z.eqb_eq in Ei; subst; reflexivity.
Qed.

Lemma supd_eq : forall f k l, supd f k l k = l.
Proof. intros; unfold supd; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma supd_neq : forall f k l k', k <> k' -> supd f k l k' = f k'.
Proof.
  intros f k l k' H; unfold supd.
  destruct (Nat.eqb k k') eqn:E; [apply Nat.eqb_eq in E; contradiction | reflexivity].
Qed.

Lemma supd_shadow : forall f k l l', supd (supd f k l) k l' = supd f k l'.
Proof.
  intros; apply functional_extensionality; intro z; unfold supd.
  destruct (Nat.eqb k z); reflexivity.
Qed.

Lemma supd_same : forall f k, supd f k (f k) = f.
Proof.
  intros; apply functional_extensionality; intro z; unfold supd.
  destruct (Nat.eqb k z) eqn:E; [apply Nat.eqb_eq in E; subst; reflexivity | reflexivity].
Qed.

Lemma state_ext : forall s s',
  vars s = vars s' -> arrs s = arrs s' -> stks s = stks s' -> nstk s = nstk s' -> s = s'.
Proof. intros [] [] ; simpl; intros; subst; reflexivity. Qed.

(** Stack-size bookkeeping. *)
Lemma ssum_supd_ge : forall n f k l, (n <= k)%nat -> ssum n (supd f k l) = ssum n f.
Proof.
  induction n; intros f k l H; simpl; [reflexivity |].
  rewrite IHn by lia. rewrite supd_neq by lia. reflexivity.
Qed.

Lemma ssum_supd : forall n f k l, (k < n)%nat ->
  (ssum n (supd f k l) + length (f k))%nat = (ssum n f + length l)%nat.
Proof.
  induction n; intros f k l H; simpl; [lia |].
  destruct (Nat.eq_dec k n) as [-> | Hne].
  - rewrite ssum_supd_ge by lia. rewrite supd_eq. lia.
  - rewrite supd_neq by assumption. specialize (IHn f k l ltac:(lia)). lia.
Qed.

Lemma ssize_sets : forall st k l, (k < nstk st)%nat ->
  (ssize (sets st k l) + length (stks st k))%nat = (ssize st + length l)%nat.
Proof. intros; unfold sets; simpl; apply ssum_supd; assumption. Qed.

(* ************************************************************************* *)
(** ** Expressions *)

Inductive binop := OAdd | OSub | OMul | OXor | OEq | OLt | OGt.

Definition denote (o : binop) (a b : Z) : Z :=
  match o with
  | OAdd => a + b
  | OSub => a - b
  | OMul => a * b
  | OXor => Z.lxor a b
  | OEq  => if Z.eqb a b then 1 else 0
  | OLt  => if Z.ltb a b then 1 else 0
  | OGt  => if Z.ltb b a then 1 else 0
  end.

Inductive expr :=
| Cst   (n : Z)
| Var   (x : var)
| ARd   (a : aname) (i : expr)        (* a[i] *)
| Top   (k : sname)                   (* top(s)   : 0 on the empty stack *)
| Empty (k : sname)                   (* empty(s) : 1 if empty else 0 *)
| Bin   (o : binop) (e1 e2 : expr).

Fixpoint eval (st : state) (e : expr) : Z :=
  match e with
  | Cst n => n
  | Var x => vars st x
  | ARd a i => arrs st a (eval st i)
  | Top k => match stks st k with v :: _ => v | [] => 0 end
  | Empty k => match stks st k with [] => 1 | _ => 0 end
  | Bin o e1 e2 => denote o (eval st e1) (eval st e2)
  end.

(** [occurs x e]: variable [x] is read by [e]; [aoccurs a e]: array [a] is. *)
Fixpoint occurs (x : var) (e : expr) : bool :=
  match e with
  | Cst _ => false
  | Var y => Nat.eqb x y
  | ARd _ i => occurs x i
  | Top _ | Empty _ => false
  | Bin _ e1 e2 => orb (occurs x e1) (occurs x e2)
  end.

Fixpoint aoccurs (a : aname) (e : expr) : bool :=
  match e with
  | Cst _ | Var _ | Top _ | Empty _ => false
  | ARd a' i => orb (Nat.eqb a a') (aoccurs a i)
  | Bin _ e1 e2 => orb (aoccurs a e1) (aoccurs a e2)
  end.

Lemma eval_setv_notin :
  forall x v st e, occurs x e = false -> eval (setv st x v) e = eval st e.
Proof.
  intros x v st e; induction e; intro H; simpl in H |- *; try reflexivity.
  - unfold update; rewrite H; reflexivity.
  - rewrite IHe by assumption; reflexivity.
  - apply orb_false_iff in H; destruct H as [H1 H2].
    rewrite IHe1 by assumption; rewrite IHe2 by assumption; reflexivity.
Qed.

Lemma eval_seta_notin :
  forall a i v st e, aoccurs a e = false -> eval (seta st a i v) e = eval st e.
Proof.
  intros a i v st e; induction e; intro H; simpl in H |- *; try reflexivity.
  - apply orb_false_iff in H; destruct H as [H1 H2].
    rewrite IHe by assumption. apply aupd_neq_a.
    intro E; subst; rewrite Nat.eqb_refl in H1; discriminate.
  - apply orb_false_iff in H; destruct H as [H1 H2].
    rewrite IHe1 by assumption; rewrite IHe2 by assumption; reflexivity.
Qed.

(* ************************************************************************* *)
(** ** Reversible update operators (as in Janus.v) *)

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

Lemma ainv_correct : forall o a b, adenote (ainv o) (adenote o a b) b = a.
Proof.
  destruct o; intros a b; simpl.
  - lia.
  - lia.
  - rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r; reflexivity.
Qed.

(* ************************************************************************* *)
(** ** Syntax of statements *)

Inductive stmt :=
| Skip                                                (* the empty block *)
| Assign  (x : var) (o : aop) (e : expr)              (* x op= e,    needs ~ occurs x e *)
| AAssign (a : aname) (i : expr) (o : aop) (e : expr) (* a[i] op= e, needs ~ aoccurs a i, e *)
| Seq     (s1 s2 : stmt)
| If      (e1 : expr) (s1 s2 : stmt) (e2 : expr)      (* if e1 then s1 else s2 fi e2 *)
| Loop    (e1 : expr) (s1 s2 : stmt) (e2 : expr)      (* from e1 do s1 loop s2 until e2 *)
| Local   (x : var) (e1 : expr) (s : stmt) (e2 : expr)(* local x = e1  s  delocal x = e2 *)
| Push    (x : var) (k : sname)                       (* push(x, s) *)
| Pop     (x : var) (k : sname)                       (* pop(x, s) *)
| Call    (p : pname)
| Uncall  (p : pname).

Fixpoint invert (s : stmt) : stmt :=
  match s with
  | Skip               => Skip
  | Assign x o e       => Assign x (ainv o) e
  | AAssign a i o e    => AAssign a i (ainv o) e
  | Seq s1 s2          => Seq (invert s2) (invert s1)
  | If e1 s1 s2 e2     => If e2 (invert s1) (invert s2) e1
  | Loop e1 s1 s2 e2   => Loop e2 (invert s1) (invert s2) e1
  | Local x e1 s e2    => Local x e2 (invert s) e1
  | Push x k           => Pop x k
  | Pop x k            => Push x k
  | Call p             => Uncall p
  | Uncall p           => Call p
  end.

Lemma invert_invol : forall s, invert (invert s) = s.
Proof.
  induction s; simpl; try reflexivity; try (rewrite ainv_invol; reflexivity);
    try (rewrite IHs1, IHs2; reflexivity).
  rewrite IHs; reflexivity.
Qed.

(* ************************************************************************* *)
(** ** Costs *)

Record cost := mkc {
  steps           : nat;   (* executed statements (time proxy)            *)
  stack_peak      : nat;   (* peak of the total stack size over the run   *)
  call_depth_peak : nat;   (* peak call/uncall nesting                    *)
  total_calls     : nat    (* number of call/uncall events                *)
}.

Definition czero : cost := mkc 0 0 0 0.
(** Sequential composition of costs: times add, peaks take the max. *)
Definition cadd (c1 c2 : cost) : cost :=
  mkc (steps c1 + steps c2)
      (Nat.max (stack_peak c1) (stack_peak c2))
      (Nat.max (call_depth_peak c1) (call_depth_peak c2))
      (total_calls c1 + total_calls c2).
(** A compound statement (if/loop/local): one more executed statement. *)
Definition cstmt (c : cost) : cost :=
  mkc (S (steps c)) (stack_peak c) (call_depth_peak c) (total_calls c).
(** A call/uncall: one more statement, one more nesting level, one more event. *)
Definition ccall (c : cost) : cost :=
  mkc (S (steps c)) (stack_peak c) (S (call_depth_peak c)) (S (total_calls c)).
(** A primitive statement executed while the total stack size peaks at [n]. *)
Definition cprim (n : nat) : cost := mkc 1 n 0 0.
(** The empty block: no statement, current stack size [n]. *)
Definition cskip (n : nat) : cost := mkc 0 n 0 0.

Lemma cost_ext : forall c c',
  steps c = steps c' -> stack_peak c = stack_peak c' ->
  call_depth_peak c = call_depth_peak c' -> total_calls c = total_calls c' -> c = c'.
Proof. intros [] []; simpl; intros; subst; reflexivity. Qed.

Ltac cost_eq := apply cost_ext; cbn; lia.

Lemma cadd_comm : forall c1 c2, cadd c1 c2 = cadd c2 c1.
Proof. intros; cost_eq. Qed.
Lemma cadd_assoc : forall c1 c2 c3, cadd c1 (cadd c2 c3) = cadd (cadd c1 c2) c3.
Proof. intros; cost_eq. Qed.
Lemma cadd_zero_l : forall c, cadd czero c = c.
Proof. intros; cost_eq. Qed.

(* ************************************************************************* *)
(** ** Cost-instrumented big-step semantics *)

Section Sem.

Variable Γ : pname -> stmt.

(** [exec s a b c]: running [s] from state [a] terminates in state [b] with
    cost [c].  [lp e1 s1 s2 e2 a b c]: the loop body [s1 (s2 s1)^n] from [a]
    to [b] (exit test [e2] true at [b]); the entry assertion is checked by
    [E_Loop].  Primitive rules are written with an explicit [b = ...]
    equation so that derivations can be built by [eapply ...; reflexivity]. *)
Inductive exec : stmt -> state -> state -> cost -> Prop :=
| E_Skip    : forall a, exec Skip a a (cskip (ssize a))
| E_Assign  : forall x o e a b,
    occurs x e = false ->
    b = setv a x (adenote o (vars a x) (eval a e)) ->
    exec (Assign x o e) a b (cprim (ssize a))
| E_AAssign : forall ar i o e a b,
    aoccurs ar i = false -> aoccurs ar e = false ->
    b = seta a ar (eval a i) (adenote o (arrs a ar (eval a i)) (eval a e)) ->
    exec (AAssign ar i o e) a b (cprim (ssize a))
| E_Seq     : forall s1 s2 a m b c1 c2,
    exec s1 a m c1 -> exec s2 m b c2 -> exec (Seq s1 s2) a b (cadd c1 c2)
| E_IfT     : forall e1 s1 s2 e2 a b c,
    eval a e1 <> 0 -> exec s1 a b c -> eval b e2 <> 0 -> exec (If e1 s1 s2 e2) a b (cstmt c)
| E_IfF     : forall e1 s1 s2 e2 a b c,
    eval a e1 =  0 -> exec s2 a b c -> eval b e2 =  0 -> exec (If e1 s1 s2 e2) a b (cstmt c)
| E_Loop    : forall e1 s1 s2 e2 a b c,
    eval a e1 <> 0 -> lp e1 s1 s2 e2 a b c -> exec (Loop e1 s1 s2 e2) a b (cstmt c)
| E_Local   : forall x e1 s e2 a b' b c,
    vars a x = 0 -> occurs x e1 = false -> occurs x e2 = false ->
    exec s (setv a x (eval a e1)) b' c ->
    vars b' x = eval b' e2 ->
    b = setv b' x 0 ->
    exec (Local x e1 s e2) a b (cstmt c)
| E_Push    : forall x k a b,
    (k < nstk a)%nat ->
    b = setv (sets a k (vars a x :: stks a k)) x 0 ->
    exec (Push x k) a b (cprim (S (ssize a)))
| E_Pop     : forall x k a b v rest,
    (k < nstk a)%nat -> vars a x = 0 -> stks a k = v :: rest ->
    b = sets (setv a x v) k rest ->
    exec (Pop x k) a b (cprim (ssize a))
| E_Call    : forall p a b c, exec (Γ p) a b c -> exec (Call p) a b (ccall c)
| E_Uncall  : forall p a b c, exec (invert (Γ p)) a b c -> exec (Uncall p) a b (ccall c)

with lp : expr -> stmt -> stmt -> expr -> state -> state -> cost -> Prop :=
| L_one  : forall e1 s1 s2 e2 a b c,
    exec s1 a b c -> eval b e2 <> 0 -> lp e1 s1 s2 e2 a b c
| L_more : forall e1 s1 s2 e2 a a1 a2 b c1 c2 c3,
    exec s1 a a1 c1 -> eval a1 e2 = 0 ->
    exec s2 a1 a2 c2 -> eval a2 e1 = 0 ->
    lp e1 s1 s2 e2 a2 b c3 ->
    lp e1 s1 s2 e2 a b (cadd c1 (cadd c2 c3)).

Scheme exec_mut := Induction for exec Sort Prop
  with lp_mut   := Induction for lp   Sort Prop.

Lemma lp_exit_true : forall e1 s1 s2 e2 a b c, lp e1 s1 s2 e2 a b c -> eval b e2 <> 0.
Proof. intros until c; intro H; induction H; assumption. Qed.

(** *** Stack-size facts about the primitive rules. *)
Lemma ssize_push : forall a x k, (k < nstk a)%nat ->
  ssize (setv (sets a k (vars a x :: stks a k)) x 0) = S (ssize a).
Proof.
  intros a x k Hk. unfold setv, sets in *; simpl in *.
  pose proof (ssize_sets a k (vars a x :: stks a k) Hk) as H. unfold sets in H; simpl in H. lia.
Qed.

Lemma ssize_pop : forall a x k v rest, (k < nstk a)%nat -> stks a k = v :: rest ->
  S (ssize (sets (setv a x v) k rest)) = ssize a.
Proof.
  intros a x k v rest Hk Hs.
  pose proof (ssize_sets (setv a x v) k rest Hk) as H. unfold setv, sets in *; simpl in *.
  rewrite Hs in H. simpl in H. lia.
Qed.

(** The recorded peak dominates the stack size of the entry and exit states
    (so it really is the maximum over all states visited). *)
Lemma exec_peak_lo : forall s a b c, exec s a b c ->
  (ssize a <= stack_peak c)%nat /\ (ssize b <= stack_peak c)%nat.
Proof.
  apply (exec_mut
    (fun s a b c (_ : exec s a b c) =>
       (ssize a <= stack_peak c)%nat /\ (ssize b <= stack_peak c)%nat)
    (fun e1 s1 s2 e2 a b c (_ : lp e1 s1 s2 e2 a b c) =>
       (ssize a <= stack_peak c)%nat /\ (ssize b <= stack_peak c)%nat)).
  - intros; cbn; lia.
  - intros x o e a b _ Hb; subst; cbn; lia.
  - intros ar i o e a b _ _ Hb; subst; cbn; lia.
  - intros s1 s2 a m b c1 c2 _ IH1 _ IH2; cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH _; cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH _; cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH; cbn; lia.
  - intros x e1 s e2 a b' b c _ _ _ _ IH _ Hb; subst; cbn in *; lia.
  - intros x k a b Hk Hb; subst. pose proof (ssize_push a x k Hk) as E.
    unfold setv, sets in *; simpl in *; lia.
  - intros x k a b v rest Hk Hx Hs Hb; subst. pose proof (ssize_pop a x k v rest Hk Hs) as E.
    unfold setv, sets in *; simpl in *; lia.
  - intros p a b c _ IH; cbn; lia.
  - intros p a b c _ IH; cbn; lia.
  - intros e1 s1 s2 e2 a b c _ IH _; exact IH.
  - intros e1 s1 s2 e2 a a1 a2 b c1 c2 c3 _ IH1 _ _ IH2 _ _ IH3; cbn; lia.
Qed.

(* --------------------------------------------------------------------- *)
(** ** Determinism: the final state *and the cost* are determined *)

Theorem exec_det : forall s a b c, exec s a b c ->
  forall b' c', exec s a b' c' -> b = b' /\ c = c'.
Proof.
  apply (exec_mut
    (fun s a b c (_ : exec s a b c) =>
       forall b' c', exec s a b' c' -> b = b' /\ c = c')
    (fun e1 s1 s2 e2 a b c (_ : lp e1 s1 s2 e2 a b c) =>
       forall b' c', lp e1 s1 s2 e2 a b' c' -> b = b' /\ c = c')).
  - (* Skip *) intros a b' c' Hb'; inversion Hb'; subst; auto.
  - (* Assign *) intros x o e a b Hocc Hb b' c' Hb'; inversion Hb'; subst; auto.
  - (* AAssign *) intros ar i o e a b Hi He Hb b' c' Hb'; inversion Hb'; subst; auto.
  - (* Seq *) intros s1 s2 a m b c1 c2 H1 IH1 H2 IH2 b' c' Hb'; inversion Hb'; subst.
    match goal with
    | He1 : exec s1 a ?mid ?cc1, He2 : exec s2 ?mid b' ?cc2 |- _ =>
        destruct (IH1 _ _ He1) as [Em Ec1]; subst;
        destruct (IH2 _ _ He2) as [Eb Ec2]; subst; auto
    end.
  - (* IfT *) intros e1 s1 s2 e2 a b c He1 H IH He2 b' c' Hb'; inversion Hb'; subst; [| congruence].
    match goal with Hx : exec s1 a b' _ |- _ => destruct (IH _ _ Hx) as [-> ->] end; auto.
  - (* IfF *) intros e1 s1 s2 e2 a b c He1 H IH He2 b' c' Hb'; inversion Hb'; subst; [congruence |].
    match goal with Hx : exec s2 a b' _ |- _ => destruct (IH _ _ Hx) as [-> ->] end; auto.
  - (* Loop *) intros e1 s1 s2 e2 a b c He1 H IH b' c' Hb'; inversion Hb'; subst.
    match goal with Hx : lp e1 s1 s2 e2 a b' _ |- _ => destruct (IH _ _ Hx) as [-> ->] end; auto.
  - (* Local *) intros x e1 s e2 a b' b c Hx He1 He2 H IH Hb' Hb bb cc Hbb; inversion Hbb; subst.
    match goal with
    | Hx2 : exec s _ ?b2 ?c2 |- setv _ _ _ = setv ?b2 _ _ /\ _ =>
        destruct (IH _ _ Hx2) as [E1 E2]; subst
    end; auto.
  - (* Push *) intros x k a b Hk Hb b' c' Hb'; inversion Hb'; subst; auto.
  - (* Pop *) intros x k a b v rest Hk Hx Hs Hb b' c' Hb'; inversion Hb'; subst.
    match goal with
    | Hs2 : stks a k = ?v2 :: ?r2 |- sets (setv a x v) k rest = sets (setv a x ?v2) k ?r2 /\ _ =>
        rewrite Hs in Hs2; injection Hs2; intros; subst
    end; auto.
  - (* Call *) intros p a b c H IH b' c' Hb'; inversion Hb'; subst.
    match goal with Hx : exec (Γ p) a b' _ |- _ => destruct (IH _ _ Hx) as [-> ->] end; auto.
  - (* Uncall *) intros p a b c H IH b' c' Hb'; inversion Hb'; subst.
    match goal with Hx : exec (invert (Γ p)) a b' _ |- _ => destruct (IH _ _ Hx) as [-> ->] end; auto.
  - (* L_one *) intros e1 s1 s2 e2 a b c H IH He b' c' Hb'; inversion Hb'; subst.
    + match goal with Hx : exec s1 a b' _ |- _ => destruct (IH _ _ Hx) as [-> ->] end; auto.
    + (* the other run took another round: its first leg has [eval _ e2 = 0],
         contradicting the exit test [eval b e2 <> 0] of this single round. *)
      match goal with
      | Hx : exec s1 a ?aa _, He0 : eval ?aa e2 = 0 |- _ =>
          destruct (IH _ _ Hx) as [E1 E2]; subst
      end; congruence.
  - (* L_more *)
    intros e1 s1 s2 e2 a a1 a2 b c1 c2 c3 H1 IH1 He2 H2 IH2 He1 H3 IH3 b' c' Hb'; inversion Hb'; subst.
    + (* the other run exited immediately: contradicts our continuing round. *)
      match goal with Hx : exec s1 a b' _ |- _ => destruct (IH1 _ _ Hx) as [E1 E2]; subst end;
      congruence.
    + match goal with
      | Hi1 : exec s1 a ?aa1 _, Hi2 : exec s2 ?aa1 ?aa2 _, Hi3 : lp e1 s1 s2 e2 ?aa2 b' _ |- _ =>
          destruct (IH1 _ _ Hi1) as [E1 E1']; subst;
          destruct (IH2 _ _ Hi2) as [E2 E2']; subst;
          destruct (IH3 _ _ Hi3) as [E3 E3']; subst
      end; auto.
Qed.

(* --------------------------------------------------------------------- *)
(** ** Reversal preserves the cost exactly *)

(** Open iteration with accumulated cost (cf. [Janus.opn]). *)
Inductive opn (e1 : expr) (s1 s2 : stmt) (e2 : expr) : state -> state -> cost -> Prop :=
| O_nil  : forall a, opn e1 s1 s2 e2 a a czero
| O_cons : forall a a1 a2 b c1 c2 c3,
    exec s1 a a1 c1 -> eval a1 e2 = 0 ->
    exec s2 a1 a2 c2 -> eval a2 e1 = 0 ->
    opn e1 s1 s2 e2 a2 b c3 -> opn e1 s1 s2 e2 a b (cadd c1 (cadd c2 c3)).

Lemma opn_snoc :
  forall e1 s1 s2 e2 a m co, opn e1 s1 s2 e2 a m co ->
  forall m1 m2 c1 c2,
    exec s1 m m1 c1 -> eval m1 e2 = 0 ->
    exec s2 m1 m2 c2 -> eval m2 e1 = 0 ->
    forall c, c = cadd co (cadd c1 c2) -> opn e1 s1 s2 e2 a m2 c.
Proof.
  intros e1 s1 s2 e2 a m co H.
  induction H; intros m1 m2 c1' c2' Hs1 He2 Hs2 He1 c Hc; subst c.
  - replace (cadd czero (cadd c1' c2')) with (cadd c1' (cadd c2' czero)) by cost_eq.
    eapply O_cons; eauto. apply O_nil.
  - replace (cadd (cadd c1 (cadd c2 c3)) (cadd c1' c2'))
      with (cadd c1 (cadd c2 (cadd c3 (cadd c1' c2')))) by cost_eq.
    eapply O_cons; eauto.
Qed.

Lemma opn_to_lp :
  forall e1 s1 s2 e2 a m co, opn e1 s1 s2 e2 a m co ->
  forall b c1, exec s1 m b c1 -> eval b e2 <> 0 ->
  forall c, c = cadd co c1 -> lp e1 s1 s2 e2 a b c.
Proof.
  intros e1 s1 s2 e2 a m co H. induction H; intros b' c1' Hs1 Hex c Hc; subst c.
  - rewrite cadd_zero_l. apply L_one; assumption.
  - replace (cadd (cadd c1 (cadd c2 c3)) c1') with (cadd c1 (cadd c2 (cadd c3 c1'))) by cost_eq.
    eapply L_more; eauto.
Qed.

Lemma assign_inv_ok :
  forall a x o e, occurs x e = false ->
    exec (Assign x (ainv o) e) (setv a x (adenote o (vars a x) (eval a e))) a
         (cprim (ssize (setv a x (adenote o (vars a x) (eval a e))))).
Proof.
  intros a x o e Hocc.
  eapply E_Assign; [assumption |].
  unfold setv at 1 2; simpl. rewrite update_eq.
  rewrite (eval_setv_notin x _ a e Hocc). rewrite ainv_correct.
  rewrite update_shadow, update_same. destruct a; reflexivity.
Qed.

Lemma aassign_inv_ok :
  forall a ar i o e, aoccurs ar i = false -> aoccurs ar e = false ->
    exec (AAssign ar i (ainv o) e)
         (seta a ar (eval a i) (adenote o (arrs a ar (eval a i)) (eval a e))) a
         (cprim (ssize (seta a ar (eval a i) (adenote o (arrs a ar (eval a i)) (eval a e))))).
Proof.
  intros a ar i o e Hi He.
  eapply E_AAssign; [assumption | assumption |].
  rewrite (eval_seta_notin ar _ _ a i Hi).
  rewrite (eval_seta_notin ar _ _ a e He).
  unfold seta at 1 2; simpl. rewrite aupd_eq, ainv_correct, aupd_shadow, aupd_same.
  destruct a; reflexivity.
Qed.

Theorem exec_cost_rev : forall s a b c, exec s a b c -> exec (invert s) b a c.
Proof.
  apply (exec_mut
    (fun s a b c (_ : exec s a b c) => exec (invert s) b a c)
    (fun e1 s1 s2 e2 a b c (_ : lp e1 s1 s2 e2 a b c) =>
       exists q co c1, opn e2 (invert s1) (invert s2) e1 b q co /\
                       exec (invert s1) q a c1 /\ c = cadd co c1)).
  - (* Skip *) intros a. apply E_Skip.
  - (* Assign *) intros x o e a b Hocc Hb. cbn [invert]. subst b. apply assign_inv_ok; assumption.
  - (* AAssign *) intros ar i o e a b Hi He Hb. cbn [invert]. subst b. apply aassign_inv_ok; assumption.
  - (* Seq *) intros s1 s2 a m b c1 c2 H1 IH1 H2 IH2. cbn [invert]. rewrite cadd_comm.
    eapply E_Seq; eassumption.
  - (* IfT *) intros e1 s1 s2 e2 a b c He1 H IH He2. cbn [invert]. apply E_IfT; assumption.
  - (* IfF *) intros e1 s1 s2 e2 a b c He1 H IH He2. cbn [invert]. apply E_IfF; assumption.
  - (* Loop *) intros e1 s1 s2 e2 a b c He1 H IH. cbn [invert].
    destruct IH as [q [co [c1 [Hopn [Hq Hc]]]]].
    apply E_Loop.
    + eapply lp_exit_true; eassumption.
    + eapply opn_to_lp; eauto.
  - (* Local *) intros x e1 s e2 a b' b c Hx He1 He2 H IH Hb' Hb. cbn [invert]. subst b.
    eapply E_Local with (b' := setv a x (eval a e1)).
    + unfold setv; simpl; apply update_eq.
    + assumption.
    + assumption.
    + rewrite (eval_setv_notin x 0 b' e2 He2).
      rewrite <- Hb' at 1.
      replace (setv (setv b' x 0) x (vars b' x)) with b'; [exact IH |].
      unfold setv; simpl. rewrite update_shadow, update_same. destruct b'; reflexivity.
    + rewrite (eval_setv_notin x _ a e1 He1). unfold setv; simpl. apply update_eq.
    + unfold setv; simpl. rewrite update_shadow. rewrite <- Hx.
      rewrite update_same. destruct a; reflexivity.
  - (* Push *) intros x k a b Hk Hb. cbn [invert]. subst b.
    rewrite <- (ssize_push a x k Hk).
    eapply E_Pop with (v := vars a x) (rest := stks a k).
    + unfold setv, sets; simpl; assumption.
    + unfold setv, sets; simpl; apply update_eq.
    + unfold setv, sets; simpl; apply supd_eq.
    + unfold setv, sets; simpl. rewrite update_shadow, supd_shadow, supd_same.
      rewrite update_same. destruct a; reflexivity.
  - (* Pop *) intros x k a b v rest Hk Hx Hs Hb. cbn [invert]. subst b.
    rewrite <- (ssize_pop a x k v rest Hk Hs).
    eapply E_Push.
    + unfold setv, sets; simpl; assumption.
    + unfold setv, sets; simpl. rewrite update_eq, supd_eq, supd_shadow.
      rewrite <- Hs at 1. rewrite supd_same, update_shadow.
      rewrite <- Hx. rewrite update_same. destruct a; reflexivity.
  - (* Call *) intros p a b c H IH. cbn [invert]. apply E_Uncall; assumption.
  - (* Uncall *) intros p a b c H IH. cbn [invert]. apply E_Call.
    rewrite invert_invol in IH. assumption.
  - (* L_one *) intros e1 s1 s2 e2 a b c H IH He.
    exists b, czero, c. split; [apply O_nil | split; [assumption | cost_eq]].
  - (* L_more *) intros e1 s1 s2 e2 a a1 a2 b c1 c2 c3 H1 IH1 He2 H2 IH2 He1 H3 IH3.
    destruct IH3 as [q [co [c3' [Hopn [Hq Hc]]]]]. subst c3.
    exists a1, (cadd co (cadd c3' c2)), c1.
    split; [| split; [assumption | cost_eq]].
    eapply opn_snoc; eauto.
Qed.

Corollary exec_cost_iff : forall s a b c, exec s a b c <-> exec (invert s) b a c.
Proof.
  intros; split; intro H.
  - apply exec_cost_rev; assumption.
  - apply exec_cost_rev in H; rewrite invert_invol in H; assumption.
Qed.

Corollary exec_injective : forall s a a' b c c',
  exec s a b c -> exec s a' b c' -> a = a' /\ c = c'.
Proof.
  intros s a a' b c c' H1 H2.
  apply exec_cost_rev in H1. apply exec_cost_rev in H2.
  eapply exec_det; eauto.
Qed.

End Sem.

(* ************************************************************************* *)
(** ** Law 3: soundness of syntactic resource checks

    These are the theorems behind the static checks of [jana_py/costcheck.py].
    Assumptions are explicit and minimal:
      - (a) "no push" must mean *no push and no pop*: an [uncall] runs the
        inverted body, in which every push has become a pop and vice versa.
      - (b),(c) acyclicity of the call graph is witnessed by a ranking
        [rank : pname -> nat] with rank(callee) < rank(caller); the bound [h]
        plays the role of the longest path from the entry.
      - all predicates are closed under [invert], so [uncall] needs no extra
        hypothesis. *)

(** [stackfree ok s]: no push/pop in [s], and every call site targets a
    procedure accepted by [ok] (the reachable, already-checked procedures). *)
Fixpoint stackfree (ok : pname -> bool) (s : stmt) : bool :=
  match s with
  | Skip | Assign _ _ _ | AAssign _ _ _ _ => true
  | Seq s1 s2 | If _ s1 s2 _ | Loop _ s1 s2 _ => andb (stackfree ok s1) (stackfree ok s2)
  | Local _ _ s _ => stackfree ok s
  | Push _ _ | Pop _ _ => false
  | Call p | Uncall p => ok p
  end.

Lemma stackfree_invert : forall ok s, stackfree ok (invert s) = stackfree ok s.
Proof.
  induction s; simpl; try reflexivity.
  - rewrite IHs1, IHs2; apply andb_comm.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - assumption.
Qed.

(** [calls_below rank h s]: every call site in [s] targets a procedure of
    rank < h. *)
Fixpoint calls_below (rank : pname -> nat) (h : nat) (s : stmt) : bool :=
  match s with
  | Skip | Assign _ _ _ | AAssign _ _ _ _ | Push _ _ | Pop _ _ => true
  | Seq s1 s2 | If _ s1 s2 _ | Loop _ s1 s2 _ =>
      andb (calls_below rank h s1) (calls_below rank h s2)
  | Local _ _ s _ => calls_below rank h s
  | Call p | Uncall p => Nat.ltb (rank p) h
  end.

Lemma calls_below_invert : forall rank h s, calls_below rank h (invert s) = calls_below rank h s.
Proof.
  induction s; simpl; try reflexivity.
  - rewrite IHs1, IHs2; apply andb_comm.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - assumption.
Qed.

Lemma calls_below_mono : forall rank h h' s, (h <= h')%nat ->
  calls_below rank h s = true -> calls_below rank h' s = true.
Proof.
  intros rank h h' s Hle; induction s; simpl; intro H; try reflexivity;
    try (apply andb_true_iff in H; destruct H as [H1 H2];
         rewrite IHs1, IHs2 by assumption; reflexivity);
    try (apply IHs; assumption);
    apply Nat.ltb_lt in H; apply Nat.ltb_lt; lia.
Qed.

(** [callfree s]: no call/uncall at all in [s].
    [loops_callfree s]: no call/uncall inside any loop body (either part). *)
Fixpoint callfree (s : stmt) : bool :=
  match s with
  | Skip | Assign _ _ _ | AAssign _ _ _ _ | Push _ _ | Pop _ _ => true
  | Seq s1 s2 | If _ s1 s2 _ | Loop _ s1 s2 _ => andb (callfree s1) (callfree s2)
  | Local _ _ s _ => callfree s
  | Call _ | Uncall _ => false
  end.

Fixpoint loops_callfree (s : stmt) : bool :=
  match s with
  | Loop _ s1 s2 _ => andb (callfree s1) (callfree s2)
  | Seq s1 s2 | If _ s1 s2 _ => andb (loops_callfree s1) (loops_callfree s2)
  | Local _ _ s _ => loops_callfree s
  | _ => true
  end.

Lemma callfree_invert : forall s, callfree (invert s) = callfree s.
Proof.
  induction s; simpl; try reflexivity.
  - rewrite IHs1, IHs2; apply andb_comm.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - assumption.
Qed.

Lemma loops_callfree_invert : forall s, loops_callfree (invert s) = loops_callfree s.
Proof.
  induction s; simpl; try reflexivity.
  - rewrite IHs1, IHs2; apply andb_comm.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite !callfree_invert; reflexivity.
  - assumption.
Qed.

(** Syntactic call count of a statement given a cost [g p] per call site of
    [p]; loop bodies contribute 0 (they are required to be call-free). *)
Fixpoint cbound_s (g : pname -> nat) (s : stmt) : nat :=
  match s with
  | Seq s1 s2 | If _ s1 s2 _ => (cbound_s g s1 + cbound_s g s2)%nat
  | Local _ _ s _ => cbound_s g s
  | Call p | Uncall p => g p
  | _ => 0%nat
  end.

Lemma cbound_s_invert : forall g s, cbound_s g (invert s) = cbound_s g s.
Proof.
  induction s; simpl; try reflexivity.
  - rewrite IHs1, IHs2; lia.
  - rewrite IHs1, IHs2; reflexivity.
  - assumption.
Qed.

Section Checks.

Variable Γ : pname -> stmt.

(** (a) No push/pop anywhere reachable => the stack never grows: the peak is
    the stack size at entry (0 when all stacks start empty). *)
Theorem no_push_stack_zero : forall ok,
  (forall p, ok p = true -> stackfree ok (Γ p) = true) ->
  forall s a b c, exec Γ s a b c -> stackfree ok s = true ->
  stack_peak c = ssize a /\ ssize b = ssize a.
Proof.
  intros ok Henv.
  apply (exec_mut Γ
    (fun s a b c (_ : exec Γ s a b c) =>
       stackfree ok s = true -> stack_peak c = ssize a /\ ssize b = ssize a)
    (fun e1 s1 s2 e2 a b c (_ : lp Γ e1 s1 s2 e2 a b c) =>
       stackfree ok s1 = true -> stackfree ok s2 = true ->
       stack_peak c = ssize a /\ ssize b = ssize a)).
  - intros a _; cbn; auto.
  - intros x o e a b _ Hb _; subst; cbn; auto.
  - intros ar i o e a b _ _ Hb _; subst; cbn; auto.
  - intros s1 s2 a m b c1 c2 _ IH1 _ IH2 Hsf; cbn in Hsf.
    apply andb_true_iff in Hsf; destruct Hsf as [H1 H2].
    specialize (IH1 H1); specialize (IH2 H2); cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH _ Hsf; cbn in Hsf.
    apply andb_true_iff in Hsf; destruct Hsf as [H1 H2]. specialize (IH H1); cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH _ Hsf; cbn in Hsf.
    apply andb_true_iff in Hsf; destruct Hsf as [H1 H2]. specialize (IH H2); cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH Hsf; cbn in Hsf.
    apply andb_true_iff in Hsf; destruct Hsf as [H1 H2]. specialize (IH H1 H2); cbn; lia.
  - intros x e1 s e2 a b' b c _ _ _ _ IH _ Hb Hsf; subst; cbn in Hsf.
    specialize (IH Hsf); cbn in *; lia.
  - intros x k a b _ _ Hsf; discriminate.
  - intros x k a b v rest _ _ _ _ Hsf; discriminate.
  - intros p a b c _ IH Hsf; cbn in Hsf; cbn. apply IH, Henv, Hsf.
  - intros p a b c _ IH Hsf; cbn in Hsf; cbn. apply IH. rewrite stackfree_invert. apply Henv, Hsf.
  - intros e1 s1 s2 e2 a b c _ IH _ H1 H2. apply IH, H1.
  - intros e1 s1 s2 e2 a a1 a2 b c1 c2 c3 _ IH1 _ _ IH2 _ _ IH3 H1 H2.
    specialize (IH1 H1); specialize (IH2 H2); specialize (IH3 H1 H2); cbn; lia.
Qed.

(** The call graph is acyclic, witnessed by a ranking: every procedure only
    calls procedures of strictly smaller rank. *)
Definition env_ranked (rank : pname -> nat) : Prop :=
  forall p, calls_below rank (rank p) (Γ p) = true.

(** (b) Acyclic call graph => the call depth never exceeds the rank bound. *)
Theorem acyclic_depth_bound : forall rank, env_ranked rank ->
  forall s a b c, exec Γ s a b c ->
  forall h, calls_below rank h s = true -> (call_depth_peak c <= h)%nat.
Proof.
  intros rank Henv.
  apply (exec_mut Γ
    (fun s a b c (_ : exec Γ s a b c) =>
       forall h, calls_below rank h s = true -> (call_depth_peak c <= h)%nat)
    (fun e1 s1 s2 e2 a b c (_ : lp Γ e1 s1 s2 e2 a b c) =>
       forall h, calls_below rank h s1 = true -> calls_below rank h s2 = true ->
       (call_depth_peak c <= h)%nat)).
  - intros a h _; cbn; lia.
  - intros x o e a b _ _ h _; cbn; lia.
  - intros ar i o e a b _ _ _ h _; cbn; lia.
  - intros s1 s2 a m b c1 c2 _ IH1 _ IH2 h Hcb; cbn in Hcb.
    apply andb_true_iff in Hcb; destruct Hcb as [H1 H2].
    specialize (IH1 h H1); specialize (IH2 h H2); cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH _ h Hcb; cbn in Hcb.
    apply andb_true_iff in Hcb; destruct Hcb as [H1 H2]. specialize (IH h H1); cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH _ h Hcb; cbn in Hcb.
    apply andb_true_iff in Hcb; destruct Hcb as [H1 H2]. specialize (IH h H2); cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH h Hcb; cbn in Hcb.
    apply andb_true_iff in Hcb; destruct Hcb as [H1 H2]. specialize (IH h H1 H2); cbn; lia.
  - intros x e1 s e2 a b' b c _ _ _ _ IH _ _ h Hcb; cbn in Hcb. specialize (IH h Hcb); cbn; lia.
  - intros x k a b _ _ h _; cbn; lia.
  - intros x k a b v rest _ _ _ _ h _; cbn; lia.
  - intros p a b c _ IH h Hcb; cbn in Hcb. apply Nat.ltb_lt in Hcb.
    specialize (IH (rank p) (Henv p)); cbn; lia.
  - intros p a b c _ IH h Hcb; cbn in Hcb. apply Nat.ltb_lt in Hcb.
    specialize (IH (rank p)). rewrite calls_below_invert in IH.
    specialize (IH (Henv p)); cbn; lia.
  - intros e1 s1 s2 e2 a b c _ IH _ h H1 H2. apply IH, H1.
  - intros e1 s1 s2 e2 a a1 a2 b c1 c2 c3 _ IH1 _ _ IH2 _ _ IH3 h H1 H2.
    specialize (IH1 h H1); specialize (IH2 h H2); specialize (IH3 h H1 H2); cbn; lia.
Qed.

(** A call-free statement performs no call events. *)
Lemma exec_callfree : forall s a b c, exec Γ s a b c -> callfree s = true -> total_calls c = 0%nat.
Proof.
  apply (exec_mut Γ
    (fun s a b c (_ : exec Γ s a b c) => callfree s = true -> total_calls c = 0%nat)
    (fun e1 s1 s2 e2 a b c (_ : lp Γ e1 s1 s2 e2 a b c) =>
       callfree s1 = true -> callfree s2 = true -> total_calls c = 0%nat)).
  - intros a _; reflexivity.
  - intros x o e a b _ _ _; reflexivity.
  - intros ar i o e a b _ _ _ _; reflexivity.
  - intros s1 s2 a m b c1 c2 _ IH1 _ IH2 Hcf; cbn in Hcf.
    apply andb_true_iff in Hcf; destruct Hcf as [H1 H2].
    specialize (IH1 H1); specialize (IH2 H2); cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH _ Hcf; cbn in Hcf.
    apply andb_true_iff in Hcf; destruct Hcf as [H1 H2]. specialize (IH H1); cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH _ Hcf; cbn in Hcf.
    apply andb_true_iff in Hcf; destruct Hcf as [H1 H2]. specialize (IH H2); cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH Hcf; cbn in Hcf.
    apply andb_true_iff in Hcf; destruct Hcf as [H1 H2]. specialize (IH H1 H2); cbn; lia.
  - intros x e1 s e2 a b' b c _ _ _ _ IH _ _ Hcf; cbn in Hcf. specialize (IH Hcf); cbn; lia.
  - intros x k a b _ _ _; reflexivity.
  - intros x k a b v rest _ _ _ _ _; reflexivity.
  - intros p a b c _ _ Hcf; discriminate.
  - intros p a b c _ _ Hcf; discriminate.
  - intros e1 s1 s2 e2 a b c _ IH _ H1 H2. apply IH, H1.
  - intros e1 s1 s2 e2 a a1 a2 b c1 c2 c3 _ IH1 _ _ IH2 _ _ IH3 H1 H2.
    specialize (IH1 H1); specialize (IH2 H2); specialize (IH3 H1 H2); cbn; lia.
Qed.

(** Per-call-site cost with fuel [h]: 1 + the bound of the callee's body. *)
Fixpoint gh (h : nat) : pname -> nat :=
  match h with
  | O => fun _ => 0%nat
  | S h' => fun p => S (cbound_s (gh h') (Γ p))
  end.

(** The syntactic call bound of the card:
    calls(P) = Σ_{call sites in P} (1 + calls(callee)), loops contribute 0. *)
Definition cbound (h : nat) (s : stmt) : nat := cbound_s (gh h) s.

(** (c) No call inside any loop body + acyclic call graph => the number of
    call events is bounded by the syntactic count, independently of the input. *)
Theorem no_call_in_loop_bounded_calls : forall rank, env_ranked rank ->
  (forall p, loops_callfree (Γ p) = true) ->
  forall s a b c, exec Γ s a b c -> loops_callfree s = true ->
  forall h, calls_below rank h s = true -> (total_calls c <= cbound h s)%nat.
Proof.
  intros rank Henv Hloops.
  unfold cbound.
  apply (exec_mut Γ
    (fun s a b c (_ : exec Γ s a b c) =>
       loops_callfree s = true ->
       forall h, calls_below rank h s = true -> (total_calls c <= cbound_s (gh h) s)%nat)
    (fun e1 s1 s2 e2 a b c (_ : lp Γ e1 s1 s2 e2 a b c) =>
       callfree s1 = true -> callfree s2 = true -> total_calls c = 0%nat)).
  - intros a _ h _; cbn; lia.
  - intros x o e a b _ _ _ h _; cbn; lia.
  - intros ar i o e a b _ _ _ _ h _; cbn; lia.
  - intros s1 s2 a m b c1 c2 _ IH1 _ IH2 Hlc h Hcb; cbn in Hlc, Hcb.
    apply andb_true_iff in Hlc; destruct Hlc as [L1 L2].
    apply andb_true_iff in Hcb; destruct Hcb as [H1 H2].
    specialize (IH1 L1 h H1); specialize (IH2 L2 h H2); cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH _ Hlc h Hcb; cbn in Hlc, Hcb.
    apply andb_true_iff in Hlc; destruct Hlc as [L1 L2].
    apply andb_true_iff in Hcb; destruct Hcb as [H1 H2].
    specialize (IH L1 h H1); cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH _ Hlc h Hcb; cbn in Hlc, Hcb.
    apply andb_true_iff in Hlc; destruct Hlc as [L1 L2].
    apply andb_true_iff in Hcb; destruct Hcb as [H1 H2].
    specialize (IH L2 h H2); cbn; lia.
  - intros e1 s1 s2 e2 a b c _ _ IH Hlc h _; cbn in Hlc.
    apply andb_true_iff in Hlc; destruct Hlc as [L1 L2].
    specialize (IH L1 L2); cbn; lia.
  - intros x e1 s e2 a b' b c _ _ _ _ IH _ _ Hlc h Hcb; cbn in Hlc, Hcb.
    specialize (IH Hlc h Hcb); cbn; lia.
  - intros x k a b _ _ _ h _; cbn; lia.
  - intros x k a b v rest _ _ _ _ _ h _; cbn; lia.
  - intros p a b c _ IH _ h Hcb; cbn in Hcb. apply Nat.ltb_lt in Hcb.
    destruct h as [| h']; [lia |].
    specialize (IH (Hloops p) h' (calls_below_mono rank (rank p) h' (Γ p) ltac:(lia) (Henv p))).
    cbn; lia.
  - intros p a b c _ IH _ h Hcb; cbn in Hcb. apply Nat.ltb_lt in Hcb.
    destruct h as [| h']; [lia |].
    rewrite loops_callfree_invert in IH. specialize (IH (Hloops p) h').
    rewrite calls_below_invert, cbound_s_invert in IH.
    specialize (IH (calls_below_mono rank (rank p) h' (Γ p) ltac:(lia) (Henv p))).
    cbn; lia.
  - intros e1 s1 s2 e2 a b c H _ _ H1 H2. eapply exec_callfree; eassumption.
  - intros e1 s1 s2 e2 a a1 a2 b c1 c2 c3 Ha _ _ Hb _ _ _ IH3 H1 H2.
    pose proof (exec_callfree _ _ _ _ Ha H1). pose proof (exec_callfree _ _ _ _ Hb H2).
    specialize (IH3 H1 H2); cbn; lia.
Qed.

End Checks.

(* ************************************************************************* *)
(** ** Arithmetic helpers *)

Lemma to_nat_lt : forall x y, 0 <= x -> x < y -> (Z.to_nat x < Z.to_nat y)%nat.
Proof. intros; apply Z2Nat.inj_lt; lia. Qed.

Lemma to_nat_pos : forall x, 0 < x -> (0 < Z.to_nat x)%nat.
Proof. intros. change 0%nat with (Z.to_nat 0). apply Z2Nat.inj_lt; lia. Qed.

Lemma lxor_cancel1 : forall x y, Z.lxor x (Z.lxor x y) = y.
Proof. intros. rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l. reflexivity. Qed.

Lemma lxor_cancel2 : forall x y, Z.lxor y (Z.lxor x y) = x.
Proof. intros. rewrite (Z.lxor_comm x y). apply lxor_cancel1. Qed.

(* ************************************************************************* *)
(** ** Law 1: gcd (tests/jana2014/fixtures/examples/gcd.ja)

      procedure gcd(int a, int b, stack log)
        from  empty(log)
        loop  if a > b then a -= b  local int t = 1 push(t,log) delocal int t = 0
                       else b -= a  local int t = 0 push(t,log) delocal int t = 0
              fi top(log) = 1
        until a = b

    Parameters are global variables 0 (a), 1 (b); the local t is variable 2;
    the stack log is stack 0; the procedure is number 0. *)

Module GCD.

Notation vA := 0%nat.  Notation vB := 1%nat.  Notation vT := 2%nat.
Notation sLOG := 0%nat.  Notation pGCD := 0%nat.

Definition log_step (v : Z) : stmt := Local vT (Cst v) (Push vT sLOG) (Cst 0).

Definition gcd_if : stmt :=
  If (Bin OGt (Var vA) (Var vB))
     (Seq (Assign vA ASub (Var vB)) (log_step 1))
     (Seq (Assign vB ASub (Var vA)) (log_step 0))
     (Bin OEq (Top sLOG) (Cst 1)).

Definition gcd_loop : stmt :=
  Loop (Empty sLOG) Skip gcd_if (Bin OEq (Var vA) (Var vB)).

Definition Γgcd : pname -> stmt := fun _ => gcd_loop.

(** [SubSteps a b n]: the subtractive Euclid from (a,b) takes [n] steps. *)
Inductive SubSteps : Z -> Z -> nat -> Prop :=
| SS_eq : forall a, SubSteps a a 0
| SS_gt : forall a b n, b < a -> SubSteps (a - b) b n -> SubSteps a b (S n)
| SS_lt : forall a b n, a < b -> SubSteps a (b - a) n -> SubSteps a b (S n).

Lemma SubSteps_det : forall a b n, SubSteps a b n -> forall m, SubSteps a b m -> n = m.
Proof.
  induction 1; intros m Hm; inversion Hm; subst; try lia;
    f_equal; apply IHSubSteps; assumption.
Qed.

Lemma SubSteps_sym : forall a b n, SubSteps a b n -> SubSteps b a n.
Proof.
  induction 1; [apply SS_eq | apply SS_lt; assumption | apply SS_gt; assumption].
Qed.

(** The executable count (fuel = a + b suffices):
      sub_steps a b = 0                       if a = b
                    = 1 + sub_steps (a-b) b   if a > b
                    = 1 + sub_steps a (b-a)   otherwise. *)
Fixpoint sub_steps_f (f : nat) (a b : Z) : nat :=
  match f with
  | O => O
  | S f' => if Z.eqb a b then O
            else if Z.ltb b a then S (sub_steps_f f' (a - b) b)
            else S (sub_steps_f f' a (b - a))
  end.
Definition sub_steps (a b : Z) : nat := sub_steps_f (Z.to_nat (a + b)) a b.

Lemma sub_steps_f_spec : forall f a b, 0 < a -> 0 < b ->
  (Z.to_nat (a + b) <= f)%nat -> SubSteps a b (sub_steps_f f a b).
Proof.
  induction f; intros a b Ha Hb Hf; simpl.
  - pose proof (to_nat_pos (a + b) ltac:(lia)). lia.
  - destruct (Z.eqb a b) eqn:E.
    + apply Z.eqb_eq in E; subst; apply SS_eq.
    + apply Z.eqb_neq in E. destruct (Z.ltb b a) eqn:L.
      * apply Z.ltb_lt in L. apply SS_gt; [assumption |].
        pose proof (to_nat_lt (a - b + b) (a + b) ltac:(lia) ltac:(lia)).
        apply IHf; lia.
      * apply Z.ltb_ge in L. apply SS_lt; [lia |].
        pose proof (to_nat_lt (a + (b - a)) (a + b) ltac:(lia) ltac:(lia)).
        apply IHf; lia.
Qed.

Lemma sub_steps_spec : forall a b, 0 < a -> 0 < b -> SubSteps a b (sub_steps a b).
Proof. intros; apply sub_steps_f_spec; lia. Qed.

(** One loop round, case a > b: subtract, push 1. *)
Lemma gcd_if_gt : forall st a b,
  vars st vA = a -> vars st vB = b -> vars st vT = 0 -> nstk st = 1%nat -> b < a ->
  exists st' c, exec Γgcd gcd_if st st' c /\
    vars st' vA = a - b /\ vars st' vB = b /\ vars st' vT = 0 /\ nstk st' = 1%nat /\
    arrs st' = arrs st /\ stks st' sLOG = 1 :: stks st sLOG /\
    c = mkc 4 (S (length (stks st sLOG))) 0 0.
Proof.
  intros st a b HA HB HT HN Hlt.
  eexists; eexists; split.
  - eapply E_IfT.
    + cbn. rewrite HA, HB, (proj2 (Z.ltb_lt b a) Hlt). discriminate.
    + eapply E_Seq.
      * eapply E_Assign; reflexivity.
      * eapply E_Local.
        -- cbn. exact HT.
        -- reflexivity.
        -- reflexivity.
        -- eapply E_Push; [cbn; lia | reflexivity].
        -- cbn. reflexivity.
        -- reflexivity.
    + cbn. discriminate.
  - cbn. rewrite HA, HB, HN. repeat split. apply cost_ext; cbn; lia.
Qed.

(** One loop round, case a < b: subtract, push 0. *)
Lemma gcd_if_lt : forall st a b,
  vars st vA = a -> vars st vB = b -> vars st vT = 0 -> nstk st = 1%nat -> a < b ->
  exists st' c, exec Γgcd gcd_if st st' c /\
    vars st' vA = a /\ vars st' vB = b - a /\ vars st' vT = 0 /\ nstk st' = 1%nat /\
    arrs st' = arrs st /\ stks st' sLOG = 0 :: stks st sLOG /\
    c = mkc 4 (S (length (stks st sLOG))) 0 0.
Proof.
  intros st a b HA HB HT HN Hlt.
  eexists; eexists; split.
  - eapply E_IfF.
    + cbn. rewrite HA, HB, (proj2 (Z.ltb_ge b a) ltac:(lia)). reflexivity.
    + eapply E_Seq.
      * eapply E_Assign; reflexivity.
      * eapply E_Local.
        -- cbn. exact HT.
        -- reflexivity.
        -- reflexivity.
        -- eapply E_Push; [cbn; lia | reflexivity].
        -- cbn. reflexivity.
        -- reflexivity.
    + cbn. reflexivity.
  - cbn. rewrite HA, HB, HN. repeat split. apply cost_ext; cbn; lia.
Qed.

(** The loop body [s1 (s2 s1)^n] of gcd, by strong induction on a + b. *)
Lemma gcd_lp : forall n a b st, (Z.to_nat (a + b) <= n)%nat -> 0 < a -> 0 < b ->
  vars st vA = a -> vars st vB = b -> vars st vT = 0 -> nstk st = 1%nat ->
  exists st' c k, SubSteps a b k /\
    lp Γgcd (Empty sLOG) Skip gcd_if (Bin OEq (Var vA) (Var vB)) st st' c /\
    vars st' vA = Z.gcd a b /\ vars st' vB = Z.gcd a b /\ vars st' vT = 0 /\
    nstk st' = 1%nat /\ arrs st' = arrs st /\
    length (stks st' sLOG) = (k + length (stks st sLOG))%nat /\
    c = mkc (4 * k) (length (stks st sLOG) + k) 0 0.
Proof.
  induction n; intros a b st Hn Ha Hb HA HB HT HN.
  - exfalso. pose proof (to_nat_pos (a + b) ltac:(lia)). lia.
  - destruct (Z.eq_dec a b) as [Heq | Hne].
    + rewrite <- Heq in *. clear Heq. exists st, (cskip (ssize st)), 0%nat.
      split; [apply SS_eq |].
      split; [apply L_one; [apply E_Skip | cbn; rewrite HA, HB, Z.eqb_refl; discriminate] |].
      rewrite Z.gcd_diag, Z.abs_eq by lia.
      repeat split; try assumption. rewrite HN. apply cost_ext; cbn; lia.
    + destruct (Z_lt_le_dec b a) as [Hgt | Hle].
      * destruct (gcd_if_gt st a b HA HB HT HN Hgt)
          as [a2 [c2 [Hex [HA2 [HB2 [HT2 [HN2 [Harr2 [Hst2 Hc2]]]]]]]]].
        assert (Hn' : (Z.to_nat (a - b + b) <= n)%nat).
        { pose proof (to_nat_lt (a - b + b) (a + b) ltac:(lia) ltac:(lia)). lia. }
        destruct (IHn (a - b) b a2 Hn' ltac:(lia) Hb HA2 HB2 HT2 HN2)
          as [st' [c3 [k [HSS [Hlp [HA' [HB' [HT' [HN' [Harr' [Hlen' Hc3]]]]]]]]]]].
        exists st', (cadd (cskip (ssize st)) (cadd c2 c3)), (S k).
        split; [apply SS_gt; assumption |].
        split.
        { eapply L_more.
          - apply E_Skip.
          - cbn. rewrite HA, HB, (proj2 (Z.eqb_neq a b) Hne). reflexivity.
          - exact Hex.
          - cbn. rewrite Hst2. reflexivity.
          - exact Hlp. }
        rewrite HA', HB', (Z.gcd_comm (a - b) b), Z.gcd_sub_diag_r, Z.gcd_comm.
        repeat split; try assumption; try congruence.
        -- rewrite Hlen', Hst2. cbn. lia.
        -- subst c2 c3. rewrite HN, Hst2. apply cost_ext; cbn; lia.
      * destruct (gcd_if_lt st a b HA HB HT HN ltac:(lia))
          as [a2 [c2 [Hex [HA2 [HB2 [HT2 [HN2 [Harr2 [Hst2 Hc2]]]]]]]]].
        assert (Hn' : (Z.to_nat (a + (b - a)) <= n)%nat).
        { pose proof (to_nat_lt (a + (b - a)) (a + b) ltac:(lia) ltac:(lia)). lia. }
        destruct (IHn a (b - a) a2 Hn' Ha ltac:(lia) HA2 HB2 HT2 HN2)
          as [st' [c3 [k [HSS [Hlp [HA' [HB' [HT' [HN' [Harr' [Hlen' Hc3]]]]]]]]]]].
        exists st', (cadd (cskip (ssize st)) (cadd c2 c3)), (S k).
        split; [apply SS_lt; [lia | assumption] |].
        split.
        { eapply L_more.
          - apply E_Skip.
          - cbn. rewrite HA, HB, (proj2 (Z.eqb_neq a b) Hne). reflexivity.
          - exact Hex.
          - cbn. rewrite Hst2. reflexivity.
          - exact Hlp. }
        rewrite HA', HB', Z.gcd_sub_diag_r.
        repeat split; try assumption; try congruence.
        -- rewrite Hlen', Hst2. cbn. lia.
        -- subst c2 c3. rewrite HN, Hst2. apply cost_ext; cbn; lia.
Qed.

(** *** L1.  gcd on (a, b) with a, b > 0 and an empty log terminates with
    a = b = gcd(a,b); the log holds exactly [sub_steps a b] values, the stack
    peak is [sub_steps a b], and steps = 2 + 4 sub_steps a b
    (call + from, plus if/assign/local/push per round). *)
Theorem gcd_stack_eq_divisions : forall a b st, 0 < a -> 0 < b ->
  vars st vA = a -> vars st vB = b -> vars st vT = 0 ->
  nstk st = 1%nat -> stks st sLOG = [] ->
  exists st' c,
    exec Γgcd (Call pGCD) st st' c /\
    vars st' vA = Z.gcd a b /\ vars st' vB = Z.gcd a b /\
    length (stks st' sLOG) = sub_steps a b /\
    stack_peak c = sub_steps a b /\
    steps c = (2 + 4 * sub_steps a b)%nat /\
    call_depth_peak c = 1%nat /\ total_calls c = 1%nat.
Proof.
  intros a b st Ha Hb HA HB HT HN HL.
  destruct (gcd_lp (Z.to_nat (a + b)) a b st (le_n _) Ha Hb HA HB HT HN)
    as [st' [c [k [HSS [Hlp [HA' [HB' [_ [_ [_ [Hlen Hc]]]]]]]]]]].
  assert (Hk : k = sub_steps a b).
  { eapply SubSteps_det; [exact HSS | apply sub_steps_spec; assumption]. }
  exists st', (ccall (cstmt c)).
  split.
  { apply E_Call. unfold Γgcd, gcd_loop. apply E_Loop.
    - cbn. rewrite HL. discriminate.
    - exact Hlp. }
  subst c k. rewrite HL in Hlen. cbn in Hlen.
  repeat split; try assumption; cbn; try rewrite HL; cbn; lia.
Qed.

(** *** Relation to the Euclidean division sequence.
    [Quots a b l]: [l] is the list of quotients of the Euclidean division
    sequence (a,b) -> (b, a mod b) -> ... ending at the first zero remainder.
    Its length is the number of Euclidean divisions.  The subtractive count is
    the sum of the quotients minus one (the last division, which ends with
    a = b, performs one subtraction fewer than its quotient). *)
Inductive Quots : Z -> Z -> list Z -> Prop :=
| Q_last : forall a b, 0 < b -> a mod b = 0 -> Quots a b [a / b]
| Q_more : forall a b l, 0 < b -> a mod b <> 0 -> Quots b (a mod b) l -> Quots a b (a / b :: l).

Definition zsum (l : list Z) : Z := fold_right Z.add 0 l.

Lemma Quots_total : forall n a b, (Z.to_nat (a + 2 * b) <= n)%nat -> 0 < a -> 0 < b ->
  exists l, Quots a b l.
Proof.
  induction n; intros a b Hn Ha Hb.
  - exfalso. pose proof (to_nat_pos (a + 2 * b) ltac:(lia)). lia.
  - destruct (Z.eq_dec (a mod b) 0) as [E | E].
    + exists [a / b]. apply Q_last; assumption.
    + pose proof (Z.mod_pos_bound a b Hb) as [Hr0 Hrb].
      assert (Hn' : (Z.to_nat (b + 2 * (a mod b)) <= n)%nat).
      { pose proof (to_nat_lt (b + 2 * (a mod b)) (a + 2 * b) ltac:(lia)).
        destruct (Z_lt_le_dec a b) as [Hab | Hab].
        - rewrite Z.mod_small in * by lia. lia.
        - lia. }
      destruct (IHn b (a mod b) Hn' Hb ltac:(lia)) as [l Hl].
      exists (a / b :: l). apply Q_more; assumption.
Qed.

(** k subtractions of b from (k+1) b reach b. *)
Lemma SubSteps_mult : forall k b, 0 < b -> SubSteps (Z.of_nat k * b + b) b k.
Proof.
  induction k; intros b Hb.
  - replace (Z.of_nat 0 * b + b) with b by lia. apply SS_eq.
  - rewrite Nat2Z.inj_succ. apply SS_gt; [nia |].
    replace (Z.succ (Z.of_nat k) * b + b - b) with (Z.of_nat k * b + b) by lia.
    apply IHk; assumption.
Qed.

(** k subtractions of b from k b + r (0 < r < b) reach r. *)
Lemma SubSteps_shift : forall k b r m, 0 < b -> 0 < r < b ->
  SubSteps r b m -> SubSteps (Z.of_nat k * b + r) b (k + m).
Proof.
  induction k; intros b r m Hb Hr Hm.
  - replace (Z.of_nat 0 * b + r) with r by lia. exact Hm.
  - rewrite Nat2Z.inj_succ. apply SS_gt; [nia |].
    replace (Z.succ (Z.of_nat k) * b + r - b) with (Z.of_nat k * b + r) by lia.
    apply IHk; assumption.
Qed.

(** sub_steps a b = (sum of the Euclidean quotients) - 1. *)
Theorem SubSteps_quotients : forall a b l, 0 < a -> Quots a b l ->
  forall n, SubSteps a b n -> Z.of_nat n + 1 = zsum l.
Proof.
  intros a b l Ha H. induction H; intros n Hn.
  - (* a = b * q, q >= 1 : q - 1 subtractions *)
    pose proof (Z.div_mod a b ltac:(lia)) as Hdm. rewrite H0 in Hdm.
    assert (Hq : 0 < a / b) by nia.
    destruct (Z.to_nat (a / b)) as [| k] eqn:Ek; [lia |].
    assert (Hqk : a / b = Z.of_nat (S k)) by (rewrite <- Ek, Z2Nat.id; lia).
    assert (HSS : SubSteps a b k).
    { replace a with (Z.of_nat k * b + b) by (rewrite Hqk, Nat2Z.inj_succ in Hdm; nia).
      apply SubSteps_mult; assumption. }
    rewrite (SubSteps_det _ _ _ Hn _ HSS). cbn. lia.
  - (* a = b * q + r, 0 < r < b : q subtractions then continue from (r, b) *)
    pose proof (Z.div_mod a b ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound a b H) as [Hr0 Hrb].
    pose proof (Z.div_pos a b ltac:(lia) H) as Hq0.
    pose proof (sub_steps_spec (a mod b) b ltac:(lia) H) as Hm.
    pose proof (SubSteps_shift (Z.to_nat (a / b)) b (a mod b) _ H ltac:(lia) Hm) as HSS.
    rewrite Z2Nat.id in HSS by assumption.
    replace (a / b * b + a mod b) with a in HSS by nia.
    rewrite (SubSteps_det _ _ _ Hn _ HSS).
    specialize (IHQuots ltac:(lia) _ (SubSteps_sym _ _ _ Hm)).
    unfold zsum in *. cbn. rewrite Nat2Z.inj_add, Z2Nat.id by assumption. lia.
Qed.

Corollary sub_steps_quotients : forall a b l, 0 < a -> 0 < b -> Quots a b l ->
  Z.of_nat (sub_steps a b) + 1 = zsum l.
Proof.
  intros a b l Ha Hb Hq. apply (SubSteps_quotients a b l Ha Hq).
  apply sub_steps_spec; assumption.
Qed.

(** *** Fibonacci corollary. *)
Fixpoint fib (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => match n' with O => 1 | S n'' => fib n' + fib n'' end
  end.

Lemma fib_SS : forall n, fib (S (S n)) = fib (S n) + fib n.
Proof. reflexivity. Qed.

Lemma fib_pos : forall n, 0 <= fib n /\ 0 < fib (S n).
Proof.
  induction n; [cbn; lia |].
  destruct IHn as [H1 H2]. split; [lia |]. rewrite fib_SS. lia.
Qed.

(** From (F(k+2), F(k+1)) the subtractive Euclid takes exactly k steps
    (= the number of Euclidean divisions). *)
Lemma fib_SubSteps2 : forall k,
  SubSteps (fib (S (S k))) (fib (S k)) k /\ SubSteps (fib (S (S (S k)))) (fib (S (S k))) (S k).
Proof.
  induction k.
  - split.
    + apply SS_eq.
    + apply SS_gt; [cbn; lia |]. replace (fib 3 - fib 2) with (fib 2) by (cbn; lia). apply SS_eq.
  - destruct IHk as [IH1 IH2]. split; [exact IH2 |].
    rewrite (fib_SS (S (S k))).
    pose proof (fib_pos (S k)) as [_ Hpos].
    apply SS_gt; [lia |].
    replace (fib (S (S (S k))) + fib (S (S k)) - fib (S (S (S k)))) with (fib (S (S k))) by lia.
    apply SubSteps_sym. exact IH2.
Qed.

Lemma gcd_fib_sub_steps : forall k, sub_steps (fib (S (S k))) (fib (S k)) = k.
Proof.
  intro k. pose proof (fib_pos k) as [_ H1]. pose proof (fib_pos (S k)) as [_ H2].
  eapply SubSteps_det; [apply sub_steps_spec; assumption | apply fib_SubSteps2].
Qed.

(** RC-03's observation (checked there at 6 points), now for every k:
    on consecutive Fibonacci numbers the stack peak of gcd is exactly k. *)
Theorem gcd_fib_stack : forall k st,
  vars st vA = fib (S (S k)) -> vars st vB = fib (S k) -> vars st vT = 0 ->
  nstk st = 1%nat -> stks st sLOG = [] ->
  exists st' c, exec Γgcd (Call pGCD) st st' c /\
    stack_peak c = k /\ length (stks st' sLOG) = k /\ steps c = (2 + 4 * k)%nat.
Proof.
  intros k st HA HB HT HN HL.
  pose proof (fib_pos k) as [_ H1]. pose proof (fib_pos (S k)) as [_ H2].
  destruct (gcd_stack_eq_divisions _ _ st H2 H1 HA HB HT HN HL)
    as [st' [c [Hex [_ [_ [Hlen [Hpk [Hst _]]]]]]]].
  rewrite gcd_fib_sub_steps in Hlen, Hpk, Hst.
  exists st', c. auto.
Qed.

End GCD.

(* ************************************************************************* *)
(** ** Law 2: bubble sort (tests/jana2014/fixtures/examples/bubble_sort.ja)

      procedure bsort(int a[], int sz, stack gb)
        local int i=0
          from  i=0
          loop  local int j = sz - 1
                  from  j = sz-1
                  loop  if a[j] < a[j-1] then
                           local int t1 = a[j]
                             local int t2 = a[j-1]
                               a[j-1] ^= t1 ^ t2
                               a[j]   ^= t1 ^ t2
                             delocal int t2 = a[j]
                           delocal int t1 = a[j-1]
                           local int t = 1  push(t,gb)  delocal int t = 0
                        else
                           local int t = -1 push(t,gb)  delocal int t = 0
                        fi top(gb) = 1
                        j -= 1
                  until j = i
                delocal int j = i
                i += 1
          until i=sz
        delocal int i=sz

    Variables: i=0, j=1, t1=2, t2=3, t=4, sz=5; array a = 0; stack gb = 0. *)

Module BSORT.

Notation vI := 0%nat.  Notation vJ := 1%nat.  Notation vT1 := 2%nat.
Notation vT2 := 3%nat. Notation vT := 4%nat.  Notation vSZ := 5%nat.
Notation aA := 0%nat.  Notation sGB := 0%nat. Notation pBSORT := 0%nat.

Definition jm1 : expr := Bin OSub (Var vJ) (Cst 1).
Definition szm1 : expr := Bin OSub (Var vSZ) (Cst 1).

Definition swap_stmt : stmt :=
  Local vT1 (ARd aA (Var vJ))
    (Local vT2 (ARd aA jm1)
       (Seq (AAssign aA jm1 AXor (Bin OXor (Var vT1) (Var vT2)))
            (AAssign aA (Var vJ) AXor (Bin OXor (Var vT1) (Var vT2))))
       (ARd aA (Var vJ)))
    (ARd aA jm1).

Definition log_step (v : Z) : stmt := Local vT (Cst v) (Push vT sGB) (Cst 0).

Definition bsort_if : stmt :=
  If (Bin OLt (ARd aA (Var vJ)) (ARd aA jm1))
     (Seq swap_stmt (log_step 1))
     (log_step (-1))
     (Bin OEq (Top sGB) (Cst 1)).

Definition inner_body : stmt := Seq bsort_if (Assign vJ ASub (Cst 1)).
Definition inner_e1 : expr := Bin OEq (Var vJ) szm1.
Definition inner_e2 : expr := Bin OEq (Var vJ) (Var vI).
Definition inner_loop : stmt :=
  Local vJ szm1 (Loop inner_e1 Skip inner_body inner_e2) (Var vI).

Definition outer_body : stmt := Seq inner_loop (Assign vI AAdd (Cst 1)).
Definition outer_e1 : expr := Bin OEq (Var vI) (Cst 0).
Definition outer_e2 : expr := Bin OEq (Var vI) (Var vSZ).
Definition bsort_body : stmt :=
  Local vI (Cst 0) (Loop outer_e1 Skip outer_body outer_e2) (Var vSZ).

Definition Γbs : pname -> stmt := fun _ => bsort_body.

(** Number of comparisons: tri n = 0 + 1 + ... + (n-1) = n(n-1)/2. *)
Fixpoint tri (n : nat) : nat :=
  match n with O => O | S n' => (n' + tri n')%nat end.

Lemma tri_twice : forall n, (2 * tri n + n = n * n)%nat.
Proof. induction n; cbn [tri]; nia. Qed.

Lemma tri_div : forall n, tri n = (n * (n - 1) / 2)%nat.
Proof.
  intro n. apply Nat.div_unique with (r := 0%nat); [lia |].
  pose proof (tri_twice n). rewrite Nat.mul_sub_distr_l, Nat.mul_1_r. lia.
Qed.

(** One comparison round (the [if]): any array contents, exactly one push;
    [w] = 1 if the branch swapped (7 statements) and 0 otherwise (3). *)
Lemma bsort_if_run : forall st i j sz,
  vars st vI = i -> vars st vJ = j -> vars st vSZ = sz ->
  vars st vT1 = 0 -> vars st vT2 = 0 -> vars st vT = 0 -> nstk st = 1%nat ->
  exists st' c w, exec Γbs bsort_if st st' c /\
    vars st' vI = i /\ vars st' vJ = j /\ vars st' vSZ = sz /\
    vars st' vT1 = 0 /\ vars st' vT2 = 0 /\ vars st' vT = 0 /\ nstk st' = 1%nat /\
    length (stks st' sGB) = S (length (stks st sGB)) /\ (w <= 1)%nat /\
    c = mkc (3 + 4 * w) (S (length (stks st sGB))) 0 0.
Proof.
  intros st i j sz HI HJ HSZ HT1 HT2 HT HN.
  destruct (Z.ltb (arrs st aA j) (arrs st aA (j - 1))) eqn:Hcmp.
  - (* then: swap, push 1 *)
    eexists; eexists; exists 1%nat; split.
    + eapply E_IfT.
      * cbn. rewrite HJ, Hcmp. discriminate.
      * eapply E_Seq.
        -- eapply E_Local.
           ++ cbn; exact HT1.
           ++ reflexivity.
           ++ reflexivity.
           ++ eapply E_Local.
              ** cbn; exact HT2.
              ** reflexivity.
              ** reflexivity.
              ** eapply E_Seq; [eapply E_AAssign; reflexivity | eapply E_AAssign; reflexivity].
              ** cbn. rewrite HJ. rewrite aupd_eq.
                 rewrite aupd_neq_i with (i := j - 1) (i' := j) by lia.
                 rewrite lxor_cancel1. reflexivity.
              ** reflexivity.
           ++ cbn. rewrite HJ.
              rewrite aupd_neq_i with (i := j) (i' := j - 1) by lia.
              rewrite aupd_eq, lxor_cancel2. reflexivity.
           ++ reflexivity.
        -- eapply E_Local.
           ++ cbn; exact HT.
           ++ reflexivity.
           ++ reflexivity.
           ++ eapply E_Push; [cbn; lia | reflexivity].
           ++ cbn; reflexivity.
           ++ reflexivity.
      * cbn. discriminate.
    + cbn. rewrite HI, HJ, HSZ, HN. repeat split; try reflexivity; try lia;
        apply cost_ext; cbn; lia.
  - (* else: push -1 *)
    eexists; eexists; exists 0%nat; split.
    + eapply E_IfF.
      * cbn. rewrite HJ, Hcmp. reflexivity.
      * eapply E_Local.
        -- cbn; exact HT.
        -- reflexivity.
        -- reflexivity.
        -- eapply E_Push; [cbn; lia | reflexivity].
        -- cbn; reflexivity.
        -- reflexivity.
      * cbn. reflexivity.
    + cbn. rewrite HI, HJ, HSZ, HN. repeat split; try reflexivity; try lia;
        apply cost_ext; cbn; lia.
Qed.

(** The inner loop body from j = i + k down to j = i: k rounds, k pushes. *)
Lemma inner_lp : forall k st i sz,
  vars st vI = i -> vars st vJ = i + Z.of_nat k -> vars st vSZ = sz -> i + Z.of_nat k < sz ->
  vars st vT1 = 0 -> vars st vT2 = 0 -> vars st vT = 0 -> nstk st = 1%nat ->
  exists st' c w, lp Γbs inner_e1 Skip inner_body inner_e2 st st' c /\
    vars st' vI = i /\ vars st' vJ = i /\ vars st' vSZ = sz /\
    vars st' vT1 = 0 /\ vars st' vT2 = 0 /\ vars st' vT = 0 /\ nstk st' = 1%nat /\
    length (stks st' sGB) = (k + length (stks st sGB))%nat /\ (w <= k)%nat /\
    c = mkc (4 * k + 4 * w) (length (stks st sGB) + k) 0 0.
Proof.
  induction k; intros st i sz HI HJ HSZ Hlt HT1 HT2 HT HN.
  - exists st, (cskip (ssize st)), 0%nat.
    split.
    { apply L_one; [apply E_Skip |].
      cbn. rewrite HI, HJ. replace (i + Z.of_nat 0) with i by lia.
      rewrite Z.eqb_refl. discriminate. }
    rewrite HN. repeat split; try assumption; try lia;
      apply cost_ext; cbn; lia.
  - destruct (bsort_if_run st i (i + Z.of_nat (S k)) sz HI HJ HSZ HT1 HT2 HT HN)
      as [a1 [c1 [w1 [Hex1 [HI1 [HJ1 [HSZ1 [HT11 [HT21 [HT1' [HN1 [Hlen1 [Hw1 Hc1]]]]]]]]]]]]].
    set (a2 := setv a1 vJ (adenote ASub (vars a1 vJ) (eval a1 (Cst 1)))).
    assert (Hex2 : exec Γbs inner_body st a2 (cadd c1 (cprim (ssize a1)))).
    { eapply E_Seq; [exact Hex1 | eapply E_Assign; reflexivity]. }
    destruct (IHk a2 i sz) as [st' [c3 [w3 [Hlp [HI' [HJ' [HSZ' [HT1'' [HT2'' [HT'' [HN' [Hlen3 [Hw3 Hc3]]]]]]]]]]]]];
      try (unfold a2; cbn; assumption).
    { unfold a2; cbn. rewrite HJ1. lia. }
    { lia. }
    exists st', (cadd (cskip (ssize st)) (cadd (cadd c1 (cprim (ssize a1))) c3)), (w1 + w3)%nat.
    split.
    { eapply L_more.
      - apply E_Skip.
      - cbn. rewrite HJ, HI.
        rewrite (proj2 (Z.eqb_neq (i + Z.of_nat (S k)) i) ltac:(lia)). reflexivity.
      - exact Hex2.
      - unfold a2; cbn. rewrite HJ1, HSZ1.
        rewrite (proj2 (Z.eqb_neq (i + Z.of_nat (S k) - 1) (sz - 1)) ltac:(lia)). reflexivity.
      - exact Hlp. }
    assert (E1 : ssize st = length (stks st sGB)) by (rewrite HN; reflexivity).
    assert (E2 : ssize a1 = S (length (stks st sGB))) by (rewrite HN1; cbn; lia).
    assert (E3 : length (stks a2 sGB) = S (length (stks st sGB))) by (unfold a2; cbn; exact Hlen1).
    repeat split; try assumption; try lia.
    subst c1 c3. rewrite E1, E2, E3. apply cost_ext; cbn; lia.
Qed.

(** The outer loop body with m rounds left (i + m = sz): tri m pushes. *)
Lemma outer_lp : forall m st i sz,
  vars st vI = i -> vars st vSZ = sz -> 0 <= i -> i + Z.of_nat m = sz ->
  vars st vJ = 0 -> vars st vT1 = 0 -> vars st vT2 = 0 -> vars st vT = 0 -> nstk st = 1%nat ->
  exists st' c w, lp Γbs outer_e1 Skip outer_body outer_e2 st st' c /\
    vars st' vI = sz /\ vars st' vSZ = sz /\ vars st' vJ = 0 /\
    vars st' vT1 = 0 /\ vars st' vT2 = 0 /\ vars st' vT = 0 /\ nstk st' = 1%nat /\
    length (stks st' sGB) = (tri m + length (stks st sGB))%nat /\ (w <= tri m)%nat /\
    c = mkc (3 * m + 4 * tri m + 4 * w) (length (stks st sGB) + tri m) 0 0.
Proof.
  induction m; intros st i sz HI HSZ Hi Hm HJ HT1 HT2 HT HN.
  - exists st, (cskip (ssize st)), 0%nat.
    split.
    { apply L_one; [apply E_Skip |].
      cbn. rewrite HI, HSZ. replace sz with i by lia. rewrite Z.eqb_refl. discriminate. }
    rewrite HN. repeat split; try assumption; try lia;
      apply cost_ext; cbn; lia.
  - (* local j = sz - 1 *)
    set (a1 := setv st vJ (eval st szm1)).
    destruct (inner_lp m a1 i sz) as [b1 [c1 [w1 [Hlp1 [HI1 [HJ1 [HSZ1 [HT11 [HT21 [HT1' [HN1 [Hlen1 [Hw1 Hc1]]]]]]]]]]]]];
      try (unfold a1; cbn; assumption).
    { unfold a1; cbn. rewrite HSZ. lia. }
    { lia. }
    set (a2 := setv b1 vJ 0).
    assert (Hex_inner : exec Γbs inner_loop st a2 (cstmt (cstmt c1))).
    { unfold inner_loop. eapply E_Local.
      - exact HJ.
      - reflexivity.
      - reflexivity.
      - apply E_Loop; [| exact Hlp1].
        unfold a1; cbn. rewrite Z.eqb_refl. discriminate.
      - cbn. rewrite HJ1, HI1. reflexivity.
      - reflexivity. }
    set (a3 := setv a2 vI (adenote AAdd (vars a2 vI) (eval a2 (Cst 1)))).
    assert (Hex_body : exec Γbs outer_body st a3 (cadd (cstmt (cstmt c1)) (cprim (ssize a2)))).
    { eapply E_Seq; [exact Hex_inner | eapply E_Assign; reflexivity]. }
    destruct (IHm a3 (i + 1) sz) as [st' [c3 [w3 [Hlp3 [HI' [HSZ' [HJ' [HT1'' [HT2'' [HT'' [HN' [Hlen3 [Hw3 Hc3]]]]]]]]]]]]];
      try (unfold a3, a2; cbn; assumption).
    { unfold a3, a2; cbn. rewrite HI1. reflexivity. }
    { lia. }
    { lia. }
    { unfold a3, a2; cbn. reflexivity. }
    exists st', (cadd (cskip (ssize st)) (cadd (cadd (cstmt (cstmt c1)) (cprim (ssize a2))) c3)), (w1 + w3)%nat.
    split.
    { eapply L_more.
      - apply E_Skip.
      - cbn. rewrite HI, HSZ. rewrite (proj2 (Z.eqb_neq i sz) ltac:(lia)). reflexivity.
      - exact Hex_body.
      - unfold a3, a2; cbn. rewrite HI1. rewrite (proj2 (Z.eqb_neq (i + 1) 0) ltac:(lia)). reflexivity.
      - exact Hlp3. }
    assert (E0 : stks a1 sGB = stks st sGB) by reflexivity.
    rewrite E0 in Hlen1.
    assert (E1 : ssize st = length (stks st sGB)) by (rewrite HN; reflexivity).
    assert (E2 : ssize a2 = (m + length (stks st sGB))%nat) by (unfold a2; cbn; rewrite HN1; cbn; lia).
    assert (E3 : length (stks a3 sGB) = (m + length (stks st sGB))%nat) by (unfold a3, a2; cbn; exact Hlen1).
    repeat split; try assumption.
    + rewrite Hlen3, E3. cbn [tri]. lia.
    + cbn [tri]. lia.
    + subst c1 c3. rewrite E0, E1, E2, E3. apply cost_ext; cbn; lia.
Qed.

(** *** L2.  bsort on an array of size n (ANY contents): stack_peak = the number
    of comparisons n(n-1)/2 (one push per comparison, never popped), and
    steps = 3 + 3n + 4C + 4w with C = n(n-1)/2 and w = number of swaps
    performed (0 <= w <= C); so steps in [3+3n+4C, 3+3n+8C] and depends on
    the array contents only through w. *)
Theorem bsort_stack_eq_comparisons : forall n st,
  vars st vSZ = Z.of_nat n -> vars st vI = 0 -> vars st vJ = 0 ->
  vars st vT1 = 0 -> vars st vT2 = 0 -> vars st vT = 0 ->
  nstk st = 1%nat -> stks st sGB = [] ->
  exists st' c w,
    exec Γbs (Call pBSORT) st st' c /\
    length (stks st' sGB) = (n * (n - 1) / 2)%nat /\
    stack_peak c = (n * (n - 1) / 2)%nat /\
    (w <= n * (n - 1) / 2)%nat /\
    steps c = (3 + 3 * n + 4 * (n * (n - 1) / 2) + 4 * w)%nat /\
    call_depth_peak c = 1%nat /\ total_calls c = 1%nat.
Proof.
  intros n st HSZ HI HJ HT1 HT2 HT HN HL.
  destruct (outer_lp n (setv st vI (eval st (Cst 0))) 0 (Z.of_nat n))
    as [st' [c [w [Hlp [HI' [HSZ' [HJ' [HT1' [HT2' [HT' [HN' [Hlen [Hw Hc]]]]]]]]]]]]];
    try (cbn; assumption); try lia.
  { cbn; reflexivity. }
  exists (setv st' vI 0), (ccall (cstmt (cstmt c))), w.
  split.
  { apply E_Call. unfold Γbs, bsort_body. eapply E_Local.
    - exact HI.
    - reflexivity.
    - reflexivity.
    - apply E_Loop; [cbn; discriminate | exact Hlp].
    - cbn. rewrite HI', HSZ'. reflexivity.
    - reflexivity. }
  pose proof (tri_div n) as Htri. rewrite <- Htri.
  cbn in Hlen. rewrite HL in Hlen. cbn in Hlen.
  subst c. repeat split; cbn; try rewrite HL; cbn; lia.
Qed.

End BSORT.
