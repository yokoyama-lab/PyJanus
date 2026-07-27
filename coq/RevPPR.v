(** * RevPPR.v — Paolini--Piccolo--Roversi's parametric Janus is a [REV_PRIM]

    Their Matita development (TYPES 2015, doi:10.4230/LIPIcs.TYPES.2015.7)
    abstracts Janus over a record [params] (a type of constants, of unary /
    binary / *reversible* operators, and an involution [rev_fun] on the last)
    and a record [sem_params] carrying the evaluation functions plus **one**
    semantic obligation:

    [[
      reverse_eval_rev : forall r a b c,
        evaluate_rev r a b = return c -> evaluate_rev (rev r) c b = return a
    ]]

    Our [RevCore.REV_PRIM] asks for three laws instead — but at the level of
    whole *primitives*, not of operators.  This file shows the two line up:
    [PPR_PARAMS] transcribes their two records, [PPRPrim] builds a [REV_PRIM]
    from it, and the three laws are *derived* — [pinv_invol] from the operator
    involution, [pstep_det] from functionality of evaluation, and [pstep_rev]
    from [reverse_eval_rop] together with the non-occurrence side condition
    [~ In x (fv e)] (their [ev_expr_irrelevant_from_non_present_variable]).

    Consequently **their language is an instance of our framework** and inherits
    [exec_rev]/[exec_iff]/[exec_det]/[exec_injective] for free
    ([PPRLang.ppr_reversible]) — including the constructs their [stm] and our
    [RevLang.stmt] share exactly: assignment, call/uncall, skip, sequence,
    assertion-guarded [if]/[fi] and [from]/[loop]/[until].

    Two design points inherited from them, both new here:

      - **the store is a [list const] indexed by variable position**, not a
        function [var -> Z].  So the resulting Janus instance needs **no
        functional extensionality**: [janus_list_reversible] is closed under the
        global context, where [RevJanus.janus_reversible] uses funext.
      - **operator evaluation is partial** ([option]-valued), matching the
        interpreter (division by zero is an error) where [Janus.v]'s [eval] is
        total.

    The one place we do not follow them: their procedure environment is a
    [list stm] read with [nth_opt] (a call out of range is stuck), ours is a
    total [pname -> stmt].  Nothing in the reversibility argument depends on it.

    Their side condition lives in the *syntax* (the [ASSIGN] constructor carries
    a proof that [x] does not occur in [e]); here it is a premise of [pstep], so
    an aliasing assignment is stuck rather than unrepresentable.  Same programs,
    same runs. *)

From Stdlib Require Import List ZArith Bool.
Import ListNotations.
Require Import RevCore.

(* ===================================================================== *)
(** ** Their [params] + [sem_params], as a module type. *)

Module Type PPR_PARAMS.
  Parameter const : Type.
  Parameter op1 : Type.
  Parameter op2 : Type.
  Parameter rop : Type.                       (* the reversible update operators *)
  Parameter rop_inv : rop -> rop.             (* their [rev_fun] *)

  Parameter eval_op1 : op1 -> const -> option const.
  Parameter eval_op2 : op2 -> const -> const -> option const.
  Parameter eval_rop : rop -> const -> const -> option const.
  Parameter to_bool : const -> bool.          (* their [const_to_bool] *)

  (** [params]'s obligation: the operator involution. *)
  Axiom rop_inv_invol : forall r, rop_inv (rop_inv r) = r.
  (** [sem_params]'s single obligation: [reverse_eval_rev]. *)
  Axiom reverse_eval_rop : forall r a b c,
    eval_rop r a b = Some c -> eval_rop (rop_inv r) c b = Some a.
End PPR_PARAMS.

(* ===================================================================== *)
(** ** The induced [REV_PRIM]. *)

Module PPRPrim (Q : PPR_PARAMS) <: REV_PRIM.
Import Q.

(** *** Expressions (their [Expression]) and the store (their [syn_state]). *)
Inductive expr : Type :=
| EVar (n : nat)
| ECst (c : const)
| EOp1 (o : op1) (e : expr)
| EOp2 (o : op2) (e1 e2 : expr).

Definition state : Type := list const.

Fixpoint fv (e : expr) : list nat :=
  match e with
  | EVar n => [n]
  | ECst _ => []
  | EOp1 _ e1 => fv e1
  | EOp2 _ e1 e2 => fv e1 ++ fv e2
  end.

Fixpoint evalE (e : expr) (s : state) : option const :=
  match e with
  | EVar n => nth_error s n
  | ECst c => Some c
  | EOp1 o e1 => match evalE e1 s with Some c => eval_op1 o c | None => None end
  | EOp2 o e1 e2 =>
      match evalE e1 s, evalE e2 s with
      | Some c1, Some c2 => eval_op2 o c1 c2
      | _, _ => None
      end
  end.

(** *** Positional store update (their [update]). *)
Fixpoint upd (s : state) (n : nat) (c : const) : state :=
  match s, n with
  | [], _ => []
  | _ :: t, O => c :: t
  | h :: t, S k => h :: upd t k c
  end.

Lemma nth_error_upd_hit : forall s n v c,
  nth_error s n = Some v -> nth_error (upd s n c) n = Some c.
Proof.
  induction s as [|h t IH]; intros [|k] v c H; simpl in *;
    try discriminate; try reflexivity.
  eapply IH; exact H.
Qed.

Lemma nth_error_upd_miss : forall s n m c,
  m <> n -> nth_error (upd s n c) m = nth_error s m.
Proof.
  induction s as [|h t IH]; intros [|k] [|j] c H; simpl; try reflexivity.
  - congruence.
  - apply IH; congruence.
Qed.

Lemma upd_upd : forall s n c c', upd (upd s n c) n c' = upd s n c'.
Proof.
  induction s as [|h t IH]; intros [|k] c c'; simpl; try reflexivity.
  rewrite IH; reflexivity.
Qed.

Lemma upd_same : forall s n v, nth_error s n = Some v -> upd s n v = s.
Proof.
  induction s as [|h t IH]; intros [|k] v H; simpl in *; try discriminate.
  - injection H; intro; subst; reflexivity.
  - rewrite (IH k v H); reflexivity.
Qed.

(** Their [ev_expr_irrelevant_from_non_present_variable]: writing to a variable
    the expression does not mention cannot change the expression's value. *)
Lemma evalE_upd : forall e s n c,
  ~ In n (fv e) -> evalE e (upd s n c) = evalE e s.
Proof.
  induction e as [m|c0|o e1 IH1|o e1 IH1 e2 IH2]; intros s n c H; simpl in *.
  - apply nth_error_upd_miss; intro; subst; apply H; left; reflexivity.
  - reflexivity.
  - rewrite (IH1 s n c H); reflexivity.
  - rewrite (IH1 s n c), (IH2 s n c); try reflexivity;
      intro Hin; apply H; apply in_or_app; [ right | left ]; exact Hin.
Qed.

(** *** Primitives: one reversible assignment [x op= e]. *)
Inductive prim_ : Type := Assign (r : rop) (x : nat) (e : expr).
Definition prim := prim_.

Definition pinv (p : prim) : prim :=
  match p with Assign r x e => Assign (rop_inv r) x e end.

Definition pstep (p : prim) (s1 s2 : state) : Prop :=
  match p with
  | Assign r x e =>
      ~ In x (fv e) /\
      exists v1 v2 c,
        nth_error s1 x = Some v1 /\
        evalE e s1 = Some v2 /\
        eval_rop r v1 v2 = Some c /\
        s2 = upd s1 x c
  end.

(** *** Guards: an expression, read as a boolean (their [const_to_bool]). *)
Definition guard : Type := expr.
Definition gtest (g : guard) (s : state) : bool :=
  match evalE g s with Some c => to_bool c | None => false end.

(** *** The three [REV_PRIM] laws, derived from their two obligations. *)

Lemma pinv_invol : forall p, pinv (pinv p) = p.
Proof. intros [r x e]; simpl; rewrite rop_inv_invol; reflexivity. Qed.

Lemma pstep_det : forall p a b b', pstep p a b -> pstep p a b' -> b = b'.
Proof.
  intros [r x e] a b b' [_ [v1 [v2 [c [H1 [H2 [H3 H4]]]]]]]
                        [_ [w1 [w2 [d [K1 [K2 [K3 K4]]]]]]].
  rewrite H1 in K1; injection K1; intro; subst w1.
  rewrite H2 in K2; injection K2; intro; subst w2.
  rewrite H3 in K3; injection K3; intro; subst d.
  subst; reflexivity.
Qed.

Theorem pstep_rev : forall p a b, pstep p a b -> pstep (pinv p) b a.
Proof.
  intros [r x e] a b [Hfv [v1 [v2 [c [H1 [H2 [H3 H4]]]]]]]; simpl.
  split; [ exact Hfv | ].
  exists c, v2, v1; repeat split.
  - subst b; apply nth_error_upd_hit with (v := v1); exact H1.
  - subst b; rewrite (evalE_upd e a x c Hfv); exact H2.
  - apply reverse_eval_rop; exact H3.
  - subst b; rewrite upd_upd; symmetry; apply upd_same; exact H1.
Qed.

End PPRPrim.

(* ===================================================================== *)
(** ** Their language, reversible — for free. *)

Module PPRLang (Q : PPR_PARAMS).
Module Pr := PPRPrim Q.
Module L := RevLang Pr.

(** Reversibility of every program of their language, as an instance of the
    generic [exec_injective] — no bespoke argument. *)
Theorem ppr_reversible : forall Γ s a a' b,
  L.exec Γ s a b -> L.exec Γ s a' b -> a = a'.
Proof. intros Γ s a a' b H1 H2; eapply L.exec_injective; eassumption. Qed.

Corollary ppr_iff : forall Γ s a b,
  L.exec Γ s a b <-> L.exec Γ (L.invert s) b a.
Proof. intros; apply L.exec_iff. Qed.

End PPRLang.

(* ===================================================================== *)
(** ** A concrete instance: their [concrjanus], over [Z].

    Reversible updates [+= -= ^=]; read-only operators [* / % < =], with [/]
    and [%] genuinely **partial** (division by zero has no value), which is what
    the interpreter does and what [Janus.v]'s total [eval] cannot express. *)

Module JanusZ <: PPR_PARAMS.
  Definition const := Z.

  Inductive rop_ : Type := RAdd | RSub | RXor.
  Definition rop := rop_.
  Definition rop_inv (r : rop) : rop :=
    match r with RAdd => RSub | RSub => RAdd | RXor => RXor end.

  Inductive op1_ : Type := ONeg.
  Definition op1 := op1_.
  Inductive op2_ : Type := OMul | ODiv | OMod | OLt | OEq.
  Definition op2 := op2_.

  Definition eval_op1 (o : op1) (a : const) : option const :=
    match o with ONeg => Some (Z.opp a) end.

  Definition eval_op2 (o : op2) (a b : const) : option const :=
    match o with
    | OMul => Some (Z.mul a b)
    | ODiv => if Z.eqb b 0 then None else Some (Z.div a b)
    | OMod => if Z.eqb b 0 then None else Some (Z.modulo a b)
    | OLt  => Some (if Z.ltb a b then 1%Z else 0%Z)
    | OEq  => Some (if Z.eqb a b then 1%Z else 0%Z)
    end.

  Definition eval_rop (r : rop) (a b : const) : option const :=
    match r with
    | RAdd => Some (Z.add a b)
    | RSub => Some (Z.sub a b)
    | RXor => Some (Z.lxor a b)
    end.

  Definition to_bool (c : const) : bool := negb (Z.eqb c 0).

  Lemma rop_inv_invol : forall r, rop_inv (rop_inv r) = r.
  Proof. intros [| |]; reflexivity. Qed.

  Lemma reverse_eval_rop : forall r a b c,
    eval_rop r a b = Some c -> eval_rop (rop_inv r) c b = Some a.
  Proof.
    intros [| |] a b c H; simpl in *; injection H; intro; subst c; f_equal.
    - apply Z.add_simpl_r.
    - apply Z.sub_add.
    - rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r; reflexivity.
  Qed.
End JanusZ.

Module JZ := PPRLang JanusZ.

(** **Janus over a list store, reversible and axiom-free.**  Compare
    [RevJanus.janus_reversible], which needs [functional_extensionality]
    because its store is a *function* [var -> Z]. *)
Theorem janus_list_reversible : forall Γ s a a' b,
  JZ.L.exec Γ s a b -> JZ.L.exec Γ s a' b -> a = a'.
Proof. exact JZ.ppr_reversible. Qed.

Theorem janus_list_iff : forall Γ s a b,
  JZ.L.exec Γ s a b <-> JZ.L.exec Γ (JZ.L.invert s) b a.
Proof. exact JZ.ppr_iff. Qed.

(** A sanity run: with the store [[3; 5]], the program [x0 += x1] yields
    [[8; 5]], and its inverse takes it back. *)
Definition ex_add : JZ.L.stmt :=
  JZ.L.Prim (JZ.Pr.Assign JanusZ.RAdd 0 (JZ.Pr.EVar 1)).
Definition ex_env : JZ.L.pname -> JZ.L.stmt := fun _ => JZ.L.Skip.

Example ex_add_runs : JZ.L.exec ex_env ex_add [3; 5]%Z [8; 5]%Z.
Proof.
  apply JZ.L.E_Prim; simpl; split.
  - simpl; intros [H|H]; discriminate || contradiction.
  - exists 3%Z, 5%Z, 8%Z; repeat split.
Qed.

Example ex_add_inverts : JZ.L.exec ex_env (JZ.L.invert ex_add) [8; 5]%Z [3; 5]%Z.
Proof. apply JZ.L.exec_rev; exact ex_add_runs. Qed.

(** Partiality is real: [x / 0] has no value, so the guard reading it is false
    and nothing steps. *)
Example div_by_zero_stuck :
  JZ.Pr.evalE (JZ.Pr.EOp2 JanusZ.ODiv (JZ.Pr.EVar 0) (JZ.Pr.ECst 0%Z)) [7]%Z = None.
Proof. reflexivity. Qed.
