(** * RevLowerExpr.v — the expression lowering preserves values

    [RevLowering.v] verifies the *encodings* vjanus uses (swap as an XOR triple,
    push/pop, the local-array bracket, address injectivity) each in isolation.
    What it does not do is relate a *translation function* to a *source
    semantics*.  Per `docs/vjanus-lowering-soundness.md`, the smallest
    self-contained slice of that is the **expression** lowering, and this file
    is it: a Coq model of jana2014's scalar expression language, a Coq model of
    `lower.ml`'s [expr], and

      [seval g e = Some v -> eval 0 (enc g) (lower e) = v]

    -- every source expression that *has* a value is lowered to a frame-core
    expression with the same value.

    The reference for the source semantics is PyJanus's [Runtime._eval_bin] /
    [_check_bin_operands] (`jana_py/runtime.py`), read off directly:

      - [/] and [%] are Python's, i.e. **floor** division and floor modulus, and
        raise on a zero divisor.  Coq's [Z.div]/[Z.modulo] are also floor, so
        the two agree on the whole domain where the source has a value;
      - [&&], [||] and [!] **type-error unless their operands are booleans**, so
        [seval] has no value there rather than coercing.  This is what licenses
        `lower.ml`'s arithmetic encodings [&& = l*r] and [|| = l + r - l*r];
      - comparisons yield Python [bool], i.e. 0/1.

    Modelling the boolean restriction as "no value" makes the source semantics
    *at most* as permissive as PyJanus, so the theorem covers a subset of real
    programs -- it can understate coverage, never overstate soundness.

    Two negative results are recorded too, because they are the point of doing
    this mechanically rather than by eye:

      - [div_zero_diverges] — the lowering is **not** sound where the source has
        no value: PyJanus raises on `x / 0`, while the frame core's [BDiv] is
        total and quietly yields 0.  Any end-to-end soundness statement needs a
        no-division-by-zero side condition (or a guarded [BDiv]).
      - [or_squares_wrong] — the encoding [|| = l*l + r*r] that `lower.ml` used
        to have is refuted at [l = r = 1]; the comment in `lower.ml` says this was
        caught by hand, and here it is mechanically.

    Out of scope for this slice (each needs the ref-classification model): array
    and struct l-values, stacks, [size]/[top]/[empty], and the Cantor index fold
    -- whose injectivity is already in [RevLowering.v]. *)

From Stdlib Require Import ZArith Bool Lia.
Require Import RevFrame.
Import RevFrame.
Open Scope Z_scope.

(* ===================================================================== *)
(** ** The source: jana2014's scalar expressions. *)

Inductive sbin :=
| SAdd | SSub | SMul | SDiv | SMod          (* + - * / %   *)
| SEq | SNe | SLt | SGt | SLe | SGe         (* == != < > <= >= *)
| SAnd | SOr                                (* && ||       *)
| SXorB | SAndB | SOrB.                     (* ^ & |       *)

Inductive sexpr :=
| SNum (z : Z)
| SVar (n : nat)
| SNot (e : sexpr)
| SBin (o : sbin) (a b : sexpr).

Definition b2z (b : bool) : Z := if b then 1 else 0.

(** "is a boolean", i.e. what PyJanus's [isinstance(v, bool)] admits once a
    comparison's [True]/[False] is read as 1/0. *)
Definition isb (v : Z) : bool := Z.eqb v 0 || Z.eqb v 1.

(** PyJanus's bool check is on the *Python* type, so it is decided by the
    expression's **shape**, not by its value: only a comparison, [!], [&&] or
    [||] produces a Python [bool].  A variable holding 1 is an [int] and is
    rejected.  ([empty s] also qualifies, but stacks are outside this slice.) *)
Definition isbool (e : sexpr) : bool :=
  match e with
  | SNot _ => true
  | SBin (SEq | SNe | SLt | SGt | SLe | SGe | SAnd | SOr) _ _ => true
  | _ => false
  end.

(** ...and the well-formedness that check induces: every [!], [&&], [||] has
    boolean-shaped operands.  ([bok] keeps the [SBin] case one shape.) *)
Definition bok (o : sbin) (a b : sexpr) : bool :=
  match o with SAnd | SOr => isbool a && isbool b | _ => true end.

Fixpoint wf (e : sexpr) : bool :=
  match e with
  | SNum _ | SVar _ => true
  | SNot e1 => isbool e1 && wf e1
  | SBin o a b => bok o a b && wf a && wf b
  end.

Definition sbin_den (o : sbin) (a b : Z) : option Z :=
  match o with
  | SAdd => Some (a + b)
  | SSub => Some (a - b)
  | SMul => Some (a * b)
  | SDiv => if Z.eqb b 0 then None else Some (a / b)
  | SMod => if Z.eqb b 0 then None else Some (a mod b)
  | SEq  => Some (b2z (Z.eqb a b))
  | SNe  => Some (b2z (negb (Z.eqb a b)))
  | SLt  => Some (b2z (Z.ltb a b))
  | SGt  => Some (b2z (Z.ltb b a))
  | SLe  => Some (b2z (Z.leb a b))
  | SGe  => Some (b2z (Z.leb b a))
  | SAnd => Some (b2z (negb (Z.eqb a 0) && negb (Z.eqb b 0)))
  | SOr  => Some (b2z (negb (Z.eqb a 0) || negb (Z.eqb b 0)))
  | SXorB => Some (Z.lxor a b)
  | SAndB => Some (Z.land a b)
  | SOrB  => Some (Z.lor a b)
  end.

Fixpoint seval (g : nat -> Z) (e : sexpr) : option Z :=
  match e with
  | SNum z => Some z
  | SVar n => Some (g n)
  | SNot e1 =>
      match seval g e1 with
      | Some v => Some (b2z (Z.eqb v 0))
      | None => None
      end
  | SBin o a b =>
      match seval g a, seval g b with
      | Some va, Some vb => sbin_den o va vb
      | _, _ => None
      end
  end.

(* ===================================================================== *)
(** ** The lowering, transcribed from [lower.ml]'s [expr]. *)

(** A source name is lowered to a *global* slot or to a *local* one, exactly as
    `lower.ml`'s [ref_of] classifies it.  [lv] is the set of names currently
    bound by an enclosing [local] -- the minimal form of that ref
    classification, and what [local]/[delocal] needs. *)
Definition scope := nat -> bool.
Definition sc_set (lv : scope) (x : nat) : scope :=
  fun n => Nat.eqb n x || lv n.

Definition sref (lv : scope) (n : nat) : ref := if lv n then RL n else RG n.
Definition sloc (lv : scope) (n : nat) : loc := if lv n then L 0 n else G n.

Lemma sref_loc : forall lv n, loc_of_ref 0 (sref lv n) = sloc lv n.
Proof. intros lv n; unfold sref, sloc; destruct (lv n); reflexivity. Qed.

Fixpoint lower (lv : scope) (e : sexpr) : RevFrame.expr :=
  match e with
  | SNum z => Cst z
  | SVar n => Rd (sref lv n)
  | SNot e1 => Bin BEq (lower lv e1) (Cst 0)
  | SBin o a b =>
      let l := lower lv a in
      let r := lower lv b in
      match o with
      | SAdd => Bin BAdd l r
      | SSub => Bin BSub l r
      | SMul => Bin BMul l r
      | SDiv => Bin BDiv l r
      | SMod => Bin BMod l r
      | SEq  => Bin BEq l r
      | SLt  => Bin BLt l r
      | SGt  => Bin BLt r l
      | SGe  => Bin BSub (Cst 1) (Bin BLt l r)
      | SLe  => Bin BSub (Cst 1) (Bin BLt r l)
      | SNe  => Bin BSub (Cst 1) (Bin BEq l r)
      | SAnd => Bin BMul l r
      | SOr  => Bin BSub (Bin BAdd l r) (Bin BMul l r)
      | SXorB => Bin BXor l r
      | SAndB => Bin BAnd l r
      | SOrB  => Bin BOr l r
      end
  end.

(** A source store lands in the globals or the depth-0 locals, according to the
    scope.  Every other cell of the frame store is unused by this fragment. *)
Definition enc (lv : scope) (g : nat -> Z) : store :=
  fun l => match l with
           | G n => if lv n then 0 else g n
           | L 0 n => if lv n then g n else 0
           | _ => 0
           end.

Lemma enc_var : forall lv g n, enc lv g (sloc lv n) = g n.
Proof. intros lv g n; unfold enc, sloc; destruct (lv n) eqn:E; now rewrite E. Qed.

(* ===================================================================== *)
(** ** The boolean encodings are right (and the old one was wrong). *)

Lemma isb_cases : forall v, isb v = true -> v = 0 \/ v = 1.
Proof.
  intros v H; unfold isb in H; apply orb_true_iff in H as [H|H];
    apply Z.eqb_eq in H; auto.
Qed.

(** A boolean-shaped expression really does evaluate to 0/1 -- every such form
    returns [b2z] of something.  This is what the syntactic check buys, and what
    the arithmetic encodings need. *)
Lemma isbool_isb : forall g e v,
  isbool e = true -> seval g e = Some v -> isb v = true.
Proof.
  intros g [z|n|e1|o a b] v Hb H; simpl in Hb; try discriminate.
  - (* SNot *) simpl in H.
    destruct (seval g e1) as [v1|]; [|discriminate].
    injection H; intro; subst v; unfold isb, b2z; destruct (Z.eqb v1 0); reflexivity.
  - (* comparisons and the boolean connectives *)
    simpl in H.
    destruct (seval g a) as [va|]; [|discriminate].
    destruct (seval g b) as [vb|]; [|destruct o; discriminate].
    destruct o; simpl in Hb, H; try discriminate;
      injection H; intro; subst v; unfold isb, b2z;
      match goal with |- context[if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma and_encoding : forall a b, isb a = true -> isb b = true ->
  a * b = b2z (negb (Z.eqb a 0) && negb (Z.eqb b 0)).
Proof.
  intros a b Ha Hb.
  apply isb_cases in Ha as [->| ->]; apply isb_cases in Hb as [->| ->]; reflexivity.
Qed.

Lemma or_encoding : forall a b, isb a = true -> isb b = true ->
  a + b - a * b = b2z (negb (Z.eqb a 0) || negb (Z.eqb b 0)).
Proof.
  intros a b Ha Hb.
  apply isb_cases in Ha as [->| ->]; apply isb_cases in Hb as [->| ->]; reflexivity.
Qed.

(** The encoding [lower.ml] used to have.  It is wrong exactly where both
    operands hold: it yields 2, not 1. *)
Example or_squares_wrong :
  exists a b, isb a = true /\ isb b = true /\
    a * a + b * b <> b2z (negb (Z.eqb a 0) || negb (Z.eqb b 0)).
Proof. exists 1, 1; repeat split; discriminate. Qed.

(* ===================================================================== *)
(** ** Value preservation. *)

Theorem lower_expr_sound : forall lv g e v,
  wf e = true -> seval g e = Some v -> eval 0 (enc lv g) (lower lv e) = v.
Proof.
  intros lv g e; induction e as [z | n | e1 IH1 | o a IHa b IHb]; intros v Hw H.
  - (* SNum *) simpl in H |- *; congruence.
  - (* SVar *) simpl in H |- *; rewrite sref_loc, enc_var; congruence.
  - (* SNot *)
    simpl in Hw; apply andb_true_iff in Hw as [_ Hw].
    simpl in H |- *.
    destruct (seval g e1) as [v1|] eqn:E1; [|discriminate].
    rewrite (IH1 v1 Hw eq_refl).
    injection H; intro; subst v; unfold b2z; destruct (Z.eqb v1 0); reflexivity.
  - (* SBin *)
    simpl in Hw; apply andb_true_iff in Hw as [Hw Hwb];
      apply andb_true_iff in Hw as [Hbo Hwa].
    simpl in H.
    destruct (seval g a) as [va|] eqn:Ea; [|discriminate].
    destruct (seval g b) as [vb|] eqn:Eb; [|destruct o; discriminate].
    specialize (IHa va Hwa eq_refl); specialize (IHb vb Hwb eq_refl).
    destruct o; simpl; rewrite IHa, IHb; simpl in H, Hbo;
      try (injection H; intro; subst v; reflexivity).
    + (* SDiv *) destruct (Z.eqb vb 0) eqn:Hz; [discriminate|].
      injection H; intro; subst v; reflexivity.
    + (* SMod *) destruct (Z.eqb vb 0) eqn:Hz; [discriminate|].
      injection H; intro; subst v; reflexivity.
    + (* SNe *) injection H; intro; subst v; unfold b2z;
      destruct (Z.eqb va vb); reflexivity.
    + (* SLe *) injection H; intro; subst v; unfold b2z.
      destruct (Z.leb va vb) eqn:Hle.
      * apply Z.leb_le in Hle. destruct (Z.ltb vb va) eqn:Hlt; [|reflexivity].
        apply Z.ltb_lt in Hlt; lia.
      * apply Z.leb_gt in Hle. destruct (Z.ltb vb va) eqn:Hlt; [reflexivity|].
        apply Z.ltb_ge in Hlt; lia.
    + (* SGe *) injection H; intro; subst v; unfold b2z.
      destruct (Z.leb vb va) eqn:Hle.
      * apply Z.leb_le in Hle. destruct (Z.ltb va vb) eqn:Hlt; [|reflexivity].
        apply Z.ltb_lt in Hlt; lia.
      * apply Z.leb_gt in Hle. destruct (Z.ltb va vb) eqn:Hlt; [reflexivity|].
        apply Z.ltb_ge in Hlt; lia.
    + (* SAnd *) apply andb_true_iff in Hbo as [Ba Bb].
      injection H; intro; subst v; apply and_encoding;
        [ exact (isbool_isb g a va Ba Ea) | exact (isbool_isb g b vb Bb Eb) ].
    + (* SOr *) apply andb_true_iff in Hbo as [Ba Bb].
      injection H; intro; subst v; apply or_encoding;
        [ exact (isbool_isb g a va Ba Ea) | exact (isbool_isb g b vb Bb Eb) ].
Qed.

(* ===================================================================== *)
(** ** The guard is never spuriously triggered.

    [RevFrame.safe] refuses an expression that would divide by zero.  For the
    lowering to be *usable* it is not enough that the core agrees where it runs:
    the guard must accept everything the source accepts, or the core would
    reject programs PyJanus happily executes.  It does: a source expression that
    has a value lowers to a safe one. *)

Theorem lower_expr_safe : forall lv g e v,
  wf e = true -> seval g e = Some v -> safe 0 (enc lv g) (lower lv e) = true.
Proof.
  intros lv g e; induction e as [z | n | e1 IH1 | o a IHa b IHb]; intros v Hw H.
  - reflexivity.
  - reflexivity.
  - (* SNot *)
    simpl in Hw; apply andb_true_iff in Hw as [_ Hw].
    simpl in H |- *.
    destruct (seval g e1) as [v1|] eqn:E1; [|discriminate].
    rewrite (IH1 v1 Hw eq_refl); reflexivity.
  - (* SBin *)
    simpl in Hw; apply andb_true_iff in Hw as [Hw Hwb];
      apply andb_true_iff in Hw as [_ Hwa].
    simpl in H.
    destruct (seval g a) as [va|] eqn:Ea; [|discriminate].
    destruct (seval g b) as [vb|] eqn:Eb; [|destruct o; discriminate].
    assert (Sa : safe 0 (enc lv g) (lower lv a) = true) by (eapply IHa; [exact Hwa|reflexivity]).
    assert (Sb : safe 0 (enc lv g) (lower lv b) = true) by (eapply IHb; [exact Hwb|reflexivity]).
    assert (Vb : eval 0 (enc lv g) (lower lv b) = vb)
      by (apply lower_expr_sound; [exact Hwb | exact Eb]).
    destruct o; simpl in H |- *; rewrite ?Sa, ?Sb, ?Vb; simpl; try reflexivity.
    + (* SDiv *) destruct (Z.eqb vb 0) eqn:Hz; [discriminate|reflexivity].
    + (* SMod *) destruct (Z.eqb vb 0) eqn:Hz; [discriminate|reflexivity].
Qed.

(** Together: the lowering of a source expression that has a value is safe and
    computes that value -- so guarding the core costs nothing on the programs
    the reference semantics accepts. *)
Corollary lower_expr_ok : forall lv g e v,
  wf e = true -> seval g e = Some v ->
  safe 0 (enc lv g) (lower lv e) = true /\ eval 0 (enc lv g) (lower lv e) = v.
Proof.
  intros lv g e v Hw H; split;
    [ eapply lower_expr_safe; eassumption | apply lower_expr_sound; assumption ].
Qed.

(** The well-formedness hypothesis is not decoration: without it the theorem is
    **false**.  `2 && 3` is a type error in PyJanus, has value 1 under the
    connective's own meaning, and lowers to `2 * 3 = 6`.  vjanus computed the 6
    until `lower.ml` grew the same syntactic check. *)
Example and_needs_wf :
  let e := SBin SAnd (SNum 2) (SNum 3) in
  wf e = false
  /\ seval (fun _ => 0) e = Some 1
  /\ eval 0 (enc (fun _ => false) (fun _ => 0)) (lower (fun _ => false) e) = 6.
Proof. repeat split; reflexivity. Qed.

(** And the check really is on the *shape*: a variable holding 1 is an [int],
    so `b && c` is ill-formed however [b] and [c] happen to evaluate -- exactly
    what PyJanus's [isinstance(v, bool)] does. *)
Example bool_check_is_syntactic :
  wf (SBin SAnd (SVar 0) (SVar 1)) = false
  /\ wf (SBin SAnd (SBin SEq (SVar 0) (SNum 1)) (SBin SLt (SNum 0) (SVar 1))) = true.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(** ** The divergence this guard was added for. *)

(** [bden] is still total -- [eval] of the lowered expression has a value even
    at a zero divisor.  What changed is that [RevFrame.safe] now *refuses* such
    an expression, and every rule that evaluates one carries [safe] as a side
    condition, so no step is taken.  These examples pin the arithmetic that made
    the divergence invisible before the guard existed. *)
Example div_zero_diverges :
  seval (fun _ => 0) (SBin SDiv (SNum 7) (SNum 0)) = None
  /\ eval 0 (enc (fun _ => false) (fun _ => 0)) (lower (fun _ => false) (SBin SDiv (SNum 7) (SNum 0))) = 0.
Proof. split; reflexivity. Qed.

(** And the modulus is worse than the quotient: [Z.modulo a 0 = a], so `x % 0`
    lowers to something that quietly returns the *dividend*. *)
Example mod_zero_diverges :
  seval (fun _ => 0) (SBin SMod (SNum 7) (SNum 0)) = None
  /\ eval 0 (enc (fun _ => false) (fun _ => 0)) (lower (fun _ => false) (SBin SMod (SNum 7) (SNum 0))) = 7.
Proof. split; reflexivity. Qed.

(** Floor, not truncation: [-7 / 2 = -4] in both PyJanus (Python [//]) and the
    core ([Z.div]).  A C-style truncating division would give -3, so this is a
    real agreement and not an accident of the sign-free examples. *)
Example floor_division_agrees :
  seval (fun _ => 0) (SBin SDiv (SNum (-7)) (SNum 2)) = Some (-4)
  /\ eval 0 (enc (fun _ => false) (fun _ => 0)) (lower (fun _ => false) (SBin SDiv (SNum (-7)) (SNum 2))) = -4.
Proof. split; reflexivity. Qed.

Example floor_modulus_agrees :
  seval (fun _ => 0) (SBin SMod (SNum (-7)) (SNum 2)) = Some 1
  /\ eval 0 (enc (fun _ => false) (fun _ => 0)) (lower (fun _ => false) (SBin SMod (SNum (-7)) (SNum 2))) = 1.
Proof. split; reflexivity. Qed.
