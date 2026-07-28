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
  | SAnd => if isb a && isb b
            then Some (b2z (negb (Z.eqb a 0) && negb (Z.eqb b 0))) else None
  | SOr  => if isb a && isb b
            then Some (b2z (negb (Z.eqb a 0) || negb (Z.eqb b 0))) else None
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
      | Some v => if isb v then Some (b2z (Z.eqb v 0)) else None
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

Fixpoint lower (e : sexpr) : RevFrame.expr :=
  match e with
  | SNum z => Cst z
  | SVar n => Rd (RG n)
  | SNot e1 => Bin BEq (lower e1) (Cst 0)
  | SBin o a b =>
      let l := lower a in
      let r := lower b in
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

(** A source store is the globals of the frame store. *)
Definition enc (g : nat -> Z) : store :=
  fun l => match l with G n => g n | _ => 0 end.

Lemma enc_var : forall g n, enc g (loc_of_ref 0 (RG n)) = g n.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(** ** The boolean encodings are right (and the old one was wrong). *)

Lemma isb_cases : forall v, isb v = true -> v = 0 \/ v = 1.
Proof.
  intros v H; unfold isb in H; apply orb_true_iff in H as [H|H];
    apply Z.eqb_eq in H; auto.
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

Theorem lower_expr_sound : forall g e v,
  seval g e = Some v -> eval 0 (enc g) (lower e) = v.
Proof.
  intros g e; induction e as [z | n | e1 IH1 | o a IHa b IHb]; intros v H.
  - (* SNum *) simpl in H |- *; congruence.
  - (* SVar *) simpl in H |- *; congruence.
  - (* SNot *)
    simpl in H |- *.
    destruct (seval g e1) as [v1|] eqn:E1; [|discriminate].
    destruct (isb v1) eqn:Hb; [|discriminate].
    rewrite (IH1 v1 eq_refl); simpl in H |- *.
    injection H; intro; subst v; unfold b2z; destruct (Z.eqb v1 0); reflexivity.
  - (* SBin *)
    simpl in H.
    destruct (seval g a) as [va|] eqn:Ea; [|discriminate].
    destruct (seval g b) as [vb|] eqn:Eb; [|destruct o; discriminate].
    specialize (IHa va eq_refl); specialize (IHb vb eq_refl).
    destruct o; simpl; rewrite IHa, IHb; simpl in H;
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
    + (* SAnd *) destruct (isb va) eqn:Hva; [|discriminate].
      destruct (isb vb) eqn:Hvb; [|discriminate].
      injection H; intro; subst v; apply and_encoding; assumption.
    + (* SOr *) destruct (isb va) eqn:Hva; [|discriminate].
      destruct (isb vb) eqn:Hvb; [|discriminate].
      injection H; intro; subst v; apply or_encoding; assumption.
Qed.

(* ===================================================================== *)
(** ** Where it does *not* hold: a total [BDiv] against a partial source. *)

(** PyJanus raises "Division by zero"; the frame core's [BDiv] is total and
    [Z.div _ 0 = 0], so the lowered expression quietly has a value.  An
    end-to-end soundness theorem therefore needs a no-division-by-zero side
    condition, or the core needs a guarded division. *)
Example div_zero_diverges :
  seval (fun _ => 0) (SBin SDiv (SNum 7) (SNum 0)) = None
  /\ eval 0 (enc (fun _ => 0)) (lower (SBin SDiv (SNum 7) (SNum 0))) = 0.
Proof. split; reflexivity. Qed.

(** And the modulus is worse than the quotient: [Z.modulo a 0 = a], so `x % 0`
    lowers to something that quietly returns the *dividend*. *)
Example mod_zero_diverges :
  seval (fun _ => 0) (SBin SMod (SNum 7) (SNum 0)) = None
  /\ eval 0 (enc (fun _ => 0)) (lower (SBin SMod (SNum 7) (SNum 0))) = 7.
Proof. split; reflexivity. Qed.

(** Floor, not truncation: [-7 / 2 = -4] in both PyJanus (Python [//]) and the
    core ([Z.div]).  A C-style truncating division would give -3, so this is a
    real agreement and not an accident of the sign-free examples. *)
Example floor_division_agrees :
  seval (fun _ => 0) (SBin SDiv (SNum (-7)) (SNum 2)) = Some (-4)
  /\ eval 0 (enc (fun _ => 0)) (lower (SBin SDiv (SNum (-7)) (SNum 2))) = -4.
Proof. split; reflexivity. Qed.

Example floor_modulus_agrees :
  seval (fun _ => 0) (SBin SMod (SNum (-7)) (SNum 2)) = Some 1
  /\ eval 0 (enc (fun _ => 0)) (lower (SBin SMod (SNum (-7)) (SNum 2))) = 1.
Proof. split; reflexivity. Qed.
