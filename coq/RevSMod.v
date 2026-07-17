(** * RevSMod.v — signed modular arithmetic (the [-m bits] mode), verified

    PyJanus's global [-m bits] mode wraps *every* value — stores and expression
    intermediates alike — into the *signed* window [[-2^(bits-1), 2^(bits-1))]
    via [_normalize_int]:

        norm v = ((v + 2^(bits-1)) mod 2^bits) - 2^(bits-1).

    (This differs from the per-variable sized types of [RevMod.v]/[RevExtMod.v],
    where only stores wrap and intermediates stay unbounded; the signed window
    also matters, because `<`, `/`, `%` on the signed representation differ from
    the unsigned one.)  This file verifies the arithmetic that a `-m`-aware
    modular core rests on: [norm] lands in the signed window, is idempotent, is a
    ring map onto it, and — crucially — the wrapping updates [x += k] / [x -= k]
    are mutually inverse bijections on that window.  Packaged as a [REV_PRIM]
    instance, [RevLang] then gives reversibility of a signed-modular language for
    free ([smod_reversible]). *)

From Stdlib Require Import ZArith Lia.
Require Import RevCore.
Open Scope Z_scope.

Module Type BITS.
  Parameter bits : nat.
  Axiom bits_pos : (1 <= bits)%nat.
End BITS.

Module SModPrim (Import B : BITS) <: REV_PRIM.
  Definition M : Z := 2 ^ (Z.of_nat bits).
  Definition half : Z := 2 ^ (Z.of_nat bits - 1).

  Lemma half_pos : 0 < half.
  Proof. unfold half. apply Z.pow_pos_nonneg; [ lia | pose proof bits_pos; lia ]. Qed.

  Lemma M_eq : M = 2 * half.
  Proof.
    unfold M, half. pose proof bits_pos as Hb.
    replace (Z.of_nat bits) with (1 + (Z.of_nat bits - 1)) at 1 by lia.
    rewrite Z.pow_add_r by lia. ring.
  Qed.

  Lemma M_pos : 0 < M. Proof. rewrite M_eq; pose proof half_pos; lia. Qed.

  (** The signed wrap. *)
  Definition norm (v : Z) : Z := (v + half) mod M - half.

  Lemma norm_range : forall v, -half <= norm v < half.
  Proof.
    intro v. unfold norm. pose proof (Z.mod_pos_bound (v + half) M M_pos).
    pose proof M_eq. lia.
  Qed.

  Lemma norm_id : forall v, -half <= v < half -> norm v = v.
  Proof.
    intros v Hv. unfold norm. rewrite Z.mod_small; [ ring | pose proof M_eq; lia ].
  Qed.

  (** [norm] absorbs a wrapped summand — the key ring-map fact. *)
  Lemma norm_absorb : forall w c, norm (norm w + c) = norm (w + c).
  Proof.
    intros w c. unfold norm.
    replace ((w + half) mod M - half + c + half) with ((w + half) mod M + c) by ring.
    rewrite Zplus_mod_idemp_l.
    replace (w + half + c) with (w + c + half) by ring.
    reflexivity.
  Qed.

  Lemma norm_add_rev : forall a k, -half <= a < half -> norm (norm (a + k) - k) = a.
  Proof.
    intros a k Ha. replace (norm (a + k) - k) with (norm (a + k) + (- k)) by ring.
    rewrite norm_absorb. replace (a + k + - k) with a by ring. apply norm_id; exact Ha.
  Qed.

  Lemma norm_sub_rev : forall a k, -half <= a < half -> norm (norm (a - k) + k) = a.
  Proof.
    intros a k Ha. rewrite norm_absorb.
    replace (a - k + k) with a by ring. apply norm_id; exact Ha.
  Qed.

  (** *** The [REV_PRIM] instance: a signed-modular register. *)
  Definition state := Z.
  Definition guard := Z.
  Definition gtest (k : Z) (a : Z) : bool := Z.eqb a k.

  Inductive prim_ : Type := AddC (k : Z) | SubC (k : Z).
  Definition prim := prim_.

  Definition pstep (p : prim) (a b : Z) : Prop :=
    -half <= a < half /\
    match p with AddC k => b = norm (a + k) | SubC k => b = norm (a - k) end.

  Definition pinv (p : prim) : prim :=
    match p with AddC k => SubC k | SubC k => AddC k end.

  Lemma pinv_invol : forall p, pinv (pinv p) = p.
  Proof. destruct p; reflexivity. Qed.

  Lemma pstep_det : forall p a b b', pstep p a b -> pstep p a b' -> b = b'.
  Proof. destruct p; intros a b b' [_ Hb] [_ Hb']; subst; reflexivity. Qed.

  Lemma pstep_rev : forall p a b, pstep p a b -> pstep (pinv p) b a.
  Proof.
    destruct p as [k | k]; intros a b [Ha Hb]; subst; simpl; split.
    - apply norm_range.
    - symmetry; apply norm_add_rev; exact Ha.
    - apply norm_range.
    - symmetry; apply norm_sub_rev; exact Ha.
  Qed.
End SModPrim.

(** Reversibility of a signed-modular reversible language, for free. *)
Module SModFacts (B : BITS).
  Module P := SModPrim B.
  Module L := RevLang P.
  Theorem smod_reversible :
    forall (Γ : L.pname -> L.stmt) (s : L.stmt) (a a' b : Z),
      L.exec Γ s a b -> L.exec Γ s a' b -> a = a'.
  Proof. exact L.exec_injective. Qed.
End SModFacts.

(** ** Concrete check: an 8-bit register (signed [-128, 128)). *)

Module B8 <: BITS.
  Definition bits := 8%nat.
  Lemma bits_pos : (1 <= bits)%nat. Proof. unfold bits; lia. Qed.
End B8.

Module P8 := SModPrim B8.
Module I8 := RevLang P8.
Definition Γ0 : I8.pname -> I8.stmt := fun _ => I8.Skip.

(** 100 += 50 wraps to -106 in signed 8-bit (150 -> 150 - 256), matching
    PyJanus's `-m 8`, and unlike the unbounded core's 150. *)
Example s8_wraps : I8.exec Γ0 (I8.Prim (P8.AddC 50)) 100 (-106).
Proof.
  apply I8.E_Prim. unfold P8.pstep, P8.norm, P8.half, P8.M, B8.bits. cbn.
  split; [ lia | reflexivity ].
Qed.

(** And it is reversible: the wrapping update run backward recovers 100. *)
Example s8_reversible :
  I8.exec Γ0 (I8.invert (I8.Prim (P8.AddC 50))) (-106) 100.
Proof. apply I8.exec_rev. apply s8_wraps. Qed.
