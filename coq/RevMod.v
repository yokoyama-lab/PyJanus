(** * RevMod.v — bounded (modular) reversible assignment: the basis for i8/i16/…

    Janus's sized integer types [i8]/[i16]/[i32]/[i64] and [u8]/…/[u64] (and the
    global [-m bits] mode) give each register a modulus [M = 2^bits]: every
    update wraps, so the stored value lives in [Z/M], not in [Z].  The verified
    frame core ([RevFrame.v]) is a pure [Z] machine, so [vjanus] cannot *run*
    bounded-type programs faithfully — wrapping a [Z] cell after each step is not
    reversible (it is injective only *within* one residue window).  Reversibility
    is recovered exactly when the state is constrained to a residue system.

    This file formalizes that: over a fixed modulus [M > 0], with the register
    held canonical in [[0, M)], the wrapping updates

        x += k   ==>   x := (x + k) mod M
        x -= k   ==>   x := (x - k) mod M

    are mutually inverse bijections.  Supplying the three [REV_PRIM] local laws
    makes [RevLang] hand back [exec_rev]/[exec_iff]/[exec_det]/[exec_injective]
    for a genuinely modular language — a machine-checked account of why bounded
    integer arithmetic is reversible, and the semantic target a modular verified
    core would extract to.  (The canonicity guard [0 <= a < M] carried by each
    step is what a [Z/M] cell type would enforce structurally.) *)

From Stdlib Require Import ZArith Lia.
Require Import RevCore.
Open Scope Z_scope.

Module Type MODULUS.
  Parameter M : Z.
  Axiom M_pos : 0 < M.
End MODULUS.

Module ModPrim (Import Mod : MODULUS) <: REV_PRIM.
  Definition state := Z.
  Definition guard := Z.
  Definition gtest (k : Z) (a : Z) : bool := Z.eqb a k.

  Inductive prim_ : Type := AddC (k : Z) | SubC (k : Z).
  Definition prim := prim_.

  (* the register is held canonical in [0, M); the update wraps mod M *)
  Definition pstep (p : prim) (a b : Z) : Prop :=
    0 <= a < M /\
    match p with
    | AddC k => b = (a + k) mod M
    | SubC k => b = (a - k) mod M
    end.

  Definition pinv (p : prim) : prim :=
    match p with AddC k => SubC k | SubC k => AddC k end.

  Lemma pinv_invol : forall p, pinv (pinv p) = p.
  Proof. destruct p; reflexivity. Qed.

  Lemma pstep_det : forall p a b b', pstep p a b -> pstep p a b' -> b = b'.
  Proof. destruct p; intros a b b' [_ Hb] [_ Hb']; subst; reflexivity. Qed.

  Lemma pstep_rev : forall p a b, pstep p a b -> pstep (pinv p) b a.
  Proof.
    pose proof M_pos as HM.
    destruct p as [k | k]; intros a b [Ha Hb]; subst; simpl; split.
    - apply Z.mod_pos_bound; assumption.
    - rewrite Zminus_mod_idemp_l. replace (a + k - k) with a by ring.
      symmetry; apply Z.mod_small; assumption.
    - apply Z.mod_pos_bound; assumption.
    - rewrite Zplus_mod_idemp_l. replace (a - k + k) with a by ring.
      symmetry; apply Z.mod_small; assumption.
  Qed.
End ModPrim.

(** Reversibility of a bounded (modular) reversible language, for free. *)
Module ModFacts (Mod : MODULUS).
  Module P := ModPrim Mod.
  Module L := RevLang P.
  Theorem mod_reversible :
    forall (Γ : L.pname -> L.stmt) (s : L.stmt) (a a' b : Z),
      L.exec Γ s a b -> L.exec Γ s a' b -> a = a'.
  Proof. exact L.exec_injective. Qed.
End ModFacts.

(** ** Concrete check: an i8 register (M = 256) wraps and is reversible. *)

Module M256 <: MODULUS.
  Definition M := 256.
  Lemma M_pos : 0 < M. Proof. unfold M; lia. Qed.
End M256.

Module P8 := ModPrim M256.
Module I8 := RevLang P8.
Definition Γ0 : I8.pname -> I8.stmt := fun _ => I8.Skip.

(** 250 += 10 wraps to 4 (260 mod 256), unlike the unbounded core's 260. *)
Example i8_wraps : I8.exec Γ0 (I8.Prim (P8.AddC 10)) 250 4.
Proof.
  apply I8.E_Prim. unfold P8.pstep, M256.M.
  split; [ lia | reflexivity ].
Qed.

(** And it is reversible: running the update backward recovers 250 from 4. *)
Example i8_wrap_reversible :
  I8.exec Γ0 (I8.invert (I8.Prim (P8.AddC 10))) 4 250.
Proof. apply I8.exec_rev. apply i8_wraps. Qed.
