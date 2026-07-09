(** * RevLowering.v — correctness of the two nontrivial vjanus lowering rules

    [vjanus]'s [lower.ml] translates jana2014 into the verified frame core.  Most
    rules map one source construct to one core primitive, so their correctness is
    immediate.  Two rules do NOT — they *encode* a source construct that has no
    core counterpart — and those are exactly where a translator can silently go
    wrong.  This file machine-checks both encodings.  (Whole-translator semantic
    preservation — a Coq model of all of [lower.ml] proved to commute with the
    source semantics — is a separate, larger undertaking; here we verify the two
    load-bearing rules that carry real proof obligations.)

    1. **Swap via an XOR triple.**  The frame core has no [Swap] primitive, so
       [x <=> y] is lowered to [x ^= y; y ^= x; x ^= y] (three reversible
       [OXor] updates).  We prove this triple computes the swap AND is its own
       inverse — the two facts that make [uncall] of a swap correct.

    2. **Self-swap is rejected for a reason.**  When the two operands alias the
       same cell, the XOR triple collapses that cell to 0 instead of leaving it
       unchanged — so [a[i] <=> a[i]] would destroy data.  This is precisely why
       [vjanus] / the PyJanus runtime reject an aliased swap; we prove the
       collapse.

    3. **The clean local-array bracket.**  A [local int a[n]] is lowered by
       bracketing the body with a per-cell [a[c] += 0] / [a[c] -= 0].  We prove
       each bracket is the identity on the store, so the local-array lowering
       neither adds nor loses information. *)

From Stdlib Require Import ZArith Lia.
Require Import RevIO.   (* store, upd, upd_same and friends *)
Open Scope Z_scope.

(** ** XOR algebra: the two cancellation identities the swap relies on. *)

Lemma lxor_cancel_l : forall a b, Z.lxor a (Z.lxor b a) = b.
Proof.
  intros a b.
  rewrite (Z.lxor_comm b a), <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l.
  reflexivity.
Qed.

Lemma lxor_cancel_r : forall a b, Z.lxor (Z.lxor a b) a = b.
Proof.
  intros a b.
  rewrite (Z.lxor_comm a b), Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r.
  reflexivity.
Qed.

(** ** 1. Swap via the XOR triple [x ^= y; y ^= x; x ^= y].

    Two distinct cells are a pair [(x, y)]; each [^=] rewrites one component. *)
Definition xor3 (p : Z * Z) : Z * Z :=
  let '(x, y) := p in
  let x1 := Z.lxor x y in       (* x ^= y *)
  let y1 := Z.lxor y x1 in      (* y ^= x *)
  let x2 := Z.lxor x1 y1 in     (* x ^= y *)
  (x2, y1).

Theorem xor3_swaps : forall x y, xor3 (x, y) = (y, x).
Proof.
  intros x y. unfold xor3.
  rewrite (lxor_cancel_l y x).          (* y1 = y ^ (x ^ y) = x *)
  rewrite (lxor_cancel_r x y).          (* x2 = (x ^ y) ^ x = y *)
  reflexivity.
Qed.

(** The swap is its own inverse, so [uncall] of a swap is the same swap. *)
Theorem xor3_selfinverse : forall p, xor3 (xor3 p) = p.
Proof.
  intros [x y]. rewrite (xor3_swaps x y), (xor3_swaps y x). reflexivity.
Qed.

(** ** 2. Aliased self-swap collapses the cell to 0 (why it is rejected).

    If both operands are the *same* cell, all three [^=] act on that one cell:
    [x ^= x; x ^= x; x ^= x], which yields 0 — not [x].  A correct self-swap
    would be the identity, so this loses data unless the cell was already 0. *)
Definition xor3_alias (x : Z) : Z :=
  let x1 := Z.lxor x x in
  let x2 := Z.lxor x1 x1 in
  Z.lxor x2 x2.

Theorem xor3_alias_zero : forall x, xor3_alias x = 0.
Proof.
  intro x. unfold xor3_alias.
  rewrite !Z.lxor_nilpotent. reflexivity.
Qed.

Corollary self_swap_unsound :
  forall x, x <> 0 -> xor3_alias x <> x.
Proof. intros x Hx. rewrite xor3_alias_zero. intro; apply Hx; auto. Qed.

(** ** 3. The clean local-array bracket [a[c] += 0] / [a[c] -= 0] is identity. *)

Theorem add_zero_noop : forall c s, upd c (s c + 0) s = s.
Proof. intros c s. rewrite Z.add_0_r. apply upd_same. Qed.

Theorem sub_zero_noop : forall c s, upd c (s c - 0) s = s.
Proof. intros c s. rewrite Z.sub_0_r. apply upd_same. Qed.
