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

(** ** 4. Stack [push]/[pop]: XOR-swap into the top cell, plus a counter bump.

    [vjanus] lowers [push(x,s)] to
    [s.arr[top] ^= x; x ^= s.arr[top]; s.arr[top] ^= x; top += 1]
    — an XOR swap of the top cell and [x], then a counter increment — and [pop]
    to the same swap after [top -= 1].  Both touch the same cell (arr[top]), so
    we model that cell [c], the register [x], and the counter [t].  Correctness:
    [pop] undoes [push]; and with a clean top cell it is the stack semantics
    (the value moves onto the stack, [x] is consumed to 0). *)
Definition push (st : Z * Z * nat) : Z * Z * nat :=
  match st with (c, x, t) => match xor3 (c, x) with (c', x') => (c', x', S t) end end.
Definition pop (st : Z * Z * nat) : Z * Z * nat :=
  match st with
  | (c, x, S t') => match xor3 (c, x) with (c', x') => (c', x', t') end
  | (c, x, O)    => (c, x, O)
  end.

Theorem pop_push : forall c x t, pop (push (c, x, t)) = (c, x, t).
Proof.
  intros c x t. unfold push. rewrite (xor3_swaps c x).
  unfold pop. rewrite (xor3_swaps x c). reflexivity.
Qed.

(** With a clean top cell (c = 0), push stores x and zeroes the register. *)
Theorem push_clean : forall x t, push (0, x, t) = (x, 0, S t).
Proof. intros x t. unfold push. rewrite (xor3_swaps 0 x). reflexivity. Qed.

(** ** 5. Struct-array cell addressing is injective.

    A struct-array element field lowers to the flat cell [elem*n + off], where
    [n] is the slot count per element and [off < n] is the field offset within an
    element.  This addressing never makes two distinct (element, field) pairs
    alias — the Euclidean-division uniqueness that keeps the lowering sound. *)
Theorem addr_injective :
  forall n e1 o1 e2 o2 : nat,
    (o1 < n)%nat -> (o2 < n)%nat ->
    (e1 * n + o1 = e2 * n + o2)%nat -> e1 = e2 /\ o1 = o2.
Proof.
  intros n e1 o1 e2 o2 H1 H2 H.
  apply (Nat.div_mod_unique n e1 e2 o1 o2 H1 H2).
  rewrite (Nat.mul_comm n e1), (Nat.mul_comm n e2). exact H.
Qed.

(** ** 6. The Cantor pairing folding multi-dim array indices is injective.

    [vjanus]'s [cantor_val] folds a multi-dimensional index [a, b, …] into one
    flat cell with the Cantor pairing [(a+b)*(a+b+1)/2 + b] (nested for higher
    rank).  Distinct multi-indices must map to distinct cells or the array
    lowering would alias.  We prove the two-argument pairing injective; the
    triangular number is defined by the recurrence [T(k+1) = (k+1) + T(k)] (so
    [T k = k*(k+1)/2], proved in [tri_closed]) which makes the monotonicity the
    whole argument turns on definitional. *)
Section Cantor.
Local Open Scope nat_scope.

Fixpoint tri (k : nat) : nat :=
  match k with O => 0 | S k' => S k' + tri k' end.

Definition cantor2 (a b : nat) : nat := tri (a + b) + b.

(** The standard closed form, tying [cantor2] to [vjanus]'s [cantor_val]. *)
Lemma tri_closed : forall k, tri k = k * (k + 1) / 2.
Proof.
  assert (H2 : forall k, 2 * tri k = k * (k + 1)).
  { induction k; simpl tri; [ reflexivity | nia ]. }
  intro k. rewrite <- (Nat.div_mul (tri k) 2) by lia.
  rewrite (Nat.mul_comm (tri k) 2), H2. reflexivity.
Qed.

Lemma tri_mono : forall k1 k2, k1 <= k2 -> tri k1 <= tri k2.
Proof. intros k1 k2 H. induction H; simpl; lia. Qed.

Lemma tri_step_bound : forall s b, b <= s -> tri s + b < tri (S s).
Proof. intros s b H. simpl. lia. Qed.

Lemma diag_unique : forall s1 b1 s2 b2,
  b1 <= s1 -> b2 <= s2 -> tri s1 + b1 = tri s2 + b2 -> s1 = s2.
Proof.
  intros s1 b1 s2 b2 Hb1 Hb2 H.
  destruct (Nat.lt_trichotomy s1 s2) as [L | [E | G]]; [ | assumption | ].
  - exfalso. assert (tri (S s1) <= tri s2) by (apply tri_mono; lia).
    pose proof (tri_step_bound s1 b1 Hb1). lia.
  - exfalso. assert (tri (S s2) <= tri s1) by (apply tri_mono; lia).
    pose proof (tri_step_bound s2 b2 Hb2). lia.
Qed.

Theorem cantor2_injective : forall a1 b1 a2 b2,
  cantor2 a1 b1 = cantor2 a2 b2 -> a1 = a2 /\ b1 = b2.
Proof.
  intros a1 b1 a2 b2 H. unfold cantor2 in H.
  assert (Hs : a1 + b1 = a2 + b2)
    by (apply (diag_unique (a1 + b1) b1 (a2 + b2) b2); lia).
  rewrite Hs in H. split; lia.
Qed.
End Cantor.
