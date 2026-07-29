(** * RevSemantics.v — the semantics of the framework language, and their agreement

    The framework language [RevCore.RevLang] has been given several semantics
    across this development, each proved to agree with the big-step one in the
    file that introduced it.  Nothing said so far that they *all* agree with each
    other, and the pairwise statements were scattered.  This file is the hub: it
    names each semantics and states every pair.

    | # | name    | definition                                  | file             |
    |---|---------|---------------------------------------------|------------------|
    | 1 | [big]   | [L.exec]                                    | [RevCore.v]      |
    | 2 | [small] | [SS.multistep] on residual programs         | [RevSmallStep.v] |
    | 3 | [den]   | [Dn.denote Dexec], a relation per statement | [RevDenote.v]    |
    | 4 | [inv]   | run the *inverted* program backwards        | [RevCore.v]      |
    | 5 | [flat]  | compile to labelled code, run the machine   | [RevCompile.v]   |

    (4) is the semantics an *inverse interpreter* implements: PyJanus's
    `--inverse` and `vjanus -inverse` compute an initial store from a final one,
    and what justifies them is that running [invert s] backwards is the same
    relation as running [s] forwards.  It is a semantics of [s] in its own right,
    not a derived operation.

    (5) is the semantics a *compiler* gives: erase the structured control flow
    into indexed jumps and run the resulting code.  It is the only one of the
    five that never looks at the syntax tree.

    **State of the agreement.**  Among (1)–(4) all **six** pairs are proved as
    [iff]s.  For (5) the direction [big -> flat] is proved (the compiler loses no
    behaviour) and **the converse is not yet proved**, so the four pairs
    involving [flat] are currently implications and not equivalences.  What is
    missing is stated precisely in [RevCompile.v]; it is a confinement plus
    first-arrival argument about machine runs, not a gap in the compiler.  The
    naming here keeps the distinction visible: [*_iff] versus [*_sound].

    **Why all pairs and not just a spanning tree.**  Six [iff]s to [big] would
    imply the rest, but only to a reader who does the composition.  Every pair is
    written out below as a named theorem so that "these semantics define the same
    relation" is something the machine has checked rather than something the
    reader assembles.  The proofs are of course compositions — that is the point.

    Closed under [functional_extensionality] only (see [audit.sh]). *)

From Stdlib Require Import Bool Arith.
Require Import RevCore RevSmallStep RevDenote RevFix RevCompile.

Module Semantics (P : REV_PRIM).

(* One language instance, threaded through all five semantics.  Applying
   [RevLang] twice gives two distinct inductive types, so the modules below are
   *projected out* of a single chain rather than instantiated separately --
   otherwise none of the theorems in this file would typecheck. *)
Module Cp := RevCompile.Compile P.
Module Fx := Cp.Fxx.
Module Dn := Fx.D.
Module SS := Dn.SSx.
Module L := SS.L.

Section WithEnv.
Variable G : L.pname -> L.stmt.

(* ===================================================================== *)
(** ** The five semantics. *)

(** 1. Big-step: the inductive relation of [RevCore]. *)
Definition big (s : L.stmt) (a b : P.state) : Prop := L.exec G s a b.

(** 2. Small-step: reduce a residual program to [RSkip]. *)
Definition small (s : L.stmt) (a b : P.state) : Prop :=
  SS.multistep G (SS.embed s) a SS.RSkip b.

(** 3. Denotational: the relation [denote] assigns to the statement, in the
       environment that maps each procedure to its big-step meaning. *)
Definition den (s : L.stmt) (a b : P.state) : Prop :=
  Dn.denote (Dn.Dexec G) s a b.

(** 4. Inverse execution: what an inverse interpreter computes — run the
       inverted program from the final store and land on the initial one. *)
Definition inv (s : L.stmt) (a b : P.state) : Prop := L.exec G (L.invert s) b a.

(** 5. Compiler-mediated: flatten the control flow to labelled code, run the
       machine from label 0 to the exit label. *)
Definition flat (s : L.stmt) (a b : P.state) : Prop := Cp.crun G s a b.

(* ===================================================================== *)
(** ** The six pairs among big-step, small-step, denotational and inverse. *)

Theorem big_small_iff : forall s a b, big s a b <-> small s a b.
Proof. intros; apply SS.equiv. Qed.

Theorem big_den_iff : forall s a b, big s a b <-> den s a b.
Proof. intros s a b; symmetry; apply Dn.adequacy. Qed.

Theorem big_inv_iff : forall s a b, big s a b <-> inv s a b.
Proof. intros; apply L.exec_iff. Qed.

Theorem small_den_iff : forall s a b, small s a b <-> den s a b.
Proof.
  intros s a b; split; intro H.
  - exact (proj1 (big_den_iff s a b) (proj2 (big_small_iff s a b) H)).
  - exact (proj1 (big_small_iff s a b) (proj2 (big_den_iff s a b) H)).
Qed.

Theorem small_inv_iff : forall s a b, small s a b <-> inv s a b.
Proof.
  intros s a b; split; intro H.
  - exact (proj1 (big_inv_iff s a b) (proj2 (big_small_iff s a b) H)).
  - exact (proj1 (big_small_iff s a b) (proj2 (big_inv_iff s a b) H)).
Qed.

Theorem den_inv_iff : forall s a b, den s a b <-> inv s a b.
Proof.
  intros s a b; split; intro H.
  - exact (proj1 (big_inv_iff s a b) (proj2 (big_den_iff s a b) H)).
  - exact (proj1 (big_den_iff s a b) (proj2 (big_inv_iff s a b) H)).
Qed.

(** All six at once.  Anything proved about one of the four transports to the
    other three. *)
Definition agree4 (s : L.stmt) (a b : P.state) : Prop :=
  (big s a b <-> small s a b) /\ (big s a b <-> den s a b)
  /\ (big s a b <-> inv s a b) /\ (small s a b <-> den s a b)
  /\ (small s a b <-> inv s a b) /\ (den s a b <-> inv s a b).

Theorem all_agree4 : forall s a b, agree4 s a b.
Proof.
  intros s a b; unfold agree4.
  exact (conj (big_small_iff s a b)
         (conj (big_den_iff s a b)
          (conj (big_inv_iff s a b)
           (conj (small_den_iff s a b)
            (conj (small_inv_iff s a b) (den_inv_iff s a b)))))).
Qed.

(** The closed denotation of [RevFix] — the least fixed point of the
    denotational functional, which needs no environment handed to it — is a
    further description of the same relation. *)
Theorem big_fix_iff : forall s a b, big s a b <-> Dn.denote (Fx.Dfix G) s a b.
Proof.
  intros s a b; split; intro H.
  - exact (proj2 (Fx.fix_adequacy G s a b) H).
  - exact (proj1 (Fx.fix_adequacy G s a b) H).
Qed.

(* ===================================================================== *)
(** ** The four pairs involving the compiler.

    One direction only, for now: everything the source does, the compiled code
    does.  The converse — that the machine invents nothing — is the open half;
    see the closing note of [RevCompile.v]. *)

Theorem big_flat_sound : forall s a b, big s a b -> flat s a b.
Proof. intros s a b H; exact (Cp.crun_sound G s a b H). Qed.

Theorem small_flat_sound : forall s a b, small s a b -> flat s a b.
Proof.
  intros s a b H; exact (big_flat_sound s a b (proj2 (big_small_iff s a b) H)).
Qed.

Theorem den_flat_sound : forall s a b, den s a b -> flat s a b.
Proof.
  intros s a b H; exact (big_flat_sound s a b (proj2 (big_den_iff s a b) H)).
Qed.

Theorem inv_flat_sound : forall s a b, inv s a b -> flat s a b.
Proof.
  intros s a b H; exact (big_flat_sound s a b (proj2 (big_inv_iff s a b) H)).
Qed.

(** The compiled code of the *inverted* program runs a source execution
    backwards — the correctness statement of a compiled inverse interpreter,
    which is the composition of the pair (4) with the compiler direction. *)
Theorem flat_inverse_sound : forall s a b, big s a b -> flat (L.invert s) b a.
Proof.
  intros s a b H.
  exact (big_flat_sound (L.invert s) b a (proj1 (big_inv_iff s a b) H)).
Qed.

(* ===================================================================== *)
(** ** What transports.

    Reversibility was proved once, on [big]; through the pairs it is a property
    of the small-step, denotational and inverse semantics as well, none of which
    was proved reversible directly. *)

Theorem small_injective : forall s a a' b, small s a b -> small s a' b -> a = a'.
Proof.
  intros s a a' b H1 H2.
  eapply L.exec_injective;
    [ exact (proj2 (big_small_iff s a b) H1)
    | exact (proj2 (big_small_iff s a' b) H2) ].
Qed.

Theorem den_injective : forall s a a' b, den s a b -> den s a' b -> a = a'.
Proof.
  intros s a a' b H1 H2.
  eapply L.exec_injective;
    [ exact (proj2 (big_den_iff s a b) H1)
    | exact (proj2 (big_den_iff s a' b) H2) ].
Qed.

Theorem inv_injective : forall s a a' b, inv s a b -> inv s a' b -> a = a'.
Proof.
  intros s a a' b H1 H2.
  eapply L.exec_injective;
    [ exact (proj2 (big_inv_iff s a b) H1)
    | exact (proj2 (big_inv_iff s a' b) H2) ].
Qed.

Theorem small_det : forall s a b b', small s a b -> small s a b' -> b = b'.
Proof.
  intros s a b b' H1 H2.
  eapply L.exec_det;
    [ exact (proj2 (big_small_iff s a b) H1)
    | exact (proj2 (big_small_iff s a b') H2) ].
Qed.

Theorem den_det : forall s a b b', den s a b -> den s a b' -> b = b'.
Proof.
  intros s a b b' H1 H2.
  eapply L.exec_det;
    [ exact (proj2 (big_den_iff s a b) H1)
    | exact (proj2 (big_den_iff s a b') H2) ].
Qed.

End WithEnv.
End Semantics.
