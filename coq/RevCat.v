(** * RevCat.v — the dagger inverse category of partial injections (multi-object)

    [RevInverse.v] exhibited the reversible *relations on one fixed state* as an
    inverse monoid.  That is the one-object shadow of the genuine structure.
    Here we build the multi-object version: the category \textsf{PInj} of
    \emph{partial injections between arbitrary types}, with

      - sequential composition [compH], identities [idH], and a contravariant
        involution (\emph{dagger}) [convH] — a dagger category;
      - a \emph{restriction} operator [rst] making it a restriction category in
        the sense of Cockett--Lack (restriction is a sub-identity, restrictions
        commute, [rst R ; R = R]);
      - the inverse-category law [R ; R† ; R = R] for every partial injection,
        with the dagger as the partial inverse.

    Reversible structured programs are then the \emph{endomorphisms} on a single
    object: for a fixed [state], [hrel state state] is [RevInverse]'s inverse
    monoid, and [RevDenote.denote] lands in \textsf{PInj} with [invert] realized
    by the dagger.  Everything is up to relational equivalence [heq] (pointwise
    [<->], a setoid), so the development is \emph{axiom-free}. *)

From Stdlib Require Import Bool.
Require Import RevCore RevAlgebra RevDenote RevInverse.

(* ===================================================================== *)
(** ** Heterogeneous relations and their (di)category structure. *)

Definition hrel (A B : Type) := A -> B -> Prop.
Definition idH  {A : Type} : hrel A A := fun a b => a = b.
Definition compH {A B C : Type} (R : hrel A B) (S : hrel B C) : hrel A C :=
  fun a c => exists b, R a b /\ S b c.
Definition convH {A B : Type} (R : hrel A B) : hrel B A := fun b a => R a b.

(** Relational equivalence (the setoid we work up to). *)
Definition heq {A B : Type} (R S : hrel A B) : Prop := forall a b, R a b <-> S a b.

Lemma heq_refl  : forall A B (R : hrel A B), heq R R.
Proof. intros A B R a b; tauto. Qed.
Lemma heq_sym   : forall A B (R S : hrel A B), heq R S -> heq S R.
Proof. intros A B R S H a b; split; apply H. Qed.
Lemma heq_trans : forall A B (R S T : hrel A B), heq R S -> heq S T -> heq R T.
Proof. intros A B R S T H1 H2 a b; rewrite (H1 a b); apply H2. Qed.

(** *** Category laws. *)
Lemma compH_idH_l : forall A B (R : hrel A B), heq (compH idH R) R.
Proof.
  intros A B R a b; unfold compH, idH; split.
  - intros [m [Hm H]]; subst m; exact H.
  - intro H; exists a; split; [ reflexivity | exact H ].
Qed.

Lemma compH_idH_r : forall A B (R : hrel A B), heq (compH R idH) R.
Proof.
  intros A B R a b; unfold compH, idH; split.
  - intros [m [H Hm]]; subst m; exact H.
  - intro H; exists b; split; [ exact H | reflexivity ].
Qed.

Lemma compH_assoc : forall A B C D (R : hrel A B) (S : hrel B C) (T : hrel C D),
  heq (compH (compH R S) T) (compH R (compH S T)).
Proof.
  intros A B C D R S T a d; unfold compH; split.
  - intros [c [[b [H1 H2]] H3]]; exists b; split; [ exact H1 | exists c; tauto ].
  - intros [b [H1 [c [H2 H3]]]]; exists c; split; [ exists b; tauto | exact H3 ].
Qed.

(** *** Dagger (involution) laws. *)
Lemma convH_invol : forall A B (R : hrel A B), heq (convH (convH R)) R.
Proof. intros A B R a b; unfold convH; tauto. Qed.

Lemma convH_idH : forall A, heq (convH (@idH A)) idH.
Proof. intros A a b; unfold convH, idH; split; intro H; symmetry; exact H. Qed.

Lemma convH_compH : forall A B C (R : hrel A B) (S : hrel B C),
  heq (convH (compH R S)) (compH (convH S) (convH R)).
Proof. intros A B C R S c a; unfold convH, compH; split; intros [b [H1 H2]]; exists b; tauto. Qed.

(* ===================================================================== *)
(** ** Partial injections: the maps of \textsf{PInj}. *)

Definition detH {A B : Type} (R : hrel A B) : Prop :=
  forall a b b', R a b -> R a b' -> b = b'.

(** A partial injection: single-valued forwards \emph{and} backwards. *)
Definition pinj {A B : Type} (R : hrel A B) : Prop := detH R /\ detH (convH R).

Lemma pinj_idH : forall A, pinj (@idH A).
Proof. intro A; split; intros a b b'; unfold idH, convH; congruence. Qed.

Lemma pinj_convH : forall A B (R : hrel A B), pinj R -> pinj (convH R).
Proof.
  intros A B R [d c]; split.
  - exact c.
  - intros a b b' H1 H2; unfold convH in *; eapply d; eassumption.
Qed.

Lemma pinj_compH : forall A B C (R : hrel A B) (S : hrel B C),
  pinj R -> pinj S -> pinj (compH R S).
Proof.
  intros A B C R S [dR cR] [dS cS]; split.
  - intros a c c' [b [Hab Hbc]] [b' [Hab' Hbc']].
    assert (b = b') by (eapply dR; eassumption); subst b'; eapply dS; eassumption.
  - intros c a a' [b [Hcb Hba]] [b' [Hcb' Hba']]; unfold convH in *.
    assert (b = b') by (eapply cS; unfold convH; eassumption); subst b'.
    eapply cR; unfold convH; eassumption.
Qed.

(* ===================================================================== *)
(** ** Restriction structure (Cockett--Lack). *)

(** The domain idempotent of [R]: a partial identity on [dom R]. *)
Definition rst {A B : Type} (R : hrel A B) : hrel A A := compH R (convH R).

Definition sub_idH {A : Type} (E : hrel A A) : Prop := forall a b, E a b -> a = b.

(** Restriction is a partial identity (needs [R] injective, i.e. [pinj]). *)
Lemma rst_sub_id : forall A B (R : hrel A B), pinj R -> sub_idH (rst R).
Proof.
  intros A B R [_ c] a a' [b [Hab Ha'b]]; unfold convH in Ha'b.
  eapply c; unfold convH; eassumption.
Qed.

(** Partial identities commute (idempotents commute: the inverse-category /
    Ehresmann--Schein--Nambooripad hallmark). *)
Lemma sub_idH_comm : forall A (E F : hrel A A),
  sub_idH E -> sub_idH F -> heq (compH E F) (compH F E).
Proof.
  intros A E F HE HF a b; unfold compH; split.
  - intros [m [H1 H2]]; assert (a = m) by (apply HE; exact H1); subst m;
      assert (a = b) by (apply HF; exact H2); subst b; exists a; split; assumption.
  - intros [m [H1 H2]]; assert (a = m) by (apply HF; exact H1); subst m;
      assert (a = b) by (apply HE; exact H2); subst b; exists a; split; assumption.
Qed.

(** Restriction axiom (R1): [rst R ; R = R]. *)
Lemma rst_comp : forall A B (R : hrel A B), pinj R -> heq (compH (rst R) R) R.
Proof.
  intros A B R [_ c] a b; unfold rst, compH, convH; split.
  - intros [a' [[b0 [Hab0 Ha'b0]] Ha'b]].
    assert (a = a') by (eapply c; unfold convH; eassumption); subst a'; exact Ha'b.
  - intro H; exists a; split; [ exists b; split; exact H | exact H ].
Qed.

(** Restrictions of parallel maps commute (axiom R2). *)
Lemma rst_comm : forall A B (R S : hrel A B),
  pinj R -> pinj S -> heq (compH (rst R) (rst S)) (compH (rst S) (rst R)).
Proof.
  intros A B R S HR HS; apply sub_idH_comm;
    [ apply rst_sub_id; exact HR | apply rst_sub_id; exact HS ].
Qed.

(* ===================================================================== *)
(** ** The inverse-category law: the dagger is the partial inverse. *)

(** [R ; R† ; R = R] for every partial injection. *)
Theorem pinj_inverse_law : forall A B (R : hrel A B),
  pinj R -> heq (compH (compH R (convH R)) R) R.
Proof.
  intros A B R Hp; unfold rst in *; apply rst_comp; exact Hp.
Qed.

(** [R† ; R ; R† = R†] (the symmetric law). *)
Theorem pinj_inverse_law' : forall A B (R : hrel A B),
  pinj R -> heq (compH (compH (convH R) R) (convH R)) (convH R).
Proof.
  intros A B R Hp.
  apply (pinj_inverse_law B A (convH R) (pinj_convH _ _ _ Hp)).
Qed.

(** Both restriction idempotents [R†;R] and [R;R†] are partial identities. *)
Theorem rst_dom : forall A B (R : hrel A B), pinj R -> sub_idH (compH (convH R) R).
Proof.
  intros A B R Hp; change (compH (convH R) R) with (rst (convH R)).
  apply rst_sub_id, pinj_convH; exact Hp.
Qed.

Theorem rst_cod : forall A B (R : hrel A B), pinj R -> sub_idH (compH R (convH R)).
Proof. intros A B R Hp; apply rst_sub_id; exact Hp. Qed.

(* ===================================================================== *)
(** ** Connection: reversible programs are the endomorphisms of \textsf{PInj}.

    On one object [state], [hrel state state] is exactly [RevAlgebra.rel],
    [compH]/[idH]/[convH] are [compR]/[idR]/[conv], and [pinj] is [reversible];
    so [RevInverse]'s inverse monoid is the endo-hom-set, and [RevDenote.denote]
    sends every program to a \textsf{PInj}-endomorphism, with [invert] realized
    by the dagger. *)
Module CatDenote (P : REV_PRIM).
Module Dn := RevDenote.Denote P.

Lemma endo_is_rel : forall (R : hrel P.state P.state), R = (R : @rel P.state).
Proof. reflexivity. Qed.

Section WithEnv.
Variable D : Dn.denv.
Hypothesis HD : forall p, reversible (D p).

(** Each program denotes a partial-injection endomorphism on [state]. *)
Theorem denote_pinj : forall s, pinj (Dn.denote D s).
Proof.
  intro s; destruct (Dn.denote_reversible D HD s) as [df db]; split.
  - exact df.
  - exact db.
Qed.

(** The program inverter is the dagger of \textsf{PInj}. *)
Theorem denote_invert_dagger : forall s,
  heq (Dn.denote D (Dn.L.invert s)) (convH (Dn.denote D s)).
Proof. intros s a b; exact (Dn.denote_invert D s a b). Qed.

(** Hence the inverse-category law holds for every program denotation. *)
Corollary denote_inverse_law : forall s,
  heq (compH (compH (Dn.denote D s) (convH (Dn.denote D s))) (Dn.denote D s))
      (Dn.denote D s).
Proof. intro s; apply pinj_inverse_law, denote_pinj. Qed.

End WithEnv.
End CatDenote.
