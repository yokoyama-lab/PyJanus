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
(** ** The meet-semilattice of restriction idempotents.

    The partial identities on a fixed object are ordered by inclusion, and
    under that order composition is their \emph{meet} and [idH] is the top.
    [sub_idH_comm] above is already the commutativity of that meet; the
    remaining laws are proved here, so that the semilattice is available as
    a structure and not only as a collection of facts.

    This is the abstraction that a guard algebra instantiates: in a
    reversible pebble game a guard cuts out the configurations at which a
    move is enabled, conjunction of guards is composition of the
    corresponding partial identities, and ``no constraint'' is [idH]. *)

(** Inclusion order on relations (the counterpart of [heq]). *)
Definition hle {A B : Type} (R S : hrel A B) : Prop := forall a b, R a b -> S a b.

Lemma hle_refl : forall A B (R : hrel A B), hle R R.
Proof. intros A B R a b H; exact H. Qed.

Lemma hle_trans : forall A B (R S T : hrel A B), hle R S -> hle S T -> hle R T.
Proof. intros A B R S T H1 H2 a b H; apply H2, H1, H. Qed.

Lemma hle_antisym : forall A B (R S : hrel A B), hle R S -> hle S R -> heq R S.
Proof. intros A B R S H1 H2 a b; split; [ apply H1 | apply H2 ]. Qed.

(** Partial identities are closed under composition. *)
Lemma sub_idH_compH : forall A (E F : hrel A A),
  sub_idH E -> sub_idH F -> sub_idH (compH E F).
Proof.
  intros A E F HE HF a b [m [H1 H2]].
  assert (a = m) by (apply HE; exact H1); subst m; apply HF; exact H2.
Qed.

(** ... and are idempotent. *)
Lemma sub_idH_idem : forall A (E : hrel A A), sub_idH E -> heq (compH E E) E.
Proof.
  intros A E HE a b; unfold compH; split.
  - intros [m [H1 H2]]; assert (a = m) by (apply HE; exact H1); subst m; exact H2.
  - intro H; assert (a = b) by (apply HE; exact H); subst b; exists a; split; exact H.
Qed.

(** [idH] is the top. *)
Lemma sub_idH_le_idH : forall A (E : hrel A A), sub_idH E -> hle E idH.
Proof. intros A E HE a b H; unfold idH; apply HE; exact H. Qed.

(** Composition is a lower bound of both arguments ... *)
Lemma compH_le_l : forall A (E F : hrel A A),
  sub_idH E -> sub_idH F -> hle (compH E F) E.
Proof.
  intros A E F HE HF a b [m [H1 H2]].
  assert (a = m) by (apply HE; exact H1); subst m.
  assert (a = b) by (apply HF; exact H2); subst b; exact H1.
Qed.

Lemma compH_le_r : forall A (E F : hrel A A),
  sub_idH E -> sub_idH F -> hle (compH E F) F.
Proof.
  intros A E F HE HF a b [m [H1 H2]].
  assert (a = m) by (apply HE; exact H1); subst m; exact H2.
Qed.

(** ... and is the greatest such: it is the meet. *)
Lemma compH_greatest : forall A (E F G : hrel A A),
  sub_idH G -> hle G E -> hle G F -> hle G (compH E F).
Proof.
  intros A E F G HG H1 H2 a b H.
  assert (a = b) by (apply HG; exact H); subst b.
  exists a; split; [ apply H1; exact H | apply H2; exact H ].
Qed.

(** Packaged: the partial identities on [A] form a meet-semilattice with
    top [idH] and meet [compH].  (Associativity is [compH_assoc], which
    holds for all relations.) *)
Theorem sub_idH_meet_semilattice : forall A (E F G : hrel A A),
  sub_idH E -> sub_idH F -> sub_idH G ->
      sub_idH (compH E F)
   /\ heq (compH E F) (compH F E)
   /\ heq (compH E E) E
   /\ hle (compH E F) E
   /\ hle (compH E F) F
   /\ (hle G E -> hle G F -> hle G (compH E F))
   /\ hle E idH.
Proof.
  (* [repeat split] would also break apart the [<->] hidden inside [heq];
     [apply conj] splits only the top-level conjunction. *)
  intros A E F G HE HF HG; repeat apply conj.
  - apply sub_idH_compH; assumption.
  - apply sub_idH_comm; assumption.
  - apply sub_idH_idem; assumption.
  - apply compH_le_l; assumption.
  - apply compH_le_r; assumption.
  - intros H1 H2; apply compH_greatest; assumption.
  - apply sub_idH_le_idH; assumption.
Qed.

(* ===================================================================== *)
(** ** The remaining Cockett--Lack axioms [R3] and [R4].

    [rst_comp] (R1) and [rst_comm] (R2) are above.  The restriction-category
    axiomatisation needs two more, and both hold in \textsf{PInj}: *)

(** [R3]: $\overline{\bar{R}\,;S} = \bar{R}\,;\bar{S}$ for $R,S$ out of the
    same object.  Restricting [S] to the domain of [R] has, as its own
    domain, the intersection of the two domains. *)
Theorem rst_R3 : forall A B C (R : hrel A B) (S : hrel A C),
  pinj R -> pinj S ->
  heq (rst (compH (rst R) S)) (compH (rst R) (rst S)).
Proof.
  intros A B C R S HR HS a b.
  assert (HRid : sub_idH (rst R)) by (apply rst_sub_id; exact HR).
  assert (HSid : sub_idH (rst S)) by (apply rst_sub_id; exact HS).
  destruct HS as [_ cS].
  unfold rst, compH, convH in *; split.
  - intros [c [[a' [Ha Sa]] [b' [Hb Sb]]]].
    (* [rst R] is a partial identity, so [a' = a] and [b' = b]. *)
    assert (a = a') by (apply HRid; exact Ha); subst a'.
    assert (b = b') by (apply HRid; exact Hb); subst b'.
    (* [S] is backwards deterministic, so the shared [c] forces [a = b]. *)
    assert (a = b) by (eapply cS; unfold convH; eassumption).
    subst b; exists a; split; [ exact Ha | exists c; split; exact Sa ].
  - intros [m [Ha Hm]].
    assert (a = m) by (apply HRid; exact Ha); subst m.
    assert (a = b) by (apply HSid; exact Hm); subst b.
    destruct Hm as [c [Sa _]].
    exists c; split; exists a; split; assumption.
Qed.

(** [R4]: $R\,;\bar{S} = \overline{R\,;S}\,;R$ for $R : A \to B$,
    $S : B \to C$.  Testing the domain of [S] after [R] is the same as
    testing the domain of the composite before [R]. *)
Theorem rst_R4 : forall A B C (R : hrel A B) (S : hrel B C),
  pinj R -> pinj S ->
  heq (compH R (rst S)) (compH (rst (compH R S)) R).
Proof.
  intros A B C R S HR HS a c.
  assert (HSid : sub_idH (rst S)) by (apply rst_sub_id; exact HS).
  assert (HRSid : sub_idH (rst (compH R S)))
    by (apply rst_sub_id; apply pinj_compH; assumption).
  destruct HR as [dR _].
  unfold rst, compH, convH in *; split.
  - intros [b [Rab Hb]].
    assert (b = c) by (apply HSid; exact Hb); subst c.
    destruct Hb as [d [Sbd _]].
    exists a; split; [ | exact Rab ].
    exists d; split; exists b; split; assumption.
  - intros [a' [Haa' Ra'c]].
    assert (a = a') by (apply HRSid; exact Haa'); subst a'.
    destruct Haa' as [e [[b0 [Rab0 Sb0e]] _]].
    (* [R] is forwards deterministic, so [b0 = c]. *)
    assert (b0 = c) by (eapply dR; eassumption); subst b0.
    exists c; split; [ exact Ra'c | exists e; split; exact Sb0e ].
Qed.

(* ===================================================================== *)
(** ** Concrete instances (regression checks on a two-element type).

    The general statements above are checked against explicit relations on
    [bool], so that a later change that vacuously satisfies them is caught. *)

Definition botH {A B : Type} : hrel A B := fun _ _ => False.

(** The partial identity on $\{\mathsf{true}\}$, and its complement. *)
Definition Etrue  : hrel bool bool := fun a b => a = true  /\ b = true.
Definition Efalse : hrel bool bool := fun a b => a = false /\ b = false.
(** A total bijection: negation. *)
Definition Rneg   : hrel bool bool := fun a b => b = negb a.

Example Etrue_sub_id : sub_idH Etrue.
Proof. intros a b [Ha Hb]; subst; reflexivity. Qed.

Example Efalse_sub_id : sub_idH Efalse.
Proof. intros a b [Ha Hb]; subst; reflexivity. Qed.

Example Rneg_pinj : pinj Rneg.
Proof.
  split; intros a b b' H1 H2; unfold Rneg, convH in *; subst.
  - reflexivity.
  - destruct b, b'; simpl in *; congruence.
Qed.

(** A total map has the identity as its restriction. *)
Example rst_Rneg_is_idH : heq (rst Rneg) idH.
Proof.
  intros a b; unfold rst, compH, convH, Rneg, idH; split.
  - intros [c [H1 H2]]; subst c; destruct a, b; simpl in *; congruence.
  - intro H; subst b; exists (negb a); split; reflexivity.
Qed.

(** The meet of two disjoint partial identities is the bottom. *)
Example meet_of_disjoint_is_bot : heq (compH Etrue Efalse) botH.
Proof.
  intros a b; unfold compH, Etrue, Efalse, botH; split.
  - intros [m [[_ Hm] [Hm' _]]]; subst m; discriminate.
  - contradiction.
Qed.

(** The meet is idempotent, and [idH] really is above it. *)
Example meet_idem_true : heq (compH Etrue Etrue) Etrue.
Proof. apply sub_idH_idem, Etrue_sub_id. Qed.

Example Etrue_below_idH : hle Etrue idH.
Proof. apply sub_idH_le_idH, Etrue_sub_id. Qed.

(** [R3] and [R4] instantiated at concrete relations. *)
Example R3_at_Rneg : heq (rst (compH (rst Rneg) Rneg)) (compH (rst Rneg) (rst Rneg)).
Proof. apply rst_R3; apply Rneg_pinj. Qed.

Example R4_at_Rneg : heq (compH Rneg (rst Rneg)) (compH (rst (compH Rneg Rneg)) Rneg).
Proof. apply rst_R4; apply Rneg_pinj. Qed.

(** The checks are not vacuous: [Etrue] and [Efalse] are distinct, and
    [botH] is strictly below [idH] on [bool]. *)
Example Etrue_neq_Efalse : ~ heq Etrue Efalse.
Proof.
  intro H; destruct (H true true) as [H1 _].
  destruct H1 as [_ Hf]; [ split; reflexivity | discriminate ].
Qed.

Example botH_strictly_below_idH : hle (@botH bool bool) idH /\ ~ heq (@botH bool bool) idH.
Proof.
  split.
  - intros a b [].
  - intro H; destruct (H true true) as [_ H2]; exact (H2 eq_refl).
Qed.

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
