(** * RevInverse.v — reversible programs form an inverse monoid (dagger structure)

    The canonical model of reversible computation is the category [PInj] of sets
    and partial injections, which is an *inverse category*: composition has a
    contravariant *dagger* [†] (here the relational converse [conv]) satisfying
    the partial-injection law [R ; R† ; R = R], and the restriction idempotents
    [R† ; R] commute.  This file establishes that structure for the framework,
    one level above any concrete language:

      - the relations on a fixed [state], under sequential composition [compR]
        with unit [idR] and involution [conv], form an *involutive monoid*
        (associativity, units, [conv] an involution and contravariant);
      - the *reversible* relations form an *inverse monoid*: the partial-injection
        laws [R;R†;R ≡ R] and [R†;R;R† ≡ R†] hold, the restriction idempotents
        [R†;R] and [R;R†] are sub-diagonal (partial identities), and any two
        partial identities commute (the Ehresmann--Schein--Nambooripad hallmark
        of inverse semigroups);
      - the compositional denotation [denote] of [RevDenote.v] is an
        *involutive-monoid homomorphism* whose image, for reversible procedure
        environments, lands in this inverse monoid of partial injections
        ([invert] is realized by the dagger).

    Everything is stated up to relational equivalence [req] (pointwise [<->]),
    a setoid, so the development stays \emph{axiom-free} — no propositional or
    functional extensionality is needed to phrase the equations. *)

From Stdlib Require Import Bool.
Require Import RevCore RevAlgebra RevDenote.

(* ===================================================================== *)
(** ** The involutive / inverse monoid of relations on a fixed state. *)
Section InverseMonoid.
Context {state : Type}.

(** Relational equivalence: the setoid we work up to. *)
Definition req (R S : @rel state) : Prop := forall a b, R a b <-> S a b.

Lemma req_refl  : forall R, req R R.
Proof. intros R a b; tauto. Qed.
Lemma req_sym   : forall R S, req R S -> req S R.
Proof. intros R S H a b; split; apply H. Qed.
Lemma req_trans : forall R S T, req R S -> req S T -> req R T.
Proof. intros R S T H1 H2 a b; rewrite (H1 a b); apply H2. Qed.

(** *** Monoid laws. *)
Lemma compR_id_l : forall R, req (compR idR R) R.
Proof.
  intros R a b; unfold compR, idR; split.
  - intros [m [Hm H]]; subst m; exact H.
  - intro H; exists a; split; [ reflexivity | exact H ].
Qed.

Lemma compR_id_r : forall R, req (compR R idR) R.
Proof.
  intros R a b; unfold compR, idR; split.
  - intros [m [H Hm]]; subst m; exact H.
  - intro H; exists b; split; [ exact H | reflexivity ].
Qed.

Lemma compR_assoc : forall R S T,
  req (compR (compR R S) T) (compR R (compR S T)).
Proof.
  intros R S T a b; unfold compR; split.
  - intros [m [[k [H1 H2]] H3]]; exists k; split; [ exact H1 | exists m; tauto ].
  - intros [k [H1 [m [H2 H3]]]]; exists m; split; [ exists k; tauto | exact H3 ].
Qed.

(** *** Dagger (involution) laws. *)
Lemma conv_invol : forall R, req (conv (conv R)) R.
Proof. intros R a b; unfold conv; tauto. Qed.

Lemma conv_idR : req (conv (@idR state)) idR.
Proof. intros a b; unfold conv, idR; split; intro H; symmetry; exact H. Qed.

Lemma conv_compR : forall R S, req (conv (compR R S)) (compR (conv S) (conv R)).
Proof. intros R S a b; apply conv_comp. Qed.

(* --------------------------------------------------------------------- *)
(** *** Restriction idempotents are partial identities, and they commute. *)

(** A relation below the diagonal: a partial identity. *)
Definition sub_id (E : @rel state) : Prop := forall a b, E a b -> a = b.

Lemma dom_sub_id : forall R, reversible R -> sub_id (compR (conv R) R).
Proof.
  intros R [dR _] a b [k [Hak Hkb]]; unfold conv in Hak.
  eapply dR; eassumption.
Qed.

Lemma cod_sub_id : forall R, reversible R -> sub_id (compR R (conv R)).
Proof.
  intros R [_ cR] a b [k [Hak Hbk]]; unfold conv in Hbk.
  eapply cR; unfold conv; eassumption.
Qed.

(** Any two partial identities commute — the defining property of inverse
    semigroups (idempotents commute). *)
Lemma sub_id_comm : forall E F,
  sub_id E -> sub_id F -> req (compR E F) (compR F E).
Proof.
  intros E F HE HF a b; unfold compR; split.
  - intros [m [H1 H2]]; assert (a = m) by (apply HE; exact H1); subst m;
      assert (a = b) by (apply HF; exact H2); subst b; exists a; split; assumption.
  - intros [m [H1 H2]]; assert (a = m) by (apply HF; exact H1); subst m;
      assert (a = b) by (apply HE; exact H2); subst b; exists a; split; assumption.
Qed.

(* --------------------------------------------------------------------- *)
(** *** The partial-injection (inverse-semigroup) laws. *)

Lemma inv_law1 : forall R,
  reversible R -> req (compR (compR R (conv R)) R) R.
Proof.
  intros R [dR cR] a b; unfold compR, conv; split.
  - intros [m [[k [Hak Hmk]] Hmb]].
    (* [R a k] and [R m k] force [a = m] by backward determinism. *)
    assert (a = m) by (eapply cR; unfold conv; eassumption); subst m; exact Hmb.
  - intro H; exists a; split; [ exists b; split; exact H | exact H ].
Qed.

Lemma inv_law2 : forall R,
  reversible R -> req (compR (compR (conv R) R) (conv R)) (conv R).
Proof.
  intros R [dR cR] a b; unfold compR, conv; split.
  - intros [m [[k [Hka Hkm]] Hbm]].
    (* [R k a] and [R k m] force [a = m] by forward determinism. *)
    assert (a = m) by (eapply dR; eassumption); subst m; exact Hbm.
  - intro H; exists a; split; [ exists b; split; exact H | exact H ].
Qed.

End InverseMonoid.

(* ===================================================================== *)
(** ** The denotation is an involutive-monoid homomorphism into [PInj].

    For a reversible procedure environment, [denote D] sends each statement to a
    partial injection, sends [Skip]/[Seq] to the monoid unit/multiplication, and
    sends [invert] to the dagger. *)
Module InvMonoidHom (P : REV_PRIM).
Module Dn := RevDenote.Denote P.
Import P.

Section Hom.
Variable D : Dn.denv.

(** Unit and multiplication are respected definitionally. *)
Lemma hom_skip : req (Dn.denote D Dn.L.Skip) idR.
Proof. apply req_refl. Qed.

Lemma hom_seq : forall s1 s2,
  req (Dn.denote D (Dn.L.Seq s1 s2)) (compR (Dn.denote D s1) (Dn.denote D s2)).
Proof. intros s1 s2; apply req_refl. Qed.

(** The inverter is realized by the dagger (from [denote_invert]). *)
Lemma hom_invert : forall s,
  req (Dn.denote D (Dn.L.invert s)) (conv (Dn.denote D s)).
Proof. intros s a b; exact (Dn.denote_invert D s a b). Qed.

(** When every procedure denotes a partial injection, so does every program:
    the image lies in the inverse monoid, where the partial-injection laws hold. *)
Hypothesis HD : forall p, reversible (D p).

Theorem image_reversible : forall s, reversible (Dn.denote D s).
Proof. apply Dn.denote_reversible; exact HD. Qed.

Corollary image_inverse_law : forall s,
  req (compR (compR (Dn.denote D s) (conv (Dn.denote D s))) (Dn.denote D s))
      (Dn.denote D s).
Proof. intro s; apply inv_law1; apply image_reversible. Qed.

End Hom.
End InvMonoidHom.
