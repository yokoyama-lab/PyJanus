(** * RevSMC.v — PInj's two symmetric monoidal structures, and distributivity

    [RevCat.v] gives \textsf{PInj} as a dagger restriction category and
    [RevTrace.v] adds the coproduct and a trace operator, but stops short of the
    monoidal structure itself: the note there says the results are "enough for
    [loop_is_trace], not enough to cite the categorical theorem".  This file
    supplies the missing structure, so the theorem can be stated:

      - \textsf{PInj} is **symmetric monoidal for the coproduct** [(+, 0)]:
        associator, unitors (with [Empty_set] the unit) and symmetry, each a
        partial injection, mutually inverse, natural, and satisfying the
        pentagon, triangle and hexagon coherence laws;
      - likewise **for the product** [(×, 1)] (unit [unit]);
      - and the two are related by a **distributor**
        [δ : A × (B + C) ≅ (A × B) + (A × C)], again a natural isomorphism.

    [RevTraced.v] then adds the remaining trace axioms on top, completing
    "distributive traced symmetric monoidal category".

    The one device that makes this tractable: every structural map here is the
    *graph of a bijection*, so we define [fnH] once and each coherence law
    becomes an equation between plain functions, discharged by case analysis.
    Only naturality genuinely quantifies over morphisms.  Everything is up to
    the relational equivalence [heq] and is axiom-free. *)

From Stdlib Require Import Bool.
Require Import RevCore RevAlgebra RevCat RevTrace.

(* ===================================================================== *)
(** ** The graph of a function. *)

Definition fnH {A B : Type} (f : A -> B) : hrel A B := fun a b => b = f a.

Lemma fnH_id : forall A, heq (fnH (fun a : A => a)) idH.
Proof. intros A a b; unfold fnH, idH; split; intro H; congruence. Qed.

Lemma fnH_comp : forall A B C (f : A -> B) (g : B -> C),
  heq (compH (fnH f) (fnH g)) (fnH (fun a => g (f a))).
Proof.
  intros A B C f g a c; unfold compH, fnH; split.
  - intros [b [-> ->]]; reflexivity.
  - intro H; exists (f a); split; [ reflexivity | exact H ].
Qed.

Lemma fnH_ext : forall A B (f g : A -> B),
  (forall a, f a = g a) -> heq (fnH f) (fnH g).
Proof. intros A B f g H a b; unfold fnH; rewrite H; split; auto. Qed.

Definition injectiveF {A B : Type} (f : A -> B) := forall a a', f a = f a' -> a = a'.

Lemma pinj_fnH : forall A B (f : A -> B), injectiveF f -> pinj (fnH f).
Proof.
  intros A B f Hi; split.
  - intros a b b' H1 H2; unfold fnH in *; congruence.
  - intros b a a' H1 H2; unfold convH, fnH in *; apply Hi; congruence.
Qed.

(** Two functions that are mutually inverse give mutually inverse graphs, which
    is what "structural isomorphism" means here. *)
Definition isoH {A B : Type} (R : hrel A B) (S : hrel B A) : Prop :=
  heq (compH R S) idH /\ heq (compH S R) idH.

Lemma isoH_fnH : forall A B (f : A -> B) (g : B -> A),
  (forall a, g (f a) = a) -> (forall b, f (g b) = b) -> isoH (fnH f) (fnH g).
Proof.
  intros A B f g Hgf Hfg; split.
  - eapply heq_trans; [ apply fnH_comp | ].
    eapply heq_trans; [ apply (fnH_ext A A (fun a => g (f a)) (fun a => a) Hgf)
                      | apply fnH_id ].
  - eapply heq_trans; [ apply fnH_comp | ].
    eapply heq_trans; [ apply (fnH_ext B B (fun b => f (g b)) (fun b => b) Hfg)
                      | apply fnH_id ].
Qed.

(** Congruence and normalisation: since every structural map is an [fnH], a
    composite of them is the [fnH] of the composite function, so each coherence
    law reduces to an equation between plain functions. *)

Lemma compH_heq : forall A B C (R R' : hrel A B) (S S' : hrel B C),
  heq R R' -> heq S S' -> heq (compH R S) (compH R' S').
Proof.
  intros A B C R R' S S' HR HS a c; unfold compH; split;
    intros [b [H1 H2]]; exists b; split;
    solve [ apply HR; assumption | apply HS; assumption
          | apply (proj2 (HR a b)); assumption | apply (proj2 (HS b c)); assumption ].
Qed.

Definition sum_map {A B C D : Type} (f : A -> C) (g : B -> D) (x : A + B) : C + D :=
  match x with inl a => inl (f a) | inr b => inr (g b) end.

Definition prod_map {A B C D : Type} (f : A -> C) (g : B -> D) (x : A * B) : C * D :=
  (f (fst x), g (snd x)).

Definition prodH {A B C D : Type} (R : hrel A C) (S : hrel B D) : hrel (A * B) (C * D) :=
  fun x y => R (fst x) (fst y) /\ S (snd x) (snd y).

Lemma sumH_fnH : forall A B C D (f : A -> C) (g : B -> D),
  heq (sumH (fnH f) (fnH g)) (fnH (sum_map f g)).
Proof.
  intros A B C D f g [a|b] [c|d]; unfold sumH, fnH, sum_map; simpl; split;
    intro H; try discriminate; try contradiction;
    solve [ congruence | injection H; intro; subst; reflexivity ].
Qed.

Lemma prodH_fnH : forall A B C D (f : A -> C) (g : B -> D),
  heq (prodH (fnH f) (fnH g)) (fnH (prod_map f g)).
Proof.
  intros A B C D f g [a b] [c d]; unfold prodH, fnH, prod_map; simpl; split.
  - intros [-> ->]; reflexivity.
  - intro H; injection H; auto.
Qed.

Lemma idH_fnH : forall A, heq (@idH A) (fnH (fun a => a)).
Proof. intro A; apply heq_sym; apply fnH_id. Qed.

Lemma sumH_heq : forall A B C D (R R' : hrel A C) (S S' : hrel B D),
  heq R R' -> heq S S' -> heq (sumH R S) (sumH R' S').
Proof.
  intros A B C D R R' S S' HR HS [a|b] [c|d]; unfold sumH; simpl;
    solve [ tauto | apply HR | apply HS ].
Qed.

Lemma prodH_heq : forall A B C D (R R' : hrel A C) (S S' : hrel B D),
  heq R R' -> heq S S' -> heq (prodH R S) (prodH R' S').
Proof.
  intros A B C D R R' S S' HR HS [a b] [c d]; unfold prodH; simpl.
  split; intros [H1 H2]; split;
    solve [ apply HR; assumption | apply HS; assumption
          | apply (proj2 (HR a c)); assumption | apply (proj2 (HS b d)); assumption ].
Qed.

(** Both sides normalise to a function graph; then compare the functions. *)
Lemma heq_fn2 : forall A B (R S : hrel A B) (f g : A -> B),
  heq R (fnH f) -> heq S (fnH g) -> (forall a, f a = g a) -> heq R S.
Proof.
  intros A B R S f g HR HS Hfg.
  eapply heq_trans; [ exact HR | ].
  eapply heq_trans; [ apply (fnH_ext A B f g Hfg) | apply heq_sym; exact HS ].
Qed.

(* ===================================================================== *)
(** ** The coproduct is symmetric monoidal, with [Empty_set] the unit. *)

Definition assocS_f {A B C : Type} (x : A + (B + C)) : (A + B) + C :=
  match x with
  | inl a => inl (inl a)
  | inr (inl b) => inl (inr b)
  | inr (inr c) => inr c
  end.

Definition assocS_g {A B C : Type} (x : (A + B) + C) : A + (B + C) :=
  match x with
  | inl (inl a) => inl a
  | inl (inr b) => inr (inl b)
  | inr c => inr (inr c)
  end.

Definition assocS {A B C : Type} : hrel (A + (B + C)) ((A + B) + C) := fnH assocS_f.
Definition assocS' {A B C : Type} : hrel ((A + B) + C) (A + (B + C)) := fnH assocS_g.

Definition swapS_f {A B : Type} (x : A + B) : B + A :=
  match x with inl a => inr a | inr b => inl b end.
Definition swapS {A B : Type} : hrel (A + B) (B + A) := fnH swapS_f.

Definition lunitS_f {A : Type} (x : Empty_set + A) : A :=
  match x with inl e => match e with end | inr a => a end.
Definition lunitS_g {A : Type} (a : A) : Empty_set + A := inr a.
Definition lunitS {A : Type} : hrel (Empty_set + A) A := fnH lunitS_f.
Definition lunitS' {A : Type} : hrel A (Empty_set + A) := fnH lunitS_g.

Definition runitS_f {A : Type} (x : A + Empty_set) : A :=
  match x with inl a => a | inr e => match e with end end.
Definition runitS_g {A : Type} (a : A) : A + Empty_set := inl a.
Definition runitS {A : Type} : hrel (A + Empty_set) A := fnH runitS_f.
Definition runitS' {A : Type} : hrel A (A + Empty_set) := fnH runitS_g.

(** *** Each structural map is a partial injection. *)

Lemma pinj_assocS : forall A B C, pinj (@assocS A B C).
Proof.
  intros A B C; apply pinj_fnH; intros [a|[b|c]] [a'|[b'|c']] H;
    unfold assocS_f in H; congruence.
Qed.

Lemma pinj_swapS : forall A B, pinj (@swapS A B).
Proof.
  intros A B; apply pinj_fnH; intros [a|b] [a'|b'] H; unfold swapS_f in H; congruence.
Qed.

Lemma pinj_lunitS : forall A, pinj (@lunitS A).
Proof.
  intro A; apply pinj_fnH; intros [[]|a] [[]|a'] H; unfold lunitS_f in H; congruence.
Qed.

Lemma pinj_runitS : forall A, pinj (@runitS A).
Proof.
  intro A; apply pinj_fnH; intros [a|[]] [a'|[]] H; unfold runitS_f in H; congruence.
Qed.

(** *** ...and each is an isomorphism. *)

Lemma iso_assocS : forall A B C, isoH (@assocS A B C) assocS'.
Proof.
  intros A B C; apply isoH_fnH;
    [ intros [a|[b|c]] | intros [[a|b]|c] ]; reflexivity.
Qed.

Lemma iso_swapS : forall A B, isoH (@swapS A B) swapS.
Proof. intros A B; apply isoH_fnH; intros [a|b]; reflexivity. Qed.

Lemma iso_lunitS : forall A, isoH (@lunitS A) lunitS'.
Proof. intro A; apply isoH_fnH; [ intros [[]|a] | intro a ]; reflexivity. Qed.

Lemma iso_runitS : forall A, isoH (@runitS A) runitS'.
Proof. intro A; apply isoH_fnH; [ intros [a|[]] | intro a ]; reflexivity. Qed.

(** *** Coherence: pentagon, triangle, hexagon. *)

(** Pentagon: the two ways of reassociating a four-fold sum agree. *)
Theorem sumS_pentagon : forall A B C D,
  heq (compH (@assocS A B (C + D)) (@assocS (A + B) C D))
      (compH (sumH (@idH A) (@assocS B C D))
             (compH (@assocS A (B + C) D) (sumH (@assocS A B C) (@idH D)))).
Proof.
  intros A B C D.
  eapply heq_fn2 with
    (f := fun x => assocS_f (assocS_f x))
    (g := fun x => sum_map assocS_f (fun d : D => d)
                     (assocS_f (sum_map (fun a : A => a) assocS_f x))).
  - apply fnH_comp.
  - eapply heq_trans;
      [ apply compH_heq;
        [ eapply heq_trans;
            [ apply sumH_heq; [ apply idH_fnH | apply heq_refl ] | apply sumH_fnH ]
        | apply compH_heq;
            [ apply heq_refl
            | eapply heq_trans;
                [ apply sumH_heq; [ apply heq_refl | apply idH_fnH ] | apply sumH_fnH ] ] ]
      | ].
    eapply heq_trans; [ apply compH_heq; [ apply heq_refl | apply fnH_comp ] | ].
    apply fnH_comp.
  - intros [a|[b|[c|d]]]; reflexivity.
Qed.

(** Triangle: the unitors agree through the associator. *)
Theorem sumS_triangle : forall A B,
  heq (compH (@assocS A Empty_set B) (sumH (@runitS A) (@idH B)))
      (sumH (@idH A) (@lunitS B)).
Proof.
  intros A B.
  eapply heq_fn2 with
    (f := fun x => sum_map runitS_f (fun b : B => b) (assocS_f x))
    (g := sum_map (fun a : A => a) lunitS_f).
  - eapply heq_trans;
      [ apply compH_heq;
        [ apply heq_refl
        | eapply heq_trans;
            [ apply sumH_heq; [ apply heq_refl | apply idH_fnH ] | apply sumH_fnH ] ]
      | apply fnH_comp ].
  - eapply heq_trans;
      [ apply sumH_heq; [ apply idH_fnH | apply heq_refl ] | apply sumH_fnH ].
  - intros [a|[[]|b]]; reflexivity.
Qed.

(** Hexagon (symmetry vs. associativity). *)
Theorem sumS_hexagon : forall A B C,
  heq (compH (@assocS A B C) (compH (@swapS (A + B) C) (@assocS C A B)))
      (compH (sumH (@idH A) (@swapS B C))
             (compH (@assocS A C B) (sumH (@swapS A C) (@idH B)))).
Proof.
  intros A B C.
  eapply heq_fn2 with
    (f := fun x => assocS_f (swapS_f (assocS_f x)))
    (g := fun x => sum_map swapS_f (fun b : B => b)
                     (assocS_f (sum_map (fun a : A => a) swapS_f x))).
  - eapply heq_trans; [ apply compH_heq; [ apply heq_refl | apply fnH_comp ] | ].
    apply fnH_comp.
  - eapply heq_trans;
      [ apply compH_heq;
        [ eapply heq_trans;
            [ apply sumH_heq; [ apply idH_fnH | apply heq_refl ] | apply sumH_fnH ]
        | apply compH_heq;
            [ apply heq_refl
            | eapply heq_trans;
                [ apply sumH_heq; [ apply heq_refl | apply idH_fnH ] | apply sumH_fnH ] ] ]
      | ].
    eapply heq_trans; [ apply compH_heq; [ apply heq_refl | apply fnH_comp ] | ].
    apply fnH_comp.
  - intros [a|[b|c]]; reflexivity.
Qed.

(* ===================================================================== *)
(** ** The product is symmetric monoidal, with [unit] the unit. *)

Lemma pinj_prodH : forall A B C D (R : hrel A C) (S : hrel B D),
  pinj R -> pinj S -> pinj (prodH R S).
Proof.
  intros A B C D R S [dR cR] [dS cS]; split.
  - intros [a b] [c d] [c' d'] [H1 H2] [H3 H4]; simpl in *.
    f_equal; [ eapply dR | eapply dS ]; eauto.
  - intros [c d] [a b] [a' b'] [H1 H2] [H3 H4]; unfold convH in *; simpl in *.
    f_equal; [ eapply cR | eapply cS ]; unfold convH; eauto.
Qed.

Lemma convH_prodH : forall A B C D (R : hrel A C) (S : hrel B D),
  heq (convH (prodH R S)) (prodH (convH R) (convH S)).
Proof. intros A B C D R S [c d] [a b]; unfold convH, prodH; simpl; tauto. Qed.

Lemma prodH_idH : forall A B, heq (prodH (@idH A) (@idH B)) idH.
Proof.
  intros A B [a b] [a' b']; unfold prodH, idH; simpl; split.
  - intros [-> ->]; reflexivity.
  - intro H; injection H; auto.
Qed.

Lemma prodH_compH : forall A B C D E F
                           (R : hrel A C) (R' : hrel C E)
                           (S : hrel B D) (S' : hrel D F),
  heq (prodH (compH R R') (compH S S')) (compH (prodH R S) (prodH R' S')).
Proof.
  intros A B C D E F R R' S S' [a b] [e f]; unfold prodH, compH; simpl; split.
  - intros [[m [H1 H2]] [n [H3 H4]]]; exists (m, n); simpl; tauto.
  - intros [[m n] [[H1 H2] [H3 H4]]]; simpl in *; split;
      [ exists m | exists n ]; tauto.
Qed.

Definition assocP_f {A B C : Type} (x : A * (B * C)) : (A * B) * C :=
  (fst x, fst (snd x), snd (snd x)).
Definition assocP_g {A B C : Type} (x : (A * B) * C) : A * (B * C) :=
  (fst (fst x), (snd (fst x), snd x)).
Definition assocP {A B C : Type} : hrel (A * (B * C)) ((A * B) * C) := fnH assocP_f.
Definition assocP' {A B C : Type} : hrel ((A * B) * C) (A * (B * C)) := fnH assocP_g.

Definition swapP_f {A B : Type} (x : A * B) : B * A := (snd x, fst x).
Definition swapP {A B : Type} : hrel (A * B) (B * A) := fnH swapP_f.

Definition lunitP_f {A : Type} (x : unit * A) : A := snd x.
Definition lunitP_g {A : Type} (a : A) : unit * A := (tt, a).
Definition lunitP {A : Type} : hrel (unit * A) A := fnH lunitP_f.
Definition lunitP' {A : Type} : hrel A (unit * A) := fnH lunitP_g.

Definition runitP_f {A : Type} (x : A * unit) : A := fst x.
Definition runitP_g {A : Type} (a : A) : A * unit := (a, tt).
Definition runitP {A : Type} : hrel (A * unit) A := fnH runitP_f.
Definition runitP' {A : Type} : hrel A (A * unit) := fnH runitP_g.

Lemma pinj_assocP : forall A B C, pinj (@assocP A B C).
Proof.
  intros A B C; apply pinj_fnH; intros [a [b c]] [a' [b' c']] H;
    unfold assocP_f in H; simpl in H; congruence.
Qed.

Lemma pinj_swapP : forall A B, pinj (@swapP A B).
Proof.
  intros A B; apply pinj_fnH; intros [a b] [a' b'] H; unfold swapP_f in H;
    simpl in H; congruence.
Qed.

Lemma pinj_lunitP : forall A, pinj (@lunitP A).
Proof.
  intro A; apply pinj_fnH; intros [[] a] [[] a'] H; unfold lunitP_f in H;
    simpl in H; congruence.
Qed.

Lemma pinj_runitP : forall A, pinj (@runitP A).
Proof.
  intro A; apply pinj_fnH; intros [a []] [a' []] H; unfold runitP_f in H;
    simpl in H; congruence.
Qed.

Lemma iso_assocP : forall A B C, isoH (@assocP A B C) assocP'.
Proof.
  intros A B C; apply isoH_fnH;
    [ intros [a [b c]] | intros [[a b] c] ]; reflexivity.
Qed.

Lemma iso_swapP : forall A B, isoH (@swapP A B) swapP.
Proof. intros A B; apply isoH_fnH; intros [a b]; reflexivity. Qed.

Lemma iso_lunitP : forall A, isoH (@lunitP A) lunitP'.
Proof. intro A; apply isoH_fnH; [ intros [[] a] | intro a ]; reflexivity. Qed.

Lemma iso_runitP : forall A, isoH (@runitP A) runitP'.
Proof. intro A; apply isoH_fnH; [ intros [a []] | intro a ]; reflexivity. Qed.

Theorem prodP_pentagon : forall A B C D,
  heq (compH (@assocP A B (C * D)) (@assocP (A * B) C D))
      (compH (prodH (@idH A) (@assocP B C D))
             (compH (@assocP A (B * C) D) (prodH (@assocP A B C) (@idH D)))).
Proof.
  intros A B C D.
  eapply heq_fn2 with
    (f := fun x => assocP_f (assocP_f x))
    (g := fun x => prod_map assocP_f (fun d : D => d)
                     (assocP_f (prod_map (fun a : A => a) assocP_f x))).
  - apply fnH_comp.
  - eapply heq_trans;
      [ apply compH_heq;
        [ eapply heq_trans;
            [ apply prodH_heq; [ apply idH_fnH | apply heq_refl ] | apply prodH_fnH ]
        | apply compH_heq;
            [ apply heq_refl
            | eapply heq_trans;
                [ apply prodH_heq; [ apply heq_refl | apply idH_fnH ] | apply prodH_fnH ] ] ]
      | ].
    eapply heq_trans; [ apply compH_heq; [ apply heq_refl | apply fnH_comp ] | ].
    apply fnH_comp.
  - intros [a [b [c d]]]; reflexivity.
Qed.

Theorem prodP_triangle : forall A B,
  heq (compH (@assocP A unit B) (prodH (@runitP A) (@idH B)))
      (prodH (@idH A) (@lunitP B)).
Proof.
  intros A B.
  eapply heq_fn2 with
    (f := fun x => prod_map runitP_f (fun b : B => b) (assocP_f x))
    (g := prod_map (fun a : A => a) lunitP_f).
  - eapply heq_trans;
      [ apply compH_heq;
        [ apply heq_refl
        | eapply heq_trans;
            [ apply prodH_heq; [ apply heq_refl | apply idH_fnH ] | apply prodH_fnH ] ]
      | apply fnH_comp ].
  - eapply heq_trans;
      [ apply prodH_heq; [ apply idH_fnH | apply heq_refl ] | apply prodH_fnH ].
  - intros [a [[] b]]; reflexivity.
Qed.

Theorem prodP_hexagon : forall A B C,
  heq (compH (@assocP A B C) (compH (@swapP (A * B) C) (@assocP C A B)))
      (compH (prodH (@idH A) (@swapP B C))
             (compH (@assocP A C B) (prodH (@swapP A C) (@idH B)))).
Proof.
  intros A B C.
  eapply heq_fn2 with
    (f := fun x => assocP_f (swapP_f (assocP_f x)))
    (g := fun x => prod_map swapP_f (fun b : B => b)
                     (assocP_f (prod_map (fun a : A => a) swapP_f x))).
  - eapply heq_trans; [ apply compH_heq; [ apply heq_refl | apply fnH_comp ] | ].
    apply fnH_comp.
  - eapply heq_trans;
      [ apply compH_heq;
        [ eapply heq_trans;
            [ apply prodH_heq; [ apply idH_fnH | apply heq_refl ] | apply prodH_fnH ]
        | apply compH_heq;
            [ apply heq_refl
            | eapply heq_trans;
                [ apply prodH_heq; [ apply heq_refl | apply idH_fnH ] | apply prodH_fnH ] ] ]
      | ].
    eapply heq_trans; [ apply compH_heq; [ apply heq_refl | apply fnH_comp ] | ].
    apply fnH_comp.
  - intros [a [b c]]; reflexivity.
Qed.

(* ===================================================================== *)
(** ** Distributivity: [A × (B + C) ≅ (A × B) + (A × C)]. *)

Definition distr_f {A B C : Type} (x : A * (B + C)) : (A * B) + (A * C) :=
  match snd x with inl b => inl (fst x, b) | inr c => inr (fst x, c) end.

Definition distr_g {A B C : Type} (x : (A * B) + (A * C)) : A * (B + C) :=
  match x with inl p => (fst p, inl (snd p)) | inr p => (fst p, inr (snd p)) end.

Definition distrH {A B C : Type} : hrel (A * (B + C)) ((A * B) + (A * C)) := fnH distr_f.
Definition distrH' {A B C : Type} : hrel ((A * B) + (A * C)) (A * (B + C)) := fnH distr_g.

Lemma pinj_distrH : forall A B C, pinj (@distrH A B C).
Proof.
  intros A B C; apply pinj_fnH; intros [a [b|c]] [a' [b'|c']] H;
    unfold distr_f in H; simpl in H; congruence.
Qed.

Theorem iso_distrH : forall A B C, isoH (@distrH A B C) distrH'.
Proof.
  intros A B C; apply isoH_fnH;
    [ intros [a [b|c]] | intros [[a b]|[a c]] ]; reflexivity.
Qed.

(** Naturality of the distributor in all three arguments. *)
Theorem distrH_natural : forall A A' B B' C C'
    (R : hrel A A') (S : hrel B B') (T : hrel C C'),
  heq (compH (prodH R (sumH S T)) (@distrH A' B' C'))
      (compH (@distrH A B C) (sumH (prodH R S) (prodH R T))).
Proof.
  intros A A' B B' C C' R S T [a [b|c]] y; split.
  - (* left injection, forwards *)
    intros [[m1 m2] [[H1 H2] Hy]].
    unfold prodH in H1, H2; simpl in H1, H2.
    destruct m2 as [b'|c']; unfold sumH in H2; simpl in H2; [ | contradiction ].
    unfold distrH, fnH, distr_f in Hy; simpl in Hy; subst y.
    exists (inl (a, b)); split; [ reflexivity | ].
    unfold sumH, prodH; simpl; split; assumption.
  - (* left injection, backwards *)
    intros [k [Hk Hy]].
    unfold distrH, fnH, distr_f in Hk; simpl in Hk; subst k.
    destruct y as [[y1 y2]|[y1 y2]]; unfold sumH in Hy; simpl in Hy;
      [ | contradiction ].
    unfold prodH in Hy; simpl in Hy; destruct Hy as [Hy1 Hy2].
    exists (y1, inl y2); split.
    + unfold prodH, sumH; simpl; split; assumption.
    + unfold distrH, fnH, distr_f; reflexivity.
  - (* right injection, forwards *)
    intros [[m1 m2] [[H1 H2] Hy]].
    unfold prodH in H1, H2; simpl in H1, H2.
    destruct m2 as [b'|c']; unfold sumH in H2; simpl in H2; [ contradiction | ].
    unfold distrH, fnH, distr_f in Hy; simpl in Hy; subst y.
    exists (inr (a, c)); split; [ reflexivity | ].
    unfold sumH, prodH; simpl; split; assumption.
  - (* right injection, backwards *)
    intros [k [Hk Hy]].
    unfold distrH, fnH, distr_f in Hk; simpl in Hk; subst k.
    destruct y as [[y1 y2]|[y1 y2]]; unfold sumH in Hy; simpl in Hy;
      [ contradiction | ].
    unfold prodH in Hy; simpl in Hy; destruct Hy as [Hy1 Hy2].
    exists (y1, inr y2); split.
    + unfold prodH, sumH; simpl; split; assumption.
    + unfold distrH, fnH, distr_f; reflexivity.
Qed.

(* ===================================================================== *)
(** ** Naturality of the structural maps.

    A monoidal category needs its associator, unitors and symmetry to be natural
    *transformations*, not merely isomorphisms; these are the squares. *)

Theorem assocS_natural : forall A A' B B' C C'
    (R : hrel A A') (S : hrel B B') (T : hrel C C'),
  heq (compH (sumH R (sumH S T)) (@assocS A' B' C'))
      (compH (@assocS A B C) (sumH (sumH R S) T)).
Proof.
  intros A A' B B' C C' R S T x y; split.
  - intros [m [Hm Hy]]; unfold assocS, fnH in Hy; subst y.
    destruct x as [a|[b|c]]; destruct m as [a'|[b'|c']];
      unfold sumH in Hm; simpl in Hm; try contradiction.
    + exists (inl (inl a)); split; [ reflexivity | unfold sumH; simpl; exact Hm ].
    + exists (inl (inr b)); split; [ reflexivity | unfold sumH; simpl; exact Hm ].
    + exists (inr c); split; [ reflexivity | unfold sumH; simpl; exact Hm ].
  - intros [k [Hk Hy]]; unfold assocS, fnH in Hk; subst k.
    destruct x as [a|[b|c]]; simpl in Hy;
      destruct y as [[a'|b']|c']; unfold sumH in Hy; simpl in Hy;
      try contradiction.
    + exists (inl a'); split; [ unfold sumH; simpl; exact Hy | reflexivity ].
    + exists (inr (inl b')); split; [ unfold sumH; simpl; exact Hy | reflexivity ].
    + exists (inr (inr c')); split; [ unfold sumH; simpl; exact Hy | reflexivity ].
Qed.

Theorem swapS_natural : forall A A' B B' (R : hrel A A') (S : hrel B B'),
  heq (compH (sumH R S) (@swapS A' B')) (compH (@swapS A B) (sumH S R)).
Proof.
  intros A A' B B' R S x y; split.
  - intros [m [Hm Hy]]; unfold swapS, fnH in Hy; subst y.
    destruct x as [a|b]; destruct m as [a'|b']; unfold sumH in Hm; simpl in Hm;
      try contradiction.
    + exists (inr a); split; [ reflexivity | unfold sumH; simpl; exact Hm ].
    + exists (inl b); split; [ reflexivity | unfold sumH; simpl; exact Hm ].
  - intros [k [Hk Hy]]; unfold swapS, fnH in Hk; subst k.
    destruct x as [a|b]; destruct y as [b'|a']; unfold sumH in Hy; simpl in Hy;
      try contradiction.
    + exists (inl a'); split; [ unfold sumH; simpl; exact Hy | reflexivity ].
    + exists (inr b'); split; [ unfold sumH; simpl; exact Hy | reflexivity ].
Qed.

Theorem lunitS_natural : forall A A' (R : hrel A A'),
  heq (compH (sumH (@idH Empty_set) R) (@lunitS A')) (compH (@lunitS A) R).
Proof.
  intros A A' R [[]|a] y; split.
  - intros [m [Hm Hy]]; unfold lunitS, fnH in Hy.
    destruct m as [[]|a']; unfold sumH in Hm; simpl in Hm.
    simpl in Hy; subst y; exists a; split; [ reflexivity | exact Hm ].
  - intros [k [Hk Hy]]; unfold lunitS, fnH in Hk; simpl in Hk; subst k.
    exists (inr y); split; [ unfold sumH; simpl; exact Hy | reflexivity ].
Qed.

Theorem runitS_natural : forall A A' (R : hrel A A'),
  heq (compH (sumH R (@idH Empty_set)) (@runitS A')) (compH (@runitS A) R).
Proof.
  intros A A' R [a|[]] y; split.
  - intros [m [Hm Hy]]; unfold runitS, fnH in Hy.
    destruct m as [a'|[]]; unfold sumH in Hm; simpl in Hm.
    simpl in Hy; subst y; exists a; split; [ reflexivity | exact Hm ].
  - intros [k [Hk Hy]]; unfold runitS, fnH in Hk; simpl in Hk; subst k.
    exists (inl y); split; [ unfold sumH; simpl; exact Hy | reflexivity ].
Qed.

Theorem assocP_natural : forall A A' B B' C C'
    (R : hrel A A') (S : hrel B B') (T : hrel C C'),
  heq (compH (prodH R (prodH S T)) (@assocP A' B' C'))
      (compH (@assocP A B C) (prodH (prodH R S) T)).
Proof.
  intros A A' B B' C C' R S T [a [b c]] y; split.
  - intros [[m1 [m2 m3]] [[H1 [H2 H3]] Hy]]; simpl in *.
    unfold assocP, fnH, assocP_f in Hy; simpl in Hy; subst y.
    exists (a, b, c); split; [ reflexivity | ].
    unfold prodH; simpl; repeat split; assumption.
  - intros [k [Hk Hy]]; unfold assocP, fnH, assocP_f in Hk; simpl in Hk; subst k.
    destruct y as [[y1 y2] y3]; unfold prodH in Hy; simpl in Hy.
    destruct Hy as [[H1 H2] H3].
    exists (y1, (y2, y3)); split; [ unfold prodH; simpl; repeat split; assumption | ].
    unfold assocP, fnH, assocP_f; reflexivity.
Qed.

Theorem swapP_natural : forall A A' B B' (R : hrel A A') (S : hrel B B'),
  heq (compH (prodH R S) (@swapP A' B')) (compH (@swapP A B) (prodH S R)).
Proof.
  intros A A' B B' R S [a b] y; split.
  - intros [[m1 m2] [[H1 H2] Hy]]; simpl in *.
    unfold swapP, fnH, swapP_f in Hy; simpl in Hy; subst y.
    exists (b, a); split; [ reflexivity | unfold prodH; simpl; split; assumption ].
  - intros [k [Hk Hy]]; unfold swapP, fnH, swapP_f in Hk; simpl in Hk; subst k.
    destruct y as [y1 y2]; unfold prodH in Hy; simpl in Hy; destruct Hy as [H1 H2].
    exists (y2, y1); split; [ unfold prodH; simpl; split; assumption | ].
    unfold swapP, fnH, swapP_f; reflexivity.
Qed.

Theorem lunitP_natural : forall A A' (R : hrel A A'),
  heq (compH (prodH (@idH unit) R) (@lunitP A')) (compH (@lunitP A) R).
Proof.
  intros A A' R [[] a] y; split.
  - intros [[m1 m2] [[H1 H2] Hy]]; simpl in *.
    unfold lunitP, fnH, lunitP_f in Hy; simpl in Hy; subst y.
    exists a; split; [ reflexivity | exact H2 ].
  - intros [k [Hk Hy]]; unfold lunitP, fnH, lunitP_f in Hk; simpl in Hk; subst k.
    exists (tt, y); split; [ unfold prodH, idH; simpl; split; [ reflexivity | exact Hy ] | ].
    unfold lunitP, fnH, lunitP_f; reflexivity.
Qed.

Theorem runitP_natural : forall A A' (R : hrel A A'),
  heq (compH (prodH R (@idH unit)) (@runitP A')) (compH (@runitP A) R).
Proof.
  intros A A' R [a []] y; split.
  - intros [[m1 m2] [[H1 H2] Hy]]; simpl in *.
    unfold runitP, fnH, runitP_f in Hy; simpl in Hy; subst y.
    exists a; split; [ reflexivity | exact H1 ].
  - intros [k [Hk Hy]]; unfold runitP, fnH, runitP_f in Hk; simpl in Hk; subst k.
    exists (y, tt); split; [ unfold prodH, idH; simpl; split; [ exact Hy | reflexivity ] | ].
    unfold runitP, fnH, runitP_f; reflexivity.
Qed.
