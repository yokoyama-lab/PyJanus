(** * RevTraced.v — the trace axioms, on top of the monoidal structure

    [RevTrace.v] defines the trace and proves it closed on \textsf{PInj}, plus
    yanking, vanishing-I and left naturality.  [RevSMC.v] then supplies the
    symmetric monoidal structure those axioms are stated relative to.  This file
    adds the axioms that need that structure.

    Proved here:

      - [trace_natural_r]  — naturality in the output object:
        [Tr(f ; (g ⊕ id)) = Tr(f) ; g];
      - [trace_superposing] — [Tr(g ⊕ f) = g ⊕ Tr(f)], with the two sides lined
        up by the associator (the frame core's loop sitting beside an untouched
        computation).

    Still open, and stated precisely at the end of the file: **vanishing-II** and
    **dinaturality**.  Both are path-surgery arguments over the feedback object
    rather than case analyses, which is why they are not here yet. *)

From Stdlib Require Import Bool Arith.
Require Import RevCore RevAlgebra RevCat RevTrace RevSMC.

(* ===================================================================== *)
(** ** Naturality in the output. *)

(** The feedback part of [f ; (g ⊕ id)] is [f]'s own: post-composing with
    something that leaves the wire alone cannot change the loop. *)
Lemma fb_natural_r : forall A B B' U (f : hrel (A + U) (B + U)) (g : hrel B B'),
  forall u u', fb (compH f (sumH g (@idH U))) u u' <-> fb f u u'.
Proof.
  intros A B B' U f g u u'; unfold fb, compH; split.
  - intros [[m|m] [H1 H2]]; unfold sumH in H2; simpl in H2;
      [ contradiction | unfold idH in H2; subst m; exact H1 ].
  - intro H; exists (inr u'); split; [ exact H | unfold sumH, idH; reflexivity ].
Qed.

Lemma pathn_natural_r : forall A B B' U (f : hrel (A + U) (B + U)) (g : hrel B B') n,
  forall u u', pathn (compH f (sumH g (@idH U))) n u u' <-> pathn f n u u'.
Proof.
  intros A B B' U f g n; induction n; intros u u'; simpl; [ tauto | ].
  unfold compH; split.
  - intros [m [H1 H2]]; exists m; split;
      [ apply (fb_natural_r A B B' U f g); exact H1 | apply IHn; exact H2 ].
  - intros [m [H1 H2]]; exists m; split;
      [ apply (fb_natural_r A B B' U f g); exact H1 | apply IHn; exact H2 ].
Qed.

Theorem trace_natural_r : forall A B B' U (f : hrel (A + U) (B + U)) (g : hrel B B'),
  heq (traceH (compH f (sumH g (@idH U)))) (compH (traceH f) g).
Proof.
  intros A B B' U f g a b'; unfold traceH, compH; split.
  - intros [[[m|m] [H1 H2]] | [n [u [u' [[[m|m] [E1 E2]] [Hp [[k|k] [X1 X2]]]]]]]];
      unfold sumH in *; simpl in *;
      try contradiction; try (unfold idH in *; subst; contradiction).
    + exists m; split; [ left; exact H1 | exact H2 ].
    + unfold idH in E2; subst m.
      exists k; split; [ | exact X2 ].
      right; exists n, u, u'; repeat split;
        [ exact E1 | apply (pathn_natural_r A B B' U f g n); exact Hp | exact X1 ].
  - intros [m [[H|[n [u [u' [E1 [Hp X]]]]]] Hg]].
    + left; exists (inl m); split; [ exact H | unfold sumH; simpl; exact Hg ].
    + right; exists n, u, u'; repeat split.
      * exists (inr u); split; [ exact E1 | unfold sumH, idH; reflexivity ].
      * apply (pathn_natural_r A B B' U f g n); exact Hp.
      * exists (inl m); split; [ exact X | unfold sumH; simpl; exact Hg ].
Qed.

(* ===================================================================== *)
(** ** Superposing: a traced loop beside an untouched computation. *)

(** [g ⊕ f] with the feedback object pulled to the outside:
    [(W+X)+U → (Z+Y)+U]. *)
Definition sup {W Z X Y U : Type}
  (g : hrel W Z) (f : hrel (X + U) (Y + U)) : hrel ((W + X) + U) ((Z + Y) + U) :=
  compH assocS' (compH (sumH g f) assocS).

Lemma fb_sup : forall W Z X Y U (g : hrel W Z) (f : hrel (X + U) (Y + U)),
  forall u u', fb (sup g f) u u' <-> fb f u u'.
Proof.
  intros W Z X Y U g f u u'; unfold fb, sup, compH, assocS, assocS', fnH,
    assocS_f, assocS_g, sumH; simpl; split.
  - intros [m [Hm [k [Hk Hy]]]]; subst m.
    destruct k as [z|[y|v]]; simpl in Hk; try contradiction;
      simpl in Hy; try discriminate.
    injection Hy; intro; subst v; exact Hk.
  - intro H; exists (inr (inr u)); split; [ reflexivity | ].
    exists (inr (inr u')); split; [ exact H | reflexivity ].
Qed.

Lemma pathn_sup : forall W Z X Y U (g : hrel W Z) (f : hrel (X + U) (Y + U)) n,
  forall u u', pathn (sup g f) n u u' <-> pathn f n u u'.
Proof.
  intros W Z X Y U g f n; induction n; intros u u'; simpl; [ tauto | ].
  unfold compH; split.
  - intros [m [H1 H2]]; exists m; split;
      [ apply (fb_sup W Z X Y U g f); exact H1 | apply IHn; exact H2 ].
  - intros [m [H1 H2]]; exists m; split;
      [ apply (fb_sup W Z X Y U g f); exact H1 | apply IHn; exact H2 ].
Qed.

Theorem trace_superposing : forall W Z X Y U (g : hrel W Z) (f : hrel (X + U) (Y + U)),
  heq (traceH (sup g f)) (sumH g (traceH f)).
Proof.
  intros W Z X Y U g f x y; unfold traceH, sup, compH, sumH,
    assocS, assocS', fnH, assocS_f, assocS_g; split.
  - intros [[m [Hm [k [Hk Hy]]]] | [n [u [u' [[m [Hm [k [Hk Hy]]]] [Hp Hx]]]]]].
    + (* exits immediately *)
      destruct x as [w|x']; simpl in Hm; subst m;
        destruct k as [z|[y'|v]]; simpl in Hk; try contradiction;
        simpl in Hy; try discriminate; injection Hy; intro; subst y; simpl.
      * exact Hk.
      * left; exact Hk.
    + (* enters the wire: only the [X] side can *)
      destruct x as [w|x']; simpl in Hm; subst m;
        destruct k as [z|[y'|v]]; simpl in Hk; try contradiction;
        simpl in Hy; try discriminate.
      injection Hy; intro; subst v.
      destruct Hx as [m2 [Hm2 [k2 [Hk2 Hy2]]]]; subst m2.
      destruct k2 as [z2|[y2|v2]]; simpl in Hk2; try contradiction;
        simpl in Hy2; try discriminate; injection Hy2; intro; subst y; simpl.
      right; exists n, u, u'; repeat split;
        [ exact Hk | apply (pathn_sup W Z X Y U g f n); exact Hp | exact Hk2 ].
  - destruct x as [w|x'].
    + (* the untouched side *)
      intro H; destruct y as [z|y']; simpl in H; [ | contradiction ].
      left; exists (inl w); split; [ reflexivity | ].
      exists (inl z); split; [ exact H | reflexivity ].
    + (* the traced side *)
      intro H; destruct y as [z|y']; simpl in H; [ contradiction | ].
      destruct H as [H | [n [u [u' [E1 [Hp Hex]]]]]].
      * left; exists (inr (inl x')); split; [ reflexivity | ].
        exists (inr (inl y')); split; [ exact H | reflexivity ].
      * right; exists n, u, u'; repeat split.
        -- exists (inr (inl x')); split; [ reflexivity | ].
           exists (inr (inr u)); split; [ exact E1 | reflexivity ].
        -- apply (pathn_sup W Z X Y U g f n); exact Hp.
        -- exists (inr (inr u')); split; [ reflexivity | ].
           exists (inr (inl y')); split; [ exact Hex | reflexivity ].
Qed.

(* ===================================================================== *)
(** ** What is still missing for the full phrase.

    "\textsf{PInj} is a distributive traced symmetric monoidal category" needs,
    beyond everything above, two more trace axioms:

    - **vanishing-II**: tracing out [U ⊕ V] in one go is tracing out [V] and then
      [U],
      [[
        Tr^{U+V}(f) = Tr^U (Tr^V (assocS' ; f ; assocS))
      ]]
    - **dinaturality**: sliding a map along the feedback wire,
      [[
        Tr^U (f ; (id ⊕ h)) = Tr^{U'} ((id ⊕ h) ; f)
      ]]

    Neither is a case analysis: both are statements about the *paths* the
    execution formula sums over.  Vanishing-II has to decompose a path through
    [U ⊎ V] into the [V]-segments between successive [U]-visits, and dinaturality
    has to re-index a path along [h].  They need path-surgery lemmas
    ([pathn_snoc] is the only one of that kind so far), not the pointwise
    reasoning that discharges the axioms above.

    Until they are proved, the honest statement of what is machine-checked is:
    \textsf{PInj} is symmetric monoidal for the coproduct and for the product,
    distributive, and carries a trace operator that is closed on it, commutes
    with the dagger, and satisfies yanking, vanishing-I, and naturality in both
    arguments, plus superposing. *)
