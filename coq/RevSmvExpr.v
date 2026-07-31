(** * RevSmvExpr.v — the expression encoding of the totality checker, verified

    [jana_py/smv.py] compiles Janus expressions into SMV terms.  Two things there
    can silently turn a proof of [INVARSPEC pc != ERR] into a lie, and both were
    found by running the corpus rather than by reasoning:

      - **nuXmv's integer [/] truncates toward zero while Janus (like Python)
        floors**, and nuXmv has no integer [mod] at all inside the SMT engine.
        Writing [/] straight through is wrong for every negative dividend, so
        [_div_defines] emits a correction.  Until now that correction was checked
        on four sign combinations by a test.  [mfdiv_correct] proves it.
      - **Janus comparisons yield integers**, so [x += (y > 0)] is legal; the
        translation is two-sorted and refuses such expressions rather than
        guessing.  That refusal is what [tri]/[trb] below model, and
        [tr_sound] says the translation is right wherever it is defined.

    The source semantics is [RevLowerExpr]'s [seval] — the same [sexpr] that
    [RevLowerStmt.v] uses for the vjanus lowering — so this file connects the
    checker's encoding to the semantics the rest of the development already
    reasons about, rather than inventing a private notion of "the value of an
    expression".

    [tests/verify/test_smv_expr.py] pins [smv.py]'s emitted macro to the shape
    proved correct here, so the theorem stays about the code that actually runs. *)

From Stdlib Require Import ZArith Bool Lia.
Require Import RevLowerExpr.
Open Scope Z_scope.

(* ===================================================================== *)
(** ** The fragment of SMV that [smv.py] emits.

    Two-sorted, as SMV is: a term denotes an integer or a boolean, and using one
    where the other is expected has no value.  [MQuot] is nuXmv's [/] — Rocq's
    [Z.quot] truncates toward zero, which is exactly nuXmv's behaviour and
    exactly *not* Janus's. *)

Inductive sm :=
| MNum (z : Z)
| MVar (n : nat)
| MAdd (a b : sm) | MSub (a b : sm) | MMul (a b : sm)
| MQuot (a b : sm)                       (** nuXmv [/]: truncates toward zero *)
| MEq (a b : sm) | MLt (a b : sm) | MLe (a b : sm)
| MNot (a : sm) | MAnd (a b : sm) | MOr (a b : sm)
| MIff (a b : sm)                        (** nuXmv [<->] *)
| MCase (c t e : sm).                    (** [case c : t; TRUE : e; esac] *)

Inductive val := Vi (z : Z) | Vb (b : bool).

(** Written without a local abbreviation for the binary cases: [simpl] then
    reduces predictably, which the proofs below rely on. *)
Fixpoint smeval (g : nat -> Z) (m : sm) : option val :=
  match m with
  | MNum z => Some (Vi z)
  | MVar n => Some (Vi (g n))
  | MAdd a b =>
      match smeval g a, smeval g b with
      | Some (Vi x), Some (Vi y) => Some (Vi (x + y)) | _, _ => None end
  | MSub a b =>
      match smeval g a, smeval g b with
      | Some (Vi x), Some (Vi y) => Some (Vi (x - y)) | _, _ => None end
  | MMul a b =>
      match smeval g a, smeval g b with
      | Some (Vi x), Some (Vi y) => Some (Vi (x * y)) | _, _ => None end
  | MQuot a b =>
      match smeval g a, smeval g b with
      | Some (Vi x), Some (Vi y) => Some (Vi (Z.quot x y)) | _, _ => None end
  | MEq a b =>
      match smeval g a, smeval g b with
      | Some (Vi x), Some (Vi y) => Some (Vb (Z.eqb x y)) | _, _ => None end
  | MLt a b =>
      match smeval g a, smeval g b with
      | Some (Vi x), Some (Vi y) => Some (Vb (Z.ltb x y)) | _, _ => None end
  | MLe a b =>
      match smeval g a, smeval g b with
      | Some (Vi x), Some (Vi y) => Some (Vb (Z.leb x y)) | _, _ => None end
  | MNot a =>
      match smeval g a with Some (Vb x) => Some (Vb (negb x)) | _ => None end
  | MAnd a b =>
      match smeval g a, smeval g b with
      | Some (Vb x), Some (Vb y) => Some (Vb (x && y)) | _, _ => None end
  | MOr a b =>
      match smeval g a, smeval g b with
      | Some (Vb x), Some (Vb y) => Some (Vb (x || y)) | _, _ => None end
  | MIff a b =>
      match smeval g a, smeval g b with
      | Some (Vb x), Some (Vb y) => Some (Vb (Bool.eqb x y)) | _, _ => None end
  | MCase c t e =>
      match smeval g c with
      | Some (Vb true) => smeval g t
      | Some (Vb false) => smeval g e
      | _ => None
      end
  end.

(* ===================================================================== *)
(** ** The floor-division macro, exactly as [_div_defines] emits it.

    [smv.py] binds [tq] and [tr] as DEFINEs and refers to them; the terms below
    repeat those subterms instead, which denotes the same thing — a DEFINE is a
    macro, not a let-binding with its own semantics. *)

Definition mtq (a b : sm) : sm := MCase (MEq b (MNum 0)) (MNum 0) (MQuot a b).
Definition mtr (a b : sm) : sm := MSub a (MMul b (mtq a b)).

Definition mfdiv (a b : sm) : sm :=
  MCase (MEq (mtr a b) (MNum 0)) (mtq a b)
    (MCase (MIff (MLt (mtr a b) (MNum 0)) (MLt b (MNum 0)))
       (mtq a b)
       (MSub (mtq a b) (MNum 1))).

Definition mfmod (a b : sm) : sm := MSub a (MMul b (mfdiv a b)).

(** The arithmetic content, on its own: correcting the truncating quotient by
    one when the truncating remainder and the divisor disagree in sign gives the
    flooring quotient. *)
Lemma floor_from_trunc : forall a b, b <> 0 ->
  (let q := Z.quot a b in
   let r := a - b * q in
   if Z.eqb r 0 then q
   else if Bool.eqb (Z.ltb r 0) (Z.ltb b 0) then q else q - 1)
  = a / b.
Proof.
  intros a b Hb; simpl.
  assert (Hrem : a - b * Z.quot a b = Z.rem a b) by (pose proof (Z.quot_rem a b Hb); lia).
  rewrite Hrem.
  assert (Hbnd : Z.abs (Z.rem a b) < Z.abs b) by (apply Z.rem_bound_abs; exact Hb).
  destruct (Z.eqb_spec (Z.rem a b) 0) as [Hz | Hnz].
  - apply Z.div_unique with (r := 0);
      [ destruct (Z.lt_trichotomy b 0) as [Hlt | [He | Hgt]]; lia
      | pose proof (Z.quot_rem a b Hb); lia ].
  - destruct (Z.ltb_spec (Z.rem a b) 0) as [Hr0 | Hr0];
      destruct (Z.ltb_spec b 0) as [Hb0 | Hb0]; simpl.
    + (* both negative: the truncating remainder is already a flooring one *)
      apply Z.div_unique with (r := Z.rem a b);
        [ right; lia
        | pose proof (Z.quot_rem a b Hb); lia ].
    + (* r < 0 <= b: shift by one *)
      apply Z.div_unique with (r := Z.rem a b + b);
        [ left; lia
        | pose proof (Z.quot_rem a b Hb); lia ].
    + (* 0 <= r, b < 0: shift by one *)
      apply Z.div_unique with (r := Z.rem a b + b);
        [ right; lia
        | pose proof (Z.quot_rem a b Hb); lia ].
    + (* both nonnegative *)
      apply Z.div_unique with (r := Z.rem a b);
        [ left; lia
        | pose proof (Z.quot_rem a b Hb); lia ].
Qed.

Lemma mtq_eval : forall g a b x y,
  smeval g a = Some (Vi x) -> smeval g b = Some (Vi y) -> y <> 0 ->
  smeval g (mtq a b) = Some (Vi (Z.quot x y)).
Proof.
  intros g a b x y Ha Hb Hy; unfold mtq; cbn [smeval]; rewrite Hb; cbn [smeval].
  destruct (Z.eqb_spec y 0) as [Hz | Hz]; [ lia | ].
  cbn [smeval]; rewrite ?Ha, ?Hb; reflexivity.
Qed.

Lemma mtr_eval : forall g a b x y,
  smeval g a = Some (Vi x) -> smeval g b = Some (Vi y) -> y <> 0 ->
  smeval g (mtr a b) = Some (Vi (x - y * Z.quot x y)).
Proof.
  intros g a b x y Ha Hb Hy; unfold mtr; cbn [smeval].
  rewrite (mtq_eval g a b x y Ha Hb Hy), ?Ha, ?Hb; reflexivity.
Qed.

(** **The** theorem for the division trap: the macro [smv.py] emits denotes
    Janus's (Python's) flooring quotient, not nuXmv's truncating one. *)
Theorem mfdiv_correct : forall g a b x y,
  smeval g a = Some (Vi x) -> smeval g b = Some (Vi y) -> y <> 0 ->
  smeval g (mfdiv a b) = Some (Vi (x / y)).
Proof.
  intros g a b x y Ha Hb Hy.
  rewrite <- (floor_from_trunc x y Hy); cbv zeta.
  unfold mfdiv; cbn [smeval].
  rewrite (mtr_eval g a b x y Ha Hb Hy); cbn [smeval].
  destruct (Z.eqb_spec (x - y * Z.quot x y) 0) as [Hz | Hnz].
  - apply (mtq_eval g a b x y Ha Hb Hy).
  - cbn [smeval]; rewrite ?(mtr_eval g a b x y Ha Hb Hy), ?Hb; cbn [smeval].
    destruct (Bool.eqb ((x - y * Z.quot x y) <? 0) (y <? 0)).
    + apply (mtq_eval g a b x y Ha Hb Hy).
    + cbn [smeval]; rewrite (mtq_eval g a b x y Ha Hb Hy); reflexivity.
Qed.

Theorem mfmod_correct : forall g a b x y,
  smeval g a = Some (Vi x) -> smeval g b = Some (Vi y) -> y <> 0 ->
  smeval g (mfmod a b) = Some (Vi (x mod y)).
Proof.
  intros g a b x y Ha Hb Hy; unfold mfmod; cbn [smeval].
  rewrite (mfdiv_correct g a b x y Ha Hb Hy), ?Ha, ?Hb.
  f_equal; f_equal; pose proof (Z.div_mod x y Hy); lia.
Qed.

(** And the trap itself, as a counterexample rather than a claim: writing
    nuXmv's [/] straight through disagrees with Janus already at [-7 / 2]. *)
Theorem naive_division_is_wrong :
  smeval (fun _ => 0) (MQuot (MNum (-7)) (MNum 2)) = Some (Vi (-3))
  /\ (-7) / 2 = -4.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(** ** The two-sorted translation, as [_iexpr] / [_bexpr].

    Integer position accepts numbers, variables and arithmetic; boolean position
    accepts comparisons, [&&], [||] and [!].  Anything else — a comparison used
    as an integer, an integer used as a condition, a bitwise operator — has no
    translation, which is [smv.py] raising [SmvUnsupported] rather than
    guessing. *)

Fixpoint tri (e : sexpr) : option sm :=
  match e with
  | SNum z => Some (MNum z)
  | SVar n => Some (MVar n)
  | SNot _ => None
  | SBin o a b =>
      match tri a, tri b with
      | Some ma, Some mb =>
          match o with
          | SAdd => Some (MAdd ma mb)
          | SSub => Some (MSub ma mb)
          | SMul => Some (MMul ma mb)
          | SDiv => Some (mfdiv ma mb)
          | SMod => Some (mfmod ma mb)
          | _ => None
          end
      | _, _ => None
      end
  end.

Fixpoint trb (e : sexpr) : option sm :=
  match e with
  | SNum _ | SVar _ => None
  | SNot e1 => match trb e1 with Some m => Some (MNot m) | None => None end
  | SBin o a b =>
      match o with
      | SAnd => match trb a, trb b with
                | Some ma, Some mb => Some (MAnd ma mb) | _, _ => None end
      | SOr => match trb a, trb b with
               | Some ma, Some mb => Some (MOr ma mb) | _, _ => None end
      | SEq | SNe | SLt | SGt | SLe | SGe =>
          match tri a, tri b with
          | Some ma, Some mb =>
              match o with
              | SEq => Some (MEq ma mb)
              | SNe => Some (MNot (MEq ma mb))
              | SLt => Some (MLt ma mb)
              | SGt => Some (MLt mb ma)
              | SLe => Some (MLe ma mb)
              | SGe => Some (MLe mb ma)
              | _ => None
              end
          | _, _ => None
          end
      | _ => None
      end
  end.

(** Wherever the translation is defined it agrees with [seval]: an integer-position
    term denotes the same integer, and a boolean-position term denotes the boolean
    whose 0/1 encoding [seval] produces. *)
Lemma tr_sound : forall g e,
  (forall m v, tri e = Some m -> seval g e = Some v -> smeval g m = Some (Vi v))
  /\ (forall m v, trb e = Some m -> seval g e = Some v ->
        exists c, v = b2z c /\ smeval g m = Some (Vb c)).
Proof.
  intros g; induction e as [ z | n | e1 IH1 | o a IHa b IHb ]; split.
  (* SNum, then SVar: integer position translates, boolean position refuses *)
  - intros m v Hm Hv; simpl in Hm, Hv;
      injection Hm as <-; injection Hv as <-; reflexivity.
  - intros m v Hm; simpl in Hm; discriminate.
  - intros m v Hm Hv; simpl in Hm, Hv;
      injection Hm as <-; injection Hv as <-; reflexivity.
  - intros m v Hm; simpl in Hm; discriminate.
  (* SNot has no integer translation *)
  - intros m v Hm; simpl in Hm; discriminate.
  - intros m v Hm Hv; simpl in Hm, Hv.
    destruct (trb e1) as [m1|] eqn:Hm1; [ | discriminate ].
    destruct (seval g e1) as [v1|] eqn:Hv1; [ | discriminate ].
    destruct (proj2 IH1 m1 v1 eq_refl eq_refl) as [c [Hc Hs]].
    injection Hm as <-; injection Hv as <-.
    exists (Z.eqb v1 0); split; [ reflexivity | ].
    simpl; rewrite Hs; subst v1; destruct c; reflexivity.
  - (* integer position *)
    intros m v Hm Hv; simpl in Hm, Hv.
    destruct (tri a) as [ma|] eqn:Hma; [ | destruct o; discriminate ].
    destruct (tri b) as [mb|] eqn:Hmb; [ | destruct o; discriminate ].
    destruct (seval g a) as [va|] eqn:Hva; [ | discriminate ].
    destruct (seval g b) as [vb|] eqn:Hvb; [ | discriminate ].
    pose proof (proj1 IHa ma va eq_refl eq_refl) as Ha.
    pose proof (proj1 IHb mb vb eq_refl eq_refl) as Hb.
    destruct o; simpl in Hm, Hv; try discriminate;
      injection Hm as <-.
    + simpl; rewrite Ha, Hb; simpl; congruence.
    + simpl; rewrite Ha, Hb; simpl; congruence.
    + simpl; rewrite Ha, Hb; simpl; congruence.
    + destruct (Z.eqb_spec vb 0) as [Hz | Hnz]; [ discriminate | ].
      injection Hv as <-; apply (mfdiv_correct g ma mb va vb Ha Hb Hnz).
    + destruct (Z.eqb_spec vb 0) as [Hz | Hnz]; [ discriminate | ].
      injection Hv as <-; apply (mfmod_correct g ma mb va vb Ha Hb Hnz).
  - (* boolean position *)
    intros m v Hm Hv; simpl in Hm, Hv.
    destruct (seval g a) as [va|] eqn:Hva; [ | destruct o; discriminate ].
    destruct (seval g b) as [vb|] eqn:Hvb; [ | destruct o; discriminate ].
    destruct o; simpl in Hm, Hv; try discriminate.
    (* comparisons *)
    all: try (destruct (tri a) as [ma|] eqn:Hma; [ | discriminate ];
              destruct (tri b) as [mb|] eqn:Hmb; [ | discriminate ];
              pose proof (proj1 IHa ma va eq_refl eq_refl) as Ha;
              pose proof (proj1 IHb mb vb eq_refl eq_refl) as Hb;
              injection Hm as <-; injection Hv as <-;
              simpl; rewrite Ha, Hb; simpl;
              eexists; split; [ reflexivity | reflexivity ]).
    (* && and || *)
    all: destruct (trb a) as [ma|] eqn:Hma; [ | discriminate ];
         destruct (trb b) as [mb|] eqn:Hmb; [ | discriminate ];
         destruct (proj2 IHa ma va eq_refl eq_refl) as [ca [Hca Hsa]];
         destruct (proj2 IHb mb vb eq_refl eq_refl) as [cb [Hcb Hsb]];
         injection Hm as <-; injection Hv as <-;
         simpl; rewrite Hsa, Hsb; subst va vb;
         eexists; split; [ | reflexivity ];
         destruct ca; destruct cb; reflexivity.
Qed.

Corollary tri_sound : forall g e m v,
  tri e = Some m -> seval g e = Some v -> smeval g m = Some (Vi v).
Proof. intros g e; apply (proj1 (tr_sound g e)). Qed.

Corollary trb_sound : forall g e m v,
  trb e = Some m -> seval g e = Some v ->
  exists c, v = b2z c /\ smeval g m = Some (Vb c).
Proof. intros g e; apply (proj2 (tr_sound g e)). Qed.

(** The refusals are real, not vacuous: a comparison has no integer translation
    and a variable has no boolean one — which is [smv.py] rejecting
    [x += (y > 0)] rather than picking a reading. *)
Theorem comparison_is_not_an_integer : forall a b, tri (SBin SLt a b) = None.
Proof. intros a b; simpl; destruct (tri a), (tri b); reflexivity. Qed.

Theorem variable_is_not_a_condition : forall n, trb (SVar n) = None.
Proof. reflexivity. Qed.

Theorem bitwise_is_refused : forall a b, tri (SBin SXorB a b) = None.
Proof. intros a b; simpl; destruct (tri a), (tri b); reflexivity. Qed.
