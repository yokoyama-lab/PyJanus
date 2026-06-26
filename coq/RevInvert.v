(** * RevInvert.v — the program inverter is correct for the *executable* interpreter

    [Janus.exec_iff] already states that the syntactic inverter [invert] is the
    semantic inverse at the level of the big-step *relation* [exec].  Here we
    lift that to the *runnable*, fuel-bounded interpreter [run] (the one extracted
    to OCaml in [RevExtract.v] and differentially tested against PyJanus):

        run_invert_iff :
          (exists f, run f Γ s        a = Some b)
            <->
          (exists f, run f Γ (invert s) b = Some a).

    In words: whenever the verified interpreter computes [b] from [a] by running
    [s], it computes [a] back from [b] by running [invert s] — the *extracted*
    interpreter genuinely inverts.  Two ingredients are new here and were not
    needed for soundness:

      - [run_le]      : fuel monotonicity (a successful run survives more fuel);
      - [run_complete]: completeness of [run] w.r.t. [exec] (every derivable
                        [exec] is realised by some finite fuel).

    Together with [run_sound] (from [RevExtract.v]) and the machine-checked
    [exec_rev]/[invert_invol] (from [Janus.v]), they give the executable inverse
    characterization above. *)

From Stdlib Require Import ZArith Bool Lia.
Require Import Janus RevExtract.
Import Janus.
Open Scope Z_scope.

(** Re-introduction lemmas for the guard test (converse of [nz_true]/[nz_false]). *)
Lemma nz_intro  : forall a e, eval a e <> 0 -> nz a e = true.
Proof. intros a e H; unfold nz; apply negb_true_iff, Z.eqb_neq; exact H. Qed.
Lemma nzf_intro : forall a e, eval a e =  0 -> nz a e = false.
Proof. intros a e H; unfold nz; apply negb_false_iff, Z.eqb_eq; exact H. Qed.

(** Keep [nz] folded so [simpl] exposes [run]'s control structure without
    unfolding the guard test. *)
Opaque nz.

(* ********************************************************************* *)
(** ** Fuel monotonicity. *)

Lemma run_mono_mut : forall f g, (f <= g)%nat ->
  (forall Γ s a b, run f Γ s a = Some b -> run g Γ s a = Some b) /\
  (forall Γ e1 s1 s2 e2 a b,
      runloop f Γ e1 s1 s2 e2 a = Some b -> runloop g Γ e1 s1 s2 e2 a = Some b).
Proof.
  induction f as [|f' IHf]; intros g Hle.
  - split.
    + intros Γ s a b H; simpl in H; discriminate.
    + intros Γ e1 s1 s2 e2 a b H; simpl in H; discriminate.
  - destruct g as [|g']; [lia|].
    assert (Hle' : (f' <= g')%nat) by lia.
    destruct (IHf g' Hle') as [IHr IHl].
    split.
    + intros Γ s a b H.
      destruct s as [ | x o e | x y | s1 s2 | e1 s1 s2 e2 | e1 s1 s2 e2 | p | p ];
        simpl in H |- *.
      * (* Skip *)   exact H.
      * (* Assign *) exact H.
      * (* Swap *)   exact H.
      * (* Seq *)
        destruct (run f' Γ s1 a) as [m|] eqn:E1; [|discriminate].
        apply IHr in E1; rewrite E1; apply IHr; exact H.
      * (* If *)
        destruct (nz a e1) eqn:Et.
        -- destruct (run f' Γ s1 a) as [b1|] eqn:E1; [|discriminate].
           apply IHr in E1; rewrite E1; exact H.
        -- destruct (run f' Γ s2 a) as [b2|] eqn:E2; [|discriminate].
           apply IHr in E2; rewrite E2; exact H.
      * (* Loop *)
        destruct (nz a e1) eqn:Et; [|discriminate].
        apply IHl; exact H.
      * (* Call *)   apply IHr; exact H.
      * (* Uncall *) apply IHr; exact H.
    + intros Γ e1 s1 s2 e2 a b H; simpl in H |- *.
      destruct (run f' Γ s1 a) as [a1|] eqn:E1; [|discriminate].
      apply IHr in E1; rewrite E1.
      destruct (nz a1 e2) eqn:Ex; [exact H|].
      destruct (run f' Γ s2 a1) as [a2|] eqn:E2; [|discriminate].
      apply IHr in E2; rewrite E2.
      destruct (nz a2 e1) eqn:Ec; [discriminate|].
      apply IHl; exact H.
Qed.

Lemma run_le : forall f g Γ s a b,
  (f <= g)%nat -> run f Γ s a = Some b -> run g Γ s a = Some b.
Proof. intros f g Γ s a b Hle; apply (proj1 (run_mono_mut f g Hle)). Qed.

Lemma runloop_le : forall f g Γ e1 s1 s2 e2 a b,
  (f <= g)%nat ->
  runloop f Γ e1 s1 s2 e2 a = Some b -> runloop g Γ e1 s1 s2 e2 a = Some b.
Proof. intros f g Γ e1 s1 s2 e2 a b Hle; apply (proj2 (run_mono_mut f g Hle)). Qed.

(* ********************************************************************* *)
(** ** Completeness: every [exec] derivation is realised by some fuel. *)

Theorem run_complete : forall Γ s a b,
  exec Γ s a b -> exists f, run f Γ s a = Some b.
Proof.
  intros Γ s a b H.
  induction H using exec_mut with
    (P0 := fun e1 s1 s2 e2 a b (_ : lp Γ e1 s1 s2 e2 a b) =>
      exists f, runloop f Γ e1 s1 s2 e2 a = Some b).
  - (* E_Skip *) exists 1%nat; reflexivity.
  - (* E_Assign *)
    exists 1%nat; simpl.
    match goal with Ho : occurs _ _ = false |- _ => rewrite Ho end; reflexivity.
  - (* E_Swap *) exists 1%nat; reflexivity.
  - (* E_Seq *)
    destruct IHexec1 as [f1 H1]; destruct IHexec2 as [f2 H2].
    exists (S (Nat.max f1 f2)); simpl.
    rewrite (run_le f1 (Nat.max f1 f2) _ _ _ _ ltac:(lia) H1).
    apply (run_le f2 (Nat.max f1 f2) _ _ _ _ ltac:(lia) H2).
  - (* E_IfT *)
    destruct IHexec as [f1 H1]; exists (S f1); simpl.
    assert (Q1 : nz a e1 = true) by (apply nz_intro; assumption).
    assert (Q2 : nz b e2 = true) by (apply nz_intro; assumption).
    rewrite Q1, H1, Q2; reflexivity.
  - (* E_IfF *)
    destruct IHexec as [f1 H1]; exists (S f1); simpl.
    assert (Q1 : nz a e1 = false) by (apply nzf_intro; assumption).
    assert (Q2 : nz b e2 = false) by (apply nzf_intro; assumption).
    rewrite Q1, H1, Q2; reflexivity.
  - (* E_Loop *)
    destruct IHexec as [f1 H1]; exists (S f1); simpl.
    assert (Q1 : nz a e1 = true) by (apply nz_intro; assumption).
    rewrite Q1; exact H1.
  - (* E_Call *)
    destruct IHexec as [f1 H1]; exists (S f1); simpl; exact H1.
  - (* E_Uncall *)
    destruct IHexec as [f1 H1]; exists (S f1); simpl; exact H1.
  - (* L_one *)
    destruct IHexec as [f1 H1]; exists (S f1); simpl.
    rewrite H1.
    assert (Q : nz b e2 = true) by (apply nz_intro; assumption).
    rewrite Q; reflexivity.
  - (* L_more *)
    destruct IHexec1 as [f1 H1]; destruct IHexec2 as [f2 H2];
      destruct IHexec3 as [f3 H3].
    exists (S (Nat.max f1 (Nat.max f2 f3))); simpl.
    rewrite (run_le f1 (Nat.max f1 (Nat.max f2 f3)) _ _ _ _ ltac:(lia) H1).
    assert (Q1 : nz a1 e2 = false) by (apply nzf_intro; assumption).
    rewrite Q1.
    rewrite (run_le f2 (Nat.max f1 (Nat.max f2 f3)) _ _ _ _ ltac:(lia) H2).
    assert (Q2 : nz a2 e1 = false) by (apply nzf_intro; assumption).
    rewrite Q2.
    apply (runloop_le f3 (Nat.max f1 (Nat.max f2 f3)) _ _ _ _ _ _ _ ltac:(lia) H3).
Qed.

(* ********************************************************************* *)
(** ** Executable inverse correctness. *)

(** If the verified interpreter computes [b] from [a], then on the inverted
    program it computes [a] back from [b] (with possibly more fuel). *)
Corollary run_invert : forall fuel Γ s a b,
  run fuel Γ s a = Some b -> exists fuel', run fuel' Γ (invert s) b = Some a.
Proof.
  intros fuel Γ s a b H.
  apply run_sound in H.       (* exec Γ s a b *)
  apply exec_rev in H.        (* exec Γ (invert s) b a *)
  apply run_complete; exact H.
Qed.

(** The headline: the executable interpreter inverts, iff. *)
Theorem run_invert_iff : forall Γ s a b,
  (exists f, run f Γ s a = Some b) <-> (exists f, run f Γ (invert s) b = Some a).
Proof.
  intros Γ s a b; split; intros [f H].
  - apply run_invert in H; exact H.
  - apply run_invert in H.           (* exists f', run f' Γ (invert (invert s)) a = Some b *)
    rewrite invert_invol in H; exact H.
Qed.
