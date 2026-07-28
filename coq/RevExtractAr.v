(** * RevExtractAr.v — verified executable interpreter with arrays

    A fuel-bounded computable interpreter for [RevArr.v]'s language (arrays +
    reference procedures), proved sound vs. [RevArr.exec] and extracted to OCaml
    ([janus_arr.ml]).  The differential harness uses it to cover array-using
    fixtures. *)

From Stdlib Require Import ZArith Bool Extraction.
Require Import RevArr.
Import RevArr.
Open Scope Z_scope.

Definition nz (a : store) (e : expr) : bool := negb (Z.eqb (eval a e) 0).
Lemma nz_true  : forall a e, nz a e = true  -> eval a e <> 0.
Proof. unfold nz; intros a e H; apply negb_true_iff, Z.eqb_neq in H; exact H. Qed.
Lemma nz_false : forall a e, nz a e = false -> eval a e =  0.
Proof. unfold nz; intros a e H; apply negb_false_iff, Z.eqb_eq in H; exact H. Qed.

Fixpoint run (fuel : nat) (Γ : pname -> list var * stmt) (s : stmt) (a : store)
  {struct fuel} : option store :=
  match fuel with
  | O => None
  | S f =>
    match s with
    | Skip => Some a
    | Assign l o e =>
        if wf_assign a l e
        then Some (update a (lloc a l) (adenote o (a (lloc a l)) (eval a e)))
        else None
    | Swap l1 l2 =>
        if wf_swap l1 l2 then Some (sw a (lloc a l1) (lloc a l2)) else None
    | Enter x e =>
        if (Z.eqb (a (LS x)) 0) && (negb (occ (NS x) e))
        then Some (update a (LS x) (eval a e)) else None
    | Exit x e =>
        if (negb (occ (NS x) e)) && (Z.eqb (a (LS x)) (eval (update a (LS x) 0) e))
        then Some (update a (LS x) 0) else None
    | Seq s1 s2 =>
        match run f Γ s1 a with Some m => run f Γ s2 m | None => None end
    | If e1 s1 s2 e2 =>
        if nz a e1
        then match run f Γ s1 a with
             | Some b => if nz b e2 then Some b else None | None => None end
        else match run f Γ s2 a with
             | Some b => if nz b e2 then None else Some b | None => None end
    | Loop e1 s1 s2 e2 => if nz a e1 then runloop f Γ e1 s1 s2 e2 a else None
    | Call p args => run f Γ (rename (argsubst (fst (Γ p)) args) (snd (Γ p))) a
    | Uncall p args => run f Γ (rename (argsubst (fst (Γ p)) args) (invert (snd (Γ p)))) a
    end
  end
with runloop (fuel : nat) (Γ : pname -> list var * stmt)
             (e1 : expr) (s1 s2 : stmt) (e2 : expr) (a : store)
  {struct fuel} : option store :=
  match fuel with
  | O => None
  | S f =>
    match run f Γ s1 a with
    | None => None
    | Some a1 =>
        if nz a1 e2 then Some a1
        else match run f Γ s2 a1 with
             | None => None
             | Some a2 => if nz a2 e1 then None else runloop f Γ e1 s1 s2 e2 a2
             end
    end
  end.

Lemma run_sound_mut : forall fuel,
  (forall Γ s a b, run fuel Γ s a = Some b -> exec Γ s a b) /\
  (forall Γ e1 s1 s2 e2 a b,
      runloop fuel Γ e1 s1 s2 e2 a = Some b -> lp Γ e1 s1 s2 e2 a b).
Proof.
  induction fuel as [|f IH].
  - split; intros; simpl in *; discriminate.
  - destruct IH as [IHr IHl]. split.
    + intros Γ s a b H; destruct s; simpl in H.
      * injection H as <-; apply E_Skip.
      * destruct (wf_assign a l e) eqn:Ewf; [ | discriminate ].
        injection H as <-; apply E_Assign; exact Ewf.
      * destruct (wf_swap l1 l2) eqn:Ew; [ | discriminate ].
        injection H as <-; apply E_Swap; exact Ew.
      * destruct ((Z.eqb (a (LS x)) 0) && (negb (occ (NS x) e))) eqn:E; [ | discriminate ].
        apply andb_true_iff in E; destruct E as [E1 E2]; injection H as <-.
        apply E_Enter; [ apply Z.eqb_eq; exact E1 | apply negb_true_iff; exact E2 ].
      * destruct ((negb (occ (NS x) e)) && (Z.eqb (a (LS x)) (eval (update a (LS x) 0) e))) eqn:E;
          [ | discriminate ].
        apply andb_true_iff in E; destruct E as [E1 E2]; injection H as <-.
        apply E_Exit; [ apply negb_true_iff; exact E1 | apply Z.eqb_eq; exact E2 ].
      * destruct (run f Γ s1 a) as [m|] eqn:E1; [ | discriminate ].
        eapply E_Seq; [ apply IHr; exact E1 | apply IHr; exact H ].
      * destruct (nz a e1) eqn:Et.
        -- destruct (run f Γ s1 a) as [b1|] eqn:E1; [ | discriminate ].
           destruct (nz b1 e2) eqn:Ex; [ | discriminate ]. injection H as <-.
           apply E_IfT; [ apply nz_true; exact Et | apply IHr; exact E1 | apply nz_true; exact Ex ].
        -- destruct (run f Γ s2 a) as [b2|] eqn:E2; [ | discriminate ].
           destruct (nz b2 e2) eqn:Ex; [ discriminate | ]. injection H as <-.
           apply E_IfF; [ apply nz_false; exact Et | apply IHr; exact E2 | apply nz_false; exact Ex ].
      * destruct (nz a e1) eqn:Et; [ | discriminate ].
        apply E_Loop; [ apply nz_true; exact Et | apply IHl; exact H ].
      * apply E_Call; apply IHr; exact H.
      * apply E_Uncall; apply IHr; exact H.
    + intros Γ e1 s1 s2 e2 a b H; simpl in H.
      destruct (run f Γ s1 a) as [a1|] eqn:E1; [ | discriminate ].
      destruct (nz a1 e2) eqn:Ex.
      * injection H as <-. apply L_one; [ apply IHr; exact E1 | apply nz_true; exact Ex ].
      * destruct (run f Γ s2 a1) as [a2|] eqn:E2; [ | discriminate ].
        destruct (nz a2 e1) eqn:Ec; [ discriminate | ].
        eapply L_more;
          [ apply IHr; exact E1 | apply nz_false; exact Ex
          | apply IHr; exact E2 | apply nz_false; exact Ec | apply IHl; exact H ].
Qed.

Theorem run_sound : forall fuel Γ s a b, run fuel Γ s a = Some b -> exec Γ s a b.
Proof. intro fuel; apply (proj1 (run_sound_mut fuel)). Qed.

(* ---------- completeness ----------

   The converse of [run_sound]: the interpreter never *misses* a run either, so
   a [None] at every fuel is a statement about the program.  (Same shape as
   [RevFrame.run_complete]; the array core needs it because [driverar] is the
   second interpreter the differential harness runs.) *)

Lemma run_mono_mut : forall f g, (f <= g)%nat ->
  (forall Γ s a b, run f Γ s a = Some b -> run g Γ s a = Some b) /\
  (forall Γ e1 s1 s2 e2 a b,
     runloop f Γ e1 s1 s2 e2 a = Some b -> runloop g Γ e1 s1 s2 e2 a = Some b).
Proof.
  induction f as [|f IH]; intros g Hle.
  - split; intros; simpl in *; discriminate.
  - destruct g as [|g]; [ exfalso; apply (Nat.nle_succ_0 f Hle) | ].
    destruct (IH g (proj2 (Nat.succ_le_mono f g) Hle)) as [IHr IHl].
    split.
    + intros Γ s a b H; destruct s; simpl in H |- *; try exact H.
      * (* Seq *)
        destruct (run f Γ s1 a) as [m|] eqn:E1; [|discriminate].
        apply IHr in E1; rewrite E1; apply IHr; exact H.
      * (* If *)
        destruct (nz a e1).
        -- destruct (run f Γ s1 a) as [b1|] eqn:E1; [|discriminate].
           apply IHr in E1; rewrite E1; exact H.
        -- destruct (run f Γ s2 a) as [b2|] eqn:E2; [|discriminate].
           apply IHr in E2; rewrite E2; exact H.
      * (* Loop *)
        destruct (nz a e1); [ apply IHl; exact H | discriminate ].
      * (* Call *)   apply IHr; exact H.
      * (* Uncall *) apply IHr; exact H.
    + intros Γ e1 s1 s2 e2 a b H; simpl in H |- *.
      destruct (run f Γ s1 a) as [a1|] eqn:E1; [|discriminate].
      apply IHr in E1; rewrite E1.
      destruct (nz a1 e2); [exact H|].
      destruct (run f Γ s2 a1) as [a2|] eqn:E2; [|discriminate].
      apply IHr in E2; rewrite E2.
      destruct (nz a2 e1); [discriminate|].
      apply IHl; exact H.
Qed.

Lemma run_le : forall f g Γ s a b,
  (f <= g)%nat -> run f Γ s a = Some b -> run g Γ s a = Some b.
Proof. intros f g Γ s a b Hle; apply (proj1 (run_mono_mut f g Hle)). Qed.

Lemma runloop_le : forall f g Γ e1 s1 s2 e2 a b,
  (f <= g)%nat -> runloop f Γ e1 s1 s2 e2 a = Some b -> runloop g Γ e1 s1 s2 e2 a = Some b.
Proof. intros f g Γ e1 s1 s2 e2 a b Hle; apply (proj2 (run_mono_mut f g Hle)). Qed.

Lemma nz_intro  : forall a e, eval a e <> 0 -> nz a e = true.
Proof. unfold nz; intros a e H; apply negb_true_iff, Z.eqb_neq; exact H. Qed.
Lemma nzf_intro : forall a e, eval a e = 0 -> nz a e = false.
Proof. unfold nz; intros a e H; apply negb_false_iff, Z.eqb_eq; exact H. Qed.

Ltac guards := repeat match goal with
  | H : eval ?a ?e <> 0 |- context[nz ?a ?e] => rewrite (nz_intro a e H)
  | H : eval ?a ?e = 0  |- context[nz ?a ?e] => rewrite (nzf_intro a e H)
  | H : ?x = ?y |- context[Z.eqb ?x ?y] => rewrite (proj2 (Z.eqb_eq x y) H)
  | H : occ ?n ?e = false |- context[occ ?n ?e] => rewrite H
  | W : wf_assign ?a ?l ?e = true |- context[wf_assign ?a ?l ?e] => rewrite W
  | W : wf_swap ?l1 ?l2 = true |- context[wf_swap ?l1 ?l2] => rewrite W
  end.

Theorem run_complete : forall Γ s a b,
  exec Γ s a b -> exists f, run f Γ s a = Some b.
Proof.
  intros Γ s a b H.
  induction H using exec_mut with
    (P0 := fun e1 s1 s2 e2 a b (_ : lp Γ e1 s1 s2 e2 a b) =>
      exists f, runloop f Γ e1 s1 s2 e2 a = Some b).
  - (* E_Skip *)   exists 1%nat; reflexivity.
  - (* E_Assign *) exists 1%nat; simpl; guards; reflexivity.
  - (* E_Swap *)   exists 1%nat; simpl; guards; reflexivity.
  - (* E_Enter *)  exists 1%nat; simpl; guards; reflexivity.
  - (* E_Exit *)   exists 1%nat; simpl; guards; reflexivity.
  - (* E_Seq *)
    destruct IHexec1 as [f1 H1]; destruct IHexec2 as [f2 H2].
    exists (S (Nat.max f1 f2)); simpl.
    rewrite (run_le f1 (Nat.max f1 f2) _ _ _ _ (Nat.le_max_l _ _) H1).
    apply (run_le f2 (Nat.max f1 f2) _ _ _ _ (Nat.le_max_r _ _) H2).
  - (* E_IfT *)
    destruct IHexec as [f1 H1]; exists (S f1); simpl; guards; rewrite H1; guards; reflexivity.
  - (* E_IfF *)
    destruct IHexec as [f1 H1]; exists (S f1); simpl; guards; rewrite H1; guards; reflexivity.
  - (* E_Loop *)
    destruct IHexec as [f1 H1]; exists (S f1); simpl; guards; exact H1.
  - (* E_Call *)   destruct IHexec as [f1 H1]; exists (S f1); simpl; exact H1.
  - (* E_Uncall *) destruct IHexec as [f1 H1]; exists (S f1); simpl; exact H1.
  - (* L_one *)
    destruct IHexec as [f1 H1]; exists (S f1); simpl; rewrite H1; guards; reflexivity.
  - (* L_more *)
    destruct IHexec1 as [f1 H1]; destruct IHexec2 as [f2 H2]; destruct IHexec3 as [f3 H3].
    set (m := Nat.max f1 (Nat.max f2 f3)).
    exists (S m); simpl.
    rewrite (run_le f1 m _ _ _ _ (Nat.le_max_l _ _) H1); guards.
    rewrite (run_le f2 m _ _ _ _
              (Nat.le_trans _ _ _ (Nat.le_max_l f2 f3) (Nat.le_max_r f1 _)) H2); guards.
    apply (runloop_le f3 m _ _ _ _ _ _ _
             (Nat.le_trans _ _ _ (Nat.le_max_r f2 f3) (Nat.le_max_r f1 _)) H3).
Qed.

Corollary run_none_no_exec : forall Γ s a,
  (forall f, run f Γ s a = None) -> forall b, ~ exec Γ s a b.
Proof.
  intros Γ s a Hnone b Hex.
  destruct (run_complete Γ s a b Hex) as [f Hf].
  rewrite Hnone in Hf; discriminate.
Qed.

Extraction Language OCaml.
Extraction "janus_arr.ml" run invert.
