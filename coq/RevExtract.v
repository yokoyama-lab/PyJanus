(** * RevExtract.v — a verified executable interpreter, extracted to OCaml

    [Janus.exec] is a *relation* (good for proofs, not runnable).  Here we give a
    fuel-bounded *computable* interpreter [run] over the very same language and
    prove it **sound** with respect to [exec]:

        run fuel Γ s a = Some b  ->  exec Γ s a b.

    [run] is then extracted to OCaml ([janus_verified.ml]), yielding a verified
    reference interpreter that can be differentially tested against the PyJanus
    implementation (same `.ja` programs in, compare final stores).  The fuel
    bound is the standard device for a structurally-terminating evaluator of a
    language with unbounded loops; a successful run with *any* fuel is a genuine
    execution. *)

From Stdlib Require Import ZArith Bool Extraction.
Require Import Janus.
Import Janus.
Open Scope Z_scope.

(** A guard is "true" (taken) exactly when its value is nonzero. *)
Definition nz (a : store) (e : expr) : bool := negb (Z.eqb (eval a e) 0).

Lemma nz_true  : forall a e, nz a e = true  -> eval a e <> 0.
Proof. unfold nz; intros a e H; apply negb_true_iff, Z.eqb_neq in H; exact H. Qed.
Lemma nz_false : forall a e, nz a e = false -> eval a e =  0.
Proof. unfold nz; intros a e H; apply negb_false_iff, Z.eqb_eq in H; exact H. Qed.

(** The interpreter (mutually recursive with the loop driver, both on fuel). *)
Fixpoint run (fuel : nat) (Γ : pname -> stmt) (s : stmt) (a : store)
  {struct fuel} : option store :=
  match fuel with
  | O => None
  | S f =>
    match s with
    | Skip => Some a
    | Assign x o e =>
        if occurs x e then None
        else Some (update a x (adenote o (a x) (eval a e)))
    | Swap x y => Some (sw a x y)
    | Seq s1 s2 =>
        match run f Γ s1 a with Some m => run f Γ s2 m | None => None end
    | If e1 s1 s2 e2 =>
        if nz a e1
        then match run f Γ s1 a with
             | Some b => if nz b e2 then Some b else None | None => None end
        else match run f Γ s2 a with
             | Some b => if nz b e2 then None else Some b | None => None end
    | Loop e1 s1 s2 e2 => if nz a e1 then runloop f Γ e1 s1 s2 e2 a else None
    | Call p => run f Γ (Γ p) a
    | Uncall p => run f Γ (invert (Γ p)) a
    end
  end
with runloop (fuel : nat) (Γ : pname -> stmt)
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

(** Soundness, by mutual induction on fuel. *)
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
      * destruct (occurs x e) eqn:Eo; [ discriminate | ].
        injection H as <-; apply E_Assign; exact Eo.
      * injection H as <-; apply E_Swap.
      * destruct (run f Γ s1 a) as [m|] eqn:E1; [ | discriminate ].
        eapply E_Seq; [ apply IHr; exact E1 | apply IHr; exact H ].
      * destruct (nz a e1) eqn:Et.
        -- destruct (run f Γ s1 a) as [b1|] eqn:E1; [ | discriminate ].
           destruct (nz b1 e2) eqn:Ex; [ | discriminate ].
           injection H as <-.
           apply E_IfT; [ apply nz_true; exact Et | apply IHr; exact E1 | apply nz_true; exact Ex ].
        -- destruct (run f Γ s2 a) as [b2|] eqn:E2; [ | discriminate ].
           destruct (nz b2 e2) eqn:Ex; [ discriminate | ].
           injection H as <-.
           apply E_IfF; [ apply nz_false; exact Et | apply IHr; exact E2 | apply nz_false; exact Ex ].
      * destruct (nz a e1) eqn:Et; [ | discriminate ].
        apply E_Loop; [ apply nz_true; exact Et | apply IHl; exact H ].
      * apply E_Call; apply IHr; exact H.
      * apply E_Uncall; apply IHr; exact H.
    + intros Γ e1 s1 s2 e2 a b H; simpl in H.
      destruct (run f Γ s1 a) as [a1|] eqn:E1; [ | discriminate ].
      destruct (nz a1 e2) eqn:Ex.
      * injection H as <-.
        apply L_one; [ apply IHr; exact E1 | apply nz_true; exact Ex ].
      * destruct (run f Γ s2 a1) as [a2|] eqn:E2; [ | discriminate ].
        destruct (nz a2 e1) eqn:Ec; [ discriminate | ].
        eapply L_more;
          [ apply IHr; exact E1 | apply nz_false; exact Ex
          | apply IHr; exact E2 | apply nz_false; exact Ec | apply IHl; exact H ].
Qed.

Theorem run_sound : forall fuel Γ s a b,
  run fuel Γ s a = Some b -> exec Γ s a b.
Proof. intro fuel; apply (proj1 (run_sound_mut fuel)). Qed.

(** Therefore a successful run is reversible: re-running the inverted program
    from the result recovers the input (combining [run_sound] with the
    machine-checked [exec_iff]/[exec_injective]). *)
Corollary run_reversible : forall fuel Γ s a b a',
  run fuel Γ s a = Some b -> exec Γ s a' b -> a = a'.
Proof.
  intros fuel Γ s a b a' Hr He.
  apply run_sound in Hr.
  eapply exec_injective; [ exact Hr | exact He ].
Qed.

(* --------------------------------------------------------------------- *)
(** ** Extraction to OCaml. *)
Extraction Language OCaml.
Extraction "janus_verified.ml" run invert.
