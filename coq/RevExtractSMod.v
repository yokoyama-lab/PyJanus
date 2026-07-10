(** * RevExtractSMod.v — a verified executable interpreter for the [-m bits] core

    [RevExtSMod.v] gives the signed-modular ([-m bits]) reversible language as a
    relation.  Here we give a *runnable*, fuel-bounded interpreter [run] for it
    and prove it **sound**:

        run fuel Γ s a = Some b  ->  exec Γ s a b

    so its results inherit reversibility from [extsmod_reversible].  Mirrors
    [RevExtractMod.v] exactly, with the [PUpd] canonicity guard now the signed
    window [-half, half) and the update/evaluation wrapping via [norm].
    Extracting [run] to OCaml (as done at [M = 256] / bits = 8 here) is the
    interpreter a `-m`-aware [vjanus] would call. *)

From Stdlib Require Import ZArith Bool Lia Extraction.
Require Import RevCore RevSMod RevExtSMod.
Open Scope Z_scope.

Module ExtSModRun (B : BITS).
  Module N := SModPrim B.
  Module P := ExtSModPrim B.
  Module L := RevLang P.
  Import N P.

  (** The primitive step as a total function returning [option] (guards fail to
      [None]): a decidable refinement of the relation [pstep]. *)
  Definition pstep_fn (p : prim) (a : state) : option state :=
    match p with
    | PUpd l o e =>
        if occurs l e then None
        else if andb (- half <=? a l) (a l <? half)
             then Some (update a l (adenote o (a l) (eval a e)))
             else None
    | PSwap l1 l2 => Some (sw a l1 l2)
    | PEnter n e =>
        if andb (a (LVar n) =? 0) (negb (occurs (LVar n) e))
        then Some (update a (LVar n) (eval a e))
        else None
    | PExit n e =>
        if andb (negb (occurs (LVar n) e))
                (a (LVar n) =? eval (update a (LVar n) 0) e)
        then Some (update a (LVar n) 0)
        else None
    end.

  Lemma pstep_fn_sound : forall p a b, pstep_fn p a = Some b -> pstep p a b.
  Proof.
    destruct p; simpl; intros a b H.
    - (* PUpd *) destruct (occurs l e) eqn:Eo; [ discriminate | ].
      destruct (andb (- half <=? a l) (a l <? half)) eqn:Ec; [ | discriminate ].
      injection H as <-. apply andb_true_iff in Ec as [C1 C2].
      apply Z.leb_le in C1; apply Z.ltb_lt in C2.
      split; [ reflexivity | split; [ split; assumption | reflexivity ] ].
    - (* PSwap *) injection H as <-; reflexivity.
    - (* PEnter *)
      destruct (andb (a (LVar n) =? 0) (negb (occurs (LVar n) e))) eqn:E; [ | discriminate ].
      injection H as <-. apply andb_true_iff in E as [E1 E2].
      apply Z.eqb_eq in E1; apply negb_true_iff in E2.
      split; [ exact E1 | split; [ exact E2 | reflexivity ] ].
    - (* PExit *)
      destruct (andb (negb (occurs (LVar n) e))
                     (a (LVar n) =? eval (update a (LVar n) 0) e)) eqn:E;
        [ | discriminate ].
      injection H as <-. apply andb_true_iff in E as [E1 E2].
      apply negb_true_iff in E1; apply Z.eqb_eq in E2.
      split; [ exact E1 | split; [ reflexivity | exact E2 ] ].
  Qed.

  (** The interpreter (mutually recursive with the loop driver, both on fuel). *)
  Fixpoint run (fuel : nat) (Γ : L.pname -> L.stmt) (s : L.stmt) (a : state)
    {struct fuel} : option state :=
    match fuel with
    | O => None
    | S f =>
      match s with
      | L.Skip => Some a
      | L.Prim p => pstep_fn p a
      | L.Seq s1 s2 =>
          match run f Γ s1 a with Some m => run f Γ s2 m | None => None end
      | L.If g1 s1 s2 g2 =>
          if gtest g1 a
          then match run f Γ s1 a with
               | Some b => if gtest g2 b then Some b else None | None => None end
          else match run f Γ s2 a with
               | Some b => if gtest g2 b then None else Some b | None => None end
      | L.Loop g1 s1 s2 g2 => if gtest g1 a then runloop f Γ g1 s1 s2 g2 a else None
      | L.Call p => run f Γ (Γ p) a
      | L.Uncall p => run f Γ (L.invert (Γ p)) a
      end
    end
  with runloop (fuel : nat) (Γ : L.pname -> L.stmt)
               (g1 : guard) (s1 s2 : L.stmt) (g2 : guard) (a : state)
    {struct fuel} : option state :=
    match fuel with
    | O => None
    | S f =>
      match run f Γ s1 a with
      | None => None
      | Some a1 =>
          if gtest g2 a1 then Some a1
          else match run f Γ s2 a1 with
               | None => None
               | Some a2 => if gtest g1 a2 then None else runloop f Γ g1 s1 s2 g2 a2
               end
      end
    end.

  (** Soundness, by mutual induction on fuel. *)
  Lemma run_sound_mut : forall fuel,
    (forall Γ s a b, run fuel Γ s a = Some b -> L.exec Γ s a b) /\
    (forall Γ g1 s1 s2 g2 a b,
        runloop fuel Γ g1 s1 s2 g2 a = Some b -> L.lp Γ g1 s1 s2 g2 a b).
  Proof.
    induction fuel as [|f IH].
    - split; intros; simpl in *; discriminate.
    - destruct IH as [IHr IHl]. split.
      + intros Γ s a b H;
          destruct s as [ | p | s1 s2 | g1 s1 s2 g2 | g1 s1 s2 g2 | p | p ]; simpl in H.
        * injection H as <-; apply L.E_Skip.
        * apply L.E_Prim; apply pstep_fn_sound; exact H.
        * destruct (run f Γ s1 a) as [m|] eqn:E1; [ | discriminate ].
          eapply L.E_Seq; [ apply IHr; exact E1 | apply IHr; exact H ].
        * destruct (gtest g1 a) eqn:Et.
          -- destruct (run f Γ s1 a) as [b1|] eqn:E1; [ | discriminate ].
             destruct (gtest g2 b1) eqn:Ex; [ | discriminate ].
             injection H as <-. apply L.E_IfT; [ exact Et | apply IHr; exact E1 | exact Ex ].
          -- destruct (run f Γ s2 a) as [b2|] eqn:E2; [ | discriminate ].
             destruct (gtest g2 b2) eqn:Ex; [ discriminate | ].
             injection H as <-. apply L.E_IfF; [ exact Et | apply IHr; exact E2 | exact Ex ].
        * destruct (gtest g1 a) eqn:Et; [ | discriminate ].
          apply L.E_Loop; [ exact Et | apply IHl; exact H ].
        * apply L.E_Call; apply IHr; exact H.
        * apply L.E_Uncall; apply IHr; exact H.
      + intros Γ g1 s1 s2 g2 a b H; simpl in H.
        destruct (run f Γ s1 a) as [a1|] eqn:E1; [ | discriminate ].
        destruct (gtest g2 a1) eqn:Ex.
        * injection H as <-. apply L.L_one; [ apply IHr; exact E1 | exact Ex ].
        * destruct (run f Γ s2 a1) as [a2|] eqn:E2; [ | discriminate ].
          destruct (gtest g1 a2) eqn:Ec; [ discriminate | ].
          eapply L.L_more;
            [ apply IHr; exact E1 | exact Ex | apply IHr; exact E2 | exact Ec | apply IHl; exact H ].
  Qed.

  Theorem run_sound : forall fuel Γ s a b,
    run fuel Γ s a = Some b -> L.exec Γ s a b.
  Proof. intro fuel; apply (proj1 (run_sound_mut fuel)). Qed.

  (** Reversibility of a run: the final store determines the initial store. *)
  Corollary run_injective : forall fuel Γ s a a' b,
    run fuel Γ s a = Some b -> L.exec Γ s a' b -> a = a'.
  Proof.
    intros fuel Γ s a a' b Hr He.
    apply run_sound in Hr. eapply L.exec_injective; [ exact Hr | exact He ].
  Qed.
End ExtSModRun.

(** Instantiate at bits = 8 (matching PyJanus's `-m 8`) and extract to OCaml. *)
Module Run8 := ExtSModRun RevSMod.B8.

Extraction Language OCaml.
Extraction "janus_smod.ml" Run8.run Run8.pstep_fn.
