(** * RevArrBack.v — the invert-free backward semantics of [RevBack.v],
      ported to the flat-[local] array core [RevArr.v].

    [RevFrameBack.v] already carries the result on the frame-stacked kernel.
    [RevArr] is the other real-language kernel: arrays with runtime aliasing and
    by-reference procedures, but [local]/[delocal] on *flat* slots and, unlike
    [RevFrame], a primitive l-value [Swap].  Swap is the one atom whose inverse
    is itself ([invert (Swap l1 l2) = Swap l1 l2]), so it is the case that says
    the backward judgement is not reading the inverter's syntax: [B_Swap] is the
    converse of [E_Swap], and nothing in the proof may appeal to a difference
    between a statement and its inverse that Swap does not have.

    As in [RevBack.v] we define forward and backward judgements [fex]/[bex] over
    [RevArr.stmt] that never mention [invert] or [ainv]:

      - an atom ([Assign], [Swap], [Enter], [Exit]) backwards is the *converse*
        of its forward step;
      - [Seq] undoes its second statement first, [If] reads the exit assertion
        first, a loop runs its rounds in reverse;
      - [Call] runs the (renamed) body backwards, [Uncall] runs it forwards.

    and prove, for every procedure environment [Γ]:

      - [bex_invert]  : bex s b a  <->  exec Γ (invert s) b a
      - [fex_exec]    : fex s a b  <->  exec Γ s a b
      - [bex_fex]     : bex s b a  <->  fex s a b
      - [uncall_is_backward] :
          exec Γ (Uncall p args) a b  <->  bex (sbody p args) a b

    Together with [RevFrameBack.v] this puts the result on both of the
    development's real-language kernels. *)

From Stdlib Require Import ZArith List Bool.
Require Import RevArr.
Import ListNotations.
Open Scope Z_scope.

Section Back.
Variable Γ : pname -> (list var * stmt).

(** the callee's body with the actuals substituted for the formals — exactly
    what [E_Call] runs *)
Definition sbody (p : pname) (args : list var) : stmt :=
  rename (argsubst (fst (Γ p)) args) (snd (Γ p)).

(** ... and what [E_Uncall] runs is its inverse: renaming commutes with
    inversion, so the kernel's [Uncall] rule needs no separate treatment *)
Lemma uncall_body : forall p args,
  rename (argsubst (fst (Γ p)) args) (invert (snd (Γ p))) = invert (sbody p args).
Proof. intros p args; unfold sbody; rewrite rename_invert; reflexivity. Qed.

Inductive fex : stmt -> store -> store -> Prop :=
| F_Skip   : forall s, fex Skip s s
| F_Assign : forall l o e a b, exec Γ (Assign l o e) a b -> fex (Assign l o e) a b
| F_Swap   : forall l1 l2 a b, exec Γ (Swap l1 l2) a b -> fex (Swap l1 l2) a b
| F_Enter  : forall x e a b, exec Γ (Enter x e) a b -> fex (Enter x e) a b
| F_Exit   : forall x e a b, exec Γ (Exit x e) a b -> fex (Exit x e) a b
| F_Seq    : forall s1 s2 a m b, fex s1 a m -> fex s2 m b -> fex (Seq s1 s2) a b
| F_IfT    : forall e1 s1 s2 e2 a b,
    eval a e1 <> 0 -> fex s1 a b -> eval b e2 <> 0 -> fex (If e1 s1 s2 e2) a b
| F_IfF    : forall e1 s1 s2 e2 a b,
    eval a e1 =  0 -> fex s2 a b -> eval b e2 =  0 -> fex (If e1 s1 s2 e2) a b
| F_Loop   : forall e1 s1 s2 e2 a b,
    eval a e1 <> 0 -> flp e1 s1 s2 e2 a b -> fex (Loop e1 s1 s2 e2) a b
| F_Call   : forall p args a b, fex (sbody p args) a b -> fex (Call p args) a b
| F_Uncall : forall p args a b, bex (sbody p args) a b -> fex (Uncall p args) a b

with flp : expr -> stmt -> stmt -> expr -> store -> store -> Prop :=
| FL_one  : forall e1 s1 s2 e2 a b,
    fex s1 a b -> eval b e2 <> 0 -> flp e1 s1 s2 e2 a b
| FL_more : forall e1 s1 s2 e2 a a1 a2 b,
    fex s1 a a1 -> eval a1 e2 = 0 ->
    fex s2 a1 a2 -> eval a2 e1 = 0 ->
    flp e1 s1 s2 e2 a2 b -> flp e1 s1 s2 e2 a b

(** [bex s b a]: from [b], running [s] backwards reaches [a]. *)
with bex : stmt -> store -> store -> Prop :=
| B_Skip   : forall s, bex Skip s s
| B_Assign : forall l o e a b, exec Γ (Assign l o e) a b -> bex (Assign l o e) b a
| B_Swap   : forall l1 l2 a b, exec Γ (Swap l1 l2) a b -> bex (Swap l1 l2) b a
| B_Enter  : forall x e a b, exec Γ (Enter x e) a b -> bex (Enter x e) b a
| B_Exit   : forall x e a b, exec Γ (Exit x e) a b -> bex (Exit x e) b a
| B_Seq    : forall s1 s2 b m a, bex s2 b m -> bex s1 m a -> bex (Seq s1 s2) b a
| B_IfT    : forall e1 s1 s2 e2 b a,
    eval b e2 <> 0 -> bex s1 b a -> eval a e1 <> 0 -> bex (If e1 s1 s2 e2) b a
| B_IfF    : forall e1 s1 s2 e2 b a,
    eval b e2 =  0 -> bex s2 b a -> eval a e1 =  0 -> bex (If e1 s1 s2 e2) b a
| B_Loop   : forall e1 s1 s2 e2 b a,
    eval b e2 <> 0 -> blp e1 s1 s2 e2 b a -> bex (Loop e1 s1 s2 e2) b a
| B_Call   : forall p args b a, bex (sbody p args) b a -> bex (Call p args) b a
| B_Uncall : forall p args b a, fex (sbody p args) b a -> bex (Uncall p args) b a

with blp : expr -> stmt -> stmt -> expr -> store -> store -> Prop :=
| BL_one  : forall e1 s1 s2 e2 b a,
    bex s1 b a -> eval a e1 <> 0 -> blp e1 s1 s2 e2 b a
| BL_more : forall e1 s1 s2 e2 b a1 a2 a,
    bex s1 b a1 -> eval a1 e1 = 0 ->
    bex s2 a1 a2 -> eval a2 e2 = 0 ->
    blp e1 s1 s2 e2 a2 a -> blp e1 s1 s2 e2 b a.

Scheme fex_mut := Induction for fex Sort Prop
  with flp_mut := Induction for flp Sort Prop
  with bex_mut := Induction for bex Sort Prop
  with blp_mut := Induction for blp Sort Prop.
Combined Scheme fb_mutind from fex_mut, flp_mut, bex_mut, blp_mut.

(** the atoms' backward step is the converse forward step, so it is realised by
    the inverted atom (this is where the local reversibility of atoms enters) *)
Lemma atom_rev : forall s a b, exec Γ s a b -> exec Γ (invert s) b a.
Proof. intros; apply exec_rev; assumption. Qed.

Lemma fb_sound :
  (forall s a b, fex s a b -> exec Γ s a b) /\
  (forall e1 s1 s2 e2 a b, flp e1 s1 s2 e2 a b -> lp Γ e1 s1 s2 e2 a b) /\
  (forall s b a, bex s b a -> exec Γ (invert s) b a) /\
  (forall e1 s1 s2 e2 b a, blp e1 s1 s2 e2 b a -> lp Γ e2 (invert s1) (invert s2) e1 b a).
Proof.
  apply fb_mutind; intros; cbn [invert].
  - apply E_Skip.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - eapply E_Seq; eassumption.
  - apply E_IfT; assumption.
  - apply E_IfF; assumption.
  - apply E_Loop; assumption.
  - apply E_Call; assumption.
  - apply E_Uncall; rewrite uncall_body; assumption.
  - apply L_one; assumption.
  - eapply L_more; eassumption.
  - apply E_Skip.
  - apply (atom_rev (Assign l o e)); assumption.
  - apply (atom_rev (Swap l1 l2)); assumption.
  - apply (atom_rev (Enter x e)); assumption.
  - apply (atom_rev (Exit x e)); assumption.
  - eapply E_Seq; eassumption.
  - apply E_IfT; assumption.
  - apply E_IfF; assumption.
  - apply E_Loop; assumption.
  - apply E_Uncall; rewrite uncall_body; assumption.
  - apply E_Call; assumption.
  - apply L_one; assumption.
  - eapply L_more; eassumption.
Qed.

Lemma exec_complete :
  forall s a b, exec Γ s a b -> fex s a b /\ bex (invert s) a b.
Proof.
  apply (exec_mut Γ
    (fun s a b _ => fex s a b /\ bex (invert s) a b)
    (fun e1 s1 s2 e2 a b _ => flp e1 s1 s2 e2 a b /\ blp e2 (invert s1) (invert s2) e1 a b));
  intros; cbn [invert].
  - split; constructor.
  - split; [ apply F_Assign; apply E_Assign; assumption
           | apply B_Assign; apply (atom_rev (Assign l o e)); apply E_Assign; assumption ].
  - split; [ apply F_Swap; apply E_Swap; assumption
           | apply B_Swap; apply (atom_rev (Swap l1 l2)); apply E_Swap; assumption ].
  - split; [ apply F_Enter; apply E_Enter; assumption
           | apply B_Exit; apply (atom_rev (Enter x e)); apply E_Enter; assumption ].
  - split; [ apply F_Exit; apply E_Exit; assumption
           | apply B_Enter; apply (atom_rev (Exit x e)); apply E_Exit; assumption ].
  - match goal with H1 : _ /\ _, H2 : _ /\ _ |- _ => destruct H1, H2 end.
    split; [ eapply F_Seq | eapply B_Seq ]; eassumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end. split; [ apply F_IfT | apply B_IfT ]; assumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end. split; [ apply F_IfF | apply B_IfF ]; assumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end. split; [ apply F_Loop | apply B_Loop ]; assumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end.
    split; [ apply F_Call | apply B_Uncall ]; assumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end.
    rewrite uncall_body, invert_invol in *.
    split; [ apply F_Uncall | apply B_Call ]; assumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end. split; [ apply FL_one | apply BL_one ]; assumption.
  - match goal with H1 : _ /\ _, H2 : _ /\ _, H3 : _ /\ _ |- _ => destruct H1, H2, H3 end.
    split; [ eapply FL_more | eapply BL_more ]; eassumption.
Qed.

(** the syntactic inverter is exactly the semantic reverse: sound and complete *)
Theorem bex_invert : forall s b a, bex s b a <-> exec Γ (invert s) b a.
Proof.
  intros s b a; split; intro H.
  - apply fb_sound; assumption.
  - apply exec_complete in H. destruct H as [_ H]. rewrite invert_invol in H. exact H.
Qed.

Theorem fex_exec : forall s a b, fex s a b <-> exec Γ s a b.
Proof.
  intros s a b; split; intro H.
  - apply fb_sound; assumption.
  - apply exec_complete; assumption.
Qed.

(** reversibility with no syntax in the statement at all *)
Theorem bex_fex : forall s a b, bex s b a <-> fex s a b.
Proof.
  intros s a b; split; intro H.
  - apply bex_invert in H. apply fex_exec. apply exec_iff. exact H.
  - apply bex_invert. apply exec_iff. rewrite invert_invol. apply fex_exec. exact H.
Qed.

(** Yokoyama–Glück's reading of [uncall]: it runs the body backwards *)
Theorem uncall_is_backward : forall p args a b,
  exec Γ (Uncall p args) a b <-> bex (sbody p args) a b.
Proof.
  intros p args a b; split; intro H.
  - apply bex_invert. rewrite <- uncall_body. inversion H; subst; assumption.
  - apply E_Uncall. rewrite uncall_body. apply bex_invert. assumption.
Qed.

Corollary bex_det : forall s b a a', bex s b a -> bex s b a' -> a = a'.
Proof.
  intros s b a a' H1 H2. apply bex_invert in H1. apply bex_invert in H2.
  eapply exec_det; eassumption.
Qed.

End Back.
