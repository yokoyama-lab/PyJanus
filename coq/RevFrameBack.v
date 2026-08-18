(** * RevFrameBack.v — the invert-free backward semantics of [RevBack.v],
      ported to the frame-stacked Janus core [RevFrame.v].

    [RevFrame] is the richest kernel in this development (arrays with runtime
    aliasing, by-reference procedures resolved at the caller's depth,
    frame-stacked [local]/[delocal], [from/loop/until], [*=]/[/=] under a
    guard), and — like [RevCore] — it gives [uncall] its meaning by the
    syntactic inverter ([E_Uncall] runs [invert (Γ p)]).  Here we define
    forward and backward judgements [fex]/[bex] over [RevFrame.stmt] that never
    mention [invert] or [ainv]:

      - an atom ([Asn], [AAsn], [Enter], [Exit]) backwards is the *converse*
        of its forward step;
      - [Seq] undoes its second statement first, [If] reads the exit assertion
        first, a loop runs its rounds in reverse;
      - [Call] runs the (substituted) body backwards one frame deeper;
        [Uncall] runs it forwards.

    and prove, for every procedure environment [Γ] and depth [d]:

      - [bex_invert]  : bex d s b a  <->  exec d (invert s) b a
      - [fex_exec]    : fex d s a b  <->  exec d s a b
      - [bex_fex]     : bex d s b a  <->  fex d s a b
      - [uncall_is_backward] :
          exec d (Uncall p args) a b <-> bex (S d) (subst (rargs d args) (Γ p)) a b

    So on the kernel that runs the whole jana2014 corpus (via [vjanus]), the
    syntactic inverter is exactly the semantic reverse. *)

From Stdlib Require Import ZArith List Bool.
Require Import RevFrame.
Import ListNotations.
Open Scope Z_scope.

Section Back.
Variable Γ : nat -> stmt.

Inductive fex : nat -> stmt -> store -> store -> Prop :=
| F_Skip  : forall d s, fex d Skip s s
| F_Asn   : forall d r o e a b, exec Γ d (Asn r o e) a b -> fex d (Asn r o e) a b
| F_AAsn  : forall d r idx o e a b, exec Γ d (AAsn r idx o e) a b -> fex d (AAsn r idx o e) a b
| F_Seq   : forall d s1 s2 a m b, fex d s1 a m -> fex d s2 m b -> fex d (Seq s1 s2) a b
| F_IfT   : forall d e1 s1 s2 e2 a b,
    safe d a e1 = true -> eval d a e1 <> 0 -> fex d s1 a b ->
    safe d b e2 = true -> eval d b e2 <> 0 -> fex d (If e1 s1 s2 e2) a b
| F_IfF   : forall d e1 s1 s2 e2 a b,
    safe d a e1 = true -> eval d a e1 =  0 -> fex d s2 a b ->
    safe d b e2 = true -> eval d b e2 =  0 -> fex d (If e1 s1 s2 e2) a b
| F_Loop  : forall d e1 s1 s2 e2 a b,
    safe d a e1 = true -> eval d a e1 <> 0 -> flp d e1 s1 s2 e2 a b ->
    fex d (Loop e1 s1 s2 e2) a b
| F_Enter : forall d x e a b, exec Γ d (Enter x e) a b -> fex d (Enter x e) a b
| F_Exit  : forall d x e a b, exec Γ d (Exit x e) a b -> fex d (Exit x e) a b
| F_Call  : forall d p args a b,
    fex (S d) (subst (rargs d args) (Γ p)) a b -> fex d (Call p args) a b
| F_Uncall : forall d p args a b,
    bex (S d) (subst (rargs d args) (Γ p)) a b -> fex d (Uncall p args) a b

with flp : nat -> expr -> stmt -> stmt -> expr -> store -> store -> Prop :=
| FL_one  : forall d e1 s1 s2 e2 a b,
    fex d s1 a b -> safe d b e2 = true -> eval d b e2 <> 0 -> flp d e1 s1 s2 e2 a b
| FL_more : forall d e1 s1 s2 e2 a a1 a2 b,
    fex d s1 a a1 -> safe d a1 e2 = true -> eval d a1 e2 = 0 ->
    fex d s2 a1 a2 -> safe d a2 e1 = true -> eval d a2 e1 = 0 ->
    flp d e1 s1 s2 e2 a2 b -> flp d e1 s1 s2 e2 a b

(** [bex d s b a]: from [b], running [s] backwards at depth [d] reaches [a]. *)
with bex : nat -> stmt -> store -> store -> Prop :=
| B_Skip  : forall d s, bex d Skip s s
| B_Asn   : forall d r o e a b, exec Γ d (Asn r o e) a b -> bex d (Asn r o e) b a
| B_AAsn  : forall d r idx o e a b, exec Γ d (AAsn r idx o e) a b -> bex d (AAsn r idx o e) b a
| B_Seq   : forall d s1 s2 b m a, bex d s2 b m -> bex d s1 m a -> bex d (Seq s1 s2) b a
| B_IfT   : forall d e1 s1 s2 e2 b a,
    safe d b e2 = true -> eval d b e2 <> 0 -> bex d s1 b a ->
    safe d a e1 = true -> eval d a e1 <> 0 -> bex d (If e1 s1 s2 e2) b a
| B_IfF   : forall d e1 s1 s2 e2 b a,
    safe d b e2 = true -> eval d b e2 =  0 -> bex d s2 b a ->
    safe d a e1 = true -> eval d a e1 =  0 -> bex d (If e1 s1 s2 e2) b a
| B_Loop  : forall d e1 s1 s2 e2 b a,
    safe d b e2 = true -> eval d b e2 <> 0 -> blp d e1 s1 s2 e2 b a ->
    bex d (Loop e1 s1 s2 e2) b a
| B_Enter : forall d x e a b, exec Γ d (Enter x e) a b -> bex d (Enter x e) b a
| B_Exit  : forall d x e a b, exec Γ d (Exit x e) a b -> bex d (Exit x e) b a
| B_Call  : forall d p args b a,
    bex (S d) (subst (rargs d args) (Γ p)) b a -> bex d (Call p args) b a
| B_Uncall : forall d p args b a,
    fex (S d) (subst (rargs d args) (Γ p)) b a -> bex d (Uncall p args) b a

with blp : nat -> expr -> stmt -> stmt -> expr -> store -> store -> Prop :=
| BL_one  : forall d e1 s1 s2 e2 b a,
    bex d s1 b a -> safe d a e1 = true -> eval d a e1 <> 0 -> blp d e1 s1 s2 e2 b a
| BL_more : forall d e1 s1 s2 e2 b a1 a2 a,
    bex d s1 b a1 -> safe d a1 e1 = true -> eval d a1 e1 = 0 ->
    bex d s2 a1 a2 -> safe d a2 e2 = true -> eval d a2 e2 = 0 ->
    blp d e1 s1 s2 e2 a2 a -> blp d e1 s1 s2 e2 b a.

Scheme fex_mut := Induction for fex Sort Prop
  with flp_mut := Induction for flp Sort Prop
  with bex_mut := Induction for bex Sort Prop
  with blp_mut := Induction for blp Sort Prop.
Combined Scheme fb_mutind from fex_mut, flp_mut, bex_mut, blp_mut.

(** the atoms' backward step is the converse forward step, so it is realised by
    the inverted atom (this is where the local reversibility of atoms enters) *)
Lemma atom_rev : forall d s a b, exec Γ d s a b -> exec Γ d (invert s) b a.
Proof. intros; apply exec_rev; assumption. Qed.

Lemma fb_sound :
  (forall d s a b, fex d s a b -> exec Γ d s a b) /\
  (forall d e1 s1 s2 e2 a b, flp d e1 s1 s2 e2 a b -> lp Γ d e1 s1 s2 e2 a b) /\
  (forall d s b a, bex d s b a -> exec Γ d (invert s) b a) /\
  (forall d e1 s1 s2 e2 b a, blp d e1 s1 s2 e2 b a -> lp Γ d e2 (invert s1) (invert s2) e1 b a).
Proof.
  apply fb_mutind; intros; cbn [invert].
  - apply E_Skip.
  - assumption.
  - assumption.
  - eapply E_Seq; eassumption.
  - apply E_IfT; assumption.
  - apply E_IfF; assumption.
  - apply E_Loop; assumption.
  - assumption.
  - assumption.
  - apply E_Call; assumption.
  - apply E_Uncall; rewrite subst_invert; assumption.
  - apply L_one; assumption.
  - eapply L_more; eassumption.
  - apply E_Skip.
  - apply (atom_rev _ (Asn r o e)); assumption.
  - apply (atom_rev _ (AAsn r idx o e)); assumption.
  - eapply E_Seq; eassumption.
  - apply E_IfT; assumption.
  - apply E_IfF; assumption.
  - apply E_Loop; assumption.
  - apply (atom_rev _ (Enter x e)); assumption.
  - apply (atom_rev _ (Exit x e)); assumption.
  - apply E_Uncall; rewrite subst_invert; assumption.
  - apply E_Call; assumption.
  - apply L_one; assumption.
  - eapply L_more; eassumption.
Qed.

Lemma exec_complete :
  forall d s a b, exec Γ d s a b -> fex d s a b /\ bex d (invert s) a b.
Proof.
  apply (exec_mut Γ
    (fun d s a b _ => fex d s a b /\ bex d (invert s) a b)
    (fun d e1 s1 s2 e2 a b _ => flp d e1 s1 s2 e2 a b /\ blp d e2 (invert s1) (invert s2) e1 a b));
  intros; cbn [invert].
  - split; constructor.
  - split; [ apply F_Asn; apply E_Asn; assumption
           | apply B_Asn; apply (atom_rev _ (Asn r o e)); apply E_Asn; assumption ].
  - split; [ apply F_AAsn; apply E_AAsn; assumption
           | apply B_AAsn; apply (atom_rev _ (AAsn r idx o e)); apply E_AAsn; assumption ].
  - match goal with H1 : _ /\ _, H2 : _ /\ _ |- _ => destruct H1, H2 end.
    split; [ eapply F_Seq | eapply B_Seq ]; eassumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end. split; [ apply F_IfT | apply B_IfT ]; assumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end. split; [ apply F_IfF | apply B_IfF ]; assumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end. split; [ apply F_Loop | apply B_Loop ]; assumption.
  - split; [ apply F_Enter; apply E_Enter; assumption
           | apply B_Exit; apply (atom_rev _ (Enter x e)); apply E_Enter; assumption ].
  - split; [ apply F_Exit; apply E_Exit; assumption
           | apply B_Enter; apply (atom_rev _ (Exit x e)); apply E_Exit; assumption ].
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end.
    split; [ apply F_Call | apply B_Uncall ]; assumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end.
    rewrite <- subst_invert, invert_invol in *.
    split; [ apply F_Uncall | apply B_Call ]; assumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end. split; [ apply FL_one | apply BL_one ]; assumption.
  - match goal with H1 : _ /\ _, H2 : _ /\ _, H3 : _ /\ _ |- _ => destruct H1, H2, H3 end.
    split; [ eapply FL_more | eapply BL_more ]; eassumption.
Qed.

Theorem bex_invert : forall d s b a, bex d s b a <-> exec Γ d (invert s) b a.
Proof.
  intros d s b a; split; intro H.
  - apply fb_sound; assumption.
  - apply exec_complete in H. destruct H as [_ H]. rewrite invert_invol in H. exact H.
Qed.

Theorem fex_exec : forall d s a b, fex d s a b <-> exec Γ d s a b.
Proof.
  intros d s a b; split; intro H.
  - apply fb_sound; assumption.
  - apply exec_complete; assumption.
Qed.

Theorem bex_fex : forall d s a b, bex d s b a <-> fex d s a b.
Proof.
  intros d s a b; split; intro H.
  - apply bex_invert in H. apply fex_exec. apply exec_iff. exact H.
  - apply bex_invert. apply exec_iff. rewrite invert_invol. apply fex_exec. exact H.
Qed.

Theorem uncall_is_backward : forall d p args a b,
  exec Γ d (Uncall p args) a b <-> bex (S d) (subst (rargs d args) (Γ p)) a b.
Proof.
  intros d p args a b; split; intro H.
  - apply bex_invert. rewrite <- subst_invert. inversion H; subst; assumption.
  - apply E_Uncall. rewrite subst_invert. apply bex_invert. assumption.
Qed.

Corollary bex_det : forall d s b a a', bex d s b a -> bex d s b a' -> a = a'.
Proof.
  intros d s b a a' H1 H2. apply bex_invert in H1. apply bex_invert in H2.
  eapply exec_det; eassumption.
Qed.

End Back.
