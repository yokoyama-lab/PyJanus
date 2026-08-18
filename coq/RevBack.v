(** * RevBack.v — a semantic backward evaluation, defined without the inverter,
      and the theorem that the syntactic inverter is exactly it.

    [RevCore.RevLang] gives [uncall] its meaning *by* the syntactic inverter:
    [E_Uncall : exec (invert (Γ p)) a b -> exec (Uncall p) a b].  So the
    headline [exec_iff : exec s a b <-> exec (invert s) b a] relates the program
    to its inverse *within one relation that already mentions [invert]*.  This
    file removes that dependency and states the correctness of the inverter
    against an independent notion of "running backwards", the way Paolini,
    Piccolo & Roversi (TYPES 2015) state reversibility between two hand-written
    interpreters (a forward and a backward one) and the way Yokoyama & Glück
    (PEPM 2007) explain [uncall] as running the body backwards.

    We define, mutually, a *forward* judgement [fex] and a *backward* judgement
    [bex] on the same syntax:

      - [bex] never mentions [invert] and never mentions [pinv]: for an atom it
        is the *converse* of [pstep]; for [Seq] it undoes the second statement
        first; for [If] it reads the exit assertion first; for [Loop] it runs
        the rounds in reverse; [Call] runs the body backwards; [Uncall] runs it
        forwards.
      - [fex] is the usual forward semantics, except that [Uncall] is [bex] of
        the body — no syntactic inversion anywhere in the semantics.

    Theorems (all closed, no axioms):

      - [bex_invert]  : bex s b a  <->  exec (invert s) b a
                        — *the syntactic inverter computes the semantic reverse*
                          (sound: <-, complete: ->)
      - [fex_exec]    : fex s a b  <->  exec s a b
                        — the invert-free forward semantics is the reference one
      - [bex_fex]     : bex s b a  <->  fex s a b
                        — semantic reversibility, stated with no syntax at all
      - [uncall_is_backward] : exec (Uncall p) a b <-> bex (Γ p) a b

    Everything is generic in the primitives, so it holds for every instance of
    the framework (core Janus, arrays+local/delocal, the counter, the stack
    machine, the cellular automaton, ...). *)

Require Import RevCore.

Module Back (P : REV_PRIM).
Import P.
Include RevLang P.

Section Sem.
Variable Γ : pname -> stmt.

Inductive fex : stmt -> state -> state -> Prop :=
| F_Skip : forall a, fex Skip a a
| F_Prim : forall p a b, pstep p a b -> fex (Prim p) a b
| F_Seq  : forall s1 s2 a m b, fex s1 a m -> fex s2 m b -> fex (Seq s1 s2) a b
| F_IfT  : forall g1 s1 s2 g2 a b,
    gtest g1 a = true  -> fex s1 a b -> gtest g2 b = true  -> fex (If g1 s1 s2 g2) a b
| F_IfF  : forall g1 s1 s2 g2 a b,
    gtest g1 a = false -> fex s2 a b -> gtest g2 b = false -> fex (If g1 s1 s2 g2) a b
| F_Loop : forall g1 s1 s2 g2 a b,
    gtest g1 a = true -> flp g1 s1 s2 g2 a b -> fex (Loop g1 s1 s2 g2) a b
| F_Call : forall p a b, fex (Γ p) a b -> fex (Call p) a b
| F_Uncall : forall p a b, bex (Γ p) a b -> fex (Uncall p) a b   (* body backwards *)

with flp : guard -> stmt -> stmt -> guard -> state -> state -> Prop :=
| FL_one  : forall g1 s1 s2 g2 a b,
    fex s1 a b -> gtest g2 b = true -> flp g1 s1 s2 g2 a b
| FL_more : forall g1 s1 s2 g2 a a1 a2 b,
    fex s1 a a1 -> gtest g2 a1 = false ->
    fex s2 a1 a2 -> gtest g1 a2 = false ->
    flp g1 s1 s2 g2 a2 b -> flp g1 s1 s2 g2 a b

(** [bex s b a]: starting from [b], running [s] *backwards* reaches [a]. *)
with bex : stmt -> state -> state -> Prop :=
| B_Skip : forall a, bex Skip a a
| B_Prim : forall p a b, pstep p a b -> bex (Prim p) b a          (* converse, no pinv *)
| B_Seq  : forall s1 s2 b m a, bex s2 b m -> bex s1 m a -> bex (Seq s1 s2) b a
| B_IfT  : forall g1 s1 s2 g2 b a,
    gtest g2 b = true  -> bex s1 b a -> gtest g1 a = true  -> bex (If g1 s1 s2 g2) b a
| B_IfF  : forall g1 s1 s2 g2 b a,
    gtest g2 b = false -> bex s2 b a -> gtest g1 a = false -> bex (If g1 s1 s2 g2) b a
| B_Loop : forall g1 s1 s2 g2 b a,
    gtest g2 b = true -> blp g1 s1 s2 g2 b a -> bex (Loop g1 s1 s2 g2) b a
| B_Call : forall p b a, bex (Γ p) b a -> bex (Call p) b a          (* body backwards *)
| B_Uncall : forall p b a, fex (Γ p) b a -> bex (Uncall p) b a      (* body forwards *)

(** backward rounds: undo [s1]; if the *entry* assertion is false, undo [s2] and
    keep going, else stop. *)
with blp : guard -> stmt -> stmt -> guard -> state -> state -> Prop :=
| BL_one  : forall g1 s1 s2 g2 b a,
    bex s1 b a -> gtest g1 a = true -> blp g1 s1 s2 g2 b a
| BL_more : forall g1 s1 s2 g2 b a1 a2 a,
    bex s1 b a1 -> gtest g1 a1 = false ->
    bex s2 a1 a2 -> gtest g2 a2 = false ->
    blp g1 s1 s2 g2 a2 a -> blp g1 s1 s2 g2 b a.

Scheme fex_mut := Induction for fex Sort Prop
  with flp_mut := Induction for flp Sort Prop
  with bex_mut := Induction for bex Sort Prop
  with blp_mut := Induction for blp Sort Prop.
Combined Scheme fb_mutind from fex_mut, flp_mut, bex_mut, blp_mut.

(** ** Soundness: [fex]/[bex] derivations are [exec] derivations. *)
Lemma fb_sound :
  (forall s a b, fex s a b -> exec Γ s a b) /\
  (forall g1 s1 s2 g2 a b, flp g1 s1 s2 g2 a b -> lp Γ g1 s1 s2 g2 a b) /\
  (forall s b a, bex s b a -> exec Γ (invert s) b a) /\
  (forall g1 s1 s2 g2 b a, blp g1 s1 s2 g2 b a -> lp Γ g2 (invert s1) (invert s2) g1 b a).
Proof.
  apply fb_mutind; intros; cbn [invert].
  - apply E_Skip.
  - apply E_Prim; assumption.
  - eapply E_Seq; eassumption.
  - apply E_IfT; assumption.
  - apply E_IfF; assumption.
  - apply E_Loop; assumption.
  - apply E_Call; assumption.
  - apply E_Uncall; assumption.
  - apply L_one; assumption.
  - eapply L_more; eassumption.
  - apply E_Skip.
  - apply E_Prim; apply pstep_rev; assumption.
  - eapply E_Seq; eassumption.
  - apply E_IfT; assumption.
  - apply E_IfF; assumption.
  - apply E_Loop; assumption.
  - apply E_Uncall; assumption.
  - apply E_Call; assumption.
  - apply L_one; assumption.
  - eapply L_more; eassumption.
Qed.

(** ** Completeness: every [exec] derivation is a [fex] derivation, and the
    same derivation read on the inverted program is a [bex] derivation. *)
Lemma exec_complete :
  forall s a b, exec Γ s a b -> fex s a b /\ bex (invert s) a b.
Proof.
  apply (exec_mut Γ
    (fun s a b _ => fex s a b /\ bex (invert s) a b)
    (fun g1 s1 s2 g2 a b _ => flp g1 s1 s2 g2 a b /\ blp g2 (invert s1) (invert s2) g1 a b));
  intros; cbn [invert].
  - split; constructor.
  - split; constructor; [ assumption | apply pstep_rev; assumption ].
  - match goal with H1 : _ /\ _, H2 : _ /\ _ |- _ => destruct H1, H2 end.
    split; [ eapply F_Seq | eapply B_Seq ]; eassumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end. split; [ apply F_IfT | apply B_IfT ]; assumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end. split; [ apply F_IfF | apply B_IfF ]; assumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end. split; [ apply F_Loop | apply B_Loop ]; assumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end. split; [ apply F_Call | apply B_Uncall ]; assumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end. rewrite invert_invol in *.
    split; [ apply F_Uncall | apply B_Call ]; assumption.
  - match goal with H1 : _ /\ _ |- _ => destruct H1 end. split; [ apply FL_one | apply BL_one ]; assumption.
  - match goal with H1 : _ /\ _, H2 : _ /\ _, H3 : _ /\ _ |- _ => destruct H1, H2, H3 end.
    split; [ eapply FL_more | eapply BL_more ]; eassumption.
Qed.

(** ** The theorems. *)

(** The syntactic inverter is exactly the semantic backward evaluation. *)
Theorem bex_invert : forall s b a, bex s b a <-> exec Γ (invert s) b a.
Proof.
  intros s b a; split; intro H.
  - apply fb_sound; assumption.
  - apply exec_complete in H. destruct H as [_ H]. rewrite invert_invol in H. exact H.
Qed.

(** The invert-free forward semantics is the reference semantics. *)
Theorem fex_exec : forall s a b, fex s a b <-> exec Γ s a b.
Proof.
  intros s a b; split; intro H.
  - apply fb_sound; assumption.
  - apply exec_complete; assumption.
Qed.

(** Semantic reversibility, with no syntax in the statement. *)
Theorem bex_fex : forall s a b, bex s b a <-> fex s a b.
Proof.
  intros s a b; split; intro H.
  - apply bex_invert in H. apply fex_exec. apply exec_iff. exact H.
  - apply bex_invert. apply exec_iff. rewrite invert_invol. apply fex_exec. exact H.
Qed.

(** [uncall] really means "the body, backwards". *)
Theorem uncall_is_backward : forall p a b, exec Γ (Uncall p) a b <-> bex (Γ p) a b.
Proof.
  intros p a b; split; intro H.
  - apply bex_invert. inversion H; subst; assumption.
  - apply E_Uncall. apply bex_invert. assumption.
Qed.

(** Backward determinism of the backward semantics itself (a sanity corollary). *)
Corollary bex_det : forall s b a a', bex s b a -> bex s b a' -> a = a'.
Proof.
  intros s b a a' H1 H2. apply bex_invert in H1. apply bex_invert in H2.
  eapply exec_det; eassumption.
Qed.

End Sem.
End Back.

(** ** Instance check on core Janus: [x += 1] run backwards from [x = 1] lands on
    [x = 0], and the inverted program says the same. *)
From Stdlib Require Import ZArith.
Require Import Janus RevJanus.
Open Scope Z_scope.

Module JB := Back JanusPrim.

Example bex_x_plus_one :
  let s := JB.Prim (JanusPrim.PAssign 0%nat AAdd (Cst 1)) in
  let a := (fun _ : var => 0) in
  let b := update a 0%nat 1 in
  JB.bex (fun _ => JB.Skip) s b a.
Proof.
  intros s a b. apply JB.B_Prim. cbn. split; reflexivity.
Qed.
