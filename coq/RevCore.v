(** * RevCore.v — A reusable framework for reversible structured languages

    This development factors the reversibility argument of Janus-style
    reversible imperative languages into a *language-independent* core.

    A concrete reversible language is obtained by supplying (module type
    [REV_PRIM]):

      - a type of [state]s;
      - a type of atomic reversible [prim]itives, with a big-step relation
        [pstep], an inverter [pinv], and three *local* laws:
            [pinv_invol]  pinv (pinv p) = p
            [pstep_det]   pstep p a b -> pstep p a b' -> b = b'
            [pstep_rev]   pstep p a b -> pstep (pinv p) b a
      - a type of [guard]s with a state test [gtest].

    The functor [RevLang] then builds structured control flow — sequencing,
    *assertion-guarded* conditionals and loops, and procedure call/uncall —
    the program inverter [invert], the big-step semantics [exec], and proves
    once and for all:

      - [exec_rev]       : exec s a b  ->  exec (invert s) b a
      - [exec_iff]       : exec s a b  <-> exec (invert s) b a
      - [exec_det]       : forward determinism
      - [exec_injective] : exec s a b -> exec s a' b -> a = a'   (reversibility)

    The point of the abstraction: *the control-flow skeleton of structured
    reversible programming is language-independent — a language is reversible
    exactly when its atoms are locally invertible.*  Instantiations:
    [RevJanus.v] recovers core Janus; [RevExt.v] adds arrays and local/delocal;
    [RevToy.v] a reversible counter over Z; [RevStack.v] a reversible stack
    machine (state = [list Z]); [RevCA.v] a reversible second-order cellular
    automaton (state = a pair of bi-infinite configurations).  The last three
    share no state space or primitives with Janus, yet inherit reversibility
    verbatim from this functor. *)

Module Type REV_PRIM.
  Parameter state : Type.
  Parameter prim  : Type.
  Parameter guard : Type.
  Parameter gtest : guard -> state -> bool.
  Parameter pstep : prim -> state -> state -> Prop.
  Parameter pinv  : prim -> prim.
  Axiom pinv_invol : forall p, pinv (pinv p) = p.
  Axiom pstep_det  : forall p a b b', pstep p a b -> pstep p a b' -> b = b'.
  Axiom pstep_rev  : forall p a b, pstep p a b -> pstep (pinv p) b a.
End REV_PRIM.

Module RevLang (P : REV_PRIM).
Import P.

Definition pname := nat.

(** ** Syntax: structured control flow over abstract primitives and guards. *)
Inductive stmt :=
| Skip
| Prim   (p : prim)
| Seq    (s1 s2 : stmt)
| If     (g1 : guard) (s1 s2 : stmt) (g2 : guard)   (* if g1 then s1 else s2 fi g2 *)
| Loop   (g1 : guard) (s1 s2 : stmt) (g2 : guard)   (* from g1 do s1 loop s2 until g2 *)
| Call   (p : pname)
| Uncall (p : pname).

Fixpoint invert (s : stmt) : stmt :=
  match s with
  | Skip => Skip
  | Prim p => Prim (pinv p)
  | Seq s1 s2 => Seq (invert s2) (invert s1)
  | If g1 s1 s2 g2 => If g2 (invert s1) (invert s2) g1
  | Loop g1 s1 s2 g2 => Loop g2 (invert s1) (invert s2) g1
  | Call p => Uncall p
  | Uncall p => Call p
  end.

Lemma invert_invol : forall s, invert (invert s) = s.
Proof.
  induction s; simpl; try reflexivity.
  - rewrite pinv_invol; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
Qed.

(** ** Big-step semantics, parametric in a procedure environment [Γ]. *)
Section Sem.
Variable Γ : pname -> stmt.

Inductive exec : stmt -> state -> state -> Prop :=
| E_Skip : forall a, exec Skip a a
| E_Prim : forall p a b, pstep p a b -> exec (Prim p) a b
| E_Seq  : forall s1 s2 a m b, exec s1 a m -> exec s2 m b -> exec (Seq s1 s2) a b
| E_IfT  : forall g1 s1 s2 g2 a b,
    gtest g1 a = true  -> exec s1 a b -> gtest g2 b = true  -> exec (If g1 s1 s2 g2) a b
| E_IfF  : forall g1 s1 s2 g2 a b,
    gtest g1 a = false -> exec s2 a b -> gtest g2 b = false -> exec (If g1 s1 s2 g2) a b
| E_Loop : forall g1 s1 s2 g2 a b,
    gtest g1 a = true -> lp g1 s1 s2 g2 a b -> exec (Loop g1 s1 s2 g2) a b
| E_Call : forall p a b, exec (Γ p) a b -> exec (Call p) a b
| E_Uncall : forall p a b, exec (invert (Γ p)) a b -> exec (Uncall p) a b

with lp : guard -> stmt -> stmt -> guard -> state -> state -> Prop :=
| L_one  : forall g1 s1 s2 g2 a b,
    exec s1 a b -> gtest g2 b = true -> lp g1 s1 s2 g2 a b
| L_more : forall g1 s1 s2 g2 a a1 a2 b,
    exec s1 a a1 -> gtest g2 a1 = false ->
    exec s2 a1 a2 -> gtest g1 a2 = false ->
    lp g1 s1 s2 g2 a2 b -> lp g1 s1 s2 g2 a b.

Scheme exec_mut := Induction for exec Sort Prop
  with lp_mut   := Induction for lp   Sort Prop.

Lemma lp_exit_true :
  forall g1 s1 s2 g2 a b, lp g1 s1 s2 g2 a b -> gtest g2 b = true.
Proof. intros until b; intro H; induction H; assumption. Qed.

(** Open iteration: zero or more *continuing* rounds [s1 ; s2]. *)
Inductive opn (g1 : guard) (s1 s2 : stmt) (g2 : guard) : state -> state -> Prop :=
| O_nil  : forall a, opn g1 s1 s2 g2 a a
| O_cons : forall a a1 a2 b,
    exec s1 a a1 -> gtest g2 a1 = false ->
    exec s2 a1 a2 -> gtest g1 a2 = false ->
    opn g1 s1 s2 g2 a2 b -> opn g1 s1 s2 g2 a b.

Lemma opn_snoc :
  forall g1 s1 s2 g2 a m m1 m2,
    opn g1 s1 s2 g2 a m ->
    exec s1 m m1 -> gtest g2 m1 = false ->
    exec s2 m1 m2 -> gtest g1 m2 = false ->
    opn g1 s1 s2 g2 a m2.
Proof.
  intros g1 s1 s2 g2 a m m1 m2 H. revert m1 m2.
  induction H; intros m1 m2 Hs1 He2 Hs2 He1.
  - eapply O_cons; eauto. apply O_nil.
  - eapply O_cons; eauto.
Qed.

Lemma opn_to_lp :
  forall g1 s1 s2 g2 a m b,
    opn g1 s1 s2 g2 a m -> exec s1 m b -> gtest g2 b = true ->
    lp g1 s1 s2 g2 a b.
Proof.
  intros g1 s1 s2 g2 a m b H. induction H; intros Hs1 Hex.
  - apply L_one; assumption.
  - eapply L_more; eauto.
Qed.

(** ** Main theorem: reversal. *)
Theorem exec_rev : forall s a b, exec s a b -> exec (invert s) b a.
Proof.
  intros s a b H.
  induction H using exec_mut
    with (P0 := fun g1 s1 s2 g2 a b (_ : lp g1 s1 s2 g2 a b) =>
      exists q, opn g2 (invert s1) (invert s2) g1 b q /\ exec (invert s1) q a).
  - (* E_Skip *) apply E_Skip.
  - (* E_Prim *) cbn [invert]. apply E_Prim. apply pstep_rev. assumption.
  - (* E_Seq *) cbn [invert]. eapply E_Seq; [ exact IHexec2 | exact IHexec1 ].
  - (* E_IfT *) cbn [invert]. apply E_IfT; assumption.
  - (* E_IfF *) cbn [invert]. apply E_IfF; assumption.
  - (* E_Loop *)
    cbn [invert].
    destruct IHexec as [q [Hopn Hq]].
    apply E_Loop.
    + eapply lp_exit_true; eassumption.
    + eapply opn_to_lp; [ exact Hopn | exact Hq | eassumption ].
  - (* E_Call *) cbn [invert]. apply E_Uncall; assumption.
  - (* E_Uncall *) cbn [invert]. apply E_Call. rewrite invert_invol in IHexec. assumption.
  - (* L_one *) exists b. split; [ apply O_nil | assumption ].
  - (* L_more *)
    match goal with H : exists _, _ |- _ => destruct H as [q [Hopn Hq]] end.
    exists a1. split.
    + eapply opn_snoc; eauto.
    + assumption.
Qed.

Corollary exec_iff : forall s a b, exec s a b <-> exec (invert s) b a.
Proof.
  intros; split; intro H.
  - apply exec_rev; assumption.
  - apply exec_rev in H; rewrite invert_invol in H; assumption.
Qed.

(** ** Forward determinism, and hence backward determinism (reversibility). *)
Theorem exec_det : forall s a b, exec s a b -> forall b', exec s a b' -> b = b'.
Proof.
  intros s a b H.
  induction H using exec_mut
    with (P0 := fun g1 s1 s2 g2 a b (_ : lp g1 s1 s2 g2 a b) =>
      forall b', lp g1 s1 s2 g2 a b' -> b = b').
  - (* Skip *) intros b' Hb'; inversion Hb'; subst; reflexivity.
  - (* Prim *) intros b' Hb'; inversion Hb'; subst. eapply pstep_det; eassumption.
  - (* Seq *) intros b' Hb'; inversion Hb'; subst.
    (* the inverted run's second leg concludes in [b'], distinguishing it. *)
    match goal with
    | He2 : exec s2 ?mid b' |- _ =>
        assert (Em : m = mid) by (apply IHexec1; assumption);
        apply IHexec2; rewrite Em; exact He2
    end.
  - (* IfT *) intros b' Hb'; inversion Hb'; subst.
    + apply IHexec; assumption.
    + congruence.
  - (* IfF *) intros b' Hb'; inversion Hb'; subst.
    + congruence.
    + apply IHexec; assumption.
  - (* Loop *) intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - (* Call *) intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - (* Uncall *) intros b' Hb'; inversion Hb'; subst. apply IHexec; assumption.
  - (* L_one *) intros b' Hb'; inversion Hb'; subst.
    + apply IHexec; assumption.
    + match goal with He : gtest g2 ?aa = false |- _ =>
        match goal with Hx : exec s1 a aa |- _ => apply IHexec in Hx; subst end
      end; congruence.
  - (* L_more *) intros b' Hb'; inversion Hb'; subst.
    + match goal with Hx : exec s1 a b' |- _ => apply IHexec1 in Hx; subst end;
      congruence.
    + match goal with
      | Hi3 : lp g1 s1 s2 g2 ?aa2 b' |- _ =>
        match goal with
        | Hi2 : exec s2 ?aa1 aa2 |- _ =>
          match goal with
          | Hi1 : exec s1 a aa1 |- _ =>
              apply IHexec1 in Hi1; subst;
              apply IHexec2 in Hi2; subst;
              apply IHexec3 in Hi3; exact Hi3
          end
        end
      end.
Qed.

(** Reversibility: a final state determines the initial state — every program
    denotes an injective (partial) function. *)
Corollary exec_injective :
  forall s a a' b, exec s a b -> exec s a' b -> a = a'.
Proof.
  intros s a a' b H1 H2.
  apply exec_rev in H1. apply exec_rev in H2.
  eapply exec_det; eauto.
Qed.

End Sem.
End RevLang.
