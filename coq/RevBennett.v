(** * RevBennett.v — Bennett's reversibilization (compute--copy--uncompute)

    Bennett's theorem (1973): \emph{any} deterministic computation can be carried
    out reversibly with no net garbage, by the three-step trick

        compute $\;\to\;$ copy out the result $\;\to\;$ uncompute,

    so that the temporary garbage produced while computing is erased
    \emph{reversibly} (run backwards) rather than thrown away.  We mechanize this
    inside the dagger category of partial injections of [RevCat.v].

    Model.  A ``reversible implementation of [f] with garbage'' is an
    \emph{injective} map $r : A\times Z \to B\times G$ on input$\times$ancilla,
    whose first component is the result ($f\,a\,z = \pi_1(r(a,z))$) and whose
    second component $G$ is garbage.  Wrapping it around a fresh result register
    $Y$ (a set with a cancellative ``accumulate'' operation $\oplus$),

        \coq{Bennett} \;=\; \coq{Compute} \,;\, \coq{Copy} \,;\, \coq{Uncompute},
        \qquad \coq{Uncompute} = \coq{Compute}^\dagger,

    we prove (i) \coq{bennett\_correct}: the whole map is the graph of
    $(a,z,y)\mapsto(a,z,\;y\oplus f\,a\,z)$ — the input is restored and the
    garbage $G$ has \emph{vanished} from the output; and (ii) \coq{bennett\_pinj}:
    it is a partial injection (reversible).  A corollary instantiates $r$ with the
    input-preserving implementation $a\mapsto(f\,a,a)$, giving a reversible
    garbage-free computation of an \emph{arbitrary} $f$.  Axiom-free. *)

From Stdlib Require Import Bool.
Require Import RevCore RevAlgebra RevCat.

(** [heq] respects [pinj]. *)
Lemma pinj_heq : forall A B (R S : hrel A B), heq R S -> pinj R -> pinj S.
Proof.
  intros A B R S Hrs [d c]; split.
  - intros a b b' Hb Hb'; eapply d; apply Hrs; eassumption.
  - intros a b b' Hb Hb'; unfold convH in *; eapply c; unfold convH; apply Hrs; eassumption.
Qed.

(** Graph of a function, and its basic categorical facts. *)
Definition gr {A B : Type} (h : A -> B) : hrel A B := fun a b => b = h a.

Lemma gr_inj_pinj : forall A B (h : A -> B),
  (forall x y, h x = h y -> x = y) -> pinj (gr h).
Proof.
  intros A B h Hinj; split.
  - intros a b b' Hb Hb'; unfold gr in *; congruence.
  - intros a b b' Hb Hb'; unfold convH, gr in *; apply Hinj; congruence.
Qed.

Lemma compH_gr : forall A B C (h : A -> B) (k : B -> C),
  heq (compH (gr h) (gr k)) (gr (fun a => k (h a))).
Proof.
  intros A B C h k a c; unfold compH, gr; split.
  - intros [b [Hb Hc]]; subst b c; reflexivity.
  - intro Hc; exists (h a); split; [ reflexivity | exact Hc ].
Qed.

(* ===================================================================== *)
(** ** The Bennett construction. *)
Section Bennett.
Context {A Z B G Y : Type}.

(** The reversible (injective) implementation of [f] with garbage [G]. *)
Variable r : A * Z -> B * G.
Hypothesis r_inj : forall p q, r p = r q -> p = q.

(** Accumulating the result into the output register, cancellatively. *)
Variable op : Y -> B -> Y.
Hypothesis op_cancel : forall b y y', op y b = op y' b -> y = y'.

(** The computed result. *)
Definition fres (a : A) (z : Z) : B := fst (r (a, z)).

(** Three steps as graphs of functions over the triple [A*Z*Y] / [B*G*Y]. *)
Definition cf (s : A * Z * Y) : B * G * Y :=
  let '(a, z, y) := s in (fst (r (a, z)), snd (r (a, z)), y).
Definition cp (s : B * G * Y) : B * G * Y :=
  let '(b, g, y) := s in (b, g, op y b).
Definition tf (s : A * Z * Y) : A * Z * Y :=
  let '(a, z, y) := s in (a, z, op y (fres a z)).

Definition Compute   : hrel (A * Z * Y) (B * G * Y) := gr cf.
Definition Copy      : hrel (B * G * Y) (B * G * Y) := gr cp.
Definition Uncompute : hrel (B * G * Y) (A * Z * Y) := convH Compute.

Definition Bennett : hrel (A * Z * Y) (A * Z * Y) :=
  compH (compH Compute Copy) Uncompute.

(** *** Correctness: the wrapped map restores the input and erases the garbage. *)
Theorem bennett_correct : heq Bennett (gr tf).
Proof.
  intros s t; unfold Bennett, Compute, Copy, Uncompute, compH, convH, gr.
  split.
  - intros [m [[w [Hw Hm]] Ht]]; subst w m.
    (* [Ht : cf t = cp (cf s)]; conclude [t = tf s]. *)
    destruct s as [[a z] y]; destruct t as [[a' z'] y'].
    unfold cf, cp, tf in *.
    injection Ht; intros Hy Hg Hb.
    assert (Hr : r (a', z') = r (a, z))
      by (apply injective_projections; [ symmetry; exact Hb | symmetry; exact Hg ]).
    apply r_inj in Hr; injection Hr; intros Hz Ha; subst a' z'.
    rewrite <- Hy; reflexivity.
  - intro Ht; subst t.
    exists (cp (cf s)); split.
    + exists (cf s); split; reflexivity.
    + destruct s as [[a z] y]; unfold cf, cp, tf; reflexivity.
Qed.

(** *** Reversibility: the whole construction is a partial injection. *)
Theorem bennett_pinj : pinj Bennett.
Proof.
  apply (pinj_heq _ _ (gr tf) Bennett (heq_sym _ _ _ _ bennett_correct)).
  apply gr_inj_pinj.
  intros [[a z] y] [[a' z'] y'] Heq; unfold tf in Heq.
  injection Heq; intros Hy Hz Ha; subst a' z'.
  apply op_cancel in Hy; subst y'; reflexivity.
Qed.

(** Garbage-free reading: the output's input slots are unchanged and the result
    is accumulated; the garbage component [G] does not occur in the output. *)
Corollary bennett_garbage_free : forall a z y,
  tf (a, z, y) = (a, z, op y (fres a z)).
Proof. intros a z y; reflexivity. Qed.

End Bennett.

(* ===================================================================== *)
(** ** Universal corollary: every function has a reversible garbage-free form.

    Take the input-preserving implementation [r a = (f a, a)] (injective, the
    minimal Bennett garbage), over ancilla [Z = unit] and garbage [G = A]. *)
Section Universal.
Context {A B Y : Type}.
Variable f : A -> B.
Variable op : Y -> B -> Y.
Hypothesis op_cancel : forall b y y', op y b = op y' b -> y = y'.

Definition r_keep (p : A * unit) : B * A := (f (fst p), fst p).

Lemma r_keep_inj : forall p q, r_keep p = r_keep q -> p = q.
Proof.
  intros [a []] [a' []] H; unfold r_keep in H; simpl in H.
  injection H; intros Ha _; subst a'; reflexivity.
Qed.

(** [f] is realized reversibly with no garbage: the construction is a partial
    injection whose action accumulates exactly [f a] into the output register. *)
Theorem bennett_universal_pinj :
  pinj (@Bennett A unit B A Y r_keep op).
Proof. apply bennett_pinj; [ exact r_keep_inj | exact op_cancel ]. Qed.

Theorem bennett_universal_correct : forall a y,
  @tf A unit B A Y r_keep op (a, tt, y) = (a, tt, op y (f a)).
Proof. intros a y; unfold tf, fres, r_keep; reflexivity. Qed.

End Universal.
