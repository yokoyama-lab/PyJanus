(** * RevPipeline.v
    パイプラインの PoC（最小例）:
      「非可逆で単射と定理証明された spec」
         ⟹ 「クリーン可逆で（意味論上）正しいと証明された Janus プログラム」

    入力 = 非可逆な spec [f] と，その単射性の証明（左逆元 [g] と [g ∘ f = id]）。
    出力 = Janus 文 [R]（実行可能）と，意味論 [exec] 上での正しさ
           [exec Γ R (enc p) (enc (f p))]。
    可逆性は枠組み（[Janus.exec_iff]）から無償で従う。

    最小例: 2 変数 delta  f(a,b) = (a, b-a)。Janus では一文 [b -= a]。 *)

Require Import ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Janus.
Open Scope Z_scope.

(* ===== 入力: 非可逆で「単射と証明された」プログラム ===== *)

Definition f (p : Z * Z) : Z * Z := (fst p, snd p - fst p).
Definition g (p : Z * Z) : Z * Z := (fst p, snd p + fst p).

Lemma f_injective : forall p, g (f p) = p.
Proof. intros [a b]; unfold f, g; simpl; f_equal; ring. Qed.

(* ===== 符号化: var 0 ↦ a, var 1 ↦ b ===== *)

Definition enc (p : Z * Z) : store :=
  fun x => if Nat.eqb x 0%nat then fst p
           else if Nat.eqb x 1%nat then snd p else 0%Z.

(* ===== 出力: クリーン可逆 Janus プログラム  R := (b -= a) ===== *)

Definition R : stmt := Assign 1%nat ASub (Var 0%nat).

(* ===== 正しさ（新規貢献）: R は enc p を enc (f p) に移す ===== *)

Theorem R_computes_f :
  forall (Γ : pname -> stmt) (p : Z * Z),
    exec Γ R (enc p) (enc (f p)).
Proof.
  intros Γ [a b].
  assert (Hs :
    update (enc (a, b)) 1%nat (adenote ASub (enc (a, b) 1%nat) (eval (enc (a, b)) (Var 0%nat)))
    = enc (f (a, b))).
  { apply functional_extensionality; intro x.
    unfold enc, update, f, eval, adenote; simpl.
    destruct x as [|[|x]]; simpl; try reflexivity; ring. }
  unfold R. rewrite <- Hs. apply E_Assign. reflexivity.
Qed.

(* ===== 可逆性は枠組みから無償: invert R = (b += a) が逆を計算 ===== *)

Theorem R_reversible :
  forall (Γ : pname -> stmt) (p : Z * Z),
    exec Γ (invert R) (enc (f p)) (enc p).
Proof.
  intros Γ p. apply (proj1 (exec_iff Γ R (enc p) (enc (f p)))). apply R_computes_f.
Qed.
