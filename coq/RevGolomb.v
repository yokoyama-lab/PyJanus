(** * RevGolomb.v — divmod consume コーダ（Golomb/Rice の核）

    追加した [ODiv]/[OMod]（[Janus.v]）を実際に使う初のクリーン可逆コーダ。

    抽象スペック（非可逆・単射）:  n ↦ (n / d, n mod d)   （d>0）
      左逆元 (q,r) ↦ d*q + r が単射性（= divmod 復元）を与える。

    クリーン可逆 Janus 実装（consume パターン, 3 レジスタ n=0,q=1,r=2）:
        q += n / d ;  r += n mod d ;  n -= d*q + r
    入口 (n,0,0) を出口 (0, n/d, n mod d) へ移す。入力 n を 0 へ消費し
    （garbage-free）、商と余りに全情報を移すので可逆。可逆性は [exec_iff] から無償。

    注意: 除算/剰余は式 [Bin ODiv/OMod ...]（read-only）の中だけで使い、
    代入演算子 [aop] は AAdd/ASub のまま。だから可逆性は保たれる
    （[invert] は式に触れない）。 *)

From Stdlib Require Import ZArith Lia FunctionalExtensionality.
Require Import Janus.
Open Scope Z_scope.

Section Golomb.
Variable Γ : pname -> stmt.   (* 手続き環境（本例では未使用） *)
Variable d : Z.               (* 固定の除数 *)

(* ===== 抽象スペック（単射）: divmod とその左逆元 ===== *)

Definition f_gr (n : Z) : Z * Z := (n / d, n mod d).      (* 非可逆 encode *)
Definition g_gr (p : Z * Z) : Z := d * fst p + snd p.     (* 左逆元 decode *)

Lemma f_gr_injective : forall n, d > 0 -> g_gr (f_gr n) = n.
Proof.
  intros n Hd. unfold f_gr, g_gr; simpl.
  assert (Hdm : n = d * (n / d) + n mod d) by (apply Z.div_mod; lia). lia.
Qed.

(* ===== 符号化: var 0 ↦ n, 1 ↦ q, 2 ↦ r ===== *)

Definition enc (n q r : Z) : store :=
  fun x => if Nat.eqb x 0 then n
           else if Nat.eqb x 1 then q
           else if Nat.eqb x 2 then r else 0.

(* 単一更新の書換補題（具体 var なので nested destruct で computational）。 *)
Lemma upd0 : forall n q r v, update (enc n q r) 0%nat v = enc v q r.
Proof. intros; apply functional_extensionality; intros [|[|[|y]]]; reflexivity. Qed.
Lemma upd1 : forall n q r v, update (enc n q r) 1%nat v = enc n v r.
Proof. intros; apply functional_extensionality; intros [|[|[|y]]]; reflexivity. Qed.
Lemma upd2 : forall n q r v, update (enc n q r) 2%nat v = enc n q v.
Proof. intros; apply functional_extensionality; intros [|[|[|y]]]; reflexivity. Qed.

(* ===== クリーン可逆 Janus プログラム ===== *)

Definition sA : stmt := Assign 1%nat AAdd (Bin ODiv (Var 0%nat) (Cst d)).
Definition sB : stmt := Assign 2%nat AAdd (Bin OMod (Var 0%nat) (Cst d)).
Definition sC : stmt :=
  Assign 0%nat ASub (Bin OAdd (Bin OMul (Cst d) (Var 1%nat)) (Var 2%nat)).
Definition Rgolomb : stmt := Seq sA (Seq sB sC).

(* 各代入を「明示的 enc を入出力に持つ」ステップへ分解（coder 入口 q=r=0 仕様）。 *)
Lemma stepA0 : forall n,
  exec Γ sA (enc n 0 0) (enc n (n / d) 0).
Proof.
  intros n. unfold sA.
  assert (H : enc n (n / d) 0
    = update (enc n 0 0) 1%nat
        (adenote AAdd (enc n 0 0 1%nat) (eval (enc n 0 0) (Bin ODiv (Var 0%nat) (Cst d))))).
  { change (enc n 0 0 1%nat) with 0.
    change (eval (enc n 0 0) (Bin ODiv (Var 0%nat) (Cst d))) with (n / d).
    cbn [adenote]. rewrite upd1. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

Lemma stepB0 : forall n,
  exec Γ sB (enc n (n / d) 0) (enc n (n / d) (n mod d)).
Proof.
  intros n. unfold sB.
  assert (H : enc n (n / d) (n mod d)
    = update (enc n (n / d) 0) 2%nat
        (adenote AAdd (enc n (n / d) 0 2%nat) (eval (enc n (n / d) 0) (Bin OMod (Var 0%nat) (Cst d))))).
  { change (enc n (n / d) 0 2%nat) with 0.
    change (eval (enc n (n / d) 0) (Bin OMod (Var 0%nat) (Cst d))) with (n mod d).
    cbn [adenote]. rewrite upd2. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

Lemma stepC0 : forall n,
  d > 0 ->
  exec Γ sC (enc n (n / d) (n mod d)) (enc 0 (n / d) (n mod d)).
Proof.
  intros n Hd. unfold sC.
  assert (Hz : n - (d * (n / d) + n mod d) = 0).
  { assert (Hdm : n = d * (n / d) + n mod d) by (apply Z.div_mod; lia). lia. }
  assert (H : enc 0 (n / d) (n mod d)
    = update (enc n (n / d) (n mod d)) 0%nat
        (adenote ASub (enc n (n / d) (n mod d) 0%nat)
           (eval (enc n (n / d) (n mod d))
                 (Bin OAdd (Bin OMul (Cst d) (Var 1%nat)) (Var 2%nat))))).
  { change (enc n (n / d) (n mod d) 0%nat) with n.
    change (eval (enc n (n / d) (n mod d))
                 (Bin OAdd (Bin OMul (Cst d) (Var 1%nat)) (Var 2%nat)))
      with (d * (n / d) + n mod d).
    cbn [adenote]. rewrite upd0. rewrite Hz. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

(* ===== 正しさ（新規貢献）: encode は (n,0,0) を (0, n/d, n mod d) に移す ===== *)

Theorem golomb_encode : forall n,
  d > 0 ->
  exec Γ Rgolomb (enc n 0 0) (enc 0 (n / d) (n mod d)).
Proof.
  intros n Hd. unfold Rgolomb.
  eapply E_Seq; [ apply stepA0 | ].
  eapply E_Seq; [ apply stepB0 | ].
  apply stepC0; exact Hd.
Qed.

(* ===== 可逆性は枠組みから無償: decode = invert encode ===== *)

Theorem golomb_decode : forall n,
  d > 0 ->
  exec Γ (invert Rgolomb) (enc 0 (n / d) (n mod d)) (enc n 0 0).
Proof.
  intros n Hd.
  apply (proj1 (exec_iff Γ Rgolomb (enc n 0 0) (enc 0 (n / d) (n mod d)))).
  apply golomb_encode; exact Hd.
Qed.

End Golomb.
