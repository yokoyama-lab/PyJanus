(** * RevVarint.v — 反復 divmod（LEB128/varint の核, 固定 3 桁版）

    [RevGolomb.v] の divmod-split（[ODiv]/[OMod] consume）を 2 回連ねて、
    varint の本質である「反復的な基数 B 分解」を実証する。

    抽象スペック（非可逆・単射）:  n ↦ (n mod B, (n/B) mod B, (n/B)/B)   （B>0）
      左逆元 (d0,d1,d2) ↦ d0 + B*d1 + B*B*d2 が単射性を与える
      （桁の上限を仮定せずとも div_mod 2 回で復元できる）。

    クリーン可逆 Janus 実装（consume を 2 段、5 レジスタ
      n=0, d0=1, mid=2, d1=3, d2=4）:
        (mid += n/B; d0 += n mod B; n -= B*mid + d0)      -- 第1分解: n を消費
        (d2  += mid/B; d1 += mid mod B; mid -= B*d2 + d1) -- 第2分解: mid を消費
      入口 (n,0,0,0,0) を出口 (0, n mod B, 0, (n/B) mod B, (n/B)/B) へ。
      n と中間商 mid を 0 へ消費し（garbage-free）、3 桁に全情報を移す。
      可逆性は [exec_iff] から無償。除算/剰余は式の中だけ（invert 対象外）。 *)

From Stdlib Require Import ZArith Lia FunctionalExtensionality.
Require Import Janus.
Open Scope Z_scope.

Section Varint.
Variable Γ : pname -> stmt.
Variable B : Z.

(* ===== 抽象スペック（単射）: 3 桁分解とその左逆元 ===== *)

Definition f_vi (n : Z) : Z * Z * Z := (n mod B, (n / B) mod B, (n / B) / B).
Definition g_vi (p : Z * Z * Z) : Z :=
  fst (fst p) + B * snd (fst p) + B * B * snd p.

Lemma f_vi_injective : forall n, B > 0 -> g_vi (f_vi n) = n.
Proof.
  intros n HB. unfold f_vi, g_vi; simpl.
  assert (H1 : n = B * (n / B) + n mod B) by (apply Z.div_mod; lia).
  assert (H2 : n / B = B * ((n / B) / B) + (n / B) mod B) by (apply Z.div_mod; lia).
  nia.
Qed.

(* ===== 符号化: var 0..4 ===== *)

Definition enc5 (v0 v1 v2 v3 v4 : Z) : store :=
  fun x => if Nat.eqb x 0 then v0
           else if Nat.eqb x 1 then v1
           else if Nat.eqb x 2 then v2
           else if Nat.eqb x 3 then v3
           else if Nat.eqb x 4 then v4 else 0.

Lemma u0 : forall a b c d e v, update (enc5 a b c d e) 0%nat v = enc5 v b c d e.
Proof. intros; apply functional_extensionality; intros [|[|[|[|[|y]]]]]; reflexivity. Qed.
Lemma u1 : forall a b c d e v, update (enc5 a b c d e) 1%nat v = enc5 a v c d e.
Proof. intros; apply functional_extensionality; intros [|[|[|[|[|y]]]]]; reflexivity. Qed.
Lemma u2 : forall a b c d e v, update (enc5 a b c d e) 2%nat v = enc5 a b v d e.
Proof. intros; apply functional_extensionality; intros [|[|[|[|[|y]]]]]; reflexivity. Qed.
Lemma u3 : forall a b c d e v, update (enc5 a b c d e) 3%nat v = enc5 a b c v e.
Proof. intros; apply functional_extensionality; intros [|[|[|[|[|y]]]]]; reflexivity. Qed.
Lemma u4 : forall a b c d e v, update (enc5 a b c d e) 4%nat v = enc5 a b c d v.
Proof. intros; apply functional_extensionality; intros [|[|[|[|[|y]]]]]; reflexivity. Qed.

(* ===== クリーン可逆 Janus プログラム ===== *)

Definition sA1 : stmt := Assign 2%nat AAdd (Bin ODiv (Var 0%nat) (Cst B)).
Definition sA2 : stmt := Assign 1%nat AAdd (Bin OMod (Var 0%nat) (Cst B)).
Definition sA3 : stmt :=
  Assign 0%nat ASub (Bin OAdd (Bin OMul (Cst B) (Var 2%nat)) (Var 1%nat)).
Definition sB1 : stmt := Assign 4%nat AAdd (Bin ODiv (Var 2%nat) (Cst B)).
Definition sB2 : stmt := Assign 3%nat AAdd (Bin OMod (Var 2%nat) (Cst B)).
Definition sB3 : stmt :=
  Assign 2%nat ASub (Bin OAdd (Bin OMul (Cst B) (Var 4%nat)) (Var 3%nat)).
Definition Rvarint : stmt := Seq sA1 (Seq sA2 (Seq sA3 (Seq sB1 (Seq sB2 sB3)))).

(* 第1分解（n を mid=n/B, d0=n mod B に展開し n を消費） *)
Lemma stA1 : forall n, exec Γ sA1 (enc5 n 0 0 0 0) (enc5 n 0 (n / B) 0 0).
Proof.
  intros n. unfold sA1.
  assert (H : enc5 n 0 (n / B) 0 0
    = update (enc5 n 0 0 0 0) 2%nat
        (adenote AAdd (enc5 n 0 0 0 0 2%nat)
                 (eval (enc5 n 0 0 0 0) (Bin ODiv (Var 0%nat) (Cst B))))).
  { change (enc5 n 0 0 0 0 2%nat) with 0.
    change (eval (enc5 n 0 0 0 0) (Bin ODiv (Var 0%nat) (Cst B))) with (n / B).
    cbn [adenote]. rewrite u2. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

Lemma stA2 : forall n, exec Γ sA2 (enc5 n 0 (n / B) 0 0) (enc5 n (n mod B) (n / B) 0 0).
Proof.
  intros n. unfold sA2.
  assert (H : enc5 n (n mod B) (n / B) 0 0
    = update (enc5 n 0 (n / B) 0 0) 1%nat
        (adenote AAdd (enc5 n 0 (n / B) 0 0 1%nat)
                 (eval (enc5 n 0 (n / B) 0 0) (Bin OMod (Var 0%nat) (Cst B))))).
  { change (enc5 n 0 (n / B) 0 0 1%nat) with 0.
    change (eval (enc5 n 0 (n / B) 0 0) (Bin OMod (Var 0%nat) (Cst B))) with (n mod B).
    cbn [adenote]. rewrite u1. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

Lemma stA3 : forall n, B > 0 ->
  exec Γ sA3 (enc5 n (n mod B) (n / B) 0 0) (enc5 0 (n mod B) (n / B) 0 0).
Proof.
  intros n HB. unfold sA3.
  assert (Hz : n - (B * (n / B) + n mod B) = 0).
  { assert (Hdm : n = B * (n / B) + n mod B) by (apply Z.div_mod; lia). lia. }
  assert (H : enc5 0 (n mod B) (n / B) 0 0
    = update (enc5 n (n mod B) (n / B) 0 0) 0%nat
        (adenote ASub (enc5 n (n mod B) (n / B) 0 0 0%nat)
           (eval (enc5 n (n mod B) (n / B) 0 0)
                 (Bin OAdd (Bin OMul (Cst B) (Var 2%nat)) (Var 1%nat))))).
  { change (enc5 n (n mod B) (n / B) 0 0 0%nat) with n.
    change (eval (enc5 n (n mod B) (n / B) 0 0)
                 (Bin OAdd (Bin OMul (Cst B) (Var 2%nat)) (Var 1%nat)))
      with (B * (n / B) + n mod B).
    cbn [adenote]. rewrite u0. rewrite Hz. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

(* 第2分解（mid=n/B を d2=(n/B)/B, d1=(n/B) mod B に展開し mid を消費） *)
Lemma stB1 : forall n,
  exec Γ sB1 (enc5 0 (n mod B) (n / B) 0 0) (enc5 0 (n mod B) (n / B) 0 ((n / B) / B)).
Proof.
  intros n. unfold sB1.
  assert (H : enc5 0 (n mod B) (n / B) 0 ((n / B) / B)
    = update (enc5 0 (n mod B) (n / B) 0 0) 4%nat
        (adenote AAdd (enc5 0 (n mod B) (n / B) 0 0 4%nat)
                 (eval (enc5 0 (n mod B) (n / B) 0 0) (Bin ODiv (Var 2%nat) (Cst B))))).
  { change (enc5 0 (n mod B) (n / B) 0 0 4%nat) with 0.
    change (eval (enc5 0 (n mod B) (n / B) 0 0) (Bin ODiv (Var 2%nat) (Cst B)))
      with ((n / B) / B).
    cbn [adenote]. rewrite u4. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

Lemma stB2 : forall n,
  exec Γ sB2 (enc5 0 (n mod B) (n / B) 0 ((n / B) / B))
             (enc5 0 (n mod B) (n / B) ((n / B) mod B) ((n / B) / B)).
Proof.
  intros n. unfold sB2.
  assert (H : enc5 0 (n mod B) (n / B) ((n / B) mod B) ((n / B) / B)
    = update (enc5 0 (n mod B) (n / B) 0 ((n / B) / B)) 3%nat
        (adenote AAdd (enc5 0 (n mod B) (n / B) 0 ((n / B) / B) 3%nat)
                 (eval (enc5 0 (n mod B) (n / B) 0 ((n / B) / B))
                       (Bin OMod (Var 2%nat) (Cst B))))).
  { change (enc5 0 (n mod B) (n / B) 0 ((n / B) / B) 3%nat) with 0.
    change (eval (enc5 0 (n mod B) (n / B) 0 ((n / B) / B))
                 (Bin OMod (Var 2%nat) (Cst B))) with ((n / B) mod B).
    cbn [adenote]. rewrite u3. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

Lemma stB3 : forall n, B > 0 ->
  exec Γ sB3 (enc5 0 (n mod B) (n / B) ((n / B) mod B) ((n / B) / B))
             (enc5 0 (n mod B) 0 ((n / B) mod B) ((n / B) / B)).
Proof.
  intros n HB. unfold sB3.
  assert (Hz : n / B - (B * ((n / B) / B) + (n / B) mod B) = 0).
  { assert (Hdm : n / B = B * ((n / B) / B) + (n / B) mod B) by (apply Z.div_mod; lia). lia. }
  assert (H : enc5 0 (n mod B) 0 ((n / B) mod B) ((n / B) / B)
    = update (enc5 0 (n mod B) (n / B) ((n / B) mod B) ((n / B) / B)) 2%nat
        (adenote ASub (enc5 0 (n mod B) (n / B) ((n / B) mod B) ((n / B) / B) 2%nat)
           (eval (enc5 0 (n mod B) (n / B) ((n / B) mod B) ((n / B) / B))
                 (Bin OAdd (Bin OMul (Cst B) (Var 4%nat)) (Var 3%nat))))).
  { change (enc5 0 (n mod B) (n / B) ((n / B) mod B) ((n / B) / B) 2%nat) with (n / B).
    change (eval (enc5 0 (n mod B) (n / B) ((n / B) mod B) ((n / B) / B))
                 (Bin OAdd (Bin OMul (Cst B) (Var 4%nat)) (Var 3%nat)))
      with (B * ((n / B) / B) + (n / B) mod B).
    cbn [adenote]. rewrite u2. rewrite Hz. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

(* ===== 正しさ: encode は (n,0,0,0,0) を (0, d0, 0, d1, d2) に移す ===== *)

Theorem varint_encode : forall n, B > 0 ->
  exec Γ Rvarint (enc5 n 0 0 0 0)
                 (enc5 0 (n mod B) 0 ((n / B) mod B) ((n / B) / B)).
Proof.
  intros n HB. unfold Rvarint.
  eapply E_Seq; [ apply stA1 | ].
  eapply E_Seq; [ apply stA2 | ].
  eapply E_Seq; [ apply stA3; exact HB | ].
  eapply E_Seq; [ apply stB1 | ].
  eapply E_Seq; [ apply stB2 | ].
  apply stB3; exact HB.
Qed.

(* ===== 可逆性は枠組みから無償 ===== *)

Theorem varint_decode : forall n, B > 0 ->
  exec Γ (invert Rvarint)
       (enc5 0 (n mod B) 0 ((n / B) mod B) ((n / B) / B)) (enc5 n 0 0 0 0).
Proof.
  intros n HB.
  apply (proj1 (exec_iff Γ Rvarint (enc5 n 0 0 0 0)
                 (enc5 0 (n mod B) 0 ((n / B) mod B) ((n / B) / B)))).
  apply varint_encode; exact HB.
Qed.

End Varint.
