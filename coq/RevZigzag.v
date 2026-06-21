(** * RevZigzag.v — ZigZag 符号（符号付き ℤ ↔ 非負 ℕ の全単射）

    数え上げ/可変長符号で使う zigzag:  n ↦ 2n (n≥0) / -(2n+1) (n<0)。
    これは ℤ→ℕ の全単射で、可逆 [If]（出口述語にパリティを使う）で
    クリーンに実現できる。除算/剰余は式の中だけ（[invert] 対象外）。

    抽象スペック（単射）:
        zig n  = if n <? 0 then -(2*n+1) else 2*n
        unzig z = if z mod 2 =? 0 then z/2 else -((z+1)/2)
      [zig_unzig]: ∀ n, unzig (zig n) = n。

    クリーン可逆 Janus 実装（2 レジスタ n=0, z=1, 単一 If）:
        if (n < 0)
          then  z += -(2n+1) ; n -= -((z+1)/2)     -- 負: z 奇、n を z から消去
          else  z += 2n      ; n -= z/2             -- 非負: z 偶、同上
        fi (z mod 2)                                -- 出口述語: z のパリティ
      入口 (n,0) を出口 (0, zig n) へ。n を 0 へ消費（garbage-free）。
      then/else は出口で z のパリティ（奇/偶）が異なるので可逆。 *)

From Stdlib Require Import ZArith Lia FunctionalExtensionality.
Require Import Janus.
Open Scope Z_scope.

Section Zigzag.
Variable Γ : pname -> stmt.

(* ===== 抽象スペック（単射）===== *)

Definition zig (n : Z) : Z := if n <? 0 then -(2*n+1) else 2*n.
Definition unzig (z : Z) : Z := if Z.eqb (z mod 2) 0 then z / 2 else -((z+1) / 2).

(* 算術補題 *)
Lemma mod2_even : forall n, (2*n) mod 2 = 0.
Proof. intro n. replace (2*n) with (n*2) by ring. apply Z_mod_mult. Qed.
Lemma mod2_odd : forall n, (-(2*n+1)) mod 2 = 1.
Proof.
  intro n. replace (-(2*n+1)) with (1 + (-n-1)*2) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma div_neg : forall n, (-(2*n+1) + 1) / 2 = -n.
Proof. intro n. replace (-(2*n+1) + 1) with ((-n)*2) by ring. apply Z.div_mul. lia. Qed.
Lemma div_pos : forall n, (2*n) / 2 = n.
Proof. intro n. replace (2*n) with (n*2) by ring. apply Z.div_mul. lia. Qed.

Lemma zig_unzig : forall n, unzig (zig n) = n.
Proof.
  intro n. unfold zig, unzig.
  destruct (n <? 0) eqn:E.
  - rewrite mod2_odd. cbn [Z.eqb]. rewrite div_neg. ring.
  - rewrite mod2_even. cbn [Z.eqb]. rewrite div_pos. reflexivity.
Qed.

(* ===== 符号化: var 0 ↦ n, 1 ↦ z ===== *)

Definition encz (n z : Z) : store :=
  fun x => if Nat.eqb x 0 then n else if Nat.eqb x 1 then z else 0.

Lemma uz0 : forall n z v, update (encz n z) 0%nat v = encz v z.
Proof. intros; apply functional_extensionality; intros [|[|y]]; reflexivity. Qed.
Lemma uz1 : forall n z v, update (encz n z) 1%nat v = encz n v.
Proof. intros; apply functional_extensionality; intros [|[|y]]; reflexivity. Qed.

(* ===== プログラム断片 ===== *)

Definition e1expr : expr := Bin OLt (Var 0%nat) (Cst 0).
Definition e2expr : expr := Bin OMod (Var 1%nat) (Cst 2).
(* then: z += -(2n+1) ; n -= -((z+1)/2) *)
Definition zt : stmt := Assign 1%nat AAdd (Bin OSub (Cst 0) (Bin OAdd (Bin OMul (Cst 2) (Var 0%nat)) (Cst 1))).
Definition nt : stmt := Assign 0%nat ASub (Bin OSub (Cst 0) (Bin ODiv (Bin OAdd (Var 1%nat) (Cst 1)) (Cst 2))).
Definition thenB : stmt := Seq zt nt.
(* else: z += 2n ; n -= z/2 *)
Definition ze : stmt := Assign 1%nat AAdd (Bin OMul (Cst 2) (Var 0%nat)).
Definition ne : stmt := Assign 0%nat ASub (Bin ODiv (Var 1%nat) (Cst 2)).
Definition elseB : stmt := Seq ze ne.
Definition Rzz : stmt := If e1expr thenB elseB e2expr.

(* ----- then 系のステップ ----- *)
Lemma zt_step : forall n, exec Γ zt (encz n 0) (encz n (-(2*n+1))).
Proof.
  intros n. unfold zt.
  assert (H : encz n (-(2*n+1))
    = update (encz n 0) 1%nat
        (adenote AAdd (encz n 0 1%nat)
                 (eval (encz n 0) (Bin OSub (Cst 0) (Bin OAdd (Bin OMul (Cst 2) (Var 0%nat)) (Cst 1)))))).
  { change (encz n 0 1%nat) with 0.
    change (eval (encz n 0) (Bin OSub (Cst 0) (Bin OAdd (Bin OMul (Cst 2) (Var 0%nat)) (Cst 1))))
      with (-(2*n+1)).
    cbn [adenote]. rewrite uz1. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

Lemma nt_step : forall n, exec Γ nt (encz n (-(2*n+1))) (encz 0 (-(2*n+1))).
Proof.
  intros n. unfold nt.
  assert (HV : adenote ASub (encz n (-(2*n+1)) 0%nat)
                 (eval (encz n (-(2*n+1))) (Bin OSub (Cst 0) (Bin ODiv (Bin OAdd (Var 1%nat) (Cst 1)) (Cst 2)))) = 0).
  { change (encz n (-(2*n+1)) 0%nat) with n.
    change (eval (encz n (-(2*n+1))) (Bin OSub (Cst 0) (Bin ODiv (Bin OAdd (Var 1%nat) (Cst 1)) (Cst 2))))
      with (0 - ((-(2*n+1) + 1) / 2)).
    cbn [adenote]. rewrite div_neg. ring. }
  assert (H : encz 0 (-(2*n+1))
    = update (encz n (-(2*n+1))) 0%nat
        (adenote ASub (encz n (-(2*n+1)) 0%nat)
                 (eval (encz n (-(2*n+1))) (Bin OSub (Cst 0) (Bin ODiv (Bin OAdd (Var 1%nat) (Cst 1)) (Cst 2)))))).
  { rewrite uz0, HV. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

Lemma thenB_step : forall n, exec Γ thenB (encz n 0) (encz 0 (-(2*n+1))).
Proof. intros n. unfold thenB. eapply E_Seq; [ apply zt_step | apply nt_step ]. Qed.

(* ----- else 系のステップ ----- *)
Lemma ze_step : forall n, exec Γ ze (encz n 0) (encz n (2*n)).
Proof.
  intros n. unfold ze.
  assert (H : encz n (2*n)
    = update (encz n 0) 1%nat
        (adenote AAdd (encz n 0 1%nat) (eval (encz n 0) (Bin OMul (Cst 2) (Var 0%nat))))).
  { change (encz n 0 1%nat) with 0.
    change (eval (encz n 0) (Bin OMul (Cst 2) (Var 0%nat))) with (2*n).
    cbn [adenote]. rewrite uz1. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

Lemma ne_step : forall n, exec Γ ne (encz n (2*n)) (encz 0 (2*n)).
Proof.
  intros n. unfold ne.
  assert (HV : adenote ASub (encz n (2*n) 0%nat)
                 (eval (encz n (2*n)) (Bin ODiv (Var 1%nat) (Cst 2))) = 0).
  { change (encz n (2*n) 0%nat) with n.
    change (eval (encz n (2*n)) (Bin ODiv (Var 1%nat) (Cst 2))) with ((2*n) / 2).
    cbn [adenote]. rewrite div_pos. ring. }
  assert (H : encz 0 (2*n)
    = update (encz n (2*n)) 0%nat
        (adenote ASub (encz n (2*n) 0%nat) (eval (encz n (2*n)) (Bin ODiv (Var 1%nat) (Cst 2))))).
  { rewrite uz0, HV. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

Lemma elseB_step : forall n, exec Γ elseB (encz n 0) (encz 0 (2*n)).
Proof. intros n. unfold elseB. eapply E_Seq; [ apply ze_step | apply ne_step ]. Qed.

(* ===== 正しさ: encode は (n,0) を (0, zig n) に移す ===== *)

Theorem zigzag_encode : forall n, exec Γ Rzz (encz n 0) (encz 0 (zig n)).
Proof.
  intro n. unfold Rzz. destruct (n <? 0) eqn:E.
  - (* n < 0 *) assert (Hz : zig n = -(2*n+1)) by (unfold zig; rewrite E; reflexivity).
    rewrite Hz. eapply E_IfT.
    + change (eval (encz n 0) e1expr) with (if n <? 0 then 1 else 0). rewrite E. discriminate.
    + apply thenB_step.
    + change (eval (encz 0 (-(2*n+1))) e2expr) with ((-(2*n+1)) mod 2).
      rewrite mod2_odd. discriminate.
  - (* n >= 0 *) assert (Hz : zig n = 2*n) by (unfold zig; rewrite E; reflexivity).
    rewrite Hz. eapply E_IfF.
    + change (eval (encz n 0) e1expr) with (if n <? 0 then 1 else 0). rewrite E. reflexivity.
    + apply elseB_step.
    + change (eval (encz 0 (2*n)) e2expr) with ((2*n) mod 2). rewrite mod2_even. reflexivity.
Qed.

(* ===== 可逆性は枠組みから無償 ===== *)

Theorem zigzag_decode : forall n,
  exec Γ (invert Rzz) (encz 0 (zig n)) (encz n 0).
Proof.
  intro n.
  apply (proj1 (exec_iff Γ Rzz (encz n 0) (encz 0 (zig n)))).
  apply zigzag_encode.
Qed.

End Zigzag.
