(** * RevDeltaN.v — 一般長 n の後退差分 delta を Janus Loop で ∀ 証明

    [RevPipelineArr.v] の段階2（具体長 n=3）を、任意長 N(≥2)へ格上げする。
    Janus ループ
        from (i = N-1) do  A[i] -= A[i-1]  loop  i -= 1  until (i = 1)
    が、入力配列 a を後退差分（cell 0 はそのまま、cell j(≥1) は a j - a(j-1)）に
    変換することを、ループ不変条件 [dstore k]（カウンタ=k、cell j は k<?j なら差分済み）
    の [opn] 帰納で証明する。可逆性は [exec_iff] から無償。

    手法: RevArr の [opn]（ループ本体の反復関係）を反復回数 j に関する帰納で構成し、
    [opn_to_lp] で最終反復（i=1 で脱出）を継いで [E_Loop] に渡す。 *)

From Stdlib Require Import ZArith Lia FunctionalExtensionality.
Require Import RevArr.
Open Scope Z_scope.

Section DeltaN.
Variable Γ : pname -> (list var * stmt).
Variable a : Z -> Z.        (* 入力配列の内容（cell j ↦ a j） *)
Variable N : Z.             (* 配列長 *)
Hypothesis HN : N >= 2.

(* ===== 不変条件となる store 族 ===== *)
(*  カウンタ LS 1 = k、配列 cell j は k<?j なら差分済み(a j - a(j-1))、否なら原値 a j *)
Definition dstore (k : Z) : store :=
  fun l => match l with
           | LS x => if Nat.eqb x 1 then k else 0
           | LA arr j => if Nat.eqb arr 0
                         then (if k <? j then a j - a (j - 1) else a j)
                         else 0
           end.

Lemma dstore_LS1 : forall k, dstore k (LS 1%nat) = k.
Proof. reflexivity. Qed.
Lemma dstore_LA0 : forall k j, dstore k (LA 0%nat j) = if k <? j then a j - a (j - 1) else a j.
Proof. reflexivity. Qed.

(* j ≠ k なら閾値 k と k-1 で cell j の判定は変わらない *)
Lemma ltb_shift : forall k j, j <> k -> (k <? j) = (k - 1 <? j).
Proof.
  intros k j Hjk. destruct (k <? j) eqn:E1; destruct (k - 1 <? j) eqn:E2; try reflexivity.
  - apply Z.ltb_lt in E1; apply Z.ltb_ge in E2; lia.
  - apply Z.ltb_ge in E1; apply Z.ltb_lt in E2; lia.
Qed.

(* ===== プログラム ===== *)
Definition s1 : stmt :=
  Assign (LVa 0%nat (Var 1%nat)) ASub (ARd 0%nat (Bin OSub (Var 1%nat) (Cst 1))).
Definition s2 : stmt := Assign (LVs 1%nat) ASub (Cst 1).
Definition e1 : expr := Bin OEq (Var 1%nat) (Cst (N - 1)).
Definition e2 : expr := Bin OEq (Var 1%nat) (Cst 1).
Definition Rd : stmt := Loop e1 s1 s2 e2.

(* s1 の実行時整合性（添字が動的なので reflexivity では閉じない） *)
Lemma wf_s1 : forall k,
  wf_assign (dstore k) (LVa 0%nat (Var 1%nat)) (ARd 0%nat (Bin OSub (Var 1%nat) (Cst 1))) = true.
Proof.
  intro k.
  assert (Hidx : eval (dstore k) (Bin OSub (Var 1%nat) (Cst 1)) = k - 1).
  { cbn [eval]. rewrite dstore_LS1. reflexivity. }
  unfold wf_assign, reads_idx, lloc. cbn [eval]. rewrite !dstore_LS1.
  cbn [reads_cell]. rewrite Hidx. unfold loceqb.
  destruct (loc_eq_dec (LA 0%nat k) (LA 0%nat (k - 1))) as [E|_].
  - inversion E; lia.
  - destruct (loc_eq_dec (LA 0%nat k) (LS 1%nat)) as [E'|_]; [ discriminate E' | reflexivity ].
Qed.

(* s1: cell k を差分化（カウンタ k のまま） *)
Definition m1 (k : Z) : store := update (dstore k) (LA 0%nat k) (a k - a (k - 1)).

Lemma s1_step : forall k, exec Γ s1 (dstore k) (m1 k).
Proof.
  intro k. unfold s1, m1.
  assert (Hll : lloc (dstore k) (LVa 0%nat (Var 1%nat)) = LA 0%nat k).
  { unfold lloc. cbn [eval]. rewrite dstore_LS1. reflexivity. }
  assert (Hrd : eval (dstore k) (ARd 0%nat (Bin OSub (Var 1%nat) (Cst 1))) = a (k - 1)).
  { cbn [eval]. rewrite dstore_LS1. cbn [denote]. rewrite dstore_LA0.
    replace (k <? k - 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  assert (H : update (dstore k) (LA 0%nat k) (a k - a (k - 1))
    = update (dstore k) (lloc (dstore k) (LVa 0%nat (Var 1%nat)))
        (adenote ASub (dstore k (lloc (dstore k) (LVa 0%nat (Var 1%nat))))
                 (eval (dstore k) (ARd 0%nat (Bin OSub (Var 1%nat) (Cst 1)))))).
  { rewrite Hll, Hrd. rewrite dstore_LA0.
    replace (k <? k) with false by (symmetry; apply Z.ltb_irrefl). reflexivity. }
  rewrite H. apply E_Assign. apply wf_s1.
Qed.

(* s2: カウンタを k-1 に。これで m1 k → dstore (k-1) *)
Lemma s2_step : forall k, exec Γ s2 (m1 k) (dstore (k - 1)).
Proof.
  intro k. unfold s2, m1.
  assert (Hll : lloc (update (dstore k) (LA 0%nat k) (a k - a (k - 1))) (LVs 1%nat) = LS 1%nat)
    by reflexivity.
  assert (Hcur : update (dstore k) (LA 0%nat k) (a k - a (k - 1)) (LS 1%nat) = k).
  { unfold update, loceqb. destruct (loc_eq_dec (LA 0%nat k) (LS 1%nat)) as [E|_];
      [ discriminate E | apply dstore_LS1 ]. }
  assert (H : dstore (k - 1)
    = update (update (dstore k) (LA 0%nat k) (a k - a (k - 1))) (LS 1%nat)
        (adenote ASub (update (dstore k) (LA 0%nat k) (a k - a (k - 1)) (LS 1%nat))
                 (eval (update (dstore k) (LA 0%nat k) (a k - a (k - 1))) (Cst 1)))).
  { rewrite Hcur. cbn [eval adenote].
    apply functional_extensionality; intro l.
    unfold update, loceqb.
    destruct (loc_eq_dec (LS 1%nat) l) as [E1|N1].
    - subst l. reflexivity.
    - destruct (loc_eq_dec (LA 0%nat k) l) as [E2|N2].
      + subst l. rewrite dstore_LA0.
        replace (k - 1 <? k) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + destruct l as [x | arr j].
        * cbn [dstore]. destruct (Nat.eqb x 1) eqn:Ex;
            [ apply Nat.eqb_eq in Ex; subst x; exfalso; apply N1; reflexivity | reflexivity ].
        * cbn [dstore]. destruct (Nat.eqb arr 0) eqn:Ea; [ | reflexivity ].
          apply Nat.eqb_eq in Ea; subst arr.
          assert (Hjk : j <> k) by (intro Hc; subst j; apply N2; reflexivity).
          rewrite (ltb_shift k j Hjk). reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

(* ===== 1 反復ぶんの遷移条件（O_cons の中身）===== *)

(* 反復中（k≥2）は e2=(i=1) が偽 *)
Lemma e2_false : forall k, k >= 2 -> eval (m1 k) e2 = 0.
Proof.
  intros k Hk. unfold m1, e2. cbn [eval].
  assert (Hc : update (dstore k) (LA 0%nat k) (a k - a (k - 1)) (LS 1%nat) = k).
  { unfold update, loceqb. destruct (loc_eq_dec (LA 0%nat k) (LS 1%nat)) as [E|_];
      [ discriminate E | apply dstore_LS1 ]. }
  rewrite Hc. cbn [denote]. destruct (k =? 1) eqn:E; [ apply Z.eqb_eq in E; lia | reflexivity ].
Qed.

(* s2 後（k≤N-1 なので k-1≤N-2）は e1=(i=N-1) が偽 *)
Lemma e1_false : forall k, k <= N - 1 -> eval (dstore (k - 1)) e1 = 0.
Proof.
  intros k Hk. unfold e1. cbn [eval]. rewrite dstore_LS1. cbn [denote].
  destruct (k - 1 =? N - 1) eqn:E; [ apply Z.eqb_eq in E; lia | reflexivity ].
Qed.

(* opn を反復回数 j に関する帰納で構成: dstore(1+j) から dstore 1 まで *)
Lemma delta_opn : forall (j : nat),
  1 + Z.of_nat j <= N - 1 ->
  opn Γ e1 s1 s2 e2 (dstore (1 + Z.of_nat j)) (dstore 1).
Proof.
  induction j as [| j IH]; intro Hle.
  - simpl (Z.of_nat 0). replace (1 + 0) with 1 by ring. apply O_nil.
  - rewrite Nat2Z.inj_succ.
    set (k := 1 + Z.succ (Z.of_nat j)).
    assert (Hk2 : k >= 2) by (unfold k; lia).
    assert (HkN : k <= N - 1) by (unfold k; lia).
    (* O_cons: s1; e2=0; s2; e1=0; 残り opn *)
    eapply O_cons.
    + apply s1_step.
    + apply e2_false; exact Hk2.
    + apply s2_step.
    + apply e1_false; exact HkN.
    + (* dstore (k-1) = dstore (1 + Z.of_nat j) *)
      replace (k - 1) with (1 + Z.of_nat j) by (unfold k; ring).
      apply IH. lia.
Qed.

(* ===== 最終状態: cell 1 も差分化、カウンタ 1 ===== *)
Definition dfinal : store := update (dstore 1) (LA 0%nat 1) (a 1 - a 0).

(* 最終反復: i=1 で s1 を実行し、e2=(i=1) 真で脱出 *)
Lemma s1_final : exec Γ s1 (dstore 1) dfinal.
Proof.
  unfold dfinal. replace (a 1 - a 0) with (a 1 - a (1 - 1)) by (f_equal; f_equal; ring).
  replace (LA 0%nat 1) with (LA 0%nat 1) by reflexivity.
  pose proof (s1_step 1) as Hs. unfold m1 in Hs. exact Hs.
Qed.

Lemma e2_true_final : eval dfinal e2 <> 0.
Proof.
  unfold dfinal, e2. cbn [eval].
  assert (Hc : update (dstore 1) (LA 0%nat 1) (a 1 - a 0) (LS 1%nat) = 1).
  { unfold update, loceqb. destruct (loc_eq_dec (LA 0%nat 1) (LS 1%nat)) as [E|_];
      [ discriminate E | apply dstore_LS1 ]. }
  rewrite Hc. cbn [denote Z.eqb]. discriminate.
Qed.

(* ===== 主定理: ループは dstore(N-1)（=入力）を dfinal（=後退差分）に移す ===== *)
Theorem deltaN_computes : exec Γ Rd (dstore (N - 1)) dfinal.
Proof.
  unfold Rd. apply E_Loop.
  - (* 入口 e1=(i=N-1) 真 *)
    unfold e1. cbn [eval]. rewrite dstore_LS1. cbn [denote].
    rewrite Z.eqb_refl. discriminate.
  - (* lp: opn で N-1→1、最終 s1 で脱出 *)
    apply (opn_to_lp Γ e1 s1 s2 e2 (dstore (N - 1)) (dstore 1) dfinal).
    + replace (N - 1) with (1 + Z.of_nat (Z.to_nat (N - 2))) by
        (rewrite Z2Nat.id by lia; ring).
      apply delta_opn. rewrite Z2Nat.id by lia. lia.
    + apply s1_final.
    + apply e2_true_final.
Qed.

(* ===== 可逆性は枠組みから無償 ===== *)
Theorem deltaN_reversible : exec Γ (invert Rd) dfinal (dstore (N - 1)).
Proof.
  apply (proj1 (exec_iff Γ Rd (dstore (N - 1)) dfinal)). apply deltaN_computes.
Qed.

End DeltaN.
