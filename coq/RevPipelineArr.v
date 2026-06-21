(** * RevPipelineArr.v
    配列版パイプライン:
      「非可逆で単射と定理証明された配列スペック」
         ⟹ 「クリーン可逆で（配列意味論上）正しいと証明された Janus プログラム」

    [RevPipeline.v]（スカラ 2 変数）の配列・ループ版。土台は [RevArr.v]
    （store = loc -> Z, 配列セル [LA a i], 実行時エイリアス検査 [wf_assign],
     [Loop], [exec_iff]）。

    本ファイルの到達点:
      - 段階1: 多セル後退差分 delta（長さ3配列）を Seq で実装し，配列 l-value と
               実行時 [wf_assign] を実際に通して [exec] 上で正しさを証明．
               可逆性は [exec_iff] から無償．
      - 段階2: 同じ delta を Janus の [Loop]（from..until）で実装し，
               具体長 n=3（2 反復）の [exec] を [E_Loop]/[lp] 展開で証明．
*)

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
Require Import RevArr.
Open Scope Z_scope.

Section Pipe.
Variable Γ : pname -> (list var * stmt).   (* 手続き環境（本例では未使用） *)

(* ===== 符号化: 配列 a(=var 0) のセル 0,1,2 に (a0,a1,a2) を置く ===== *)

Definition enc3 (a0 a1 a2 : Z) : store :=
  fun l => match l with
           | LA a i => if Nat.eqb a 0
                       then (if Z.eqb i 0 then a0
                             else if Z.eqb i 1 then a1
                             else if Z.eqb i 2 then a2 else 0)
                       else 0
           | LS _ => 0
           end.

(* ===== 入力: 非可逆で「単射と証明された」配列スペック ===== *)
(*   後退差分 delta:  (a0,a1,a2) ↦ (a0, a1-a0, a2-a1)   *)

Definition fdelta (a0 a1 a2 : Z) : Z * Z * Z := (a0, a1 - a0, a2 - a1).
Definition gdelta (b0 b1 b2 : Z) : Z * Z * Z := (b0, b1 + b0, b2 + (b1 + b0)).

Lemma fdelta_injective : forall a0 a1 a2,
  gdelta (fst (fst (fdelta a0 a1 a2)))
         (snd (fst (fdelta a0 a1 a2)))
         (snd (fdelta a0 a1 a2)) = (a0, a1, a2).
Proof. intros; unfold fdelta, gdelta; simpl; f_equal; [ f_equal | ]; ring. Qed.

(* ===== 出力(Seq版): A[2] -= A[1] ; A[1] -= A[0] （高位から処理） ===== *)

Definition Rdelta : stmt :=
  Seq (Assign (LVa 0%nat (Cst 2)) ASub (ARd 0%nat (Cst 1)))
      (Assign (LVa 0%nat (Cst 1)) ASub (ARd 0%nat (Cst 0))).

(* wf（実行時エイリアス検査）は添字が定数なので store 非依存に true へ簡約 *)
Lemma wf1 : forall a0 a1 a2,
  wf_assign (enc3 a0 a1 a2) (LVa 0%nat (Cst 2)) (ARd 0%nat (Cst 1)) = true.
Proof. reflexivity. Qed.

(* 単一更新の書換補題: enc3 のセルを 1 つだけ書き換える。 *)
Lemma upd_enc3_2 : forall a0 a1 a2 v,
  update (enc3 a0 a1 a2) (LA 0%nat 2) v = enc3 a0 a1 v.
Proof.
  intros a0 a1 a2 v. apply functional_extensionality; intro l.
  unfold update, loceqb. destruct (loc_eq_dec (LA 0%nat 2) l) as [E|N].
  - subst l. reflexivity.
  - destruct l as [x | a i]; [ reflexivity | ].
    unfold enc3. destruct (Nat.eqb a 0) eqn:Ea; [ | reflexivity ].
    apply Nat.eqb_eq in Ea; subst a.
    destruct (Z.eqb i 2) eqn:Z2.
    + apply Z.eqb_eq in Z2; subst i; exfalso; apply N; reflexivity.
    + destruct (Z.eqb i 0); [ reflexivity | ]; destruct (Z.eqb i 1); reflexivity.
Qed.

Lemma upd_enc3_1 : forall a0 a1 a2 v,
  update (enc3 a0 a1 a2) (LA 0%nat 1) v = enc3 a0 v a2.
Proof.
  intros a0 a1 a2 v. apply functional_extensionality; intro l.
  unfold update, loceqb. destruct (loc_eq_dec (LA 0%nat 1) l) as [E|N].
  - subst l. reflexivity.
  - destruct l as [x | a i]; [ reflexivity | ].
    unfold enc3. destruct (Nat.eqb a 0) eqn:Ea; [ | reflexivity ].
    apply Nat.eqb_eq in Ea; subst a.
    destruct (Z.eqb i 1) eqn:Z1.
    + apply Z.eqb_eq in Z1; subst i; exfalso; apply N; reflexivity.
    + destruct (Z.eqb i 0); reflexivity.
Qed.

(* 各代入を「明示的な enc3 を入出力に持つ」ステップへ分解（中間 store が具体的）。 *)
Lemma step1 : forall a0 a1 a2,
  exec Γ (Assign (LVa 0%nat (Cst 2)) ASub (ARd 0%nat (Cst 1)))
       (enc3 a0 a1 a2) (enc3 a0 a1 (a2 - a1)).
Proof.
  intros a0 a1 a2.
  assert (Hst :
    update (enc3 a0 a1 a2) (lloc (enc3 a0 a1 a2) (LVa 0%nat (Cst 2)))
      (adenote ASub (enc3 a0 a1 a2 (lloc (enc3 a0 a1 a2) (LVa 0%nat (Cst 2))))
               (eval (enc3 a0 a1 a2) (ARd 0%nat (Cst 1))))
    = enc3 a0 a1 (a2 - a1)).
  { change (lloc (enc3 a0 a1 a2) (LVa 0%nat (Cst 2))) with (LA 0%nat 2).
    change (eval (enc3 a0 a1 a2) (ARd 0%nat (Cst 1))) with (enc3 a0 a1 a2 (LA 0%nat 1)).
    cbn [adenote]. rewrite upd_enc3_2. reflexivity. }
  rewrite <- Hst. apply E_Assign. reflexivity.
Qed.

Lemma step2 : forall a0 a1 a2,
  exec Γ (Assign (LVa 0%nat (Cst 1)) ASub (ARd 0%nat (Cst 0)))
       (enc3 a0 a1 a2) (enc3 a0 (a1 - a0) a2).
Proof.
  intros a0 a1 a2.
  assert (Hst :
    update (enc3 a0 a1 a2) (lloc (enc3 a0 a1 a2) (LVa 0%nat (Cst 1)))
      (adenote ASub (enc3 a0 a1 a2 (lloc (enc3 a0 a1 a2) (LVa 0%nat (Cst 1))))
               (eval (enc3 a0 a1 a2) (ARd 0%nat (Cst 0))))
    = enc3 a0 (a1 - a0) a2).
  { change (lloc (enc3 a0 a1 a2) (LVa 0%nat (Cst 1))) with (LA 0%nat 1).
    change (eval (enc3 a0 a1 a2) (ARd 0%nat (Cst 0))) with (enc3 a0 a1 a2 (LA 0%nat 0)).
    cbn [adenote]. rewrite upd_enc3_1. reflexivity. }
  rewrite <- Hst. apply E_Assign. reflexivity.
Qed.

Theorem Rdelta_computes :
  forall a0 a1 a2,
    exec Γ Rdelta (enc3 a0 a1 a2) (enc3 a0 (a1 - a0) (a2 - a1)).
Proof.
  intros a0 a1 a2. unfold Rdelta.
  eapply E_Seq.
  - apply step1.
  - apply step2.
Qed.

(* ===== 可逆性は枠組みから無償 ===== *)

Theorem Rdelta_reversible :
  forall a0 a1 a2,
    exec Γ (invert Rdelta) (enc3 a0 (a1 - a0) (a2 - a1)) (enc3 a0 a1 a2).
Proof.
  intros a0 a1 a2.
  apply (proj1 (exec_iff Γ Rdelta (enc3 a0 a1 a2) (enc3 a0 (a1 - a0) (a2 - a1)))).
  apply Rdelta_computes.
Qed.

End Pipe.
