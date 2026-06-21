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

(* ===================================================================== *)
(** ** 段階2: 同じ delta を Janus の Loop（from..until）で実装               *)
(*                                                                         *)
(*   from (i = 2) do  A[i] -= A[i-1]  loop  i -= 1  until (i = 1)          *)
(*                                                                         *)
(*   i は LS 1（カウンタ）、配列 a は var 0。i=2 から始め、A[2],A[1] を       *)
(*   処理して i=1 で抜ける（2 反復）。L_more → L_one で具体展開して証明。      *)
(* ===================================================================== *)

(* 符号化: 配列セル 0,1,2 ＝ a0,a1,a2、カウンタ LS 1 ＝ i。 *)
Definition encL (a0 a1 a2 i : Z) : store :=
  fun l => match l with
           | LS x => if Nat.eqb x 1 then i else 0
           | LA a j => if Nat.eqb a 0
                       then (if Z.eqb j 0 then a0
                             else if Z.eqb j 1 then a1
                             else if Z.eqb j 2 then a2 else 0)
                       else 0
           end.

(* 単一更新の書換補題（配列 2 セルとカウンタ）。 *)
Lemma updL_A2 : forall a0 a1 a2 i v,
  update (encL a0 a1 a2 i) (LA 0%nat 2) v = encL a0 a1 v i.
Proof.
  intros; apply functional_extensionality; intro l.
  unfold update, loceqb. destruct (loc_eq_dec (LA 0%nat 2) l) as [E|N].
  - subst l; reflexivity.
  - destruct l as [x | a j]; [ reflexivity | ].
    unfold encL. destruct (Nat.eqb a 0) eqn:Ea; [ | reflexivity ].
    apply Nat.eqb_eq in Ea; subst a.
    destruct (Z.eqb j 2) eqn:Z2;
      [ apply Z.eqb_eq in Z2; subst j; exfalso; apply N; reflexivity | ].
    destruct (Z.eqb j 0); [ reflexivity | ]; destruct (Z.eqb j 1); reflexivity.
Qed.

Lemma updL_A1 : forall a0 a1 a2 i v,
  update (encL a0 a1 a2 i) (LA 0%nat 1) v = encL a0 v a2 i.
Proof.
  intros; apply functional_extensionality; intro l.
  unfold update, loceqb. destruct (loc_eq_dec (LA 0%nat 1) l) as [E|N].
  - subst l; reflexivity.
  - destruct l as [x | a j]; [ reflexivity | ].
    unfold encL. destruct (Nat.eqb a 0) eqn:Ea; [ | reflexivity ].
    apply Nat.eqb_eq in Ea; subst a.
    destruct (Z.eqb j 1) eqn:Z1;
      [ apply Z.eqb_eq in Z1; subst j; exfalso; apply N; reflexivity | ].
    destruct (Z.eqb j 0); reflexivity.
Qed.

Lemma updL_S1 : forall a0 a1 a2 i v,
  update (encL a0 a1 a2 i) (LS 1%nat) v = encL a0 a1 a2 v.
Proof.
  intros; apply functional_extensionality; intro l.
  unfold update, loceqb. destruct (loc_eq_dec (LS 1%nat) l) as [E|N].
  - subst l; reflexivity.
  - destruct l as [x | a j]; [ | reflexivity ].
    unfold encL. destruct (Nat.eqb x 1) eqn:Ex; [ | reflexivity ].
    apply Nat.eqb_eq in Ex; subst x; exfalso; apply N; reflexivity.
Qed.

(* ループ本体 s1 / s2 と判定式 e1 / e2。 *)
Definition s1stmt : stmt :=
  Assign (LVa 0%nat (Var 1%nat)) ASub (ARd 0%nat (Bin OSub (Var 1%nat) (Cst 1))).
Definition s2stmt : stmt := Assign (LVs 1%nat) ASub (Cst 1).
Definition e1expr : expr := Bin OEq (Var 1%nat) (Cst 2).
Definition e2expr : expr := Bin OEq (Var 1%nat) (Cst 1).

Definition Rloop : stmt := Loop e1expr s1stmt s2stmt e2expr.

(* s1 を i=2 の店で適用: A[2] を a2-a1 に。 *)
Lemma s1_at2 : forall a0 a1 a2,
  exec Γ s1stmt (encL a0 a1 a2 2) (encL a0 a1 (a2 - a1) 2).
Proof.
  intros a0 a1 a2. unfold s1stmt.
  assert (H : encL a0 a1 (a2 - a1) 2
    = update (encL a0 a1 a2 2)
        (lloc (encL a0 a1 a2 2) (LVa 0%nat (Var 1%nat)))
        (adenote ASub (encL a0 a1 a2 2 (lloc (encL a0 a1 a2 2) (LVa 0%nat (Var 1%nat))))
                 (eval (encL a0 a1 a2 2) (ARd 0%nat (Bin OSub (Var 1%nat) (Cst 1)))))).
  { change (lloc (encL a0 a1 a2 2) (LVa 0%nat (Var 1%nat))) with (LA 0%nat 2).
    change (encL a0 a1 a2 2 (LA 0%nat 2)) with a2.
    change (eval (encL a0 a1 a2 2) (ARd 0%nat (Bin OSub (Var 1%nat) (Cst 1)))) with a1.
    cbn [adenote]. rewrite updL_A2. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

(* s1 を i=1 の店で適用: A[1] を a1-a0 に。 *)
Lemma s1_at1 : forall a0 a1 a2,
  exec Γ s1stmt (encL a0 a1 a2 1) (encL a0 (a1 - a0) a2 1).
Proof.
  intros a0 a1 a2. unfold s1stmt.
  assert (H : encL a0 (a1 - a0) a2 1
    = update (encL a0 a1 a2 1)
        (lloc (encL a0 a1 a2 1) (LVa 0%nat (Var 1%nat)))
        (adenote ASub (encL a0 a1 a2 1 (lloc (encL a0 a1 a2 1) (LVa 0%nat (Var 1%nat))))
                 (eval (encL a0 a1 a2 1) (ARd 0%nat (Bin OSub (Var 1%nat) (Cst 1)))))).
  { change (lloc (encL a0 a1 a2 1) (LVa 0%nat (Var 1%nat))) with (LA 0%nat 1).
    change (encL a0 a1 a2 1 (LA 0%nat 1)) with a1.
    change (eval (encL a0 a1 a2 1) (ARd 0%nat (Bin OSub (Var 1%nat) (Cst 1)))) with a0.
    cbn [adenote]. rewrite updL_A1. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

(* s2: カウンタ i -= 1。 *)
Lemma s2_dec : forall a0 a1 a2 i,
  exec Γ s2stmt (encL a0 a1 a2 i) (encL a0 a1 a2 (i - 1)).
Proof.
  intros a0 a1 a2 i. unfold s2stmt.
  assert (H : encL a0 a1 a2 (i - 1)
    = update (encL a0 a1 a2 i) (lloc (encL a0 a1 a2 i) (LVs 1%nat))
        (adenote ASub (encL a0 a1 a2 i (lloc (encL a0 a1 a2 i) (LVs 1%nat)))
                 (eval (encL a0 a1 a2 i) (Cst 1)))).
  { change (lloc (encL a0 a1 a2 i) (LVs 1%nat)) with (LS 1%nat).
    change (encL a0 a1 a2 i (LS 1%nat)) with i.
    change (eval (encL a0 a1 a2 i) (Cst 1)) with 1.
    cbn [adenote]. rewrite updL_S1. reflexivity. }
  rewrite H. apply E_Assign. reflexivity.
Qed.

(* ループ全体: encL .. 2 から 2 反復で delta 済み・i=1 の店へ。 *)
Theorem Rloop_computes :
  forall a0 a1 a2,
    exec Γ Rloop (encL a0 a1 a2 2) (encL a0 (a1 - a0) (a2 - a1) 1).
Proof.
  intros a0 a1 a2. unfold Rloop.
  apply E_Loop.
  - (* 入口判定 e1 = (i=2) は i=2 で真 *) cbn. discriminate.
  - (* 1 反復目: s1; e2 偽; s2; e1 偽; 残りループ *)
    eapply L_more.
    + apply s1_at2.
    + reflexivity.                       (* e2=(i=1) は i=2 で偽 *)
    + apply s2_dec.                      (* i: 2 -> 1 *)
    + reflexivity.                       (* e1=(i=2) は i=1 で偽 *)
    + (* 2 反復目: s1; e2 真で抜ける *)
      replace (encL a0 a1 (a2 - a1) (2 - 1)) with (encL a0 a1 (a2 - a1) 1)
        by (f_equal; ring).
      apply L_one.
      * apply s1_at1.
      * cbn. discriminate.               (* e2=(i=1) は i=1 で真 *)
Qed.

Theorem Rloop_reversible :
  forall a0 a1 a2,
    exec Γ (invert Rloop) (encL a0 (a1 - a0) (a2 - a1) 1) (encL a0 a1 a2 2).
Proof.
  intros a0 a1 a2.
  apply (proj1 (exec_iff Γ Rloop (encL a0 a1 a2 2) (encL a0 (a1 - a0) (a2 - a1) 1))).
  apply Rloop_computes.
Qed.

End Pipe.
