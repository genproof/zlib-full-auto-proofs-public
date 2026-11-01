(* case MATCH (24) v5: copy_f / copy_bytes one byte at a time (for the copy loops MtLoopW5.v, MtLoopO5.v) *)
From Coq Require Import ZArith List Lia.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Model.
Import ListNotations.
Local Open Scope Z_scope.

Lemma copy_f_S_win: forall n w i ow,
  fst (copy_f (S n) w (SWin i) ow) = fst (copy_f n w (SWin i) ow) ++ [Znth (i + Z.of_nat n) w].
Proof.
  induction n; intros w i ow.
  - simpl. rewrite Z.add_0_r. reflexivity.
  - change (copy_f (S (S n)) w (SWin i) ow) with (copy_f (S n) w (SWin (i + 1)) (ow ++ [Znth i w])).
    rewrite IHn. f_equal. f_equal. f_equal. lia.
Qed.

Lemma copy_f_S_out: forall n w i ow,
  fst (copy_f (S n) w (SOut i) ow) =
  fst (copy_f n w (SOut i) ow) ++ [Znth (i + Z.of_nat n) (fst (copy_f n w (SOut i) ow))].
Proof.
  induction n; intros w i ow.
  - simpl. rewrite Z.add_0_r. reflexivity.
  - change (copy_f (S (S n)) w (SOut i) ow) with (copy_f (S n) w (SOut (i + 1)) (ow ++ [Znth i ow])).
    rewrite IHn. change (copy_f (S n) w (SOut i) ow) with (copy_f n w (SOut (i + 1)) (ow ++ [Znth i ow])).
    f_equal. f_equal. f_equal. lia.
Qed.

Lemma copy_bytes_0: forall w sr ow, fst (copy_bytes w sr 0 ow) = ow.
Proof. intros. unfold copy_bytes. simpl. destruct sr; reflexivity. Qed.

Lemma copy_bytes_win_S: forall w i k ow, 0 <= k ->
  fst (copy_bytes w (SWin i) (k + 1) ow) = fst (copy_bytes w (SWin i) k ow) ++ [Znth (i + k) w].
Proof.
  intros. unfold copy_bytes. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r.
  rewrite copy_f_S_win. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma copy_bytes_out_S: forall w i k ow, 0 <= k ->
  fst (copy_bytes w (SOut i) (k + 1) ow) =
  fst (copy_bytes w (SOut i) k ow) ++ [Znth (i + k) (fst (copy_bytes w (SOut i) k ow))].
Proof.
  intros. unfold copy_bytes. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r.
  rewrite copy_f_S_out. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma copy_bytes_len': forall w sr c ow, 0 <= c -> Zlength (fst (copy_bytes w sr c ow)) = Zlength ow + c.
Proof.
  intros w sr c ow H. unfold copy_bytes.
  assert (forall n sr ow, Zlength (fst (copy_f n w sr ow)) = Zlength ow + Z.of_nat n) as L.
  { induction n; intros; simpl; [lia | ].
    destruct sr0; rewrite IHn, Zlength_app, Zlength_cons, Zlength_nil; lia. }
  rewrite L. lia.
Qed.

(* the output keeps its prefix *)
Lemma copy_bytes_prefix: forall w sr c ow, 0 <= c ->
  sublist 0 (Zlength ow) (fst (copy_bytes w sr c ow)) = ow.
Proof.
  intros w sr c ow H. unfold copy_bytes.
  assert (forall n sr ow, exists t, fst (copy_f n w sr ow) = ow ++ t) as L.
  { induction n; intros; simpl; [exists []; rewrite app_nil_r; reflexivity | ].
    destruct sr0 as [i | i].
    - destruct (IHn (SWin (i + 1)) (ow0 ++ [Znth i w])) as [t E]. rewrite E. eexists. rewrite <- app_assoc. reflexivity.
    - destruct (IHn (SOut (i + 1)) (ow0 ++ [Znth i ow0])) as [t E]. rewrite E. eexists. rewrite <- app_assoc. reflexivity. }
  destruct (L (Z.to_nat c) sr ow) as [t E]. rewrite E.
  pose proof (Zlength_nonneg ow). rewrite sublist_app1 by lia. apply sublist_same; lia.
Qed.

Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
#[local] Existing Instance Zlib.units.Inflate.CS.

Lemma mt_add1: forall p a, isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint (offset_val a p) (Vint (Int.repr 1))) = offset_val (a + 1) p.
Proof.
  intros p a P. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal. unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia.
  rewrite Ptrofs.mul_one. rewrite ptrofs_add_repr. reflexivity.
Qed.

Require Import Zlib.proof.zutil.Libc.

Lemma copy_bytes_bytes_out: forall w i k ow, 0 <= k -> 0 <= i < Zlength ow -> bytes_ok ow ->
  bytes_ok (fst (copy_bytes w (SOut i) k ow)).
Proof.
  intros w i k ow K I B. unfold copy_bytes.
  assert (forall n i ow, 0 <= i < Zlength ow -> bytes_ok ow -> bytes_ok (fst (copy_f n w (SOut i) ow))) as L.
  { induction n; intros j o J BO; simpl; [exact BO | ].
    apply IHn.
    - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    - unfold bytes_ok. apply Forall_app. split; [exact BO | ]. constructor; [ | constructor].
      apply (proj1 (Forall_Znth _ _) BO); lia. }
  apply L; auto.
Qed.
