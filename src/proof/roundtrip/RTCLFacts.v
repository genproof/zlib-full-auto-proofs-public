(* Law compress_roundtrip, part RT-CL: pure facts main needs: the zlib stream of RTFinal.dfinal consists of
   bytes (uncompress's precondition bytes_ok).  As RTUTheory.v's rtu_bytes_* (not a dependency of this law). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Zlib.proof.rfc1951.Format.
Require Import Zlib.proof.zutil.Libc.
Require Zlib.proof.roundtrip.RTFinal.
Import ListNotations.
Local Open Scope Z_scope.

Module RF := Zlib.proof.roundtrip.RTFinal.
Module FM := Zlib.proof.rfc1951.Format.

Lemma rtcl_bval_range (l: list bool) : 0 <= FM.bval l < 2 ^ Zlength l.
Proof.
  induction l as [|b r IH]; [cbn; lia|].
  cbn [FM.bval]. rewrite Zlength_cons, Z.pow_succ_r by (apply Zlength_nonneg). destruct b; cbn [Z.b2z]; lia.
Qed.

Lemma rtcl_len_sublist {A: Type} (lo hi: Z) (l: list A) : 0 <= lo <= hi -> Zlength (sublist lo hi l) <= hi - lo.
Proof.
  intros H. unfold sublist. rewrite Zlength_correct, skipn_length, firstn_length. lia.
Qed.

Lemma rtcl_bytes_pack (bs: list bool) : bytes_ok (FM.pack bs).
Proof.
  unfold FM.pack, bytes_ok. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (k & <- & _).
  set (l := sublist _ _ bs).
  assert (Zlength l <= 8)
    by (unfold l; pose proof (rtcl_len_sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs ltac:(lia)); lia).
  pose proof (rtcl_bval_range l). pose proof (Z.pow_le_mono_r 2 (Zlength l) 8 ltac:(lia) ltac:(lia)).
  change (2 ^ 8) with 256 in *. rep_lia.
Qed.

Lemma rtcl_bytes_be (v n: Z) : bytes_ok (FM.be_bytes v n).
Proof.
  unfold FM.be_bytes, FM.le_bytes, bytes_ok. apply Forall_rev. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as (i & <- & _).
  pose proof (Z.mod_pos_bound (Z.shiftr v (8 * Z.of_nat i)) 256 ltac:(lia)). rep_lia.
Qed.

Lemma rtcl_dfinal_bytes D O : RF.dfinal [] 1 15 None D O -> bytes_ok O.
Proof.
  intros (_ & bs & _ & _ & Hw). cbn iota in Hw. destruct Hw as (_ & flg & FO & EO).
  rewrite EO. unfold bytes_ok. destruct FO as (F1 & _).
  apply (proj2 (Forall_app _ _ _)); split; [repeat constructor; unfold RF.zcmf; rep_lia|].
  apply (proj2 (Forall_app _ _ _)); split; [constructor|].
  apply (proj2 (Forall_app _ _ _)); split; [apply rtcl_bytes_pack | apply rtcl_bytes_be].
Qed.
