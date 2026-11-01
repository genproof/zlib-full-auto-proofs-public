(* RT-I part rti_gz_pass: dctx_ok of deflate_roundtrip's gzip stream *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Require Import Zlib.proof.roundtrip.RTIGzPassDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma gpc_bval_range l : 0 <= bval l < 2 ^ Zlength l.
Proof.
  induction l as [|b r IH]; simpl.
  - rewrite ?Zlength_nil. simpl. lia.
  - rewrite Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg r); lia).
    destruct b; simpl; lia.
Qed.

Lemma gpc_pack_ok bs : Forall (fun b => 0 <= b < 256) (pack bs).
Proof.
  unfold pack. apply Forall_map, Forall_forall. intros k _.
  set (l := sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs). pose proof (gpc_bval_range l).
  assert (Zlength l <= 8).
  { unfold l, sublist. rewrite Zlength_correct, length_skipn, length_firstn. lia. }
  assert (2 ^ Zlength l <= 2 ^ 8) by (apply Z.pow_le_mono_r; [lia | pose proof (Zlength_nonneg l); lia]).
  unfold Basics.compose; cbv beta; fold l. change (2 ^ 8) with 256 in *. lia.
Qed.

Lemma gpc_le_ok v n : Forall (fun b => 0 <= b < 256) (le_bytes v n).
Proof.
  unfold le_bytes. apply Forall_map, Forall_forall. intros i _.
  pose proof (Z.mod_pos_bound (Z.shiftr v (8 * Z.of_nat i)) 256 ltac:(lia)). unfold Basics.compose; cbv beta. lia.
Qed.

Lemma gpc_gz_ok gh xfl : (forall g, gh = Some g -> RF.rhdr_ok g) -> (xfl = 0 \/ xfl = 2 \/ xfl = 4) ->
  gz_ok (RF.fhdr_of gh xfl).
Proof.
  intros HG HX. destruct gh as [g|].
  2:{ unfold gz_ok, RF.fhdr_of; simpl. unfold byte_ok. repeat split; try lia; exact I. }
  destruct (HG g eq_refl) as (_ & _ & HOS & HT & HE & HXB & HN & HC).
  unfold gz_ok, RF.fhdr_of; simpl. unfold byte_ok. split; [change (2 ^ 32) with 4294967296; lia|].
  split; [lia|]. split.
  { rewrite (Z.land_ones _ 8) by lia. change (2 ^ 8) with 256.
    pose proof (Z.mod_pos_bound (DS.gz_os g) 256 ltac:(lia)). lia. }
  split; [|split].
  - destruct (DS.gz_extra g) as [x|] eqn:EX; cbn; [|exact I].
    destruct (HXB x eq_refl) as (L & B).
    assert (E: firstn (Z.to_nat (RF.DS.gz_extra_len g)) x = x) by (rewrite <- L, Zlength_correct, Nat2Z.id; apply firstn_all).
    rewrite E. split; [lia|exact B].
  - destruct (DS.gz_name g) as [l|] eqn:EN; cbn; [|exact I].
    destruct (HN l eq_refl) as (l0 & -> & _ & B). rewrite removelast_last. exact B.
  - destruct (DS.gz_comment g) as [l|] eqn:EN; cbn; [|exact I].
    destruct (HC l eq_refl) as (l0 & -> & _ & B). rewrite removelast_last. exact B.
Qed.

Lemma gpc_gz_bytes h : gz_ok h -> Forall (fun b => 0 <= b < 256) (gz_bytes h).
Proof.
  intros (HT & HX & HO & HE & HN & HC). unfold byte_ok in *.
  assert (B0: Forall (fun b => 0 <= b < 256) (gz_bytes0 h)).
  { unfold gz_bytes0. rewrite !Forall_app. repeat split.
    - assert (0 <= gz_flg h <= 31) by (unfold gz_flg; destruct (gz_text h), (gz_hcrc h), (gz_extra h),
        (gz_name h), (gz_comment h); lia).
      repeat constructor; lia.
    - apply gpc_le_ok.
    - repeat constructor; lia.
    - destruct (gz_extra h) as [x|]; [|constructor]. apply Forall_app. split; [apply gpc_le_ok|].
      eapply Forall_impl; [|apply HE]. unfold byte_ok. intros; lia.
    - destruct (gz_name h) as [x|]; [|constructor]. apply Forall_app. split; [|repeat constructor; lia].
      eapply Forall_impl; [|apply HN]. cbv beta. intros; lia.
    - destruct (gz_comment h) as [x|]; [|constructor]. apply Forall_app. split; [|repeat constructor; lia].
      eapply Forall_impl; [|apply HC]. cbv beta. intros; lia. }
  unfold gz_bytes. destruct (gz_hcrc h); [|exact B0]. apply Forall_app. split; [exact B0 | apply gpc_le_ok].
Qed.

Lemma gp_dctx_ok : gp_dctx_stmt.
Proof.
  intros gh xfl wb bs D O HW HWF HD HX HO HG HDL HOL.
  pose proof (gpc_gz_ok gh xfl HG HX) as GZ.
  assert (BO: Forall (fun b => 0 <= b < 256) O).
  { rewrite HO. unfold stream_bytes. rewrite !Forall_app. repeat split.
    - apply gpc_gz_bytes, GZ.
    - apply gpc_pack_ok.
    - apply gpc_le_ok.
    - apply gpc_le_ok. }
  assert (SL: slen (gz_ctx gh xfl wb bs O) = Zlength O).
  { unfold slen. cbn [dc_w dc_hist dc_bs gz_ctx]. rewrite HO. reflexivity. }
  unfold dctx_ok. rewrite SL. cbn [dc_w dc_wb dc_hist dc_bs dc_iw dc_src gz_ctx].
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - unfold stream_ok, wrapper_ok. split; [lia|]. split; [split; [exact GZ | reflexivity]|]. split; [exact I|exact HWF].
  - unfold accepts. cbn. right. reflexivity.
  - intros; exact I.
  - intros. discriminate.
  - lia.
  - change (2 ^ 31 - 1) with 2147483647. lia.
  - unfold bytes_ok. eapply Forall_impl; [|exact BO]. intros a Ha. cbv beta in Ha. change Integers.Byte.max_unsigned with 255. lia.
  - rewrite sublist_same by lia. exact HO.
Qed.
