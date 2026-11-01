(* Law rj_bad_dictionary, main (RDMain.v), statements 9-13: cinfo, the header bytes stream[0] and stream[1]
   (CMF, FLG with FDICT and FCHECK), dictid from stream[2..5] *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.adler32.Spec.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDLawCS.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDGlobals.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDFacts.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDKit.
Require Import Zlib.harness.rj_bad_dictionary.code.
Local Open Scope Z_scope.

Lemma seg_header_ok : seg_header_stmt.
Proof.
  intros Espec gv v_strm t1 t2 room dlen streamp src outp dictp dict K.
  unfold rd_seg9, rd_A9, POST_B, POST_rd, t_zsl. abbreviate_semax.
  Intros. rename H4 into Ns, H5 into No, H6 into Nd.
  rename H3 into H6', H2 into H5', H1 into H4', H0 into H3'.
  destruct H as (H & H0 & H1 & H2). rename H3' into H3, H4' into H4, H5' into H5, H6' into H6.
  rbd_split_call.
  forward_call t1.
  { entailer!. simpl. replace (8 + t1 - 8) with t1 by lia.
    rewrite Int.signed_repr by rep_lia. reflexivity. }
  Intros cinfo.
  forward.
  rewrite Int64.unsigned_repr by rep_lia.
  forward.
  rewrite rbd_b0_val, rbd_upd_bytes by lia.
  set (x := Znth 1 src).
  assert (Hx: 0 <= x <= 255) by (apply rbd_byte_range; auto; lia).
  assert (Z1: Znth 1 (upd_Znth 0 src (rbd_b0 cinfo)) = x) by (rewrite upd_Znth_diff by lia; reflexivity).
  forward.
  { entailer!. rewrite rbd_znth_bytes, Z1 by (rewrite Zlength_upd_Znth; lia).
    simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite rbd_znth_bytes, Z1 by (rewrite Zlength_upd_Znth; lia).
  forward.
  pose proof (rbd_f0_val x Hx) as [F0 F0r].
  change (Int.zero_ext 8 (Int.zero_ext 8 (Int.or (Int.and (Int.repr x) (Int.repr 192)) (Int.repr 32))))
    with (rbd_f0_int x).
  rewrite F0, rbd_upd_bytes.
  set (s2 := upd_Znth 1 (upd_Znth 0 src (rbd_b0 cinfo)) (rbd_f0 x)).
  assert (Hs2: Zlength s2 = 6 + t2) by (unfold s2; rewrite !Zlength_upd_Znth; lia).
  assert (S20: Znth 0 s2 = rbd_b0 cinfo)
    by (unfold s2; rewrite upd_Znth_diff, upd_Znth_same by (rewrite ?Zlength_upd_Znth; lia); reflexivity).
  assert (S21: Znth 1 s2 = rbd_f0 x) by (unfold s2; rewrite upd_Znth_same by (rewrite Zlength_upd_Znth; lia); reflexivity).
  assert (B0r: 0 <= rbd_b0 cinfo <= 255) by (unfold rbd_b0; lia).
  forward.
  { entailer!. rewrite rbd_znth_bytes, S21 by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite rbd_znth_bytes, S21 by lia.
  forward.
  { entailer!. rewrite rbd_znth_bytes, S20 by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite rbd_znth_bytes, S20 by lia.
  forward.
  { entailer!. rewrite rbd_znth_bytes, S21 by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite rbd_znth_bytes, S21 by lia.
  forward.
  { entailer!.
    assert (M: Int.repr 31 <> Int.mone) by (intro X; apply (f_equal Int.unsigned) in X; vm_compute in X; discriminate).
    match goal with |- context [Int.mods (Int.repr ?v) (Int.repr 31)] =>
      assert (Hv: 0 <= v <= 65535) by (unfold rbd_b0 in *; lia);
      assert (Hr: 0 <= Z.rem v 31 < 31) by (apply Z.rem_bound_pos; lia);
      unfold Int.mods; rewrite (Int.signed_repr v), (Int.signed_repr 31) by rep_lia end.
    split; [intros [_ X]; apply M; exact X | ]. split; [ | intros [_ X]; apply M; exact X].
    rewrite Int.signed_repr by rep_lia. rep_lia. }
  pose proof (rbd_b1_val cinfo x ltac:(lia) Hx) as [B1 B1r].
  match goal with |- context [Int.zero_ext 8 (Int.zero_ext 8 (Int.add (Int.repr (rbd_f0 x)) ?m))] =>
    change (Int.zero_ext 8 (Int.zero_ext 8 (Int.add (Int.repr (rbd_f0 x)) m))) with (rbd_b1_int cinfo x) end.
  rewrite B1, rbd_upd_bytes.
  set (s3 := upd_Znth 1 s2 (rbd_b1 cinfo x)).
  assert (Hs3: Zlength s3 = 6 + t2) by (unfold s3; rewrite !Zlength_upd_Znth; lia).
  assert (S3k: forall k, 2 <= k < 6 + t2 -> Znth k s3 = Znth k src).
  { intros k Hk. unfold s3, s2. rewrite !upd_Znth_diff by (rewrite ?Zlength_upd_Znth; lia). reflexivity. }
  assert (S30: Znth 0 s3 = rbd_b0 cinfo)
    by (unfold s3; rewrite upd_Znth_diff by (rewrite ?Zlength_upd_Znth; lia); exact S20).
  assert (S31: Znth 1 s3 = rbd_b1 cinfo x) by (unfold s3; rewrite upd_Znth_same by lia; reflexivity).
  assert (Hb3: is_bytes s3).
  { unfold s3, s2, is_bytes. repeat apply Forall_upd_Znth; auto; rep_lia. }
  assert (R3: forall k, 0 <= k < 6 + t2 -> 0 <= Znth k s3 <= 255) by (intros; apply rbd_byte_range; auto; lia).
  forward.
  { entailer!. rewrite rbd_znth_bytes by lia. pose proof (R3 2 ltac:(lia)). simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  forward.
  { entailer!. rewrite rbd_znth_bytes by lia. pose proof (R3 3 ltac:(lia)). simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  forward.
  { entailer!. rewrite rbd_znth_bytes by lia. pose proof (R3 4 ltac:(lia)). simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  forward.
  { entailer!. rewrite rbd_znth_bytes by lia. pose proof (R3 5 ltac:(lia)). simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite !rbd_znth_bytes by lia.
  forward.
  pose proof (R3 2 ltac:(lia)). pose proof (R3 3 ltac:(lia)). pose proof (R3 4 ltac:(lia)). pose proof (R3 5 ltac:(lia)).
  rewrite !Int.unsigned_repr by rep_lia.
  rewrite Zlib.proof.harness.inflate_common.HarnessLib.hl_be32_or by lia.
  change (Znth 2 s3 * 2 ^ 24 + Znth 3 s3 * 2 ^ 16 + Znth 4 s3 * 2 ^ 8 + Znth 5 s3) with (rbd_dictid s3).
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  assert (Hh: rd_hdr t1 t2 s3 cinfo x) by (unfold rd_hdr; auto 7).
  eapply semax_pre; [ | apply (K s3 cinfo x)].
  unfold rd_A14, rd_in. entailer!.
Qed.
