(* Law uncompress_any, main: seg_then (UAMainKit.v) up to seg_rest: the four checks of the source after
   uncompress2 returned Z_OK (slen >= 6; the zlib header bytes src[0], src[1]; no FDICT; be32(src + slen - 4) ==
   ref_adler32(1, dst, dlen)).  As inflate_check's IKMainChk1.v (the same header check) and IKMainChk2.v
   (be32 at src + pos - k). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpec5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.uncompress_any.UALawCS Zlib.proof.harness.uncompress_any.UAGlobals
               Zlib.proof.harness.uncompress_any.UAFacts.
Require Import Zlib.harness.x_uncompress_any.code.
Require Import Zlib.proof.harness.uncompress_any.UAMainKit.
Local Open Scope logic.

Lemma c1_znth src i: 0 <= i < Zlength src ->
  forall d: val, @Znth val d i (bytes_rep src) = Vint (Int.repr (Znth i src)).
Proof.
  intros R d. unfold bytes_rep, Znth. rewrite !if_false by lia.
  rewrite nth_map' with (d' := 0); [reflexivity | ]. rewrite Zlength_correct in R. lia.
Qed.

Lemma c1_byte src i: bytes_ok src -> 0 <= i < Zlength src -> 0 <= Znth i src <= Byte.max_unsigned.
Proof. intros B R. unfold bytes_ok in B. eapply Forall_Znth in B; eauto. Qed.

Lemma c1_shr b: 0 <= b <= 255 -> Z.shiftr b 4 <= 7 ->
  Int.lt (Int.repr 7) (Int.shr (Int.repr b) (Int.repr 4)) = false.
Proof.
  intros R S. unfold Int.shr. rewrite Int.signed_repr by rep_lia. rewrite (Int.unsigned_repr 4) by rep_lia.
  assert (0 <= Z.shiftr b 4) by (apply Z.shiftr_nonneg; lia).
  unfold Int.lt. rewrite !Int.signed_repr by rep_lia. destruct (zlt 7 (Z.shiftr b 4)); auto; lia.
Qed.

Lemma c1_lor b0 b1: 0 <= b1 < 256 -> Z.lor (b0 * 256) b1 = b0 * 256 + b1.
Proof.
  intros R.
  assert (L: Z.land (b0 * 256) b1 = 0).
  { assert (E: b1 = Z.land b1 (Z.ones 8)) by (rewrite Z.land_ones by lia; rewrite Z.mod_small; lia).
    rewrite E, (Z.land_comm b1), Z.land_assoc, (Z.land_ones (b0 * 256)) by lia.
    change (2 ^ 8) with 256. rewrite Z_mod_mult. apply Z.land_0_l. }
  rewrite <- Z.lxor_lor by exact L. symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

Lemma c1_hdr b0 b1: 0 <= b0 <= 255 -> 0 <= b1 <= 255 ->
  Int.modu (Int.or (Int.shl (Int.repr b0) (Int.repr 8)) (Int.repr b1)) (Int.repr 31) =
  Int.repr ((b0 * 256 + b1) mod 31).
Proof.
  intros R0 R1. unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite or_repr, c1_lor by lia.
  unfold Int.modu. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Ltac gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].

Lemma ua_chk_ok {Espec: OracleKind} gv vsnap vdlen vslen vsnap2 vdlen2 srcp src dstp snapq cap bs slen dlen out
    (Post: ret_assert) :
  ua_ok_facts srcp src dstp cap bs slen dlen out ->
  semax Delta_m (ua_okpre gv vsnap vdlen vslen vsnap2 vdlen2 srcp src dstp snapq cap bs slen dlen out) seg_rest Post ->
  semax Delta_m (ua_okpre gv vsnap vdlen vslen vsnap2 vdlen2 srcp src dstp snapq cap bs slen dlen out) seg_then Post.
Proof.
  intros MF HR.
  pose proof MF as MF'.
  destruct MF' as (Bsrc & Hn & Hcap & Hbs & Ibs & Pdst & Psrc & Hslen & Hdlen & Hdc & Bout & H6 & Hhdr & Hchk & _).
  destruct Hhdr as (G2 & G0 & G1 & G3 & G4).
  pose proof (c1_byte src 0 Bsrc ltac:(lia)) as R0.
  pose proof (c1_byte src 1 Bsrc ltac:(lia)) as R1.
  assert (B0: forall d: val, @Znth val d 0 (bytes_rep src) = Vint (Int.repr (Znth 0 src))) by (intros; rewrite c1_znth by lia; reflexivity).
  assert (B1: forall d: val, @Znth val d 1 (bytes_rep src) = Vint (Int.repr (Znth 1 src))) by (intros; rewrite c1_znth by lia; reflexivity).
  destruct Post as [Pn Pb Pc Pr].
  unfold ua_okpre, seg_then.
  abbreviate_semax.
  forward.
  forward_call (Int.repr 1).
  { entailer!. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zlt slen 6); [lia | reflexivity]. }
  forward.
  { entailer!. rewrite B0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite B0.
  ifpost _t'12 (Int.repr 1).
  { forward. { entailer!. rewrite B0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite B0. forward. entailer!. rewrite c1_shr by rep_lia. reflexivity. }
  { exfalso. rewrite and_repr, G0 in *. contradiction. }
  ifpost _t'13 (Int.repr 1).
  { forward. { entailer!. rewrite B0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    forward. { entailer!. rewrite B1. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite B0, B1. forward. entailer!. rewrite c1_hdr by rep_lia. rewrite G3. reflexivity. }
  { exfalso. apply Int.one_not_zero. assumption. }
  gpa.
  forward. { entailer!. rewrite B1. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite B1.
  forward_call (Int.repr 1).
  { entailer!. simpl. rewrite G4. reflexivity. }
  forward.
  rewrite <- (ua_bytes_adler Ews (Zlength src) (bytes_rep src) srcp).
  forward_call (offset_val (slen-4) srcp, Ews, srcp, slen-4, Zlength src, bytes_rep src, sublist (slen-4) slen src).
  { entailer!. destruct srcp; try contradiction. simpl. f_equal.
    change (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 4))) with (Ptrofs.repr 4).
    rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc; f_equal; rewrite <- Ptrofs.sub_add_opp; unfold Ptrofs.sub;
    rewrite !Ptrofs.unsigned_repr by rep_lia; reflexivity. }
  { unfold cbuf_ok. split3; [reflexivity | auto with share | ]. split3; [lia | lia | ].
    split3; [rewrite Zlength_sublist by lia; lia | apply is_bytes_sublist; auto | rewrite sublist_bytes_rep; f_equal; f_equal; lia]. }
  ua_law.
  forward.
  rewrite <- (ua_bytes_adler Ews cap (dest_after (bytes_rep bs) cap out) dstp).
  forward_call (1, dstp, Ews, dstp, 0, cap, dest_after (bytes_rep bs) cap out, dlen, out).
  { unfold cbuf_ok. split3; [rewrite isptr_offset_val_zero by auto; reflexivity | auto with share | ].
    split3; [lia | lia | ].
    split3; [lia | exact Bout | ]. unfold dest_after; rewrite Z.add_0_l. subst dlen. unfold byte_vals.
    pose proof (Zlength_nonneg out). rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
    rewrite sublist_same by (rewrite ?Zlength_map; lia). reflexivity. }
  ua_law.
  forward_call (Int.repr 1).
  { entailer!. rewrite Hchk. simpl. rewrite Int64.eq_true. reflexivity. }
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [ | exact HR].
  unfold ua_okpre. entailer!.
Qed.
