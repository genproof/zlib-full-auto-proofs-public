(* uncompress2_z for any sizes (UWSegs.v), the loop's body, part 2: when the last call left avail_in = 0, avail_in
   becomes the next piece of the source, min(len, 2^32-1) (UModelW.uw_ain), and len decreases by it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.UWSegs.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

Lemma uw_rin_body : uw_rin_stmt.
Proof.
  intros Espec A v F Pv.
  destruct A as [gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh].
  unfold uw_M1, uw_M2, uw_lcl, uw_sep, uw_fr, uw_facts, uw_rin in *.
  abbreviate_semax.
  Intros m used out z L ai ao.
  unfold istream. Intros. unfold zstrm_at, strm_rep.
  change_compspecs Zlib.units.Uncompr.CS.
  destruct H1 as (Hhd & Hls & Hlh & Had & Hmsg & Htin & Htout & Hni & Hno & Hu & Hua & Hai & Hao & Hcap & Hraw & Hsw).
  destruct F as (Hdest & Hssh & Psp & Hsn0 & Hsrc & Hsc & Hsn & Hsub & Hbytes & Hgsh & Htsh).
  unfold zf_ok in H4.
  remember (gv inflate.code._zcalloc) as zca. remember (gv inflate.code._zcfree) as zcf.
  forward.
  forward_if.
  { (* avail_in = 0: the next piece of the source *)
    rewrite H2 in *. clear H2. subst ai.
    assert (Hlen: 0 <= Zlength src - used <= Int64.max_unsigned) by rep_lia.
    forward_if (temp _t'7 (Vint (Int.repr (Z.min (Zlength src - used - 0) uw_max)))).
    { forward. entailer!. change (Int.unsigned (Int.repr (- (1)))) with uw_max in *.
      rewrite Z.min_r by lia. f_equal. apply Int.eqm_samerepr. unfold uw_max. exists 1. reflexivity. }
    { forward. entailer!. change (Int.unsigned (Int.repr (- (1)))) with uw_max in *.
      f_equal. f_equal. unfold uw_max in *; lia. }
    forward. forward. forward.
    rewrite Z.sub_0_r in *.
    assert (Ha: 0 <= Z.min (Zlength src - used) uw_max <= uw_max) by lia.
    rewrite Int.unsigned_repr, sub64_repr by (unfold uw_max in *; rep_lia).
    sep_apply (istream_fold gv v (ZF (zf_ni z) (Z.min (Zlength src - used) uw_max) (zf_tin z) (zf_no z)
                 (zf_ao z) (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z)) L zca zcf);
      [unfold zf_ok; simpl; unfold uw_max in *; rep_lia |].
    Exists m used out (ZF (zf_ni z) (Z.min (Zlength src - used) uw_max) (zf_tin z) (zf_no z)
                 (zf_ao z) (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z)) L 0 ao.
    rewrite uw_ain_z.
    entailer!.
    unfold uw_sfacts; cbn [zf_ni zf_no zf_adler zf_msg zf_tin zf_tout]. tauto. }
  { (* avail_in <> 0: the rest of the last piece stays *)
    forward.
    sep_apply (istream_fold gv v z L zca zcf).
    Exists m used out z L ai ao.
    rewrite uw_ain_nz by lia.
    entailer!.
    unfold uw_sfacts. tauto. }
Qed.
