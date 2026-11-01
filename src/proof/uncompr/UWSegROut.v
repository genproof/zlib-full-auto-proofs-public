(* uncompress2_z for any sizes (UWSegs.v), the loop's body, part 1: when the last call left avail_out = 0,
   avail_out becomes the next piece of the destination, min(left, 2^32-1) (UModelW.uw_aout), and left decreases by
   it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.UWSegs.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

Lemma uw_rout_body : uw_rout_stmt.
Proof.
  intros Espec A v F Pv.
  destruct A as [gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh].
  unfold uw_inv, uw_M1, uw_lcl, uw_sep, uw_fr, uw_facts, uw_rout in *.
  abbreviate_semax.
  Intros m used out z L ai ao.
  unfold istream. Intros. unfold zstrm_at, strm_rep.
  change_compspecs Zlib.units.Uncompr.CS.
  forward.
  unfold uw_sfacts in H1.
  destruct H1 as (Hhd & Hls & Hlh & Had & Hmsg & Htin & Htout & Hni & Hno & Hu & Hua & Hai & Hao & Hoc & Hraw & Hsw).
  destruct F as (Hdest & _).
  assert (Hcap: 0 <= cap <= Int64.max_unsigned) by (destruct dnull; destruct Hdest as (? & ? & ? & ?); rep_lia).
  pose proof (Zlength_nonneg out).
  remember (gv inflate.code._zcalloc) as zca. remember (gv inflate.code._zcfree) as zcf.
  unfold uw_max in *.
  forward_if.
  2: { (* avail_out <> 0: nothing changes, uw_aout keeps what the last call left *)
    forward.
    sep_apply (istream_fold gv v z L zca zcf).
    Exists m used out z L ai ao.
    rewrite uw_aout_nz by lia. unfold uw_sfacts, uw_max. entailer!. }
  (* avail_out = 0: the next piece, min(left, max); left decreases by it *)
  forward_if (temp _t'6 (Vint (Int.repr (Z.min (cap - Zlength out) 4294967295)))).
  { change (Int.unsigned (Int.neg (Int.repr 1))) with 4294967295 in *. forward. entailer!.
    rewrite Z.min_r by lia. f_equal; apply Int.eqm_samerepr; exists 1; reflexivity. }
  { change (Int.unsigned (Int.neg (Int.repr 1))) with 4294967295 in *. forward. entailer!.
    rewrite H7, Z.sub_0_r, Z.min_l by lia. reflexivity. }
  forward. forward. forward.
  assert (Hz: ao = 0) by lia. subst ao.
  set (p := Z.min (cap - Zlength out) 4294967295).
  assert (Hp: 0 <= p <= 4294967295 /\ p <= cap - Zlength out) by (subst p; lia).
  rewrite Int.unsigned_repr by rep_lia. rewrite sub64_repr.
  sep_apply (istream_fold gv v (ZF (zf_ni z) (zf_ai z) (zf_tin z) (zf_no z) p (zf_tout z) (zf_msg z) (zf_dt z)
                                  (zf_adler z) (zf_res z)) L zca zcf);
    [unfold zf_ok in *; simpl; rep_lia |].
  assert (Ha: uw_aout cap out (zf_ao z) = p) by (rewrite Hz; reflexivity).
  Exists m used out (ZF (zf_ni z) (zf_ai z) (zf_tin z) (zf_no z) p (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z)
                        (zf_res z)) L ai (zf_ao z).
  rewrite Ha, Hz, Z.sub_0_r. rewrite Hz in H. unfold uw_sfacts, uw_max.
  cbn [zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt zf_adler zf_res]. entailer!.
Qed.
