(* uncompress2_z with a Z_NULL source of length 0 (UWNSegs.v), the loop's body, parts 1 and 2: when the last call
   left avail_out = 0, avail_out becomes the next piece of the destination, min(left, 2^32-1) (UModelW.uw_aout),
   and left decreases by it; avail_in, always 0, gets the next piece of the empty source, 0.  The scripts are
   UWSegROut.v's and UWSegRIn.v's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr.
Require Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.UWNSegs.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

Lemma un_rout_body : un_rout_stmt.
Proof.
  intros Espec A v F Pv.
  destruct A as [gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh].
  unfold un_inv, un_M1, un_lcl, un_sep, un_fr, un_facts, uw_rout in *.
  abbreviate_semax.
  Intros m out z L ao.
  unfold istream. Intros. unfold zstrm_at, strm_rep.
  change_compspecs Zlib.units.Uncompr.CS.
  forward.
  unfold un_sfacts in H1.
  destruct H1 as (Hhd & Hls & Hlh & Had & Hmsg & Htin & Htout & Hni & Hno & Hao & Hoc & Hraw & Hsw).
  destruct F as (Hdest & _).
  assert (Hcap: 0 <= cap <= Int64.max_unsigned) by (destruct dnull; destruct Hdest as (? & ? & ? & ?); rep_lia).
  pose proof (Zlength_nonneg out).
  remember (gv inflate.code._zcalloc) as zca. remember (gv inflate.code._zcfree) as zcf.
  unfold uw_max in *.
  forward_if.
  2: { (* avail_out <> 0: nothing changes, uw_aout keeps what the last call left *)
    forward.
    sep_apply (istream_fold gv v z L zca zcf).
    Exists m out z L ao.
    rewrite uw_aout_nz by lia. unfold un_sfacts, uw_max. entailer!. }
  (* avail_out = 0: the next piece, min(left, max); left decreases by it *)
  forward_if (temp _t'6 (Vint (Int.repr (Z.min (cap - Zlength out) 4294967295)))).
  { change (Int.unsigned (Int.neg (Int.repr 1))) with 4294967295 in *. forward. entailer!.
    rewrite Z.min_r by lia. f_equal; apply Int.eqm_samerepr; exists 1; reflexivity. }
  { change (Int.unsigned (Int.neg (Int.repr 1))) with 4294967295 in *. forward. entailer!.
    match goal with Hx: zf_ao z = 0 |- _ => rewrite Hx end. rewrite Z.sub_0_r, Z.min_l by lia. reflexivity. }
  forward. forward. forward.
  assert (Hz: ao = 0) by lia. subst ao.
  set (p := Z.min (cap - Zlength out) 4294967295).
  assert (Hp: 0 <= p <= 4294967295 /\ p <= cap - Zlength out) by (subst p; lia).
  rewrite Int.unsigned_repr by rep_lia. rewrite sub64_repr.
  sep_apply (istream_fold gv v (ZF (zf_ni z) (zf_ai z) (zf_tin z) (zf_no z) p (zf_tout z) (zf_msg z) (zf_dt z)
                                  (zf_adler z) (zf_res z)) L zca zcf);
    [unfold zf_ok in *; simpl; rep_lia |].
  assert (Ha: uw_aout cap out (zf_ao z) = p) by (rewrite Hz; reflexivity).
  Exists m out (ZF (zf_ni z) (zf_ai z) (zf_tin z) (zf_no z) p (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z)
                   (zf_res z)) L (zf_ao z).
  rewrite Ha, Hz, Z.sub_0_r. rewrite Hz in H. unfold un_sfacts, uw_max.
  cbn [zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt zf_adler zf_res]. entailer!.
Qed.

Lemma un_rin_body : un_rin_stmt.
Proof.
  intros Espec A v F Pv.
  destruct A as [gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh].
  unfold un_M1, un_lcl, un_sep, un_fr, un_facts, uw_rin in *.
  abbreviate_semax.
  Intros m out z L ao.
  unfold istream. Intros. unfold zstrm_at, strm_rep.
  change_compspecs Zlib.units.Uncompr.CS.
  remember (gv inflate.code._zcalloc) as zca. remember (gv inflate.code._zcfree) as zcf.
  forward.
  forward_if.
  { (* avail_in = 0: the next piece of the empty source, 0 *)
    forward_if (temp _t'7 (Vint (Int.repr 0))).
    { pose proof (Int.unsigned_range (Int.neg (Int.repr 1))). lia. }
    { forward. entailer!. }
    forward. forward. forward.
    rewrite Int.unsigned_repr, sub64_repr by rep_lia.
    sep_apply (istream_fold gv v (ZF (zf_ni z) 0 (zf_tin z) (zf_no z) (zf_ao z) (zf_tout z) (zf_msg z) (zf_dt z)
                                  (zf_adler z) (zf_res z)) L zca zcf);
      [unfold zf_ok in *; simpl; rep_lia |].
    Exists m out (ZF (zf_ni z) 0 (zf_tin z) (zf_no z) (zf_ao z) (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z)
                     (zf_res z)) L ao.
    unfold un_sfacts in *. cbn [zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt zf_adler zf_res].
    entailer!. tauto. }
  { (* avail_in <> 0: impossible *)
    match goal with Hx: zf_ai z = 0 |- _ => rewrite Hx in * end. contradiction. }
Qed.
