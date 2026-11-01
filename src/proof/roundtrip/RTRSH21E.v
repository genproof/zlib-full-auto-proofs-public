(* Law deflate_roundtrip (gzip header, part H21): the memory of RTRSH21.rmh_seg21 as entailments: from AH21 to the
   state of the header checks (A0 / PH21: R->h, the fields of R main reads, ih and the buffers, R's objects at the
   compspecs of bytes_same; the rest framed as F1..F4), and from PH21 back to the locals' memory at the return
   (PT21, in RTRSH21T.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec Zlib.proof.roundtrip.RTRRunKit Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRMainSpec.
Require Import Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.proof.roundtrip.RTHSpec Zlib.proof.roundtrip.RTHIfDefs.
Require Import Zlib.harness.x_deflate_roundtrip.code.
Require Import Zlib.proof.roundtrip.RTRMKit Zlib.proof.roundtrip.RTRSKit.
Require Zlib.proof.uncompr.URunFrame.
Require Import Zlib.proof.roundtrip.RTRSH21Kit.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

(* the fields of struct drun main does not read in the header checks, the padding and main's half of R *)
Definition RR21 (rf : rfinal) (vR : val) : mpred :=
  let rs := rf_rs rf in
  field_at Ews t_drun (DOT _level) (vi (rs_level rs)) vR *
  field_at Ews t_drun (DOT _method) (vi (rs_method rs)) vR *
  field_at Ews t_drun (DOT _wbits) (vi (rs_wbits rs)) vR *
  field_at Ews t_drun (DOT _mem) (vi (rs_mem rs)) vR *
  field_at Ews t_drun (DOT _strategy) (vi (rs_strategy rs)) vR *
  field_at Ews t_drun (DOT _init) (vi 0) vR *
  field_at Ews t_drun (DOT _wrap) (vi (rf_wrap rf)) vR *
  field_at Ews t_drun (DOT _wb) (vi (wb_of (rs_wbits rs))) vR *
  field_at Ews t_drun (DOT _data) (rs_datap rs) vR *
  field_at Ews t_drun (DOT _n) (vi (Zlength (rs_data rs))) vR *
  field_at Ews t_drun (DOT _nf) (vi (rf_nf rf)) vR *
  field_at Ews t_drun (DOT _dict) (rs_dictp rs) vR *
  field_at Ews t_drun (DOT _dlen) (vi (Zlength (rs_dict rs))) vR *
  field_at Ews t_drun (DOT _dict_set) (vi (rf_dset rf)) vR *
  field_at Ews t_drun (DOT _comp) (rs_compp rs) vR *
  field_at Ews t_drun (DOT _clen) (vl (Zlength (rf_O rf))) vR *
  field_at Ews t_drun (DOT _ended) (vi 1) vR *
  field_at Ews t_drun (DOT _api_ok) (vi 1) vR *
  drun_pad vR * data_at_ (Share.comp Ews) t_drun vR.

Definition F1_21 (gv : globals) (vt : val) (z1 : zfields) (L1 : live) : mpred := istream gv Tsh vt z1 (Some L1).
Definition F3_21 (gv : globals) (vs : val) : mpred := data_at_ Tsh t_strmL vs * mem_mgr gv * zfuncs gv.

(* before the header checks *)
Definition A0_21 (rf : rfinal) (vR vs vt vih : val) (gv : globals) (z1 : zfields) (L1 : live)
    (v3 v7 v9 v11 v13 : val) : environ -> mpred :=
  let rs := rf_rs rf in
  PROP (PH21_ok rs (l_xb L1) (l_nb L1) (l_cb L1); rf_hset rf = 1)
  LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih; gvars gv)
  SEP (field_at Ews t_drun (DOT _h)
         (vi (Z.land (rs_text rs) 1), (vl (rs_mtime rs), (v3, (vi (rs_os rs), (rs_xfp rs,
          (vi (Zlength (rs_xf rs)), (v7, (rs_nfp rs, (v9, (rs_cfp rs, (v11, (vi (Z.land (rs_hcrc rs) 1),
           v13)))))))))))) vR;
       field_at Ews t_drun (DOT _xf) (rs_xfp rs) vR;
       field_at Ews t_drun (DOT _nf_) (rs_nfp rs) vR;
       field_at Ews t_drun (DOT _cf) (rs_cfp rs) vR;
       field_at Ews t_drun (DOT _xlen) (vi (Zlength (rs_xf rs))) vR;
       field_at Ews t_drun (DOT _nl) (vi (Zlength (rs_nm rs))) vR;
       field_at Ews t_drun (DOT _cl) (vi (Zlength (rs_cm rs))) vR;
       data_at Tsh t_gzhL
         (Vint (Int.repr (Z.land (rs_text rs) 1)), (Vlong (Int64.repr (rs_mtime rs)),
          (Vint (Int.repr (h_xflags (l_h L1))),
          (Vint (Int.repr (rs_os rs)), (l_xb L1, (Vint (Int.repr (Zlength (rs_xf rs))),
          (Vint (Int.repr (Zlength (rs_xf rs))), (l_nb L1, (Vint (Int.repr (Zlength (rs_nm rs) + 1)), (l_cb L1,
          (Vint (Int.repr (Zlength (rs_cm rs) + 1)), (Vint (Int.repr (Z.land (rs_hcrc rs) 1)),
           Vint (Int.repr 1))))))))))))) vih;
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (rs_xf rs))) (byte_vals (rs_xf rs)) (l_xb L1);
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (rs_xf rs))) (map vi (rs_xf rs)) (rs_xfp rs);
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (rs_nm rs) + 1)) (byte_vals (rs_nm rs ++ [0]))
         (l_nb L1);
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (rs_nm rs) + 1)) (map vi (rs_nm rs ++ [0]))
         (rs_nfp rs);
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (rs_cm rs) + 1)) (byte_vals (rs_cm rs ++ [0]))
         (l_cb L1);
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (rs_cm rs) + 1)) (map vi (rs_cm rs ++ [0]))
         (rs_cfp rs);
       field_at Ews t_drun (DOT _head_set) (vi 1) vR;
       F1_21 gv vt z1 L1; RR21 rf vR; F3_21 gv vs; TT).

Lemma rmh_E1 Delta Iend rf vR vs vt vih gv z1 L1 :
  ENTAIL Delta, AH21 Iend rf vR vs vt vih gv z1 L1 |--
    @exp (environ -> mpred) _ val (fun v3 => @exp (environ -> mpred) _ val (fun v7 =>
    @exp (environ -> mpred) _ val (fun v9 => @exp (environ -> mpred) _ val (fun v11 =>
    @exp (environ -> mpred) _ val (fun v13 => A0_21 rf vR vs vt vih gv z1 L1 v3 v7 v9 v11 v13))))).
Proof.
  unfold AH21. Intros.
  destruct H1 as (Hdone & Htext & Htime & Hos & Hhcrc & Hxl & Hxb & Hnb & Hcb & Hxp & Hnp & Hcp).
  pose proof H as (RS & _ & _ & _ & Hnf & _ & _ & Hh & _).
  destruct Hh as [(_ & Hghp & Hgz) | (Hh0 & _)]; [ | lia].
  assert_PROP (live_ok L1) as HL. { unfold istream. Intros. entailer!. }
  pose proof HL as (_ & _ & _ & HW & _ & _ & _ & Hbufs & _).
  destruct (Hbufs H3) as (Hxb0 & Hnb0 & Hcb0).
  specialize (Hxb0 Hxp). specialize (Hnb0 Hnp). specialize (Hcb0 Hcp).
  destruct HW as [_ _ _ _ _ _ _ _ [Hxw _] [Hnw _] [Hcw _] _ _].
  sep_apply (head_mem6_spec5 L1 H2). unfold head_mem. rewrite H3, H4, H5.
  unfold head_rep. rewrite Hxp, Hnp, Hcp. rewrite (rm_head_cs Tsh).
  unfold hbuf_rep. rewrite !if_false by auto.
  unfold rm_dside, drun_rest, obj. Intros.
  unfold hdr_at, hx_of. rewrite Hgz, Hghp, H0. change (hpart 1 vR) with (gzh_pad (hp_of vR)).
  sep_apply (rmh_h_fold (hdr_of (rf_rs rf)) (rs_xfp (rf_rs rf)) (rs_nfp (rf_rs rf)) (rs_cfp (rf_rs rf)) vR).
  Intros v3 v7 v9 v11 v13.
  unfold opt_obj, hdr_of; cbn [gz_extra gz_name gz_comment gz_text gz_time gz_os gz_extra_len gz_hcrc]. Intros.
  unfold hdr_of in Htext, Htime, Hos, Hhcrc, Hxl;
    cbn [DS.gz_text DS.gz_time DS.gz_os DS.gz_hcrc DS.gz_extra_len] in Htext, Htime, Hos, Hhcrc, Hxl.
  rewrite <- Hxw, <- Hnw, <- Hcw, Hxb, Hnb, Hcb, Hdone, Htext, Htime, Hos, Hhcrc, Hxl.
  unfold rm_x, rm_nm, rm_cm.
  set (rs := rf_rs rf) in *.
  rewrite (bytes_cs Zlib.units.Inflate.CS Zlib.units.Adler32.CS Ews (Zlength (rs_xf rs)) _ (l_xb L1)).
  rewrite (bytes_cs Zlib.units.Inflate.CS Zlib.units.Adler32.CS Ews (Zlength (rs_nm rs ++ [0])) _ (l_nb L1)).
  rewrite (bytes_cs Zlib.units.Inflate.CS Zlib.units.Adler32.CS Ews (Zlength (rs_cm rs ++ [0])) _ (l_cb L1)).
  rewrite (bytes_cs DCS.CS Zlib.units.Adler32.CS Ews (Zlength (rs_xf rs)) _ (rs_xfp rs)).
  rewrite (bytes_cs DCS.CS Zlib.units.Adler32.CS Ews (Zlength (rs_nm rs ++ [0])) _ (rs_nfp rs)).
  rewrite (bytes_cs DCS.CS Zlib.units.Adler32.CS Ews (Zlength (rs_cm rs ++ [0])) _ (rs_cfp rs)).
  assert_PROP (isptr (l_xb L1) /\ isptr (l_nb L1) /\ isptr (l_cb L1)) as Pxnc.
  { entailer!. repeat split; match goal with H : field_compatible _ _ ?p |- isptr ?p => exact (proj1 H) end. }
  destruct Pxnc as (Px & Pn & Pc).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hxl4 & Hnl4 & Hcl4 &
                    _ & _ & _ & _ & _ & _ & _ & Pxf & Pnf & Pcf & _).
  rewrite !rmh_nz0.
  Exists v3 v7 v9 v11 v13. unfold A0_21, F1_21, RR21, F3_21.
  entailer!.
  split3; auto.
Qed.
