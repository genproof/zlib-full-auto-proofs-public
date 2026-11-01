(* Law deflate_roundtrip, main (kit: RTRMKit.v): positions 17-23 of b0 without a gzip header:
   `if (r == Z_MEM_ERROR) return 0;`, gp_assert(r == Z_STREAM_END), gp_assert(t.avail_in == 0 && t.avail_out == 0),
   gp_assert(bytes_same(ob, R.data, R.nf)) (fin_ok: ow = D = data[0..nf)), the header checks skipped
   (R.head_set = 0), inflateEnd(&t), return 0 (main's locals: rm_dside_ret, rm_istream_ret). *)
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
Require Import Zlib.harness.x_deflate_roundtrip.code.
Require Import Zlib.proof.roundtrip.RTRMKit.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma rm_bytes_is l : bytes l -> is_bytes l.
Proof. unfold bytes, is_bytes. intros Hb. eapply Forall_impl; [ | exact Hb]. intros; simpl in *; rep_lia. Qed.

Lemma rm_istream_fold gv vt z L :
  zf_ok z -> live_ok L ->
  @data_at CS Tsh t_strmL
    (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
     (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (l_sp L, (gv Zlib.inflate.code._zcalloc,
     (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)),
     (Vlong (Int64.repr (zf_adler z)), zf_res z))))))))))))) vt * state_mem gv vt L
  |-- istream gv Tsh vt z (Some L).
Proof.
  intros. unfold istream, zstrm_at, Zlib.proof.inflate.Rep.strm_rep. rewrite rm_strm_cs. entailer!.
Qed.

Lemma rm_dside_ret_flat Iend vR rf : rf_ok Iend vR rf ->
  ltac:(let t := eval cbv beta zeta delta [rm_dside drun_rest obj] in (rm_dside rf vR) in
        exact (t |-- data_at_ Tsh t_drun vR * TT)).
Proof. intros OK. apply (rm_dside_ret Iend vR rf OK). Qed.

Lemma rm_seg17 {Espec : OracleKind} I Iend rf vR vs vt vih gv ibp obp r z1 L1 ow cont :
  semax (Delta_m I Iend) (A17 Iend rf vR vs vt vih gv ibp obp r z1 L1 ow cont) seg17 POST_b.
Proof.
  unfold seg17, A17, POST_b.
  Intros.
  unfold Delta_m, Gm5, POST_m. simplify_func_tycontext.
  forward_if.
  { sep_apply (rm_dside_ret Iend vR rf H). sep_apply rm_istream_ret.
    forward. Exists (Int.repr 0). entailer!. }
  destruct H1 as [Hm | (Hr & Hai & Hao & How)].
  { subst r. contradiction H3. reflexivity. }
  subst r ow.
  forward_call (Int.one).
  unfold istream at 1. Intros. unfold zstrm_at, strm_rep. rewrite rm_strm_cs.
  forward.
  forward_if (temp _t'22 (Vint Int.one)).
  { forward. forward. entailer!. }
  { rewrite Hai in *. contradiction. }
  forward_call (Int.one).
  (* bytes_same(ob, R.data, R.nf) *)
  pose proof H as (RS & _ & _ & _ & Hnf & _).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HdL & _ & _ & _ & _ &
                    Hbd & _ & _ & _ & _ & Hpd & _).
  assert (HD : Zlength (rm_D rf) = rf_nf rf) by (unfold rm_D; rewrite Zlength_sublist; lia).
  unfold rm_dside, drun_rest, obj. Intros.
  forward. forward.
  unfold out_rep, rm_ob. rewrite HD, sublist_nil, Z.add_0_l, sublist_nil, app_nil_l, app_nil_r.
  assert_PROP (isptr obp) as Hob.
  { sep_apply (data_at_local_facts Ews (tarray tuchar (rf_nf rf)) (byte_vals (rm_D rf)) obp). entailer!. }
  rewrite (bytes_cs Zlib.units.Inflate.CS Zlib.units.Adler32.CS Ews (rf_nf rf) _ obp).
  rewrite (bytes_cs CS Zlib.units.Adler32.CS Ews (Zlength (rs_data (rf_rs rf))) _ (rs_datap (rf_rs rf))).
  assert (HDb : bytes (rm_D rf)) by (unfold rm_D; apply Forall_sublist; auto).
  assert (CB1 : cbuf_ok false obp Ews obp 0 (rf_nf rf) (rf_nf rf) (byte_vals (rm_D rf)) (rm_D rf)).
  { unfold cbuf_ok. rewrite isptr_offset_val_zero by auto. split3; [ reflexivity | auto with share | ].
    split3; [ lia | lia | ]. split3; [ lia | apply rm_bytes_is; auto | ].
    rewrite sublist_same by (unfold byte_vals; rewrite ?Zlength_map; lia). reflexivity. }
  assert (CB2 : cbuf_ok false (rs_datap (rf_rs rf)) Ews (rs_datap (rf_rs rf)) 0 (Zlength (rs_data (rf_rs rf)))
                  (rf_nf rf) (map vi (rs_data (rf_rs rf))) (rm_D rf)).
  { unfold cbuf_ok. rewrite isptr_offset_val_zero by auto. split3; [ reflexivity | auto with share | ].
    split3; [ lia | lia | ]. split3; [ lia | apply rm_bytes_is; auto | ].
    rewrite sublist_map. reflexivity. }
  forward_call (obp, Ews, obp, 0, rf_nf rf, byte_vals (rm_D rf), rm_D rf,
                rs_datap (rf_rs rf), Ews, rs_datap (rf_rs rf), 0, Zlength (rs_data (rf_rs rf)),
                map vi (rs_data (rf_rs rf)), rm_D rf, rf_nf rf).
  rewrite if_true by auto.
  forward_call (Int.one).
  rewrite <- (bytes_cs Zlib.units.Inflate.CS Zlib.units.Adler32.CS Ews (rf_nf rf) _ obp).
  rewrite <- (bytes_cs CS Zlib.units.Adler32.CS Ews (Zlength (rs_data (rf_rs rf))) _ (rs_datap (rf_rs rf))).
  (* the header checks: R.head_set = 0 *)
  forward.
  forward_if (temp _t'31 (vi (rf_hset rf))).
  { rewrite H0 in *. contradiction. }
  { forward. entailer!. }
  sep_apply (rm_istream_fold gv vt z1 L1); auto.
  assert_PROP (isptr vt) as Hvt by entailer!.
  forward_call (gv, Tsh, vt, z1, Some L1).
  { unfold istream_opt. rewrite if_false by (destruct vt; try contradiction; discriminate). cancel. }
  unfold istream_opt. rewrite if_false by (destruct vt; try contradiction; discriminate).
  sep_apply (rm_dside_ret_flat Iend vR rf H). sep_apply rm_istream_ret.
  forward. Exists (Int.repr 0). entailer!.
Qed.
