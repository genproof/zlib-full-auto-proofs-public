(* Law deflate_roundtrip, the gzip run with a header (R.head_set = 1), part H16: positions 16-20 of
   b0 from AH16: the zlib dictionary block (skipped: R.wrap = 2), `if (r == Z_MEM_ERROR) return 0;` (ih's memory
   by RTRSKit.rm_head6_ret), gp_assert(r == Z_STREAM_END), gp_assert(t.avail_in == 0 && t.avail_out == 0),
   gp_assert(bytes_same(ob, R.data, R.nf)); establishes AH21.  As RTRMSeg16.v / RTRMSeg17.v. *)
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
Require Import Zlib.proof.roundtrip.RTRMSeg16 Zlib.proof.roundtrip.RTRMSeg17.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma rmh_seg16 {Espec : OracleKind} I Iend rf vR vs vt vih gv ibp obp r z1 L1 ow cont :
  (forall z' L', semax (Delta_m6 I Iend) (AH21 Iend rf vR vs vt vih gv z' L') seg21 POST_b) ->
  semax (Delta_m6 I Iend) (AH16 Iend rf vR vs vt vih gv ibp obp r z1 L1 ow cont) seg16 POST_b.
Proof.
  intros K.
  unfold seg16, AH16. Intros.
  assert (W2: rf_wrap rf = 2) by (destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HW); auto).
  rewrite rm16_open_eq. unfold rm16_open. Intros.
  unfold Delta_m6, Gm6, POST_b, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'21 (Vint Int.zero) :: Q) (SEPx R))) end.
  { lia. }
  { forward. entailer!. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx Q (SEPx R))) end.
  { contradiction. }
  { forward. entailer!. }
  sep_apply (rm16_close rf vR).
  forward_if.
  { sep_apply (rm_dside_ret Iend vR rf H). sep_apply rm_istream_ret.
    sep_apply (rm_head6_ret L1 vih H3 H4 H5).
    forward. Exists (Int.repr 0). entailer!. }
  destruct H1 as [[Hm | (Hr & Hai & Hao & How)] HG].
  { subst r. contradiction. }
  subst r ow. specialize (HG eq_refl). destruct HG as [GE HM].
  forward_call (Int.one).
  unfold istream at 1. Intros. unfold zstrm_at, strm_rep. rewrite rm_strm_cs.
  forward.
  forward_if (temp _t'22 (Vint Int.one)).
  { forward. forward. entailer!. }
  { rewrite Hai in *. contradiction. }
  forward_call (Int.one).
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
  sep_apply (rm_istream_fold gv vt z1 L1); auto.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K z1 L1) ].
  unfold AH21, rm_dside, drun_rest, obj.
  entailer!.
Qed.
