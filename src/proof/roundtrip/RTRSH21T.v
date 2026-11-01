(* Law deflate_roundtrip (gzip header, part H21): the end of b0: the locals' memory after the header checks
   (PH21 -> PT21), inflateEnd(&t); return 0. *)
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
Require Import Zlib.proof.roundtrip.RTRSH21Kit Zlib.proof.roundtrip.RTRSH21E.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma rmh_tail {Espec : OracleKind} I Iend vR vs vt vih gv z1 L1 :
  semax (Delta_m6 I Iend) (PT21 vR vs vt vih gv z1 L1) tail21 POST_b.
Proof.
  unfold PT21, tail21, POST_b.
  unfold Delta_m6, Gm6, POST_m. simplify_func_tycontext.
  assert_PROP (isptr vt) as Hvt by entailer!.
  forward_call (gv, Tsh, vt, z1, Some L1).
  { unfold istream_opt. rewrite if_false by (destruct vt; try contradiction; discriminate). cancel. }
  unfold istream_opt. rewrite if_false by (destruct vt; try contradiction; discriminate).
  sep_apply rm_istream_ret.
  forward. Exists (Int.repr 0). entailer!.
Qed.

(* after the header checks: the locals' memory at the return *)
Lemma rmh_E2 Delta rf vR vs vt vih gv z1 L1 v3 v7 v9 v11 v13 :
  ENTAIL Delta, PH21 (rf_rs rf) vR vs vt vih gv v3 v7 v9 v11 v13 (h_xflags (l_h L1)) (l_xb L1) (l_nb L1) (l_cb L1)
    (F1_21 gv vt z1 L1) (field_at Ews t_drun (DOT _head_set) (vi 1) vR * RR21 rf vR) (F3_21 gv vs) TT
  |-- PT21 vR vs vt vih gv z1 L1.
Proof.
  unfold PH21, PT21, F1_21, RR21, F3_21.
  apply andp_left2. go_lowerx. apply andp_right; [ apply prop_right; repeat split; auto | ].
  sep_apply (rmh_R_ret_flat (rf_rs rf) (vi 0) (vi (rf_wrap rf)) (vi (wb_of (rs_wbits (rf_rs rf)))) (rf_nf rf)
               (rf_dset rf) 1 (Zlength (rf_O rf)) 1 vR).
  sep_apply (data_at_data_at_ Tsh t_gzhL).
  cancel.
Qed.
