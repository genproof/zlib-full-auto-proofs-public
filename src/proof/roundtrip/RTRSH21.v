(* Law deflate_roundtrip, the gzip run with a header (R.head_set = 1), part H21: positions 21-22 of
   b0 from AH21: the header checks (ih.done == 1; text, time, os, hcrc against R.h; extra_len == R.xlen and
   bytes_same(ih.extra, R.xf, R.xlen); bytes_same(ih.name, R.nf_, R.nl + 1); bytes_same(ih.comment, R.cf,
   R.cl + 1)) with head_mem6 = Spec5's head_rep past the header modes (RTHSpec.head_mem6_spec5) and gz_end, then
   inflateEnd(&t) and the end of b0.  As RTRMSeg17.v's tail. *)
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
Require Import Zlib.proof.roundtrip.RTRSH21Kit Zlib.proof.roundtrip.RTRSH21A Zlib.proof.roundtrip.RTRSH21B Zlib.proof.roundtrip.RTRSH21C.
Require Import Zlib.proof.roundtrip.RTRSH21E Zlib.proof.roundtrip.RTRSH21T.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

(* the header checks: parts 1-5 *)
Lemma rmh_chk {Espec : OracleKind} I Iend rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4 R :
  PH21_ok rs xb nb cb ->
  semax (Delta_m6 I Iend) (PH21 rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4) chk21
    (overridePost (PH21 rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4) R).
Proof.
  intros OK. rewrite chk21_eq.
  eapply semax_seq; [ apply rmh_X1 | ].
  eapply semax_seq; [ apply rmh_X2 | ].
  eapply semax_seq; [ apply rmh_X3; exact OK | ].
  eapply semax_seq; [ apply rmh_X4; exact OK | ].
  apply rmh_X5; exact OK.
Qed.

Lemma rmh_conseq {Espec : OracleKind} Delta (P P' Q : environ -> mpred) c :
  semax Delta P' c (overridePost P' (normal_ret_assert Q)) ->
  (local (tc_environ Delta) && P |-- P') -> (local (tc_environ Delta) && P' |-- Q) ->
  semax Delta P c (normal_ret_assert Q).
Proof.
  intros H H1 H2. eapply semax_pre_post; [ exact H1 | | | | | exact H ]; simpl;
    try exact H2; intros; apply andp_left2, derives_refl.
Qed.

Lemma rmh_seg21 {Espec : OracleKind} I Iend rf vR vs vt vih gv z1 L1 :
  semax (Delta_m6 I Iend) (AH21 Iend rf vR vs vt vih gv z1 L1) seg21 POST_b.
Proof.
  eapply semax_pre; [ apply rmh_E1 | ].
  Intros v3 v7 v9 v11 v13.
  unfold A0_21. Intros.
  unfold seg21, POST_b. unfold Delta_m6, Gm6, POST_m. simplify_func_tycontext.
  forward.
  forward_if (PH21 (rf_rs rf) vR vs vt vih gv v3 v7 v9 v11 v13 (h_xflags (l_h L1)) (l_xb L1) (l_nb L1) (l_cb L1)
                (F1_21 gv vt z1 L1) (field_at Ews t_drun (DOT _head_set) (vi 1) vR * RR21 rf vR) (F3_21 gv vs) TT).
  { eapply rmh_conseq.
    { exact (rmh_chk I Iend (rf_rs rf) vR vs vt vih gv v3 v7 v9 v11 v13 (h_xflags (l_h L1)) (l_xb L1) (l_nb L1)
               (l_cb L1) (F1_21 gv vt z1 L1) (field_at Ews t_drun (DOT _head_set) (vi 1) vR * RR21 rf vR)
               (F3_21 gv vs) TT _ H). }
    { unfold PH21. entailer!. }
    { apply andp_left2, derives_refl. } }
  { exfalso; apply Int.one_not_zero; assumption. }
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [ apply rmh_E2 | apply rmh_tail ].
Qed.
