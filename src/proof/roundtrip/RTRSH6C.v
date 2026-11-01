(* Law deflate_roundtrip (gzip header, part H6), part C: the NULL test of the inflateGetHeader block,
   `if (ih.extra == NULL || ih.name == NULL || ih.comment == NULL) return 0;` (rmh_test for the condition, the
   return with R, t, ih given back as their locals' memory), then the call part from rmh_PN (continuation). *)
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
Require Import Zlib.proof.roundtrip.RTRMSeg6.
Require Zlib.proof.roundtrip.RTRMSeg8.
Require Import Zlib.proof.roundtrip.RTRSH6Kit Zlib.proof.roundtrip.RTRSH6B.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma rmh_any_zero xb nb cb : rmh_any xb nb cb = Int.zero -> xb <> nullval /\ nb <> nullval /\ cb <> nullval.
Proof.
  unfold rmh_any. intros E.
  destruct (eq_dec xb nullval); [apply Int.one_not_zero in E; contradiction | ].
  destruct (eq_dec nb nullval); [apply Int.one_not_zero in E; contradiction | ].
  destruct (eq_dec cb nullval); [apply Int.one_not_zero in E; contradiction | ]. auto.
Qed.

Lemma rmh_null {Espec : OracleKind} I Iend rf vR vs vt vih gv z sp xb nb cb Q :
  rf_ok Iend vR rf ->
  (xb <> nullval -> nb <> nullval -> cb <> nullval ->
   semax (Delta_m6 I Iend) (rmh_PN rf vR vs vt vih gv z sp xb nb cb) hs_call (overridePost Q POST_b)) ->
  semax (Delta_m6 I Iend) (rmh_PA rf vR vs vt vih gv z sp xb nb cb) hs_tail (overridePost Q POST_b).
Proof.
  intros H K.
  rewrite hs_tail_eq. apply -> seq_assoc.
  apply semax_seq with (Q := rmh_PT rf vR vs vt vih gv z sp xb nb cb); [apply rmh_test | ].
  unfold hs_ret, rmh_PT, Delta_m6, Gm6, POST_b, POST_m. simplify_func_tycontext.
  forward_if.
  { forward. Exists (Int.repr 0).
    sep_apply (rm_dside_ret _ _ _ H). sep_apply rm_istream_ret.
    sep_apply (data_at_data_at_ Tsh t_gzhL (rmh_ih rf xb nb cb) vih).
    apply andp_right; [apply prop_right; reflexivity | cancel]. }
  match goal with Hx: rmh_any _ _ _ = Int.zero |- _ => destruct (rmh_any_zero _ _ _ Hx) as (Nx & Nn & Nc) end.
  destruct (eq_dec xb nullval); [contradiction | ]. destruct (eq_dec nb nullval); [contradiction | ].
  destruct (eq_dec cb nullval); [contradiction | ].
  Intros.
  eapply semax_pre; [ | apply (K Nx Nn Nc) ].
  unfold rmh_PN. entailer!.
Qed.
