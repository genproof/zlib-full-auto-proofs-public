(* Law deflate_roundtrip, the gzip run with a header (R.head_set = 1), part H6: positions 6-7 of
   b0 from A6 (after inflateInit2(&t, 32)): the inflateGetHeader block (malloc of the three buffers of R.xlen,
   R.nl + 1, R.cl + 1 bytes, the stores into ih, the NULL test (return 0), gp_assert(inflateGetHeader(&t, &ih) ==
   Z_OK) by RTHSpec.inflateGetHeader_spec6 on hraw6 with RTRSKit.rm_h0), then the raw dictionary block (skipped:
   R.wrap = 2); establishes AH8 with L = rm_hL rf sp vih xb nb cb. *)
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
Require Import Zlib.proof.roundtrip.RTRSH6Kit Zlib.proof.roundtrip.RTRSH6A Zlib.proof.roundtrip.RTRSH6C Zlib.proof.roundtrip.RTRSH6D.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma rmh_seg6 {Espec : OracleKind} I Iend rf vR vs vt vih gv z sp :
  rf_hset rf = 1 ->
  (rf_ok Iend vR rf -> forall xb nb cb, gz_first_ok rf (rm_hL rf sp vih xb nb cb)) ->
  (forall L, semax (Delta_m6 I Iend) (AH8 Iend rf vR vs vt vih gv z L) seg8 POST_b) ->
  semax (Delta_m6 I Iend) (A6 Iend rf vR vs vt vih gv z sp) seg6 POST_b.
Proof.
  intros Hh FG K.
  unfold seg6. apply seq_assoc.
  apply semax_seq with (Q := EX L, AH8 Iend rf vR vs vt vih gv z L);
    [ | apply extract_exists_pre; intro L; apply K].
  unfold Delta_m6, Gm6, A6, POST_b, POST_m. simplify_func_tycontext.
  rewrite rmh_split.
  Intros.
  assert (W2: rf_wrap rf = 2) by (destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X); auto).
  forward.
  forward_if (rmh_Q6 rf vR vs vt vih gv z sp).
  2: { rewrite Hh in H1. exfalso. apply Int.one_not_zero. exact H1. }
  { apply (rmh_alloc I Iend rf vR vs vt vih gv z sp _ H).
    intros xb nb cb. apply (rmh_null I Iend rf vR vs vt vih gv z sp xb nb cb _ H).
    intros _ _ _. apply (rmh_call I Iend rf vR vs vt vih gv z sp xb nb cb Hh H). }
  unfold rmh_Q6. Intros xb nb cb.
  rewrite rm6_open_eq. unfold rm6_open. Intros.
  forward.
  ifpost _t'13 Int.zero.
  { exfalso. rewrite W2 in *. lia. }
  { forward. entailer!. }
  forward_if.
  { exfalso. auto. }
  forward. Exists (rm_hL rf sp vih xb nb cb). unfold AH8. rewrite rm6_open_eq. unfold rm6_open.
  entailer!.
  apply derives_refl.
Qed.
