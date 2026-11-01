(* Law deflate_roundtrip (gzip header, part H6), part D: `gp_assert(inflateGetHeader(&t, &ih) == Z_OK);` with
   the three buffers allocated (rmh_PN), by RTHSpec.inflateGetHeader_spec6 on hraw6 (RTRSKit.rm_h0): the stream
   inflateInit2(&t, 32) left is gzip-capable in mode HEAD, so the call returns Z_OK with the header attached
   (rm_hL); ends in rmh_Q6. *)
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
Require Import Zlib.proof.roundtrip.RTRSH6Kit.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma rmh_wrap32 sp : (Z.land (i_wrap (l_s (init_live sp 32))) 2 =? 0) = false.
Proof. reflexivity. Qed.

Lemma rmh_call {Espec : OracleKind} I Iend rf vR vs vt vih gv z sp xb nb cb :
  rf_hset rf = 1 -> rf_ok Iend vR rf ->
  semax (Delta_m6 I Iend) (rmh_PN rf vR vs vt vih gv z sp xb nb cb) hs_call
    (overridePost (rmh_Q6 rf vR vs vt vih gv z sp) POST_b).
Proof.
  intros Hh H.
  assert (RS: rs_ok (rf_rs rf)) by (destruct H; auto).
  assert (W2: rf_wrap rf = 2) by (destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X); auto).
  unfold hs_call, rmh_PN, Delta_m6, Gm6, POST_b, POST_m. simplify_func_tycontext.
  Intros.
  rewrite (rmh_iw rf W2).
  assert_PROP (isptr vt) as Pvt by entailer!.
  sep_apply (rmh_raw rf vih xb nb cb H0 H1 H2).
  sep_apply (rmh_toks rf xb nb cb H0 H1 H2).
  forward_call (gv, Tsh, vt, z, Some (init_live sp 32), vih, Tsh, xb, nb, cb, rm_h0 rf).
  { rewrite rm6_iopt by auto. cancel. }
  { split; [apply rmh_hwf; auto | apply rmh_attach; auto]. }
  rewrite (RTRMSeg8.rm8_islive vt) by auto. cbv iota. rewrite rmh_wrap32. rewrite rm6_iopt by auto.
  forward_call (Int.repr 1).
  unfold rmh_Q6. Exists xb nb cb. unfold rm_hL, head_live. entailer!.
Qed.
