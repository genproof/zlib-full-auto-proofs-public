(* Law deflate_roundtrip, gzip header: THE gzip run with a header (R.head_set = 1) from A6 to main's end, in
   main's context with the v6 specifications (RTRSKit.Delta_m6): rms_hset1, over Delta_m6 and
   ifacts6, from the parts H6, H8, H16, H21 and the facts RTRSTheory.rmh_first_facts. *)
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
Require Import Zlib.proof.roundtrip.RTRSTheory Zlib.proof.roundtrip.RTRSH6 Zlib.proof.roundtrip.RTRSH8 Zlib.proof.roundtrip.RTRSH16 Zlib.proof.roundtrip.RTRSH21.
Require Zlib.proof.uncompr.URunFrame.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma rms_hset1 {Espec : OracleKind} I Iend rf vR vs vt vih gv z sp :
  ifacts6 -> rf_hset rf = 1 ->
  semax (Delta_m6 I Iend) (A6 Iend rf vR vs vt vih gv z sp) seg6 POST_b.
Proof.
  intros IF H1.
  apply rmh_seg6; [exact H1 | intros OK; exact (rmh_first_facts Iend vR rf IF OK H1 sp vih) | ].
  intros L. apply rmh_seg8. intros ibp obp r z1 L1 ow cont.
  apply rmh_seg16. intros z' L'.
  apply rmh_seg21.
Qed.
