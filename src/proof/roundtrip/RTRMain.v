(* Law deflate_roundtrip: the run of main of harness/deflate_roundtrip.c without a gzip
   header, from A6 to the end (rm_rest_nohdr), as RTRSMain.v uses it.  The body of main against
   MainLib.main_core_spec Rm (RTRMainSpec.v) is proved (Qed) in RTRSMain.v, with the gzip header
   by RTRSHdr.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRMainSpec.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.proof.roundtrip.RTRRunSpec Zlib.proof.roundtrip.RTRRunKit.
Require Zlib.proof.roundtrip.RTRRunMem.
Require Import Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.harness.x_deflate_roundtrip.code.
Require Import Zlib.proof.roundtrip.RTRMKit.
Require Import Zlib.proof.roundtrip.RTRMSeg1 Zlib.proof.roundtrip.RTRMSeg6 Zlib.proof.roundtrip.RTRMSeg8 Zlib.proof.roundtrip.RTRMSeg16 Zlib.proof.roundtrip.RTRMSeg17 Zlib.proof.roundtrip.RTRMTheory Zlib.proof.roundtrip.RTRMGap.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

(* the run without a gzip header: the parts from A6 to the end *)
Lemma rm_rest_nohdr {Espec : OracleKind} I Iend rf vR vs vt vih gv z sp :
  ifacts -> rf_ok Iend vR rf -> rf_hset rf = 0 ->
  semax (Delta_m I Iend) (A6 Iend rf vR vs vt vih gv z sp) seg6 POST_b.
Proof.
  intros IF OK H0.
  apply rm_seg6; [exact H0 | apply (rm_first_facts Iend vR rf IF rm_zd_nomem OK H0) | ].
  intros L. apply rm_seg8. intros ibp obp r z1 L1 ow cont.
  apply rm_seg16. intros r' z' L' ow' cont'.
  apply rm_seg17.
Qed.
