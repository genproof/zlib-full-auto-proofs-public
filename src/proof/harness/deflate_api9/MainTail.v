(* Law deflate_api, main: the calls after Z_STREAM_END and after deflateEnd, and return 0 (MainKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.deflate_api.ApiCS Zlib.proof.harness.deflate_api9.RunSpec
               Zlib.proof.harness.deflate_api9.ApiConv Zlib.proof.harness.deflate_api9.RunKit
               Zlib.proof.harness.deflate_api9.MainKit.
Require Import Zlib.proof.harness.deflate_api9.MainTailMsg.
Require Import Zlib.harness.x_deflate_api.code.
#[local] Existing Instance ApiCS.CS.
Local Open Scope logic.

Lemma main_tail_ok {Espec : OracleKind} I Iend rf vR vs vb gv :
  run_mem_ok -> Zlib.proof.deflate.Obligations.ob_dstream_to_end ->
  semax (Delta_m I Iend) (MA I Iend rf vR vs vb gv) msuf4 POST_m.
Proof.
  (* kit v3: rf_ok gives is_pointer_or_null (rf_msgv rf), the premise of MainTailMsg.main_tail_ok' *)
  intros HM HE.
  unfold MA at 1. apply semax_extract_PROP. intros HRF.
  assert (HP : is_pointer_or_null (rf_msgv rf)) by (destruct HRF as (_ & _ & HP & _); exact HP).
  eapply semax_pre; [ | apply (main_tail_ok' I Iend rf vR vs vb gv HM HE HP) ].
  unfold MA. entailer!.
Qed.
