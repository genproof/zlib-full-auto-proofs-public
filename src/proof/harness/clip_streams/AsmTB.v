(* Law rfc_trailing_bytes: the assembly of its program from the shared specifications, as Asm.v for the other
   three clip laws (the same G_lib and environment, with gp_assume; main against main_core_spec R_tb), and the body
   of laws_session.h's deflate_params_ok. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.MainDefs.
Require Zlib.proof.inflate_api.SpecWLib.
Require Zlib.proof.harness.laws_session.Spec Zlib.proof.harness.clip_streams.TBDefs.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Zlib.harness.rfc_trailing_bytes.code.
Require Zlib.proof.harness.clip_streams.AsmTBProof.
#[local] Existing Instance Zlib.proof.harness.clip_streams.CS.CS.

Lemma clip_asm_tb : laws_common_ok -> Zlib.proof.harness.laws_session.Spec.laws_session_ok ->
  Zlib.proof.inflate_api.SpecWLib.specw_lib_stmt ->
  semax_body (QPvarspecs p_tb) Zlib.proof.harness.clip_streams.TBDefs.Gmain_tb4
    Zlib.harness.rfc_trailing_bytes.code.f_main
    (Zlib.harness.rfc_trailing_bytes.code._main, main_core_spec R_tb) ->
  harness_safe p_tb.
Proof.
  exact Zlib.proof.harness.clip_streams.AsmTBProof.clip_asm_tb_proof.
Qed.
