(* Law rt_roundtrip (data of any length): main's context and the statement of its body.
   main (harness/rt_roundtrip.c) is proved against MainLib.main_core_spec R (WGlobals.R, the resources of the
   program's global variables) under Gmain: compress.c's compress2 for any sizes with a source that may be Z_NULL
   when empty (RTCSpecW.v, POST = RTC2.c2_res), uncompr.c's uncompress2 for any sizes with buffers that may be
   Z_NULL when empty (USpecW.v, POST = UModelW.uncompressw_rel), zcalloc / zcfree at the inflate unit's compspecs
   (for Spec5's zfuncs in USpec5.inflate_globals), the laws_common.h helpers upto, alloc_any_bytes (laws_common/Spec.v),
   copy_of and bytes_eq with arguments that may be Z_NULL when the length is 0 (CopyOfNull.copy_of_spec_n,
   BytesEqNull.bytes_eq_spec_n) and the environment.  The model facts: RTC2W.c2w_bound_stmt (compress2's run into
   compressBound bytes exists and ends with Z_OK or Z_MEM_ERROR), RTC2WFinal.c2w_final_stmt (on Z_OK its output is
   the zlib stream of the data) and UTheoryW.uw_theory_stmt (uncompress2 of that stream followed by any bytes, into
   at least as many bytes as the data has: Z_MEM_ERROR, or Z_OK with the data back and exactly the stream read). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Zlib.proof.compress.CSpec.
Require Zlib.proof.roundtrip.RTCSpecW.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.roundtrip.RTC2W Zlib.proof.roundtrip.RTC2WFinal Zlib.proof.uncompr.UTheoryW.
Require Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_common.CopyOfNull Zlib.proof.harness.laws_common.BytesEqNull.
Require Import Zlib.proof.harness.rt_roundtrip.WCS Zlib.proof.harness.rt_roundtrip.WGlobals.
Require Import Zlib.harness.rt_roundtrip.code.

Definition Gmain : funspecs :=
  [Zlib.proof.roundtrip.RTCSpecW.compress2_spec_w;
   uncompress2_spec_w; zcalloc_i; zcfree_i;
   Zlib.proof.harness.laws_common.Spec.upto_spec; Zlib.proof.harness.laws_common.Spec.any_bytes_spec;
   Zlib.proof.harness.laws_common.CopyOfNull.copy_of_spec_n;
   Zlib.proof.harness.laws_common.BytesEqNull.bytes_eq_spec_n;
   (_quickproof_malloc, malloc_spec'); gp_assert_spec].

Definition body_main_w_stmt : Prop :=
  c2w_bound_stmt -> c2w_final_stmt -> uw_theory_stmt ->
  semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
