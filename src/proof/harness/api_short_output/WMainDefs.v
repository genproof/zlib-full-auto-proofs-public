(* Law api_short_output (data of any length): main's context and the statement of its body.
   main (harness/api_short_output.c) is proved against MainLib.main_core_spec R (R: deflate's globals,
   compress.c's literal, inflate's tables and literals, as roundtrip/RTCLGlobals.v) under Gmain: compressBound
   (CSpec.v), compress2 for any sizes (RTCSpecW.v, POST = RTC2.c2_res), uncompress2 for any sizes with a
   destination that may be Z_NULL (USpecW.v, POST = UModelW.uncompressw_rel), zcalloc / zcfree at the inflate
   unit's compspecs (for Spec5's zfuncs), the helpers of laws_common.h (upto, alloc_any_bytes, copy_of; bytes_eq
   with a first argument that may be Z_NULL: BytesEqNull.v) and the environment.  The model facts: RTC2W.c2w_bound_stmt
   (compress2's run into compressBound bytes exists and ends with Z_OK or Z_MEM_ERROR), RTC2WFinal.c2w_final_stmt
   (on Z_OK its output is the zlib stream of the data) and UTheoryW.uw_theory_stmt (uncompress2 of that stream
   followed by any bytes, into less space than the data needs: Z_BUF_ERROR, the space filled with the start of the
   data, fewer bytes read than the stream has). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Zlib.proof.compress.CSpec.
Require Zlib.proof.roundtrip.RTCSpec Zlib.proof.roundtrip.RTCSpecW.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.harness.laws_common.Spec Zlib.proof.harness.laws_common.BytesEqNull.
Require Import Zlib.proof.roundtrip.RTC2W Zlib.proof.roundtrip.RTC2WFinal Zlib.proof.uncompr.UTheoryW.
Require Import Zlib.proof.harness.api_short_output.WLawCS.
Require Import Zlib.harness.api_short_output.code.

(* the resources of the program's globals that main passes on to compress2 and uncompress2 *)
Definition R (gv: globals) : mpred :=
  (deflate_globals gv * Zlib.proof.roundtrip.RTCSpec.cversion_lit gv *
   tables_rep Ers gv * version_lit gv * uversion_lit gv)%logic.

Definition Gmain : funspecs :=
  [Zlib.proof.compress.CSpec.compressBound_spec; Zlib.proof.roundtrip.RTCSpecW.compress2_spec_w;
   uncompress2_spec_w; zcalloc_i; zcfree_i;
   upto_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec_n;
   (_quickproof_malloc, malloc_spec'); gp_assert_spec].

Definition body_main_w_stmt : Prop :=
  c2w_bound_stmt -> c2w_final_stmt -> uw_theory_stmt ->
  semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
