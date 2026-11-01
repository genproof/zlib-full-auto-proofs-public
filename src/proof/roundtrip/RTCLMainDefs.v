(* Law compress_roundtrip, part RT-CL: main's context and the statement of its body.
   main (harness/compress_roundtrip.c) is proved against MainLib.main_core_spec R (RTCLGlobals.R: deflate_globals,
   compress.c's literal, inflate's tables and literals) under Gmain: compress.c's compressBound (CSpec.v),
   compress / compress2 (RTCSpec.v, POST = RTC2.c2_res), uncompr.c's uncompress / uncompress2 (USpec5.v, POST =
   UModel.uncompress_rel), zcalloc / zcfree at the inflate unit's compspecs (to build Spec5's zfuncs for
   USpec5.inflate_globals), the harness's bytes_same (adler32/HarnessBytes.v) and the environment.  The facts:
   RTC2.c2_ok (compress2 over the model) and RTIIface.ufacts (uncompress on compress2's stream). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Zlib.proof.compress.CSpec.
Require Zlib.proof.roundtrip.RTCSpec.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpec5.
Require Import Zlib.proof.roundtrip.RTC2 Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.proof.roundtrip.RTCLCS Zlib.proof.roundtrip.RTCLGlobals.
Require Import Zlib.harness.x_compress_roundtrip.code.

Definition Gmain : funspecs :=
  [Zlib.proof.compress.CSpec.compressBound_spec;
   Zlib.proof.roundtrip.RTCSpec.compress2_spec; Zlib.proof.roundtrip.RTCSpec.compress_spec;
   uncompress2_spec; uncompress_spec; zcalloc_i; zcfree_i; bytes_same_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Definition body_main_stmt : Prop :=
  c2_ok -> ufacts -> semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
