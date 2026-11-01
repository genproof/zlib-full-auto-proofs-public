(* Law rj_uncompress_any: main's context and the statement of its body.
   main (harness/rj_uncompress_any.c) is proved against MainLib.main_core_spec R (RUGlobals.R, the resources of the
   program's global variables) under Gmain: uncompr.c's uncompress2 for any sizes with a destination and a source
   that may be Z_NULL (USpecW.uncompress2_spec_w, POST = UModelW.uncompressw_rel), zcalloc / zcfree at the
   inflate unit's compspecs (for Spec5's zfuncs in USpec5.inflate_globals), the laws_common.h helpers upto,
   alloc_any_bytes, copy_of (its variant for a Z_NULL source of length 0, CopyOfNull.copy_of_spec_n) and bytes_eq
   (laws_common/Spec.v) and the environment's gp_assert.  The model fact: UTheoryWAny.uw_any_stmt (on any input,
   a documented code, at most the output size written and at most the input length read). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.uncompr.UTheoryWAny.
Require Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_common.CopyOfNull.
Require Import Zlib.proof.harness.rj_uncompress_any.RUCS.
Require Import Zlib.proof.harness.rj_uncompress_any.RUGlobals.
Require Import Zlib.harness.rj_uncompress_any.code.

Definition Gmain : funspecs :=
  [uncompress2_spec_w; zcalloc_i; zcfree_i;
   Zlib.proof.harness.laws_common.Spec.upto_spec; Zlib.proof.harness.laws_common.Spec.any_bytes_spec;
   Zlib.proof.harness.laws_common.CopyOfNull.copy_of_spec_n;
   Zlib.proof.harness.laws_common.Spec.bytes_eq_spec;
   gp_assert_spec].

Definition body_main_stmt : Prop :=
  uw_any_stmt -> semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
