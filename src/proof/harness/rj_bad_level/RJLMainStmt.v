(* Law rj_bad_level: the statement of main's proof (RJLMain.v): main of harness/rj_bad_level.c against
   MainLib.main_core_spec R (RJLGlobals.v), calling compress2 through its specification for any sizes
   (RTCSpecW.compress2_spec_w), laws_common.h's upto and any_bytes through theirs (laws_common/Spec.v) and the
   environment.  The model fact main needs about the call is RJLTheory.rjl_c2_exists / rjl_c2_res. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.roundtrip.RTCSpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rj_bad_level.RJLCS Zlib.proof.harness.rj_bad_level.RJLGlobals.
Require Import Zlib.harness.rj_bad_level.code.

Definition Gmain : funspecs :=
  [compress2_spec_w; upto_spec; any_bytes_spec;
   (_quickproof_malloc, malloc_spec'); nondet_u32_spec; gp_assert_spec; gp_assume_spec].

Definition rjl_main_stmt : Prop :=
  semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
