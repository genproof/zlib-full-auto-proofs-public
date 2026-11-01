(* Law rj_bad_block, main: statement 29 of main's body (BBWKit.bbw_loop_stmt), the do-while of inflate() calls
   in clip() pieces: the invariant BBWKit.bbw_inv is kept by every call that returns Z_OK or Z_BUF_ERROR
   (BBWDefs.bbw_call), a call returning Z_MEM_ERROR returns 0, and the loop is left in BBWKit.bbw_AT. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bit_writer.BWSpec.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.harness.bit_writer.BWLawCS Zlib.proof.harness.bit_writer.BWGlobals.
Require Import Zlib.proof.harness.bit_writer.BBWKit.
Require Import Zlib.proof.harness.bit_writer.BBWHelp.
Require Import Zlib.proof.harness.bit_writer.BBWLKit.
Require Import Zlib.proof.harness.bit_writer.BBWLPre Zlib.proof.harness.bit_writer.BBWLCall.
Require Import Zlib.proof.harness.bit_writer.BBWLTest.

(* the do-while is `Sloop body test` followed by statement 30: the body (BBWLPre.v up to the call, BBWLCall.v
   the call) leads from the invariant to bbw_C, the test (BBWLTest.v) from bbw_C back to the invariant or out of
   the loop to bbw_AT *)
Lemma bbw_loop : bbw_loop_stmt.
Proof.
  intros Espec J gv vs vbt vbit S0 kind which lits room flush strp outp F A Hnext.
  rewrite bbl_seg29_eq.
  eapply semax_seq; [ | exact Hnext].
  apply semax_loop with (Q' := bbw_C J gv vs vbt vbit strp outp S0 kind which lits room flush).
  - apply bbl_pre_ok; auto. apply bbl_call_ok; auto.
  - apply bbl_test_ok; auto.
Qed.
