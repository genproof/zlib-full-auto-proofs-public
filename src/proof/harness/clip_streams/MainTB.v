(* The main of harness/rfc_trailing_bytes.c against MainLib.main_core_spec R_tb (TBKit.main_tb_tail_stmt): the
   deflate half (TBDeflate.v), the input (TBInput.v), the inflate setup (TBSetup.v) and the inflate loop with the
   check (TBLoop.v), chained through their CPS statements. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.TBFacts Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.TBKit.
Require Import Zlib.proof.harness.clip_streams.TBDeflate Zlib.proof.harness.clip_streams.TBInput
  Zlib.proof.harness.clip_streams.TBSetup Zlib.proof.harness.clip_streams.TBLoop.
Require Import Zlib.harness.rfc_trailing_bytes.code.

Lemma body_main_tb : main_tb_tail_stmt.
Proof.
  intros J0 J P DF TF.
  start_function.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  apply semax_seq with FF; [ | apply semax_ff].
  eapply semax_pre; [ | apply (tb_deflate _ J0 J gv v_compressor v_decompressor); auto ].
  { unfold tb_A0. entailer!. }
  intros wbits n b D O dp op cp.
  apply tb_input. intros src ip FA.
  apply (tb_setup _ P); auto.
  apply (tb_loop _ P); auto.
Qed.
