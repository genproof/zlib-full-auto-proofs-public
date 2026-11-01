(* The main of harness/rt_partial.c against MainLib.main_core_spec R_rp (RPDefs.main_rpc_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.RPDefs.
Require Import Zlib.proof.harness.clip_streams.RPKit.
Require Import Zlib.proof.harness.clip_streams.RPDKit.
Require Import Zlib.proof.harness.clip_streams.RPDSegIn.
Require Import Zlib.proof.harness.clip_streams.RPDSegInit.
Require Import Zlib.proof.harness.clip_streams.RPDSegBnd.
Require Import Zlib.proof.harness.clip_streams.RPDSegLoop.
Require Import Zlib.proof.harness.clip_streams.RPDSegEnd.
Require Import Zlib.proof.harness.clip_streams.RPSetup.
Require Import Zlib.proof.harness.clip_streams.RPLoop.

(* main's body: the deflate half (statements 1-20, RPDSeg*.v) and the inflate half (RPSetup.v, RPLoop.v),
   chained through their CPS statements *)
Lemma body_main_rp : main_rpc_stmt.
Proof.
  intros J0 J P DF PF.
  start_function.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  apply semax_seq with FF; [ | apply semax_ff].
  eapply semax_pre; [ | apply (rpd_seg_inputs _ gv v_compressor v_decompressor)].
  { unfold rpd_A0. entailer!. }
  intros n D dp ep op level wbits mem strategy.
  apply (rpd_seg_init _ J0 J); auto. intros s tin tout adler msg msgv.
  apply (rpd_seg_bound _ J0 J); auto. intros b cp.
  apply (rpd_seg_loop _ J0 J); auto.
  apply rpd_seg_end. intros O.
  rewrite rpd_seg21_eq. unfold rpd_DH.
  apply (rp_setup _ P); auto. intros lim FA.
  apply (rp_loop _ P); auto.
Qed.
