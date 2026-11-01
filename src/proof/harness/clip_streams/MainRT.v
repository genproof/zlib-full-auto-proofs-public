(* The main of harness/rj_truncated.c against MainLib.main_core_spec R_rt (MainDefs.main_rt_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.clip_streams.RTIKit.
Require Import Zlib.proof.harness.clip_streams.RTSegIn.
Require Import Zlib.proof.harness.clip_streams.RTSegInit.
Require Import Zlib.proof.harness.clip_streams.RTSegBnd.
Require Import Zlib.proof.harness.clip_streams.RTSegLoop.
Require Import Zlib.proof.harness.clip_streams.RTSegEnd.
Require Import Zlib.proof.harness.clip_streams.RTSetup.
Require Import Zlib.proof.harness.clip_streams.RTLoop.
Require Import Zlib.harness.rj_truncated.code.

(* main's body: the deflate half (statements 1-18, RTSeg*.v) and the inflate half (RTSetup.v, RTLoop.v),
   chained through their CPS statements *)
Lemma body_main_rt : main_rt_stmt.
Proof.
  intros J0 J P DF PF.
  start_function.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  apply semax_seq with FF; [ | apply semax_ff].
  change (semax Delta_rt
    (PROP () LOCAL (lvar _decompressor t_zsl v_decompressor; lvar _compressor t_zsl v_compressor; gvars gv)
     SEP (data_at_ Tsh t_zsl v_decompressor; data_at_ Tsh t_zsl v_compressor; mem_mgr gv; R_rt gv))
    rt_seg1 POST_B).
  eapply semax_pre; [ | apply (seg_inputs_ok _ gv v_compressor v_decompressor)].
  { unfold rt_A0. entailer!. }
  intros n D dp op level wbits mem strategy.
  apply (seg_init_ok _ J0 J); auto. intros s tin tout adler msg msgv.
  apply (seg_bound_ok _ J0 J); auto. intros b cp.
  apply (seg_loop_ok _ J0 J); auto.
  apply seg_end_ok. intros O.
  apply (rt_setup _ P); auto. intros lim FA.
  apply (rt_loop _ P); auto.
Qed.
