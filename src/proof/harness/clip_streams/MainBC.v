(* The main of harness/rj_bad_checksum.c against MainLib.main_core_spec R_bc (MainDefs.main_bc_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.BCKit.
Require Import Zlib.proof.harness.clip_streams.BCSegIn Zlib.proof.harness.clip_streams.BCSegInit
  Zlib.proof.harness.clip_streams.BCSegBnd Zlib.proof.harness.clip_streams.BCSegLoop
  Zlib.proof.harness.clip_streams.BCSegEnd Zlib.proof.harness.clip_streams.BCSegTrl
  Zlib.proof.harness.clip_streams.BCSegISet Zlib.proof.harness.clip_streams.BCSegILoop.

Lemma body_main_bc : main_bc_stmt.
Proof.
  intros J0 J P HD HP.
  start_function.
  match goal with |- semax _ _ (Ssequence _ ?r) _ =>
    apply (semax_unfold_Ssequence (Ssequence bc_seg1 r)); [reflexivity | ]
  end.
  apply semax_seq with FF.
  2: { eapply semax_pre; [ | apply semax_ff]. apply andp_left2; apply derives_refl. }
  eapply semax_pre with (P' := bc_A0 gv v_compressor v_decompressor);
    [ unfold bc_A0; entailer!; cancel | ].
  apply (seg_inputs_ok Espec gv v_compressor v_decompressor).
  intros n D dp op level wbits mem strategy C chp.
  eapply seg_init_ok; [ exact HD | ]. intros s tin tout adler msg msgv.
  eapply seg_bound_ok; [ exact HD | ]. intros b cp.
  eapply seg_loop_ok; [ exact HD | ].
  apply seg_end_ok. intros O.
  eapply seg_trailer_ok; [ exact HP | ]. intros src HF.
  eapply seg_isetup_ok; [ exact HP | exact HF | ].
  eapply seg_iloop_ok; [ exact HP | exact HF ].
Qed.
