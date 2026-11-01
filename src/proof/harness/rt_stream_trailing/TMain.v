(* Law rt_stream_trailing (harness/rt_stream_trailing.c): main's body against main_core_spec Rm_t
   ([TMainStmt.trl_main_stmt]).  main is its six parts in sequence (TMainKit.body_parts_t): the setup and
   deflateInit2_ (TSegA), the deflate loop (TLoopD), the input object with the compressed bytes at its start
   (TSegB), inflateInit2_ (TSegC), the inflate loop (TLoopI) and the final checks (TSegE). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TSegA.
Require Import Zlib.proof.harness.rt_stream_trailing.TLoopD.
Require Import Zlib.proof.harness.rt_stream_trailing.TSegB.
Require Import Zlib.proof.harness.rt_stream_trailing.TSegC.
Require Import Zlib.proof.harness.rt_stream_trailing.TLoopI.
Require Import Zlib.proof.harness.rt_stream_trailing.TSegE.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.

Theorem trl_main : trl_main_stmt.
Proof.
  intros J P DF IF.
  start_function.
  match goal with |- semax _ _ (Ssequence _ ?r) _ =>
    apply (semax_unfold_Ssequence
             (Ssequence (Ssequence segA_t (Ssequence loopD_t (Ssequence segB_t (Ssequence segC_t
                (Ssequence loopI_t segE_t))))) r));
    [reflexivity | ]
  end.
  apply semax_seq with FF.
  2: { eapply semax_pre; [ | apply semax_ff]. apply andp_left2; apply derives_refl. }
  eapply semax_seq; [apply (tseg_a Espec J gv v_compressor v_decompressor v_at DF) | ].
  Intros u l.
  eapply semax_seq.
  { eapply semax_pre; [ | apply (tloop_d Espec J gv v_compressor v_decompressor v_at u DF)].
    apply andp_left2; apply (exp_right l); apply derives_refl. }
  Intros O c.
  eapply semax_seq; [apply (tseg_b Espec gv v_compressor v_decompressor v_at u O c) | ].
  Intros src ip.
  eapply semax_seq; [apply (tseg_c Espec P gv v_compressor v_decompressor v_at u O c src ip IF) | ].
  Intros l'.
  eapply semax_seq.
  { eapply semax_pre; [ | apply (tloop_i Espec P gv v_compressor v_decompressor v_at u O c src ip IF)].
    apply andp_left2; apply (exp_right l'); apply derives_refl. }
  Intros z L.
  eapply semax_post; [ | | | | apply (tseg_e Espec)].
  all: intros; unfold POST_t, overridePost; simpl RA_normal; simpl RA_break; simpl RA_continue; simpl RA_return.
  all: try (apply andp_left2; apply derives_refl).
  unfold frame_ret_assert, function_body_ret_assert; simpl. go_lowerx. normalize.
Qed.
