(* Law rt_stream (harness/rt_stream.c, data of any length): main's body against main_core_spec Rm
   ([UMainStmt.urts_main_stmt]).  main is its five parts in sequence (UMainKit.body_parts): the setup and
   deflateInit2_ (USegA), the deflate loop (ULoopD), inflateInit2_ (USegC), the inflate loop (ULoopI) and the
   final checks (USegE). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.USegA.
Require Import Zlib.proof.harness.rt_stream.ULoopD.
Require Import Zlib.proof.harness.rt_stream.USegC.
Require Import Zlib.proof.harness.rt_stream.ULoopI.
Require Import Zlib.proof.harness.rt_stream.USegE.
Require Import Zlib.harness.rt_stream.code.
#[local] Existing Instance LawCS.CS.

(* main's body is its five parts in sequence (UMainKit.body_parts) *)
Theorem urts_main : urts_main_stmt.
Proof.
  intros J P DF IF.
  start_function.
  match goal with |- semax _ _ (Ssequence _ ?r) _ =>
    apply (semax_unfold_Ssequence
             (Ssequence (Ssequence segA (Ssequence loopD (Ssequence segC (Ssequence loopI segE)))) r));
    [reflexivity | ]
  end.
  apply semax_seq with FF.
  2: { eapply semax_pre; [ | apply semax_ff]. apply andp_left2; apply derives_refl. }
  eapply semax_seq; [apply (useg_a Espec J gv v_compressor v_decompressor v_at DF) | ].
  Intros u l.
  eapply semax_seq.
  { eapply semax_pre; [ | apply (uloop_d Espec J gv v_compressor v_decompressor v_at u DF)]. apply andp_left2; apply (exp_right l); apply derives_refl. }
  Intros O c.
  eapply semax_seq; [apply (useg_c Espec P gv v_compressor v_decompressor v_at u O c IF) | ].
  Intros l'.
  eapply semax_seq.
  { eapply semax_pre; [ | apply (uloop_i Espec P gv v_compressor v_decompressor v_at u O c IF)]. apply andp_left2; apply (exp_right l'); apply derives_refl. }
  Intros z L.
  eapply semax_post; [ | | | | apply (useg_e Espec)].
  all: intros; unfold POST_m, overridePost; simpl RA_normal; simpl RA_break; simpl RA_continue; simpl RA_return.
  all: try (apply andp_left2; apply derives_refl).
  unfold frame_ret_assert, function_body_ret_assert; simpl. go_lowerx. normalize.
Qed.
