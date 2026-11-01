(* Laws rt_dictionary and api_dict_id: the bodies of the two mains (DWMainDefs.main_drt_stmt, main_dai_stmt).
   Each main's body is, up to the association of its sequences, the segments of DWKit.v for its program: seg_in,
   seg_init, seg_dict, seg_bnd, seg_loop, seg_end, seg_setup, seg_first, then the law's own part (api_dict_id:
   tail_api; rt_dictionary: trt_set, trt_loop, trt_end).  seg_in makes the copies (DWKit.F_drt, F_dai); the
   segments that do not use them get them as a frame (DWKit.dw_frame). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWIFacts.
Require Import Zlib.proof.harness.dictionary_w.DWMainDefs.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
Require Import Zlib.proof.harness.dictionary_w.DWSegIn.
Require Import Zlib.proof.harness.dictionary_w.DWSegInit.
Require Import Zlib.proof.harness.dictionary_w.DWSegDict.
Require Import Zlib.proof.harness.dictionary_w.DWSegBnd.
Require Import Zlib.proof.harness.dictionary_w.DWSegLoop.
Require Import Zlib.proof.harness.dictionary_w.DWSegEnd.
Require Import Zlib.proof.harness.dictionary_w.DWSetup.
Require Import Zlib.proof.harness.dictionary_w.DWFirst.
Require Import Zlib.proof.harness.dictionary_w.DWTailApi.
Require Import Zlib.proof.harness.dictionary_w.DWTrtSet.
Require Import Zlib.proof.harness.dictionary_w.DWTrtLoop.
Require Import Zlib.proof.harness.dictionary_w.DWTrtEnd.
#[local] Existing Instance CS.CS.

(* a segment that does not use the copies, with the copies as its frame *)
Ltac framed T := eapply semax_seq; [apply dw_frame; [dw_closed | T] |].

Lemma drt_main : main_drt_stmt.
Proof.
  intros J0 J1 J Q P DF DI.
  start_function.
  match goal with |- semax _ _ (Ssequence _ ?r) _ =>
    apply (semax_unfold_Ssequence
      (Ssequence seg_in_drt (Ssequence seg_init_drt (Ssequence seg_dict_drt (Ssequence seg_bnd_drt
        (Ssequence seg_loop_drt (Ssequence seg_end_drt (Ssequence seg_setup_drt (Ssequence seg_first_drt
        (Ssequence trt_set (Ssequence trt_loop (Ssequence trt_end r))))))))))))
  end.
  { reflexivity. }
  eapply semax_seq.
  { eapply semax_pre; [ | apply (proj1 seg_in_ok _ gv v_compressor v_decompressor)].
    unfold PRE0, R_drt. entailer!. }
  Intros n D dp op dict ddp level wbits mem strategy dcp ep.
  framed ltac:(apply (seg_init_drt_ok _ J0 J1 J); exact DF).
  Intros s tin tout adler msg msgv.
  framed ltac:(apply (seg_dict_drt_ok _ J0 J1 J); exact DF).
  Intros s' tin' tout' adler' ai ao msg' msgv'.
  framed ltac:(apply (seg_bnd_drt_ok _ J0 J1 J); exact DF).
  Intros b cp.
  framed ltac:(apply (proj1 seg_loop_ok _ J0 J1 J); exact DF).
  framed ltac:(apply seg_end_drt_ok).
  Intros O.
  framed ltac:(apply (proj1 seg_setup_ok)).
  Intros z sp.
  framed ltac:(apply (seg_first_drt_ok _ Q P); exact DI).
  Intros z' L.
  eapply semax_seq; [apply (trt_set_ok _ Q P); exact DI |].
  framed ltac:(apply (trt_loop_ok _ Q P); exact DI).
  eapply semax_seq; [apply trt_end_ok |].
  (* the last part ends by a return: nothing falls through *)
  eapply semax_pre; [| apply semax_ff]. intros rho. unfold bind_ret. simpl. normalize.
Qed.

Lemma dai_main : main_dai_stmt.
Proof.
  intros J0 J1 J Q P DF DI.
  start_function.
  match goal with |- semax _ _ (Ssequence _ ?r) _ =>
    apply (semax_unfold_Ssequence
      (Ssequence seg_in_dai (Ssequence seg_init_dai (Ssequence seg_dict_dai (Ssequence seg_bnd_dai
        (Ssequence seg_loop_dai (Ssequence seg_end_dai (Ssequence seg_setup_dai (Ssequence seg_first_dai
        (Ssequence tail_api r))))))))))
  end.
  { reflexivity. }
  eapply semax_seq.
  { eapply semax_pre; [ | apply (proj2 seg_in_ok _ gv v_compressor v_decompressor)].
    unfold PRE0, R_dai. entailer!. }
  Intros n D dp op dict ddp level wbits mem strategy dcp.
  framed ltac:(apply (seg_init_dai_ok _ J0 J1 J); exact DF).
  Intros s tin tout adler msg msgv.
  framed ltac:(apply (seg_dict_dai_ok _ J0 J1 J); exact DF).
  Intros s' tin' tout' adler' ai ao msg' msgv'.
  framed ltac:(apply (seg_bnd_dai_ok _ J0 J1 J); exact DF).
  Intros b cp.
  framed ltac:(apply (proj2 seg_loop_ok _ J0 J1 J); exact DF).
  framed ltac:(apply seg_end_dai_ok).
  Intros O.
  framed ltac:(apply (proj2 seg_setup_ok)).
  Intros z sp.
  framed ltac:(apply (seg_first_dai_ok _ Q P); exact DI).
  Intros z' L.
  eapply semax_seq; [apply (tail_api_ok _ Q P); exact DI |].
  eapply semax_pre; [| apply semax_ff]. intros rho. unfold bind_ret. simpl. normalize.
Qed.

Lemma dict_mains : main_drt_stmt /\ main_dai_stmt.
Proof. exact (conj drt_main dai_main). Qed.
