(* case MATCH (24) v5: from the copy loops (DmKit5 mt_loop_w_stmt / mt_loop_o_stmt) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.DmKit5 Zlib.proof.inflate.MtKit5 Zlib.proof.inflate.Steps2
  Zlib.proof.inflate.MtSel5 Zlib.proof.inflate.MtTail5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* copy = out - left; *)
Lemma mt_copy0_ok {Espec: OracleKind} (F: frame) (m: mst) (R: ret_assert):
  mwf m -> m_mode m = MATCH ->
  semax Delta_cases5 (loop_state_mt F m) mt_copy0 (overridePost (mt_pre_sel F m) R).
Proof.
  intros W HM.
  pose proof (mwf_left m W) as HLEFT.
  assert (OE: m_out m = m_aout m) by (apply mwf_out_eq; auto; rewrite HM; unfold MATCH, LENGTH, DONE, BAD; lia).
  pose proof (mw_ow _ W) as [How1 How2].
  rewrite mt_copy0_eq. unfold loop_state_mt, mt_locals, mt_seps. abbreviate_semax.
  forward.
  match goal with |- _ |-- ?G => replace G with (mt_pre_sel F m) by (destruct R; reflexivity) end.
  unfold mt_pre_sel, mt_locals, mt_seps. entailer!.
  f_equal. f_equal. unfold m_left in *. lia.
Qed.

Lemma mt_body_ok (HW: mt_loop_w_stmt) (HO: mt_loop_o_stmt) {Espec: OracleKind} (F: frame) (m: mst)
    (R: ret_assert):
  frame_ok5 F -> m_mode m = MATCH -> m_leave m = 0 -> mwf3 m ->
  RA_break R = RA_normal (case_post2 F m) ->
  semax Delta_cases5 (loop_state F m) mt_body R.
Proof.
  intros HF HM HL W3 HR. pose proof (mwf3_mwf _ W3) as W.
  rewrite mt_body_eq.
  eapply semax_seq; [apply mt_lz_ok; auto | ].
  apply semax_extract_prop. intro HL0.
  rewrite loop_state_mt_eq.
  eapply semax_seq; [apply mt_copy0_ok; auto | ].
  eapply semax_seq; [apply mt_sel_ok; auto | ].
  Intros sr cp. apply semax_extract_prop. intro ES.
  destruct (mt_src_facts m sr cp W HM ES) as [HCP _].
  pose proof (mwf_left m W) as HLEFT.
  rewrite seq_assoc. rewrite seq_assoc.
  eapply semax_seq'; [rewrite <- seq_assoc; apply mt_mid_ok; auto | ].
  eapply semax_seq'; [apply mt_loop_ok; auto | ].
  apply mt_end_ok; auto; lia.
Qed.

Lemma case_MATCH5 : mt_loop_w_stmt -> mt_loop_o_stmt ->
  forall {Espec: OracleKind} (F: frame), frame_ok5 F -> case_ok5 F MATCH 24.
Proof.
  intros HW HO Espec F HF m HM HL W3.
  rewrite seq_split by lia.
  eapply semax_seq; [ | apply semax_ff].
  apply (mt_body_ok HW HO F m); auto.
Qed.
