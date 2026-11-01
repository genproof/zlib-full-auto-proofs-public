(* inflate(), the cases DONE, BAD, MEM, SYNC (SYNC falls into `default`) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseRet.
Require Import Zlib.proof.inflate.Steps.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma mem_rep_leave_ret: forall F m r, mem_rep F (set_leave (set_m_ret m r)) = mem_rep F m.
Proof. reflexivity. Qed.

Lemma case_DONE {Espec: OracleKind} (F: frame) (m: mst):
  m_mode m = DONE -> m_leave m = 0 -> mwf m ->
  semax Delta_inflate (loop_state F m)
    (seq_of_labeled_statement (ls_drop 28 inflate_LS)) (switch_ret_assert (case_post F m)).
Proof.
  intros HM HL W. case_stmt.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  unfold loop_state. abbreviate_semax.
  forward. forward. forward.
  Exists (set_leave (set_m_ret m Z_STREAM_END)).
  unfold loop_state. rewrite mem_rep_leave_ret. frame_simpl_goal. mnorm_goal.
  entailer!.
  rewrite (stepf_DONE _ _ _ _ HM). reflexivity.
Qed.

Lemma case_BAD {Espec: OracleKind} (F: frame) (m: mst):
  m_mode m = BAD -> m_leave m = 0 -> mwf m ->
  semax Delta_inflate (loop_state F m)
    (seq_of_labeled_statement (ls_drop 29 inflate_LS)) (switch_ret_assert (case_post F m)).
Proof.
  intros HM HL W. case_stmt.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  unfold loop_state. abbreviate_semax.
  forward. forward. forward.
  Exists (set_leave (set_m_ret m Z_DATA_ERROR)).
  unfold loop_state. rewrite mem_rep_leave_ret. frame_simpl_goal. mnorm_goal.
  entailer!.
  rewrite (stepf_BAD _ _ _ _ HM). reflexivity.
Qed.

Lemma case_MEM {Espec: OracleKind} (F: frame) (m: mst):
  m_mode m = MEM -> m_leave m = 0 -> mwf m ->
  semax Delta_inflate (loop_state F m)
    (seq_of_labeled_statement (ls_drop 30 inflate_LS)) (switch_ret_assert (case_post F m)).
Proof.
  intros HM HL W. case_stmt.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  eapply semax_case_return; [ apply (stepf_MEM _ _ _ _ HM) | reflexivity | | ].
  - unfold loop_state. go_lowerx. simpl. apply prop_right. compute. split; discriminate.
  - unfold loop_state. go_lowerx. cancel.
Qed.

Lemma case_SYNC {Espec: OracleKind} (F: frame) (m: mst):
  m_mode m = SYNC -> m_leave m = 0 -> mwf m ->
  semax Delta_inflate (loop_state F m)
    (seq_of_labeled_statement (ls_drop 31 inflate_LS)) (switch_ret_assert (case_post F m)).
Proof.
  intros HM HL W. case_stmt.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  apply -> semax_skip_seq.
  eapply semax_case_return; [ apply (stepf_SYNC _ _ _ _ HM) | reflexivity | | ].
  - unfold loop_state. go_lowerx. simpl. apply prop_right. compute. split; discriminate.
  - unfold loop_state. go_lowerx. cancel.
Qed.
