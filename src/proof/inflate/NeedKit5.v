(* NeedKit.v in Delta_cases5 *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.NeedKit.
Require Export Zlib.proof.inflate.CaseRet5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma semax_ifleave5 {Espec: OracleKind} (F: frame) (m0 m1: mst) (R: ret_assert):
  mwf m1 ->
  RA_break R = RA_normal (case_post2 F m0) ->
  (m_leave m1 = 1 -> stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk m1) ->
  semax Delta_cases5 (loop_state F m1) (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)
    (overridePost (!! (m_leave m1 = 0) && loop_state F m1) R).
Proof.
  intros W1 HR Hbrk.
  pose proof (mw_leave _ W1) as HL1.
  unfold loop_state. abbreviate_semax.
  forward_if.
  - forward.
    destruct R as [Rn Rb Rc Rr]. simpl in HR. subst Rb.
    assert (E: m_leave m1 = 1) by (apply leave_from_if; auto).
    change (RA_break _) with (RA_normal (case_post2 F m0)).
    unfold case_post2. unfold RA_normal at 1.
    Exists m1. apply andp_right; [apply prop_right; auto | unfold loop_state; entailer!].
  - forward.
    assert (E: m_leave m1 = 0) by (apply leave_from_if0; auto).
    destruct R as [Rn Rb Rc Rr]. unfold RA_normal at 1.
    apply andp_right; [apply prop_right; auto | entailer!].
Qed.

Lemma semax_needbits_seq5 {Espec: OracleKind} (F: frame) (m0 m: mst) (n: Z) (NB c: statement)
    (R: ret_assert):
  semax Delta_cases5 (loop_state F m) NB (normal_ret_assert (loop_state F (needbits n m))) ->
  mwf m -> n <= 32 ->
  RA_break R = RA_normal (case_post2 F m0) ->
  (m_leave (needbits n m) = 1 -> stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk (needbits n m)) ->
  semax Delta_cases5 (!! (m_leave (needbits n m) = 0) && loop_state F (needbits n m)) c R ->
  semax Delta_cases5 (loop_state F m)
    (Ssequence (Ssequence NB (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)) c) R.
Proof.
  intros HNB W Hn HR Hbrk Hc.
  apply semax_seq with (Q := !! (m_leave (needbits n m) = 0) && loop_state F (needbits n m)); [ | exact Hc].
  eapply semax_seq'; [ exact HNB | ].
  apply (semax_ifleave5 F m0); auto. apply mwf_needbits; auto.
Qed.

Lemma semax_needbits_seq_r5 {Espec: OracleKind} (F: frame) (m0 m: mst) (n: Z) (NB c: statement)
    (R: ret_assert):
  semax Delta_cases5 (loop_state F m) NB (normal_ret_assert (loop_state F (needbits n m))) ->
  mwf m -> n <= 32 ->
  RA_break R = RA_normal (case_post2 F m0) ->
  (m_leave (needbits n m) = 1 -> stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk (needbits n m)) ->
  semax Delta_cases5 (!! (m_leave (needbits n m) = 0) && loop_state F (needbits n m)) c R ->
  semax Delta_cases5 (loop_state F m)
    (Ssequence NB (Ssequence (Sifthenelse (Etempvar _leave tint) Sbreak Sskip) c)) R.
Proof.
  intros. apply seq_assoc. eapply semax_needbits_seq5; eauto.
Qed.
