(* RT-H: mechanical port of inflate/NeedKit.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* `NEEDBITS(n); if (leave) break; c` inside a case: from a NEEDBITS loop lemma (NeedBits*.v), the break
   when the input runs out, and the continuation c with leave = 0. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.roundtrip.RTHCaseRet.
Require Export Zlib.proof.inflate.MwfLemmas.
Require Export Zlib.proof.inflate.NeedKit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.









(* the break of `if (leave) break;` after a pass that leaves with machine m1 *)
Lemma semax_ifleaveH {Espec: OracleKind} (F: frame) (m0 m1: mst) (R: ret_assert):
  mwf m1 ->
  RA_break R = RA_normal (case_postH F m0) ->
  (m_leave m1 = 1 -> stepf (f_flush F) lenfix_list distfix_list m0 = IBrk m1) ->
  semax Delta_inflate (loop_stateH F m1) (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)
    (overridePost (!! (m_leave m1 = 0) && loop_stateH F m1) R).
Proof.
  intros W1 HR Hbrk.
  pose proof (mw_leave _ W1) as HL1.
  unfold loop_stateH. abbreviate_semax.
  forward_if.
  - forward.
    destruct R as [Rn Rb Rc Rr]. simpl in HR. subst Rb.
    assert (E: m_leave m1 = 1) by (apply leave_from_if; auto).
    change (RA_break _) with (RA_normal (case_postH F m0)).
    unfold case_postH. unfold RA_normal at 1.
    Exists m1. apply andp_right; [apply prop_right; auto | unfold loop_stateH; entailer!].
  - forward.
    assert (E: m_leave m1 = 0) by (apply leave_from_if0; auto).
    destruct R as [Rn Rb Rc Rr]. unfold RA_normal at 1.
    apply andp_right; [apply prop_right; auto | entailer!].
Qed.

Lemma semax_needbits_seqH {Espec: OracleKind} (F: frame) (m0 m: mst) (n: Z) (NB c: statement)
    (R: ret_assert):
  semax Delta_inflate (loop_stateH F m) NB (normal_ret_assert (loop_stateH F (needbits n m))) ->
  mwf m -> n <= 32 ->
  RA_break R = RA_normal (case_postH F m0) ->
  (m_leave (needbits n m) = 1 -> stepf (f_flush F) lenfix_list distfix_list m0 = IBrk (needbits n m)) ->
  semax Delta_inflate (!! (m_leave (needbits n m) = 0) && loop_stateH F (needbits n m)) c R ->
  semax Delta_inflate (loop_stateH F m)
    (Ssequence (Ssequence NB (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)) c) R.
Proof.
  intros HNB W Hn HR Hbrk Hc.
  apply semax_seq with (Q := !! (m_leave (needbits n m) = 0) && loop_stateH F (needbits n m)); [ | exact Hc].
  eapply semax_seq'; [ exact HNB | ].
  apply (semax_ifleaveH F m0); auto. apply mwf_needbits; auto.
Qed.

(* the same for the right-nested form `NB; (if (leave) break; c)` that clightgen gives most sites *)
Lemma semax_needbits_seq_rH {Espec: OracleKind} (F: frame) (m0 m: mst) (n: Z) (NB c: statement)
    (R: ret_assert):
  semax Delta_inflate (loop_stateH F m) NB (normal_ret_assert (loop_stateH F (needbits n m))) ->
  mwf m -> n <= 32 ->
  RA_break R = RA_normal (case_postH F m0) ->
  (m_leave (needbits n m) = 1 -> stepf (f_flush F) lenfix_list distfix_list m0 = IBrk (needbits n m)) ->
  semax Delta_inflate (!! (m_leave (needbits n m) = 0) && loop_stateH F (needbits n m)) c R ->
  semax Delta_inflate (loop_stateH F m)
    (Ssequence NB (Ssequence (Sifthenelse (Etempvar _leave tint) Sbreak Sskip) c)) R.
Proof.
  intros. apply seq_assoc. eapply semax_needbits_seqH; eauto.
Qed.
