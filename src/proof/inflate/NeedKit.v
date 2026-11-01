(* `NEEDBITS(n); if (leave) break; c` inside a case: from a NEEDBITS loop lemma (NeedBits*.v), the break
   when the input runs out, and the continuation c with leave = 0. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.CaseRet.
Require Export Zlib.proof.inflate.MwfLemmas.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma leave_from_if: forall l, 0 <= l <= 1 -> Int.repr l <> Int.zero -> l = 1.
Proof. intros l H E. destruct (Z.eq_dec l 0); [subst; contradiction | lia]. Qed.

Lemma leave_from_if0: forall l, 0 <= l <= 1 -> Int.repr l = Int.zero -> l = 0.
Proof.
  intros l H E. destruct (Z.eq_dec l 0); auto.
  assert (l = 1) by lia. subst. discriminate.
Qed.

Lemma RA_break_overridePost: forall Q R, RA_break (overridePost Q R) = RA_break R.
Proof. intros Q [Rn Rb Rc Rr]. reflexivity. Qed.

Lemma RA_normal_overridePost: forall Q R, RA_normal (overridePost Q R) = Q.
Proof. intros Q [Rn Rb Rc Rr]. reflexivity. Qed.

(* the break of `if (leave) break;` after a pass that leaves with machine m1 *)
Lemma semax_ifleave {Espec: OracleKind} (F: frame) (m0 m1: mst) (R: ret_assert):
  mwf m1 ->
  RA_break R = RA_normal (case_post F m0) ->
  (m_leave m1 = 1 -> stepf (f_flush F) lenfix_list distfix_list m0 = IBrk m1) ->
  semax Delta_inflate (loop_state F m1) (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)
    (overridePost (!! (m_leave m1 = 0) && loop_state F m1) R).
Proof.
  intros W1 HR Hbrk.
  pose proof (mw_leave _ W1) as HL1.
  unfold loop_state. abbreviate_semax.
  forward_if.
  - forward.
    destruct R as [Rn Rb Rc Rr]. simpl in HR. subst Rb.
    assert (E: m_leave m1 = 1) by (apply leave_from_if; auto).
    change (RA_break _) with (RA_normal (case_post F m0)).
    unfold case_post. unfold RA_normal at 1.
    Exists m1. apply andp_right; [apply prop_right; auto | unfold loop_state; entailer!].
  - forward.
    assert (E: m_leave m1 = 0) by (apply leave_from_if0; auto).
    destruct R as [Rn Rb Rc Rr]. unfold RA_normal at 1.
    apply andp_right; [apply prop_right; auto | entailer!].
Qed.

Lemma semax_needbits_seq {Espec: OracleKind} (F: frame) (m0 m: mst) (n: Z) (NB c: statement)
    (R: ret_assert):
  semax Delta_inflate (loop_state F m) NB (normal_ret_assert (loop_state F (needbits n m))) ->
  mwf m -> n <= 32 ->
  RA_break R = RA_normal (case_post F m0) ->
  (m_leave (needbits n m) = 1 -> stepf (f_flush F) lenfix_list distfix_list m0 = IBrk (needbits n m)) ->
  semax Delta_inflate (!! (m_leave (needbits n m) = 0) && loop_state F (needbits n m)) c R ->
  semax Delta_inflate (loop_state F m)
    (Ssequence (Ssequence NB (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)) c) R.
Proof.
  intros HNB W Hn HR Hbrk Hc.
  apply semax_seq with (Q := !! (m_leave (needbits n m) = 0) && loop_state F (needbits n m)); [ | exact Hc].
  eapply semax_seq'; [ exact HNB | ].
  apply (semax_ifleave F m0); auto. apply mwf_needbits; auto.
Qed.

(* the same for the right-nested form `NB; (if (leave) break; c)` that clightgen gives most sites *)
Lemma semax_needbits_seq_r {Espec: OracleKind} (F: frame) (m0 m: mst) (n: Z) (NB c: statement)
    (R: ret_assert):
  semax Delta_inflate (loop_state F m) NB (normal_ret_assert (loop_state F (needbits n m))) ->
  mwf m -> n <= 32 ->
  RA_break R = RA_normal (case_post F m0) ->
  (m_leave (needbits n m) = 1 -> stepf (f_flush F) lenfix_list distfix_list m0 = IBrk (needbits n m)) ->
  semax Delta_inflate (!! (m_leave (needbits n m) = 0) && loop_state F (needbits n m)) c R ->
  semax Delta_inflate (loop_state F m)
    (Ssequence NB (Ssequence (Sifthenelse (Etempvar _leave tint) Sbreak Sskip) c)) R.
Proof.
  intros. apply seq_assoc. eapply semax_needbits_seq; eauto.
Qed.
