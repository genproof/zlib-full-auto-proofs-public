(* The branches of the header cases EXLEN and EXTRA that return in a header mode, for calls of any uInt size
   (RTH9WKit.case_ok9v, the header RTH9HDefs.hd9): a NEEDBITS that runs out of input (`if (leave) break;` with
   leave = 1) and EXTRA's copy that does not reach the end of the extra field (state->length <> 0 after the
   available input was copied).  In both the switch is left with the machine of the model's pass, still in its
   header mode, so its header is the partial header hd6 with the bytes copied so far. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHEXTRA6Cpy.
Require Import Zlib.proof.hl9h.roundtrip.H9HRTHEx6Kit.
Require Import Zlib.proof.inflate.NeedKit.
Require Import Zlib.proof.inflate.ExtraBody5.
Require Import Zlib.proof.roundtrip.RTH9HDefs.
Require Import Zlib.proof.roundtrip.RTH9WKit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* NEEDBITS keeps the state and the header: in a header mode the header after it is the partial header before *)
Lemma hd6_hd9_needbits: forall F n m, hdr_mode (m_mode m) = true -> hd6 F m |-- hd9 F (needbits n m).
Proof.
  intros F n m H. destruct (needbits_sh n m) as [S1 H1].
  unfold hd9. replace (m_mode (needbits n m)) with (m_mode m) by (unfold m_mode; rewrite S1; reflexivity).
  rewrite H. rewrite (hd6_ext F m (needbits n m)) by (rewrite ?S1, ?H1; reflexivity). apply derives_refl.
Qed.

(* if (leave) break; after a NEEDBITS: with leave = 1 the switch is left (the model's pass ends in m1) *)
Lemma semax_ifleave9 {Espec: OracleKind} (F: frame) (m0 m1: mst) (X: mpred) (R: ret_assert):
  mwf9 m1 -> RA_break R = RA_normal (case_post9 F m0) ->
  (m_leave m1 = 1 -> stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk m1) ->
  (X |-- hd9 F m1) ->
  semax Delta_cases5 (loop_stateH F m1 * (fun _ => X)) (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)
    (overridePost (!! (m_leave m1 = 0) && (loop_stateH F m1 * (fun _ => X))) R).
Proof.
  intros W1 HR Hbrk HX.
  pose proof (mw9_leave _ W1) as HL1.
  unfold loop_stateH. rewrite PQR_tok. abbreviate_semax.
  forward_if.
  - forward.
    destruct R as [Rn Rb Rc Rr]. simpl in HR. subst Rb.
    assert (E: m_leave m1 = 1) by (apply leave_from_if; auto).
    change (RA_break _) with (RA_normal (case_post9 F m0)).
    unfold case_post9. unfold RA_normal at 1.
    Exists m1. apply andp_right; [apply prop_right; auto | ].
    unfold post9, loop_stateH. rewrite PQR_tok. simpl app. sep_apply HX. entailer!.
  - forward.
    assert (E: m_leave m1 = 0) by (apply leave_from_if0; auto).
    destruct R as [Rn Rb Rc Rr]. unfold RA_normal at 1.
    apply andp_right; [apply prop_right; auto | ].
    entailer!.
Qed.

(* NEEDBITS(n); if (leave) break; c -- with a closed SEP item X (the header) framed *)
Lemma semax_needbits_seq9 {Espec: OracleKind} (F: frame) (m0 m: mst) (n: Z) (X: mpred) (NB c: statement)
    (R: ret_assert):
  semax Delta_cases5 (loop_stateH F m) NB (normal_ret_assert (loop_stateH F (needbits n m))) ->
  mwf9 m -> n <= 32 ->
  RA_break R = RA_normal (case_post9 F m0) ->
  (m_leave (needbits n m) = 1 -> stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk (needbits n m)) ->
  (X |-- hd9 F (needbits n m)) ->
  semax Delta_cases5 (!! (m_leave (needbits n m) = 0) && (loop_stateH F (needbits n m) * (fun _ => X))) c R ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => X))
    (Ssequence (Ssequence NB (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)) c) R.
Proof.
  intros HNB W Hn HR Hbrk HX Hc.
  apply semax_seq with (Q := !! (m_leave (needbits n m) = 0) && (loop_stateH F (needbits n m) * (fun _ => X)));
    [ | exact Hc].
  eapply semax_seq'; [ apply semax_frame_lsH; exact HNB | ].
  apply (semax_ifleave9 F m0); auto. apply mwf9_needbits; auto.
Qed.

(* EXTRA's leave: the copy stopped before the end of the extra field, the switch is left in mode EXTRA *)
Lemma ex_brk_ok9: forall F m m1,
  stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (set_leave m1) -> hdr_mode (m_mode m1) = true ->
  PROPx (PPx F m1) (LOCALx (LLx F (set_leave m1)) (SEPx (SLx6 F m1 (hdr_tok F m))))
  |-- RA_normal (case_post9 F m) * lift0 (hdr_tok F m).
Proof.
  intros F m m1 E HH. unfold case_post9. cbn [RA_normal]. rewrite exp_sepcon1. Exists (set_leave m1).
  rewrite sepcon_andp_prop'. apply andp_right; [apply prop_right; exact E | ].
  unfold post9, hd9. change (m_mode (set_leave m1)) with (m_mode m1). rewrite HH.
  change (PROPx (PPx F m1) (LOCALx (LLx F (set_leave m1)) (SEPx (SLx6 F m1 (hdr_tok F m)))))
    with (PROPx (PPx F (set_leave m1)) (LOCALx (LLx F (set_leave m1))
            (SEPx (SLx6 F (set_leave m1) (hdr_tok F m))))).
  rewrite <- ls_ex_tok6. change (lift0 (hdr_tok F m)) with (fun _ : environ => hdr_tok F m).
  intros rho. simpl. cancel.
Qed.
