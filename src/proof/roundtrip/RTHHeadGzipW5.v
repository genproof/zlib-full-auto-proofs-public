(* RT-H: mechanical port of inflate/HeadGzipW5.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* inflate(), switch case HEAD: the gzip branch (after NEEDBITS(16), t'7 true), from the machine m1 after NEEDBITS(16),
   proved with the hypothesis that no window is there when wbits = 0 (Inv3.v s3_head; without
   it the code's `if (state->wbits == 0) state->wbits = 15;` would change the size of win_rep's window object).
   It ends with break, with the machine the model gives (HeadDefs5.v head_gzip_m). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHCaseHyps5.
Require Import Zlib.proof.inflate.HeadDefs5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.roundtrip.RTHHeadGzipKit5.
Require Export Zlib.proof.inflate.HeadGzipW5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.



(* the gzip branch, given that a window is never there with wbits = 0 (Inv3.v s3_head) *)
Lemma head_gzip5_wH {Espec: OracleKind} (F: frame) (m0 m1: mst) (R: ret_assert):
  frame_ok5 F -> mwf m1 -> m_leave m1 = 0 ->
  (i_wbits (m_s m1) = 0 -> i_win (m_s m1) = false) ->
  RA_break R = RA_normal (case_post2H F m0) ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk (head_gzip_m m1) ->
  semax Delta_cases5 (loop_stateH F m1) head_GZIP R.
Proof.
  intros [FOK HFl] W HL HWin HR E.
  pose proof FOK as (_ & _ & _ & HRT).
  pose proof (sw_check _ (mw_s _ W)) as RC. pose proof (mw_hold _ W) as RH.
  pose proof (sw_wbits _ (mw_s _ W)) as RWB.
  remember (if i_wbits (m_s m1) =? 0 then 15 else i_wbits (m_s m1)) as w eqn:Ew.
  rewrite loop_state_gsplitH. unfold head_GZIP.
  apply semax_seq' with (P' := loop_state_gH F m1 (zv (i_mode (m_s m1))) (lv (i_check (m_s m1))) (zv w)).
  { unfold loop_state_gH. abbreviate_semax. forward. forward_if.
    - forward. entailer!. rewrite H1, Z.eqb_refl. cancel.
    - forward. entailer!. rewrite (proj2 (Z.eqb_neq _ _) H1). cancel. }
  unfold loop_state_gH. abbreviate_semax.
  forward_call (0, nullval, 0, true, Tsh, nullval, 0, 0, @nil val, @nil Z, false, Tsh, f_gv F, f_tsh F).
  { cancel. }
  Intros vret. subst vret.
  forward.
  assert (R0: lrange 0) by (unfold lrange; rep_lia).
  eapply semax_seq' with
    (P' := loop_state_gH F m1 (zv (i_mode (m_s m1))) (lv (ref_crc32 0 (hbytes2 (m_hold m1)))) (zv w)).
  { apply semax_dowhile0_g. unfold loop_state_gH.
    frame_crc_g (semax_crc2_HEAD (f_sp F) (f_vhbuf F) (f_gv F) (f_tsh F) (m_hold m1) 0 HRT RH R0). }
  eapply semax_seq' with
    (P' := loop_state_gH F (initbits m1) (zv (i_mode (m_s m1))) (lv (ref_crc32 0 (hbytes2 (m_hold m1)))) (zv w)).
  { apply semax_dowhile0_g. unfold loop_state_gH. abbreviate_semax. forward. forward. entailer!.
    apply derives_refl. }
  unfold loop_state_gH. abbreviate_semax.
  forward. forward.
  rewrite HR. cbv [case_post2H RA_normal].
  Exists (head_gzip_m m1).
  apply andp_right; [apply prop_right; exact E | ].
  rewrite head_gzip_m_eq, <- Ew, (loop_state_head_gzipH F m1 w _ HWin Ew).
  unfold loop_state_gH. entailer!.
Qed.


(* the hypothesis from the caller's invariant (cases5_HEAD: mwf3 m, mode HEAD, wrap <> 0; m1 = needbits 16 m) *)



