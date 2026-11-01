(* inflate()'s exit inf_leave (Body5Parts.v exit_part5_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Body5Parts.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.inflate_api.Body5ExitKit.
Require Import Zlib.proof.inflate_api.Body5ExitWin.
Require Import Zlib.proof.inflate_api.Body5ExitTail.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the machine after RESTORE and the window update is what the tail needs *)
Lemma tail_facts_mwin: forall flush m, mwf m -> out_inv m -> tail_facts (mwin flush m).
Proof.
  intros flush m W [O1 [O2 _]].
  pose proof (mw_s _ W) as S. pose proof (mw_ow _ W) as [OW BO]. pose proof (mw_aout _ W) as AO.
  pose proof (mw_inp _ W) as [IP _]. pose proof (mw_nx _ W) as NX. pose proof (mw_bits _ W) as BI.
  pose proof (mw_tin _ W). pose proof (mw_tout _ W). pose proof (mw_ret _ W). pose proof (mw_in _ W).
  pose proof (sw_check _ S). pose proof (sw_total _ S). pose proof (sw_wrap_range _ S). pose proof (sw_flags _ S).
  pose proof (sw_last _ S). pose proof (sw_mode _ S).
  unfold mwin. destruct (leave_ok flush m).
  - destruct (updatewindow_keep (m_s (restore m)) (win_data (restore m)))
      as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
    unfold tail_facts.
    change (m_s (upd_s (restore m) (fun s => set_i_win (updatewindow s (win_data (restore m))) true)))
      with (set_i_win (updatewindow (m_s (restore m)) (win_data (restore m))) true).
    cbn [i_mode i_last i_wrap i_flags i_check i_total i_bits set_i_win].
    rewrite A1, A2, A3, A4, A5, A6, A8.
    cbn [restore upd_s set_m_s set_m_snx set_m_sow m_s m_snx m_sow m_nx m_ow m_inp m_in m_out m_aout m_tin
         m_tout m_bits m_ret m_hold set_i_bits set_i_hold i_mode i_last i_wrap i_flags i_check i_total i_bits]
      in *.
    unfold m_left in *. cbn [m_aout m_ow upd_s set_m_s restore set_m_snx set_m_sow].
    unfold lrange, srange in *. repeat split; auto; lia.
  - unfold tail_facts.
    cbn [restore upd_s set_m_s set_m_snx set_m_sow m_s m_snx m_sow m_nx m_ow m_inp m_in m_out m_aout m_tin
         m_tout m_bits m_ret m_hold set_i_bits set_i_hold i_mode i_last i_wrap i_flags i_check i_total i_bits].
    unfold m_left in *. cbn [m_aout m_ow upd_s set_m_s restore set_m_snx set_m_sow].
    unfold lrange, srange in *. repeat split; auto; lia.
Qed.

Lemma hdr_tok_mwin: forall F w d flush m, hdr_tok (set_f_winp_dt F w d) (mwin flush m) = hdr_tok F m.
Proof.
  intros. unfold mwin. destruct (leave_ok flush m).
  - rewrite hdr_tok_winp.
    change (upd_s (restore m) (fun s => set_i_win (updatewindow s (win_data (restore m))) true))
      with (mupd (restore m)).
    rewrite hdr_tok_mupd. reflexivity.
  - reflexivity.
Qed.

Lemma fw_winp: forall F w d, f_winp (set_f_winp_dt F w d) = w.
Proof. reflexivity. Qed.
Lemma fw_flush: forall F w d, f_flush (set_f_winp_dt F w d) = f_flush F.
Proof. reflexivity. Qed.
Lemma fw_gv: forall F w d, f_gv (set_f_winp_dt F w d) = f_gv F.
Proof. reflexivity. Qed.
Lemma fw_twice: forall F w d w' d', set_f_winp_dt (set_f_winp_dt F w d) w' d' = set_f_winp_dt F w' d'.
Proof. reflexivity. Qed.
Lemma fw_res_dt: forall F w r, res_dt (set_f_winp_dt F w (f_dt F)) r = res_dt F r.
Proof. reflexivity. Qed.
Lemma fw_ret_locals: forall F w d, ret_locals (set_f_winp_dt F w d) = ret_locals F.
Proof. reflexivity. Qed.

Lemma exit_part5 : exit_part5_stmt.
Proof.
  intros Espec F X m R FO W L O WI HEX.
  pose proof FO as [(HWS & HWH & HRG & HRT) FL].
  rewrite inflate_exit_eq.
  eapply semax_seq'; [apply semax_ex_restore; exact HWS | ].
  eapply semax_seq.
  { apply semax_ex_win; auto.
    intros HB E.
    exact (HEX (Res Z_MEM_ERROR (set_mode (restore m) MEM) None) nullval
               (il_mem _ _ HB E) (fun E' => ltac:(congruence))). }
  apply extract_exists_pre. intro winp. apply semax_extract_prop. intro HWP.
  apply (ex_tail_ok Espec (set_f_winp_dt F winp (f_dt F)) X (mwin (f_flush F) m) R).
  - exact FO.
  - apply tail_facts_mwin; [exact (proj1 W) | exact O].
  - rewrite hdr_tok_mwin, locals_rep_winp, fw_ret_locals, fw_winp, fw_flush, fw_gv, fw_res_dt, fw_twice.
    pose proof (HEX (leave_fin (f_flush F) m) winp (il_ok _ _) HWP) as E.
    rewrite leave_fin_eq in E. exact E.
Qed.
