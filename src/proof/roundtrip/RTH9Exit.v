(* The exit inf_leave of inflate()'s body from a wide machine (RTH9Parts.exit_part9_stmt): the proof of the
   headless port src/proof/hl/inflate_api/HlBody5Exit.v (copied by hand), with the wide pieces RTH9ExitCall.v
   (the window update) and RTH9ExitTail.v / RTH9ExitChk.v / RTH9ExitEnd.v (the tail, assembled here) and the
   machine invariant InvW.mwf3W. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTH9Parts.
Require Import Zlib.proof.hl.inflate_api.HlBody5Parts.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitKit.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitWin.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitTail.
Require Import Zlib.proof.hl.inflate_api.HlBody5Exit.
Require Import Zlib.proof.inflate.InvW.
Require Import Zlib.proof.roundtrip.RTH9ExitWin.
Require Import Zlib.proof.roundtrip.RTH9ExitCall.
Require Import Zlib.proof.roundtrip.RTH9ExitTail.
Require Import Zlib.proof.roundtrip.RTH9ExitChk.
Require Import Zlib.proof.roundtrip.RTH9ExitEnd.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the machine after RESTORE and the window update is what the tail needs (Body5Exit.tail_facts_mwin for mwfW) *)
Lemma tail_facts_mwin9: forall flush m, mwfW m -> out_inv m -> tail_facts9 (mwin flush m).
Proof.
  intros flush m W [O1 [O2 _]].
  pose proof (mwW_s _ W) as S. pose proof (mwW_ow _ W) as [OW BO]. pose proof (mwW_aout _ W) as AO.
  pose proof (mwW_inp _ W) as [IP _]. pose proof (mwW_nx _ W) as NX. pose proof (mwW_bits _ W) as BI.
  pose proof (mwW_tin _ W). pose proof (mwW_tout _ W). pose proof (mwW_ret _ W). pose proof (mwW_in _ W).
  pose proof (sw_check _ S). pose proof (sw_total _ S). pose proof (sw_wrap_range _ S). pose proof (sw_flags _ S).
  pose proof (sw_last _ S). pose proof (sw_mode _ S).
  unfold mwin. destruct (leave_ok flush m).
  - destruct (updatewindow_keep (m_s (restore m)) (win_data (restore m)))
      as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
    unfold tail_facts9.
    change (m_s (upd_s (restore m) (fun s => set_i_win (updatewindow s (win_data (restore m))) true)))
      with (set_i_win (updatewindow (m_s (restore m)) (win_data (restore m))) true).
    cbn [i_mode i_last i_wrap i_flags i_check i_total i_bits set_i_win].
    rewrite A1, A2, A3, A4, A5, A6, A8.
    cbn [restore upd_s set_m_s set_m_snx set_m_sow m_s m_snx m_sow m_nx m_ow m_inp m_in m_out m_aout m_tin
         m_tout m_bits m_ret m_hold set_i_bits set_i_hold i_mode i_last i_wrap i_flags i_check i_total i_bits]
      in *.
    unfold m_left in *. cbn [m_aout m_ow upd_s set_m_s restore set_m_snx set_m_sow].
    unfold lrange, srange in *. repeat split; auto; lia.
  - unfold tail_facts9.
    cbn [restore upd_s set_m_s set_m_snx set_m_sow m_s m_snx m_sow m_nx m_ow m_inp m_in m_out m_aout m_tin
         m_tout m_bits m_ret m_hold set_i_bits set_i_hold i_mode i_last i_wrap i_flags i_check i_total i_bits].
    unfold m_left in *. cbn [m_aout m_ow upd_s set_m_s restore set_m_snx set_m_sow].
    unfold lrange, srange in *. repeat split; auto; lia.
Qed.

(* the tail (HlBody5ExitTail.ex_tail_ok_hl for tail_facts9) *)
Lemma ex_tail_ok9 : ex_tail_stmt9.
Proof.
  intros Espec F X m R FOK TF HRET.
  rewrite leave_tail_eq in HRET. cbn [r_m r_ret] in HRET.
  change (res_dt F (Res (lt_ret (f_flush F) m) (lt_m2 m) (Some (lt_dt (lt_m2 m))))) with (lt_dt (lt_m2 m)) in HRET.
  pose proof (lt_inn_eq9 m TF) as EI. pose proof (lt_out_eq9 m TF) as [EO RO].
  pose proof (lt_m2_keep m) as (K1 & K2 & K3 & K4 & K5).
  pose proof TF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18 & T19).
  apply ex_tail_split with (Q := tst_hl F X m (lt_m1 m) (lt_inn m) (lt_out m))
                           (S := tst_hl F X m (lt_m2 m) (lt_inn m) (lt_out m)).
  - apply et_cnt_ok9; auto.
  - apply et_chk_ok9; auto.
  - apply et_end_ok9; auto.
    + rewrite K1, K2. exact T3.
    + rewrite K2. exact T16.
    + rewrite K3. exact T17.
    + rewrite K4. exact T18.
    + rewrite K5. exact T19.
    + rep_lia.
    + rep_lia.
    + rewrite K5. unfold lt_ret, lt_r in *. exact HRET.
Qed.

Lemma exit_part9 : exit_part9_stmt.
Proof.
  intros Espec F X m R FO W L O WI HEX.
  pose proof FO as [(HWS & HWH & HRG & HRT) FL].
  rewrite inflate_exit_eq.
  eapply semax_seq'; [apply semax_ex_restore_hl; exact HWS | ].
  eapply semax_seq.
  { apply semax_ex_win9; auto.
    intros HB E.
    exact (HEX (Res Z_MEM_ERROR (set_mode (restore m) MEM) None) nullval
               (il_mem _ _ HB E) (fun E' => ltac:(congruence))). }
  apply extract_exists_pre. intro winp. apply semax_extract_prop. intro HWP.
  apply (ex_tail_ok9 Espec (set_f_winp_dt F winp (f_dt F)) X (mwin (f_flush F) m) R).
  - exact FO.
  - apply tail_facts_mwin9; [exact (proj1 W) | exact O].
  - rewrite hdr_tok_mwin, locals_rep_winp, fw_ret_locals, fw_winp, fw_flush, fw_gv, fw_res_dt, fw_twice.
    pose proof (HEX (leave_fin (f_flush F) m) winp (il_ok _ _) HWP) as E.
    rewrite leave_fin_eq in E. exact E.
Qed.
