(* RT-H: mechanical port of inflate/CaseCommon.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* Common definitions of the per-case lemmas of inflate(): the labeled statements of the switch, the
   variable and function specifications of inflate's body, and helper lemmas. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.Callees.
Require Export Zlib.proof.roundtrip.RTHLoop.
Require Export Zlib.proof.roundtrip.RTHLoop2.
Require Export Zlib.proof.inflate.CaseCommon.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the first switch of a statement *)
(* the switch (state->mode) of inflate() *)
(* the suffix of the switch from the i-th case (case i is mode HEAD + i; index 32 is `default`) *)
(* the statement of the case at index i, with the identifiers folded *)
(* reduce the projections of a concrete frame *)
(* normalize model terms: unfold the setters and the small state updates, reduce the projections *)
Ltac mnormH := unfold head_partH in *; cbn [i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was h_text h_time h_xflags h_os h_xp h_extra_len h_extra_max h_xbuf h_np h_name_max h_nbuf h_cp h_comm_max h_cbuf h_hcrc h_done m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout m_snx m_sow set_i_mode set_i_last set_i_wrap set_i_havedict set_i_flags set_i_dmax set_i_check set_i_total set_i_head set_i_wbits set_i_wsize set_i_whave set_i_wnext set_i_win set_i_wdata set_i_hold set_i_bits set_i_length set_i_offset set_i_extra set_i_lencode set_i_distcode set_i_lenbits set_i_distbits set_i_ncode set_i_nlen set_i_ndist set_i_have set_i_next set_i_lens set_i_codes set_i_sane set_i_back set_i_was set_h_text set_h_time set_h_xflags set_h_os set_h_xp set_h_extra_len set_h_extra_max set_h_xbuf set_h_np set_h_name_max set_h_nbuf set_h_cp set_h_comm_max set_h_cbuf set_h_hcrc set_h_done set_m_s set_m_h set_m_inp set_m_aout set_m_nx set_m_ow set_m_hold set_m_bits set_m_in set_m_out set_m_ret set_m_leave set_m_adler set_m_msg set_m_tin set_m_tout set_m_snx set_m_sow upd_s upd_h set_mode set_leave set_bad restore m_mode m_have m_left initbits dropbits bytebits head_partH] in *.
Ltac mnorm_goalH := unfold head_partH, win_rep; cbn [i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was h_text h_time h_xflags h_os h_xp h_extra_len h_extra_max h_xbuf h_np h_name_max h_nbuf h_cp h_comm_max h_cbuf h_hcrc h_done m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout m_snx m_sow set_i_mode set_i_last set_i_wrap set_i_havedict set_i_flags set_i_dmax set_i_check set_i_total set_i_head set_i_wbits set_i_wsize set_i_whave set_i_wnext set_i_win set_i_wdata set_i_hold set_i_bits set_i_length set_i_offset set_i_extra set_i_lencode set_i_distcode set_i_lenbits set_i_distbits set_i_ncode set_i_nlen set_i_ndist set_i_have set_i_next set_i_lens set_i_codes set_i_sane set_i_back set_i_was set_h_text set_h_time set_h_xflags set_h_os set_h_xp set_h_extra_len set_h_extra_max set_h_xbuf set_h_np set_h_name_max set_h_nbuf set_h_cp set_h_comm_max set_h_cbuf set_h_hcrc set_h_done set_m_s set_m_h set_m_inp set_m_aout set_m_nx set_m_ow set_m_hold set_m_bits set_m_in set_m_out set_m_ret set_m_leave set_m_adler set_m_msg set_m_tin set_m_tout set_m_snx set_m_sow upd_s upd_h set_mode set_leave set_bad restore m_mode m_have m_left initbits dropbits bytebits head_partH].

(* the context of inflate()'s body (Callees.v) *)
(* ---------------------------------------------------------------------------------------------- *)
(* byte arrays: a pointer into an array as the address of an element                             *)



(* the output object after one more byte *)
