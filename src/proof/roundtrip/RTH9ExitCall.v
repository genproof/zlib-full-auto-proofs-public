(* inflate()'s exit inf_leave, the window update (RTH9ExitWin.v) for calls of any uInt size: the call of
   updatewindow and the whole update, from the proof scripts of src/proof/hl/inflate_api/HlBody5ExitWin.v and
   Body5ExitWin.v (copied by hand) with the output space up to Int.max_unsigned and InvW.mwf3W. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.hl.inflate_api.HlBody5Parts.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitKit.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitWin.
Require Import Zlib.proof.inflate.InvW.

Require Import Zlib.proof.roundtrip.RTH9ExitWin.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma win_data_len9: forall m, m_left m <= m_out m <= m_aout m -> Zlength (m_ow m) <= m_aout m <= Int.max_unsigned ->
  Zlength (win_data m) = m_out m - m_left m.
Proof.
  intros m A B. pose proof (Zlength_nonneg (m_ow m)). unfold win_data, u32, m_left in *.
  rewrite Z.mod_small by rep_lia. rewrite Zlength_sublist; lia.
Qed.

Lemma win_data_slice9: forall m (oc: list val) olo on,
  m_left m <= m_out m <= m_aout m -> Zlength (m_ow m) <= m_aout m <= Int.max_unsigned ->
  0 <= olo -> olo + Zlength (m_ow m) <= on -> Zlength oc = on ->
  sublist (olo + Zlength (m_ow m) - Zlength (win_data m)) (olo + Zlength (m_ow m))
    (sublist 0 olo oc ++ byte_vals (m_ow m) ++ sublist (olo + Zlength (m_ow m)) on oc) = byte_vals (win_data m).
Proof.
  intros m oc olo on A B C D E. rewrite (win_data_len9 m A B).
  pose proof (Zlength_nonneg (m_ow m)).
  unfold win_data, u32, m_left in *. rewrite Z.mod_small by rep_lia.
  unfold byte_vals. list_solve.
Qed.

Lemma semax_ex_call9 {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (v: val) (R: ret_assert):
  frame_ok5 F -> swf (m_s m) -> m_sow m = Zlength (m_ow m) -> m_left m <= m_out m <= m_aout m ->
  Zlength (m_ow m) <= m_aout m <= Int.max_unsigned -> bytes_ok (m_ow m) ->
  (i_win (m_s m) = false ->
   ENTAIL Delta_inflate5_hl,
     PROPx [] (LOCALx (ret_locals F)
       (SEPx [mem_rep_hl (set_f_winp_dt F nullval (f_dt F)) (set_mode m MEM); locals_rep F; hdr_tok F m;
              mem_mgr (f_gv F); zfuncs (f_gv F); X]))
     |-- RA_return R (Some (zv Z_MEM_ERROR))) ->
  semax Delta_inflate5_hl (lstate_t_hl F X m v) ex_call
    (overridePost (EX winp: val, !! (i_win (m_s m) = true -> winp = f_winp F) &&
                     lstate_hl (set_f_winp_dt F winp (f_dt F)) X (mupd m)) R).
Proof.
  intros [FOK FL] SW ESOW RO RA BO HMEM. pose proof FOK as (HWS & HWH & HRG & HRT).
  cbv beta iota zeta delta [ex_call ex_win inflate_exit f_inflate fn_body].
  unfold lstate_t_hl, mem_rep_hl.
  rewrite state_rep_wp, win_rep_wp.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  destruct ob as [osh op olo on oc].
  frame_simpl. unfold strm_rep. rewrite ESOW.
  set (wp := if i_win (m_s m) then winp else nullval).
  abbreviate_semax.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
  Intros.
  pose proof (win_data_len9 m RO RA) as HL.
  destruct H0 as (Hosh & Hop & Holo & Haout & Hlo & Hoc & Hon).
  pose proof (win_data_slice9 m oc olo on RO RA Holo ltac:(lia) Hoc) as HS.
  pose proof (win_data_bytes m BO) as HB.
  forward. forward.
  forward_call (gv, shs, strmp, (in_ptr ib (m_snx m),
      (Vint (Int.repr (Zlength (m_inp m) - m_snx m)),
       (Vlong (Int64.repr (m_tin m)),
        (offset_val (olo + Zlength (m_ow m)) op,
         (Vint (Int.repr (m_aout m - Zlength (m_ow m))),
          (Vlong (Int64.repr (m_tout m)),
           (msg_val gv (m_msg m),
            (sp, (zca, (zcf, (nullval, (Vint (Int.repr dt), (Vlong (Int64.repr (m_adler m)), vres))))))))))))),
     sp, headp, wp, m_s m, osh, op, on, sublist 0 olo oc ++ byte_vals (m_ow m) ++ sublist (olo + Zlength (m_ow m)) on oc,
     olo + Zlength (m_ow m), win_data m).
  { rewrite HL. unfold m_left. entailer!. }
  { split; [unfold stream_ok_val2; auto | ].
    rewrite HL. unfold m_left in *.
    split; [lia | ]. split; [rep_lia | ].
    split; [unfold byte_vals; autorewrite with sublist; lia | ].
    intro E. unfold wp. rewrite E. reflexivity. }
  Intros vret. destruct vret as [r winp']. cbn [fst snd] in *.
  destruct H0 as [[R0 HW] | (R1 & HWF & HWN)].
  - subst r. cbn [Z.eqb].
    forward_if; [contradiction | ].
    forward.
    assert (HWW: i_win (m_s m) = true -> winp' = winp) by (intro E; rewrite (HW E); unfold wp; rewrite E; reflexivity).
    destruct R as [Rn Rb Rc Rr]; cbn [RA_normal].
    Exists winp'.
    unfold lstate_hl, mem_rep_hl.
    rewrite head_part_winp_hl, head_part_mupd_hl, hdr_tok_winp, hdr_tok_mupd, locals_rep_winp, m_have_mupd, m_left_mupd.
    unfold set_f_winp_dt. frame_simpl_goal.
    cbn [mupd upd_s set_m_s m_s m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_snx m_sow m_tin
         m_tout m_msg m_adler].
    unfold strm_rep. rewrite <- Hzca, <- Hzcf. rewrite ?ESOW.
    entailer!.
    unfold out_ok. split; [exact Hosh | ]. split; [exact Hop | ]. repeat split; lia.
  - subst r winp'. cbn [Z.eqb].
    forward_if; [ | discriminate].
    rewrite state_rep_esplit. unfold state_f9. Intros.
    forward.
    apply semax_ret_const_hl with (r := Z_MEM_ERROR); [intro rho; reflexivity | entailer! | ].
    unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
    replace (RA_return (overridePost _ R)) with (RA_return R) by (destruct R; reflexivity).
    eapply derives_trans; [ | apply (HMEM HWF)].
    apply andp_right; [apply andp_left1, derives_refl | ].
    unfold ret_locals, mem_rep_hl. rewrite head_part_set_mode_hl, head_part_winp_hl, state_rep_esplit. unfold state_f9, strm_rep.
    unfold set_f_winp_dt. frame_simpl_goal.
    cbn [set_mode upd_s set_m_s m_s m_snx m_inp m_tin m_sow m_aout m_tout m_msg m_adler m_ow].
    rewrite state_rep_e_set_mode, win_rep_set_mode.
    cbn [i_mode i_last i_wrap i_flags i_check i_total i_wsize i_hold i_bits set_i_mode].
    rewrite <- Hzca, <- Hzcf. rewrite ?ESOW. unfold MEM.
    entailer!.
Qed.

Lemma swf_restore9: forall m, mwfW m -> swf (m_s (restore m)).
Proof.
  intros m W. pose proof (mwW_hold _ W). pose proof (mwW_bits _ W).
  destruct (mwW_s _ W); constructor; cbn [restore upd_s set_m_s m_s set_i_bits set_i_hold i_mode i_last i_wrap
    i_havedict i_flags i_dmax i_check i_total i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits
    i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next
    i_lens i_codes i_sane i_back i_was]; auto.
Qed.

Lemma semax_ex_win9 {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (R: ret_assert):
  frame_ok5 F -> mwf3W m -> out_inv m ->
  (leave_ok (f_flush F) m = true -> i_win (m_s m) = false ->
   ENTAIL Delta_inflate5_hl,
     PROPx [] (LOCALx (ret_locals F)
       (SEPx [mem_rep_hl (set_f_winp_dt F nullval (f_dt F)) (set_mode (restore m) MEM); locals_rep F; hdr_tok F m;
              mem_mgr (f_gv F); zfuncs (f_gv F); X]))
     |-- RA_return R (Some (zv Z_MEM_ERROR))) ->
  semax Delta_inflate5_hl (lstate_hl F X (restore m)) ex_win
    (overridePost (EX winp: val, !! (i_win (m_s m) = true -> winp = f_winp F) &&
                     lstate_hl (set_f_winp_dt F winp (f_dt F)) X (mwin (f_flush F) m)) R).
Proof.
  intros FO [W W3] [O1 [O2 _]] HMEM. pose proof FO as [(HWS & _) FL].
  pose proof (swf_restore9 m W) as SR.
  rewrite ex_win_eq.
  eapply semax_seq'.
  { apply semax_ex_cond9; auto.
    - apply wsize_range. exact SR.
    - exact (sw_mode _ SR).
    - exact (mwW_out _ W).
    - exact (mwfW_left _ W). }
  change (leave_ok (f_flush F) (restore m)) with (leave_ok (f_flush F) m).
  destruct (leave_ok (f_flush F) m) eqn:HB.
  - unfold lstate_t_hl. abbreviate_semax. forward_if; [ | exfalso; exact (Int.one_not_zero H)].
    unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
    replace (mwin (f_flush F) m) with (mupd (restore m)) by (unfold mwin; rewrite HB; reflexivity).
    change (i_win (m_s m)) with (i_win (m_s (restore m))).
    pose proof (mwW_ow _ W) as [OW BO]. pose proof (mwW_aout _ W) as AO.
    change Delta with Delta_inflate5_hl. specialize (HMEM eq_refl).
    eapply semax_pre; [ | apply (semax_ex_call9 F X (restore m) (Vint (Int.repr (b2z true))) R); auto;
                          exact (conj OW (proj2 AO))].
    unfold lstate_t_hl. entailer!.
  - unfold lstate_t_hl. abbreviate_semax. forward_if; [exfalso; exact (H eq_refl) | ].
    forward.
    destruct R as [Rn Rb Rc Rr]; cbn [RA_normal overridePost].
    Exists (f_winp F). rewrite set_f_winp_dt_id.
    replace (mwin (f_flush F) m) with (restore m) by (unfold mwin; rewrite HB; reflexivity).
    unfold lstate_hl. entailer!.
Qed.
