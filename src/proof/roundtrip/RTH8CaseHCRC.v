(* Case HCRC (index 8) of inflate() with a partial gz_header attached, on a call that passes the header
   (RTH8Defs.case_ok8): it checks the header CRC, writes head->hcrc and head->done = 1 and goes to TYPE; past
   the header the gz_header is RTH8Spec.head_rep8a (hd8a): the header of mode HCRC (RTHSpec.head_rep6 at phase 4)
   with hcrc and done written, the buffers keeping the bytes inflate copied.  The proof follows the v6 case
   (RTHCaseHCRC6.rth_hcrc), whose lemmas it uses; there the header past HCRC had to be complete. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH8Defs.
Require Import Zlib.proof.roundtrip.RTH8CaseKit.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHCaseHyps5.
Require Import Zlib.proof.roundtrip.RTHNeedKit5.
Require Import Zlib.proof.roundtrip.RTHNeedBits.
Require Import Zlib.proof.roundtrip.RTHNeedBits2_5.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.roundtrip.RTHModeKit5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.adler32.Spec.
Require Import Zlib.proof.inflate.Cases5_HD.
Require Import Zlib.proof.roundtrip.RTHCaseHCRC6.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the pass of HCRC: no leave, and past the header done = 1 *)
Lemma hpass8_hcrc: forall flush n m, m_mode m = HCRC -> hpass8 flush (S n) m ->
  exists m', stepf2 flush lenfix_list distfix_list m = IBrk m' /\ m_leave m' = 0 /\
    (hdr_mode (m_mode m') = false -> h_done (m_h m') = 1).
Proof.
  intros flush n m HM HP. cbn [hpass8] in HP. rewrite HM in HP. cbv [hdr_mode] in HP. cbn in HP.
  destruct (stepf2 flush lenfix_list distfix_list m) as [m' | r m']; [ | contradiction].
  destruct HP as [HL P]. exists m'. split; [reflexivity | split; [exact HL | ]].
  intros Hn. destruct n as [ | n]; [contradiction | ]. cbn [hpass8] in P. rewrite Hn in P. exact P.
Qed.

(* the header past HCRC from its fields: every scalar written, extra_len with FEXTRA, the copied buffer bytes *)
Lemma head_rep8a_intro: forall hsh headp xb nb cb s h vxl lx ln lc,
  (fextra s = true -> vxl = zv (h_extra_len h)) ->
  bufok6 lx (h_extra_max h) (cxa h) (h_xbuf h) -> bufok6 ln (h_name_max h) (cna h) (h_nbuf h) ->
  bufok6 lc (h_comm_max h) (cca h) (h_cbuf h) ->
  data_at hsh t_head
     (zv (h_text h), (lv (h_time h), (zv (h_xflags h), (zv (h_os h),
      ((if h_xp h then xb else nullval), (vxl, (zv (h_extra_max h),
      ((if h_np h then nb else nullval), (zv (h_name_max h),
      ((if h_cp h then cb else nullval), (zv (h_comm_max h), (zv (h_hcrc h), zv (h_done h)))))))))))))
     headp *
   hbuf6 xb (h_extra_max h) lx * hbuf6 nb (h_name_max h) ln * hbuf6 cb (h_comm_max h) lc
  |-- head_rep8a hsh headp xb nb cb s h.
Proof.
  intros hsh headp xb nb cb s h vxl lx ln lc Hx Bx Bn Bc. unfold head_rep8a, head_rep6p.
  Exists (zv (h_text h)) (lv (h_time h)) (zv (h_xflags h)) (zv (h_os h)) vxl (zv (h_hcrc h)) lx ln lc.
  apply andp_right; [apply prop_right; tauto | apply derives_refl].
Qed.

(* a closed frame as the first SEP item *)
Lemma frame_SEP8: forall (X: mpred) P Q R,
  PROPx P (LOCALx Q (SEPx R)) * (fun _ => X) = PROPx P (LOCALx Q (SEPx (X :: R))).
Proof. intros. rewrite sepcon_comm. apply insert_SEP. Qed.

Lemma rth_hcrc8 : rth_hcrc_stmt8.
Proof.
  intros Espec F HF0 m n HM HL [W W3] HD Hh HP.
  eapply semax_pre with (P' := (loop_stateH F m * (fun _ => hd6 F m)) * (fun _ => hdr_tok F m)).
  { apply andp_left2. intro rho. simpl. cancel. }
  apply semax_frame; [intros rho te _; reflexivity | ].
  eapply semax_pre with (P' := !! hinv6 (m_s m) (m_h m) && (loop_stateH F m * (fun _ => hd6 F m))).
  { apply andp_left2. apply andp_right; [ | apply derives_refl]. unfold hd6, head_rep6. intro rho. simpl. normalize. }
  apply semax_extract_prop. intros Hinv.
  pose proof (proj1 Hinv) as Hdone.
  destruct (hpass8_hcrc _ _ _ HM HP) as (m' & Em' & HL' & HF').
  pose proof (stepf2_HCRC (f_flush F) lenfix_list distfix_list m HM) as E0.
  rewrite c_HCRC_eq in E0.
  assert (NB: Z.land (i_flags (m_s m)) 512 <> 0 -> m_leave (needbits 16 m) = 0 /\
     (negb (Z.land (i_wrap (m_s (needbits 16 m))) 4 =? 0) &&
      negb (m_hold (needbits 16 m) =? Z.land (i_check (m_s (needbits 16 m))) 65535))%bool = false).
  { intros Hf. rewrite (proj2 (Z.eqb_neq _ _) Hf) in E0. cbv zeta in E0.
    pose proof (mw_leave _ (mwf_needbits 16 m W ltac:(lia))) as HLr.
    destruct (m_leave (needbits 16 m) =? 1) eqn:EL.
    - apply Z.eqb_eq in EL. rewrite E0 in Em'. injection Em' as <-. lia.
    - apply Z.eqb_neq in EL. split; [lia | ].
      match goal with |- ?b = false => destruct b eqn:G; [ | reflexivity] end.
      rewrite E0 in Em'. injection Em' as <-. exfalso.
      pose proof (HF' eq_refl) as Hd1.
      assert (Eh: m_h (set_bad (needbits 16 m) M_hcrc) = m_h m) by (rewrite <- (hc_needbits_f_h 4 16 m); reflexivity).
      rewrite Eh in Hd1. lia. }
  rewrite seq_split by lia. eapply semax_seq; [ | apply semax_ff].
  case_body_stmt.
  apply semax_seq with (Q := EX m2: mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m = hcrc_fin m2 /\ mwf m2 /\ m_leave m2 = 0 /\
        m_s m2 = m_s m /\ m_h m2 = m_h m) &&
    (loop_stateH F m2 * (fun _ => hd6 F m))).
  - eapply semax_post with (R' := frame_ret_assert (normal_ret_assert (EX m2: mst,
      !! (stepf2 (f_flush F) lenfix_list distfix_list m = hcrc_fin m2 /\ mwf m2 /\ m_leave m2 = 0 /\
          m_s m2 = m_s m /\ m_h m2 = m_h m) && loop_stateH F m2)) (fun _ => hd6 F m)).
    5: { apply semax_frame; [intros rho te _; reflexivity | ].
    pose proof (sw_flags _ (mw_s _ W)) as Hfl.
    rewrite loop_state_hd_eqH. unfold loop_state_hdH. abbreviate_semax.
    forward.
    forward_if.
    + match goal with X: Int.and _ _ <> Int.zero |- _ => apply int_and_nz in X; [rename X into Hf | lia] end.
      destruct (NB Hf) as [HL1 G].
      apply semax_pre with (P' := loop_stateH F m); [rewrite loop_state_hd_eqH; unfold loop_state_hdH; entailer! | ].
      apply semax_seq with (Q := loop_stateH F (needbits 16 m)).
      { eapply semax_seq'; [apply semax_needbits_HCRC5H; [exact W | exact HL | lia] | ].
        unfold loop_stateH. rewrite HL1. forward_if.
        - exfalso. lia.
        - forward. entailer!. }
      pose proof (mwf_needbits 16 m W ltac:(lia)) as W1.
      assert (E1: stepf2 (f_flush F) lenfix_list distfix_list m = hcrc_fin (initbits (needbits 16 m))).
      { rewrite E0. rewrite (proj2 (Z.eqb_neq _ _) Hf). cbv zeta. rewrite HL1. cbn [Z.eqb Pos.eqb]. rewrite G. reflexivity. }
      assert (Es1: m_s (initbits (needbits 16 m)) = m_s m) by (apply needbits_f_s).
      assert (Eh1: m_h (initbits (needbits 16 m)) = m_h m) by (apply hc_needbits_f_h).
      clear E0. set (m1 := needbits 16 m) in *. clearbody m1.
      pose proof (sw_wrap_range _ (mw_s _ W1)) as Hw. pose proof (sw_check _ (mw_s _ W1)) as Hc.
      pose proof (mw_hold _ W1) as Hho.
      rewrite loop_state_hd_eqH. unfold loop_state_hdH. abbreviate_semax.
      forward.
      unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
      * forward. forward.
        unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
        { exfalso.
          assert (G': (negb (Z.land (i_wrap (m_s m1)) 4 =? 0) &&
                      negb (m_hold m1 =? Z.land (i_check (m_s m1)) 65535))%bool = true).
          { match goal with X: Int.and _ _ <> Int.zero |- _ => apply int_and_nz in X; [ | lia] end.
            match goal with X: Int64.repr _ <> _ |- _ => apply hcrc_ne in X; [ | exact Hho | exact Hc] end.
            match goal with X: (_ =? _) = false |- _ => rewrite X end.
            rewrite (proj2 (Z.eqb_neq _ _)) by assumption. reflexivity. }
          congruence. }
        { apply semax_do0_last. forward. forward. hcrc_norm_end6 m1 E1 W1 HL1 G Es1 Eh1. }
      * forward.
        unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
        { exfalso; congruence. }
        { apply semax_do0_last. forward. forward. hcrc_norm_end6 m1 E1 W1 HL1 G Es1 Eh1. }
    + match goal with X: Int.and _ _ = Int.zero |- _ => apply int_and_z in X; [rename X into Hf | lia] end.
      forward.
      Exists m. apply andp_right.
      * apply prop_right. split; [ | split; [exact W | split; [exact HL | split; reflexivity]]].
        rewrite E0. rewrite (proj2 (Z.eqb_eq _ _) Hf). reflexivity.
      * rewrite loop_state_hd_eqH. unfold loop_state_hdH. entailer!. }
    all: unfold frame_ret_assert, normal_ret_assert, overridePost; cbn [RA_normal RA_break RA_continue RA_return].
    1: (apply andp_left2; rewrite exp_sepcon1; apply exp_left; intros m2; apply exp_right with m2;
        rewrite sepcon_andp_prop'; apply derives_refl).
    all: try (intros; apply andp_left2; rewrite FF_sepcon; apply FF_left).
  - Intros m2. apply semax_extract_prop; intros (E & W2 & HL2 & Es2 & Eh2).
    assert (Hh2: i_head (m_s m2) = true) by (rewrite Es2; exact Hh).
    assert (ET: stepf2 (f_flush F) lenfix_list distfix_list m =
      IBrk (set_mode (set_m_adler (upd_s (upd_h m2 (fun h => set_h_done (set_h_hcrc h
          (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1)) (fun s => set_i_check s 0)) 0) IM.TYPE)).
    { rewrite E; unfold hcrc_fin; rewrite Hh2; reflexivity. }
    rewrite ET in Em'. injection Em' as <-.
    assert (HM': i_mode (m_s m) = IM.HCRC) by exact HM.
    assert (Hph: hph (m_s m) = 4) by (unfold hph; rewrite HM'; reflexivity).
    assert (Hcx: cx6 (m_s m) (m_h m) = cxa (m_h m)) by (unfold cx6, cxa; rewrite HM'; reflexivity).
    assert (Hcn: cn6 (m_s m) (m_h m) = cna (m_h m)) by (unfold cn6, cna; rewrite HM'; reflexivity).
    assert (Hcc: cc6 (m_s m) (m_h m) = cca (m_h m)) by (unfold cc6, cca; rewrite HM'; reflexivity).
    rewrite loop_state_hd_eqH. unfold loop_state_hdH. apply start_function_aux1 with (R1 := hd6 F m).
    unfold hd6, head_rep6, head_rep6p.
    rewrite Hph, Hcx, Hcn, Hcc.
    Intros vt vtm vxf vos vxl vhc lx ln lc.
    match goal with X: 1 <= 4 -> _ |- _ => specialize (X ltac:(lia)) end.
    match goal with X: 2 <= 4 -> _ |- _ => specialize (X ltac:(lia)) end.
    match goal with X: 3 <= 4 -> _ |- _ => destruct (X ltac:(lia)) end.
    match goal with X: 4 <= 4 -> _ |- _ => specialize (X ltac:(lia)) end.
    subst vt vtm vxf vos. rewrite Hdone.
    destruct HF0 as [HF HFl]. destruct HF as (Hshs & Hhsh & Hgsh & Htsh).
    destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
    frame_simpl. unfold head_partH. cbn [f_hsh f_headp f_xb f_nb f_cb] in *.
    rewrite Hh2. unfold hnoneH.
    abbreviate_semax.
    freeze FR := (field_at _ _ (DOT _wrap) _ _) (field_at _ _ (DOT _havedict) _ _) (field_at _ _ (DOT _hold) _ _)
      (field_at _ _ (DOT _bits) _ _) (state_rest _ _ _ _ _ _) (win_rep _ _) (in_rep _) (out_rep _ _)
      (tables_rep _ _) (locals_rep _).
    freeze FB := (hbuf6 _ _ _) (hbuf6 _ _ _) (hbuf6 _ _ _).
    forward.
    unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
    + forward. forward. forward. forward. forward.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        apply semax_pre with (PROPx P (LOCALx Q (SEPx (emp :: emp :: R)))); [entailer! |] end.
      forward_call (0, nullval, 0, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews, gv, tsh).
      forward. unfold strm_rep. remember (gv _zcalloc) as za eqn:Eza. remember (gv _zcfree) as zf eqn:Ezf.
      forward. forward. forward.
      unfold switch_ret_assert, case_post8. cbn [RA_break RA_normal].
      Exists (set_mode (set_m_adler (upd_s (upd_h m2 (fun h => set_h_done (set_h_hcrc h
          (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1)) (fun s => set_i_check s 0)) 0) IM.TYPE).
      apply andp_right; [apply prop_right; exact ET | ].
      unfold post8, hd8. match goal with |- context [hdr_mode ?x] => replace (hdr_mode x) with false by reflexivity end.
      rewrite int_hcrc by (apply (sw_flags _ (mw_s _ W2))).
      unfold hd8a. cbn [f_hsh f_headp f_xb f_nb f_cb].
      set (m' := set_mode (set_m_adler (upd_s (upd_h m2 (fun h => set_h_done (set_h_hcrc h
          (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1)) (fun s => set_i_check s 0)) 0) IM.TYPE).
      assert (Eh': m_h m' = set_h_done (set_h_hcrc (m_h m) (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1)
        by (subst m'; cbn [m_h set_mode set_m_adler upd_s upd_h set_m_h set_m_s]; rewrite Eh2; reflexivity).
      thaw FB.
      pose proof (head_rep8a_intro hsh headp xb nb cb (m_s m')
        (set_h_done (set_h_hcrc (m_h m) (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1) vxl lx ln lc) as P8.
      simpl in P8.
      assert (Hx: fextra (set_i_mode (set_i_check (m_s m2) 0) IM.TYPE) = true -> vxl = zv (h_extra_len (m_h m))).
      { intros Hx; apply H4; unfold fextra in Hx |- *; cbn in Hx; rewrite Es2 in Hx; exact Hx. }
      sep_apply (P8 Hx H6 H7 H8). clear P8.
      replace (head_rep8a hsh headp xb nb cb (set_i_mode (set_i_check (m_s m2) 0) IM.TYPE)
        (set_h_done (set_h_hcrc (m_h m) (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1))
        with (head_rep8a hsh headp xb nb cb (m_s m') (m_h m')) by (rewrite Eh'; reflexivity).
      set (HD8 := head_rep8a hsh headp xb nb cb (m_s m') (m_h m')). subst m'.
      rewrite loop_state_hd_eqH. unfold loop_state_hdH. rewrite frame_SEP8.
      frame_simpl_goal. unfold m_have, m_left. mnorm_goalH. cbn [f_gv f_hsh f_headp f_xb f_nb f_cb].
      rewrite Hh2. unfold hnoneH.
      rewrite strm_rep_unfold. rewrite <- Eza, <- Ezf.
      rest_simpl. thaw FR. unfold win_rep. entailer!.
    + match goal with X: headp = nullval |- _ => subst headp end.
      assert_PROP False by (sep_apply (data_at_local_facts hsh t_head); entailer!;
        match goal with X: field_compatible _ _ nullval |- _ => destruct X; contradiction end). contradiction.
Qed.
