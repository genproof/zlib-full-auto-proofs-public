(* RT-H: case HCRC (index 8) with a partial gz_header attached (RTHCase.case_ok6): writes hcrc and
   done, and with hfull (hpass) hands over Spec5's defined head_rep in the loop state of mode TYPE. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHCaseHyps5 Zlib.proof.roundtrip.RTHNeedKit5 Zlib.proof.roundtrip.RTHNeedBits Zlib.proof.roundtrip.RTHNeedBits2_5.
Require Import Zlib.proof.inflate.Steps2 Zlib.proof.inflate.MwfLemmas Zlib.proof.roundtrip.RTHModeKit5.
Require Import Zlib.proof.crc32.Spec Zlib.proof.adler32.Spec.
Require Import Zlib.proof.inflate.Cases5_HD.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* loop_stateH with those fields apart *)
Definition loop_state_hdH (F: frame) (m: mst) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _havedict) (zv (i_havedict (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
       field_at Ews t_state (DOT _hold) (lv (i_hold (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _bits) (zv (i_bits (m_s m))) (f_sp F);
       state_rest (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m);
       win_rep (f_winp F) (m_s m);
       head_partH F m;
       strm_rep (f_gv F) (f_shs F) (f_strmp F)
         (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
         (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
         (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F);
       in_rep (f_ib F);
       out_rep (f_ob F) (m_ow m);
       tables_rep (f_gsh F) (f_gv F);
       crc_table_at (f_tsh F) (f_gv F);
       locals_rep F).

Lemma loop_state_hd_eqH: forall F m, loop_stateH F m = loop_state_hdH F m.
Proof.
  intros. unfold loop_stateH, loop_state_hdH, mem_repH. rewrite state_rep_hd.
  f_equal. unfold SEPx. simpl. rewrite !sepcon_assoc. reflexivity.
Qed.

Ltac hcrc_norm_end6 m1 E1 W1 HL1 G Es1 Eh1 :=
  Exists (initbits m1); apply andp_right;
  [ apply prop_right; split; [rewrite E1; reflexivity | split; [apply mwf_initbits, W1 | split; [exact HL1 | split; [exact Es1 | exact Eh1]]]] | ];
  rewrite loop_state_hd_eqH; unfold loop_state_hdH, win_rep, head_partH; unfold m_have, m_left; mnorm_goalH;
  change (Int.signed (Int.repr 0)) with 0; entailer!.

Lemma hc_needbits_f_h: forall k n m, m_h (needbits_f k n m) = m_h m.
Proof.
  induction k; intros n0 m0; cbn [needbits_f]; [reflexivity | ].
  destruct (m_bits m0 <? n0); [ | reflexivity].
  destruct (m_have m0 =? 0); [reflexivity | ]. rewrite IHk. reflexivity.
Qed.

(* the pass of HCRC: no leave, and past the header the header is full *)
Lemma hpass_hcrc: forall flush n m, m_mode m = HCRC -> hpass flush (S n) m ->
  exists m', stepf2 flush lenfix_list distfix_list m = IBrk m' /\ m_leave m' = 0 /\
    (hdr_mode (m_mode m') = false -> hfull (m_s m') (m_h m')).
Proof.
  intros flush n m HM HP. cbn [hpass] in HP. rewrite HM in HP. cbv [hdr_mode] in HP. cbn in HP.
  destruct (stepf2 flush lenfix_list distfix_list m) as [m' | r m']; [ | contradiction].
  destruct HP as [HL P]. exists m'. split; [reflexivity | split; [exact HL | ]].
  intros Hn. destruct n as [ | n]; [contradiction | ]. cbn [hpass] in P. rewrite Hn in P. exact P.
Qed.

Lemma bufok6_full: forall l max cont, bufok6 l max max cont -> Zlength cont = max -> l = byte_vals cont.
Proof.
  intros l max cont [Hl [Hm Hs]] Hc.
  rewrite sublist_same in Hs by lia. rewrite sublist_same in Hs by lia. exact Hs.
Qed.

Lemma hbuf6_rep: forall b max cont, hbuf6 b max (byte_vals cont) = hbuf_rep b max cont.
Proof. reflexivity. Qed.

Lemma rth_hcrc : rth_hcrc_stmt.
Proof.
  intros Espec F HF0 m n HM HL [W W3] HD Hh HP.
  eapply semax_pre with (P' := (loop_stateH F m * (fun _ => hd6 F m)) * (fun _ => hdr_tok F m)).
  { apply andp_left2. intro rho. simpl. cancel. }
  apply semax_frame; [intros rho te _; reflexivity | ].
  eapply semax_pre with (P' := !! hinv6 (m_s m) (m_h m) && (loop_stateH F m * (fun _ => hd6 F m))).
  { apply andp_left2. apply andp_right; [ | apply derives_refl]. unfold hd6, head_rep6. intro rho. simpl. normalize. }
  apply semax_extract_prop. intros Hinv.
  pose proof (proj1 Hinv) as Hdone.
  destruct (hpass_hcrc _ _ _ HM HP) as (m' & Em' & HL' & HF').
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
      destruct (HF' eq_refl) as [Hd1 _].
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
    pose proof (HF' eq_refl) as Hfull. clear HF'.
    unfold hfull, fextra in Hfull.
    cbn [m_s m_h set_mode upd_s upd_h set_m_adler set_m_h set_m_s i_flags set_i_mode set_i_check h_done h_xp h_np
         h_cp h_extra_max h_extra_len h_name_max h_nbuf h_comm_max h_cbuf set_h_done set_h_hcrc] in Hfull.
    rewrite Eh2, Es2 in Hfull.
    destruct Hfull as (Hd1 & Hfx & Hxp & Hnp & Hcp & Hxm & Hnm & Hcm).
    assert (HM': i_mode (m_s m) = IM.HCRC) by exact HM.
    assert (Hph: hph (m_s m) = 4) by (unfold hph; rewrite HM'; reflexivity).
    assert (Hcx: cx6 (m_s m) (m_h m) = h_extra_max (m_h m)) by (unfold cx6; rewrite HM'; cbn; rewrite Hxp; lia).
    assert (Hcn: cn6 (m_s m) (m_h m) = h_name_max (m_h m)) by (unfold cn6; rewrite HM'; cbn; rewrite Hnp; lia).
    assert (Hcc: cc6 (m_s m) (m_h m) = h_comm_max (m_h m)) by (unfold cc6; rewrite HM'; cbn; rewrite Hcp; lia).
    pose proof (mw_h _ W) as Hw.
    rewrite loop_state_hd_eqH. unfold loop_state_hdH. apply start_function_aux1 with (R1 := hd6 F m).
    unfold hd6, head_rep6, head_rep6p.
    rewrite Hph, Hcx, Hcn, Hcc. replace (fextra (m_s m)) with true by (symmetry; exact Hfx).
    Intros vt vtm vxf vos vxl vhc lx ln lc.
    match goal with X: bufok6 lx _ _ _ |- _ => apply bufok6_full in X; [ | apply (hw_xbuf _ Hw)] end.
    match goal with X: bufok6 ln _ _ _ |- _ => apply bufok6_full in X; [ | apply (hw_nbuf _ Hw)] end.
    match goal with X: bufok6 lc _ _ _ |- _ => apply bufok6_full in X; [ | apply (hw_cbuf _ Hw)] end.
    match goal with X: 1 <= 4 -> _ |- _ => specialize (X ltac:(lia)) end.
    match goal with X: 2 <= 4 -> _ |- _ => specialize (X ltac:(lia)) end.
    match goal with X: 3 <= 4 -> _ |- _ => destruct (X ltac:(lia)) end.
    match goal with X: 4 <= 4 -> _ |- _ => specialize (X ltac:(lia) eq_refl) end.
    subst vt vtm vxf vos vxl lx ln lc. rewrite !hbuf6_rep. rewrite Hdone.
    destruct HF0 as [HF HFl]. destruct HF as (Hshs & Hhsh & Hgsh & Htsh).
    destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
    frame_simpl. unfold head_partH. cbn [f_hsh f_headp f_xb f_nb f_cb] in *.
    rewrite Hh2. unfold hnoneH.
    abbreviate_semax.
    freeze FR := (field_at _ _ (DOT _wrap) _ _) (field_at _ _ (DOT _havedict) _ _) (field_at _ _ (DOT _hold) _ _)
      (field_at _ _ (DOT _bits) _ _) (state_rest _ _ _ _ _ _) (win_rep _ _) (in_rep _) (out_rep _ _)
      (tables_rep _ _) (locals_rep _).
    freeze FB := (hbuf_rep _ _ _) (hbuf_rep _ _ _) (hbuf_rep _ _ _).
    forward.
    unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
    + forward. forward. forward. forward. forward.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        apply semax_pre with (PROPx P (LOCALx Q (SEPx (emp :: emp :: R)))); [entailer! |] end.
      forward_call (0, nullval, 0, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews, gv, tsh).
      forward. unfold strm_rep. remember (gv _zcalloc) as za eqn:Eza. remember (gv _zcfree) as zf eqn:Ezf.
      forward. forward. forward.
      unfold switch_ret_assert, case_post6. cbn [RA_break RA_normal].
      Exists (set_mode (set_m_adler (upd_s (upd_h m2 (fun h => set_h_done (set_h_hcrc h
          (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1)) (fun s => set_i_check s 0)) 0) IM.TYPE).
      apply andp_right; [apply prop_right; exact ET | ].
      unfold post6. match goal with |- context [hdr_mode ?x] => replace (hdr_mode x) with false by reflexivity end.
      rewrite loop_state_hd_eq. unfold loop_state_hd. frame_simpl_goal. unfold m_have, m_left.
      mnorm_goal. cbn [f_gv f_hsh f_headp f_xb f_nb f_cb]. rewrite Hh2. unfold head_rep. mnorm_goal.
      rewrite strm_rep_unfold. rewrite <- Eza, <- Ezf.
      rewrite int_hcrc by (apply (sw_flags _ (mw_s _ W2))).
      rewrite ?Eh2, ?Hxp, ?Hnp, ?Hcp.
      rest_simpl. thaw FB. thaw FR. unfold win_rep. rewrite ?Hxp, ?Hnp, ?Hcp. entailer!.
    + match goal with X: headp = nullval |- _ => subst headp end.
      assert_PROP False by (sep_apply (data_at_local_facts hsh t_head); entailer!;
        match goal with X: field_compatible _ _ nullval |- _ => destruct X; contradiction end). contradiction.
Qed.
