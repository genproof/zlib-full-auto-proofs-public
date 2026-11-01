"""Patches of docs/port-hl/cfg_rth9h.py, group hcrc (the case HCRC): see the configuration's header.

Round 1's case (RTH8CaseHCRC.rth_hcrc8) assumed a call that passes the header (hpass8): its proof read from the
pass that NEEDBITS(16) does not run out of input and that the header CRC matches.  Here both breaks are proved,
with the lemmas of src/proof/roundtrip/RTH9HHcrcKit.v: the first part of the case (up to INITBITS) ends normally
or breaks (RTH9HHcrcKit.hcrc_ret9) in RTH9HHcrcKit.hcrc_brk9, which with the header of the case's start is the
case's break (hcrc_brk9_post):
- NEEDBITS(16) out of input: the break with leave = 1 in mode HCRC, the partial header unchanged;
- a header CRC mismatch (wrap & 4 and hold <> check & 0xffff): the break in mode BAD with the raw header (done = 0).
The end of the case (the header written; past the header RTH9HDefs.hd9a's first disjunct, RTH8Spec.head_rep8a,
as round 1) is RTH9HHcrcKit.hcrc_tail9.
RTHCaseHCRC6's own HCRC case (with round 1's v6 pass) is not ported: only its tactics are needed."""

R = 'Zlib.proof.roundtrip.'
M = R + 'RTH8CaseHCRC'

_REQ = (M, 'Require Import Zlib.proof.roundtrip.RTHCaseHCRC6.',
        'Require Import Zlib.proof.roundtrip.RTHCaseHCRC6.\n'
        'Require Import Zlib.proof.roundtrip.RTH9HHcrcKit.')

# no header pass: the model's step of HCRC is all the proof reads
_INTRO = (M, '''  intros Espec F HF0 m n HM HL [W W3] HD Hh HP.''', '''  intros Espec F HF0 m HM HL [W W3] HD Hh.''')

_PASS = (M, '''  destruct (hpass8_hcrc _ _ _ HM HP) as (m' & Em' & HL' & HF').
  pose proof (stepf2_HCRC (f_flush F) lenfix_list distfix_list m HM) as E0.
  rewrite c_HCRC_eq in E0.
  assert (NB: Z.land (i_flags (m_s m)) 512 <> 0 -> m_leave (needbits 16 m) = 0 /\\
     (negb (Z.land (i_wrap (m_s (needbits 16 m))) 4 =? 0) &&
      negb (m_hold (needbits 16 m) =? Z.land (i_check (m_s (needbits 16 m))) 65535))%bool = false).
  { intros Hf. rewrite (proj2 (Z.eqb_neq _ _) Hf) in E0. cbv zeta in E0.
    pose proof (mw9_leave _ (mwf9_needbits 16 m W ltac:(lia))) as HLr.
    destruct (m_leave (needbits 16 m) =? 1) eqn:EL.
    - apply Z.eqb_eq in EL. rewrite E0 in Em'. injection Em' as <-. lia.
    - apply Z.eqb_neq in EL. split; [lia | ].
      match goal with |- ?b = false => destruct b eqn:G; [ | reflexivity] end.
      rewrite E0 in Em'. injection Em' as <-. exfalso.
      pose proof (HF' eq_refl) as Hd1.
      assert (Eh: m_h (set_bad (needbits 16 m) M_hcrc) = m_h m) by (rewrite <- (hc_needbits_f_h 4 16 m); reflexivity).
      rewrite Eh in Hd1. lia. }
''', '''  pose proof (stepf2_HCRC (f_flush F) lenfix_list distfix_list m HM) as E0.
  rewrite c_HCRC_eq in E0.
''')

# the first part ends normally (into the header writes) or breaks before them
_POST = (M, '''  - eapply semax_post with (R' := frame_ret_assert (normal_ret_assert (EX m2: mst,
      !! (stepf2 (f_flush F) lenfix_list distfix_list m = hcrc_fin m2 /\\ mwf9 m2 /\\ m_leave m2 = 0 /\\
          m_s m2 = m_s m /\\ m_h m2 = m_h m) && loop_stateH F m2)) (fun _ => hd6 F m)).
    5: { apply semax_frame; [intros rho te _; reflexivity | ].
''', '''  - eapply semax_post with (R' := frame_ret_assert (hcrc_ret9 (EX m2: mst,
      !! (stepf2 (f_flush F) lenfix_list distfix_list m = hcrc_fin m2 /\\ mwf9 m2 /\\ m_leave m2 = 0 /\\
          m_s m2 = m_s m /\\ m_h m2 = m_h m) && loop_stateH F m2) (hcrc_brk9 F m)) (fun _ => hd6 F m)).
    5: { apply semax_frame; [intros rho te _; reflexivity | ].
    unfold hcrc_ret9.
''')

# NEEDBITS(16) out of input: the break in mode HCRC; otherwise the model's step after the CRC check
_LEAVE = (M, '''      destruct (NB Hf) as [HL1 G].
      apply semax_pre with (P' := loop_stateH F m); [rewrite loop_state_hd_eqH; unfold loop_state_hdH; entailer! | ].
      apply semax_seq with (Q := loop_stateH F (needbits 16 m)).
      { eapply semax_seq'; [apply semax_needbits_HCRC5H; [exact W | exact HL | lia] | ].
        unfold loop_stateH. rewrite HL1. forward_if.
        - exfalso. lia.
        - forward. entailer!. }
      pose proof (mwf9_needbits 16 m W ltac:(lia)) as W1.
      assert (E1: stepf2 (f_flush F) lenfix_list distfix_list m = hcrc_fin (initbits (needbits 16 m))).
      { rewrite E0. rewrite (proj2 (Z.eqb_neq _ _) Hf). cbv zeta. rewrite HL1. cbn [Z.eqb Pos.eqb]. rewrite G. reflexivity. }
''', '''      apply semax_pre with (P' := loop_stateH F m); [rewrite loop_state_hd_eqH; unfold loop_state_hdH; entailer! | ].
      pose proof (mwf9_needbits 16 m W ltac:(lia)) as W1.
      destruct (Z.eq_dec (m_leave (needbits 16 m)) 1) as [EL | EL].
      { apply semax_seq with (Q := FF); [ | apply semax_pre with (P' := FF); [apply andp_left2, derives_refl | apply semax_ff]].
        eapply semax_seq'; [apply semax_needbits_HCRC5H; [exact W | exact HL | lia] | ].
        unfold loop_stateH at 1. rewrite EL. forward_if.
        - forward. unfold hcrc_brk9. Exists (needbits 16 m).
          apply andp_right.
          + apply prop_right. split; [ | split; [apply hc_needbits_f_h | intros _; apply hcrc_hd6_needbits]].
            rewrite E0. rewrite (proj2 (Z.eqb_neq _ _) Hf). cbv zeta. rewrite EL. reflexivity.
          + unfold loop_stateH. rewrite EL. entailer!.
        - discriminate. }
      assert (HL1: m_leave (needbits 16 m) = 0) by (pose proof (mw9_leave _ W1); lia).
      apply semax_seq with (Q := loop_stateH F (needbits 16 m)).
      { eapply semax_seq'; [apply semax_needbits_HCRC5H; [exact W | exact HL | lia] | ].
        unfold loop_stateH. rewrite HL1. forward_if.
        - exfalso. lia.
        - forward. entailer!. }
      assert (E1g: stepf2 (f_flush F) lenfix_list distfix_list m =
        if (negb (Z.land (i_wrap (m_s (needbits 16 m))) 4 =? 0) &&
            negb (m_hold (needbits 16 m) =? Z.land (i_check (m_s (needbits 16 m))) 65535))%bool
        then IBrk (set_bad (needbits 16 m) M_hcrc) else hcrc_fin (initbits (needbits 16 m))).
      { rewrite E0. rewrite (proj2 (Z.eqb_neq _ _) Hf). cbv zeta. rewrite HL1. reflexivity. }
      assert (Eb1: m_h (set_bad (needbits 16 m) M_hcrc) = m_h m) by (apply hc_needbits_f_h).
''')

_SET = (M, '''      clear E0. set (m1 := needbits 16 m) in *. clearbody m1.''',
        '''      clear E0 EL. set (m1 := needbits 16 m) in *. clearbody m1.''')

# the CRC check with wrap & 4: the mismatch breaks in mode BAD
_BAD = (M, '''        { exfalso.
          assert (G': (negb (Z.land (i_wrap (m_s m1)) 4 =? 0) &&
                      negb (m_hold m1 =? Z.land (i_check (m_s m1)) 65535))%bool = true).
          { match goal with X: Int.and _ _ <> Int.zero |- _ => apply int_and_nz in X; [ | lia] end.
            match goal with X: Int64.repr _ <> _ |- _ => apply hcrc_ne in X; [ | exact Hho | exact Hc] end.
            match goal with X: (_ =? _) = false |- _ => rewrite X end.
            rewrite (proj2 (Z.eqb_neq _ _)) by assumption. reflexivity. }
          congruence. }
        { apply semax_do0_last. forward. forward. hcrc_norm_end6 m1 E1 W1 HL1 G Es1 Eh1. }''',
        '''        { assert (G: (negb (Z.land (i_wrap (m_s m1)) 4 =? 0) &&
                      negb (m_hold m1 =? Z.land (i_check (m_s m1)) 65535))%bool = true).
          { match goal with X: Int.and _ _ <> Int.zero |- _ => apply int_and_nz in X; [ | lia] end.
            match goal with X: Int64.repr _ <> _ |- _ => apply hcrc_ne in X; [ | exact Hho | exact Hc] end.
            match goal with X: (_ =? _) = false |- _ => rewrite X end.
            rewrite (proj2 (Z.eqb_neq _ _)) by assumption. reflexivity. }
          rewrite G in E1g.
          pose proof (proj1 HF0) as (Hshs & _). unfold strm_rep.
          remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.
          forward. forward. forward.
          unfold hcrc_brk9. Exists (set_bad m1 M_hcrc).
          apply andp_right; [apply prop_right; split; [exact E1g | split; [exact Eb1 | discriminate]] | ].
          rewrite loop_state_hd_eqH. unfold loop_state_hdH, win_rep, head_partH. unfold m_have, m_left. mnorm_goalH.
          cbn [msg_val msg_ident]. rewrite strm_rep_unfold. rewrite <- Eza, <- Ezf. rest_simpl. entailer!. }
        { assert (G: (negb (Z.land (i_wrap (m_s m1)) 4 =? 0) &&
                      negb (m_hold m1 =? Z.land (i_check (m_s m1)) 65535))%bool = false).
          { match goal with X: Int64.eq _ _ = true |- _ => apply hcrc_eqt in X; [ | exact Hho | exact Hc] end.
            match goal with X: (_ =? _) = true |- _ => rewrite X end. apply andb_false_r. }
          rewrite G in E1g. rename E1g into E1.
          apply semax_do0_last. forward. forward. hcrc_norm_end6 m1 E1 W1 HL1 G Es1 Eh1. }''')

# the CRC check without wrap & 4: no check
_NOCHK = (M, '''        { exfalso; congruence. }
        { apply semax_do0_last. forward. forward. hcrc_norm_end6 m1 E1 W1 HL1 G Es1 Eh1. }''',
          '''        { exfalso; congruence. }
        { assert (G: (negb (Z.land (i_wrap (m_s m1)) 4 =? 0) &&
                      negb (m_hold m1 =? Z.land (i_check (m_s m1)) 65535))%bool = false).
          { match goal with X: Int.and _ _ = Int.zero |- _ => apply int_and_z in X; [rewrite X | lia] end.
            reflexivity. }
          rewrite G in E1g. rename E1g into E1.
          apply semax_do0_last. forward. forward. hcrc_norm_end6 m1 E1 W1 HL1 G Es1 Eh1. }''')

# the first part's breaks are the case's (RTH9HHcrcKit.hcrc_brk9_post)
_ENDS = (M, '''    all: unfold frame_ret_assert, normal_ret_assert, overridePost; cbn [RA_normal RA_break RA_continue RA_return].
    1: (apply andp_left2; rewrite exp_sepcon1; apply exp_left; intros m2; apply exp_right with m2;
        rewrite sepcon_andp_prop'; apply derives_refl).''',
         '''    all: unfold frame_ret_assert, hcrc_ret9, overridePost, switch_ret_assert, normal_ret_assert, case_post9;
      cbn [RA_normal RA_break RA_continue RA_return].
    1: (apply andp_left2; rewrite exp_sepcon1; apply exp_left; intros m2; apply exp_right with m2;
        rewrite sepcon_andp_prop'; apply derives_refl).
    1: (apply andp_left2; apply hcrc_brk9_post).''')

# the end of the case, the header written: RTH9HHcrcKit.hcrc_tail9 (round 1's proof, in its own lemma to keep
# the files short; past the header the case ends in RTH9HDefs.hd9a's first disjunct)
_TAIL = (M, r'''  - Intros m2. apply semax_extract_prop; intros (E & W2 & HL2 & Es2 & Eh2).
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
      unfold switch_ret_assert, case_post9. cbn [RA_break RA_normal].
      Exists (set_mode (set_m_adler (upd_s (upd_h m2 (fun h => set_h_done (set_h_hcrc h
          (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1)) (fun s => set_i_check s 0)) 0) IM.TYPE).
      apply andp_right; [apply prop_right; exact ET | ].
      unfold post9, hd9. match goal with |- context [hdr_mode ?x] => replace (hdr_mode x) with false by reflexivity end.
      rewrite int_hcrc by (apply (sw_flags _ (mw9_s _ W2))).
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
''',
         '''  - Intros m2. apply semax_extract_prop; intros (E & W2 & HL2 & Es2 & Eh2).
    exact (hcrc_tail9 F m m2 HF0 HM Hh Hdone E W2 Es2 Eh2).
''')

PATCHES = [_REQ, _INTRO, _PASS, _POST, _LEAVE, _SET, _BAD, _NOCHK, _ENDS, _TAIL]

DROP = {R + 'RTHCaseHCRC6': ['hpass_hcrc', 'rth_hcrc']}
