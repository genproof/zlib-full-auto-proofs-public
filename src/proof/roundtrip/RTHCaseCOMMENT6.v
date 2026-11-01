(* RT-H: case COMMENT (7) of inflate() with the partial header hd6 (RTHCase.case_ok6): if (flags & 0x1000)
   { the do-while storing the comment into head->comment (zstr_f), crc32, leave when the input ran out } else
   head->comment = Z_NULL; state->mode = HCRC; falls into HCRC (no `state->length = 0`: Model2.v c_COMMENT2).
   The leave branches contradict hpass. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHModeKit5.
Require Import Zlib.proof.roundtrip.RTHNC6Kit.
Require Import Zlib.proof.roundtrip.RTHNC6Mach.
Require Import Zlib.proof.roundtrip.RTHNC6Facts.
Require Import Zlib.proof.inflate.CaseNAME5.
Require Import Zlib.proof.inflate.CaseCOMMENT5.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* `state->mode = md;` with the tokens and the header framed *)
Lemma semax_mode6_T {Espec: OracleKind} (F: frame) (m: mst) (md: Z) (T: mpred):
  semax Delta_cases5 (loop_stateH F m * (fun _ => T))
    (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                       (Tstruct _inflate_state noattr)) _mode tint)
       (Econst_int (Int.repr md) tint))
    (normal_ret_assert (loop_stateH F (set_mode m md) * (fun _ => T))).
Proof.
  rewrite <- frame_normal. apply semax_frame; [ | apply semax_store_mode5H].
  intros rho te _. reflexivity.
Qed.

(* the machine before the tail: m1 with `mode = HCRC` the fallthrough machine *)
Definition comm_mid6 (F: frame) (m: mst) : environ -> mpred :=
  EX m1: mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list (fin_c m1) /\
        m_leave m1 = 0 /\ mwf3 (fin_c m1) /\ hd_ok F (fin_c m1) /\ hdr_tok F (fin_c m1) = hdr_tok F m /\
        i_head (m_s m1) = true) &&
    (loop_stateH F m1 * (fun _ => hdr_tok F m * hd6 F (fin_c m1))).

Ltac post_midc6 := match goal with |- context [RA_normal ?X] =>
  match X with context [case_post6 ?F ?m] =>
  replace (RA_normal X) with (comm_mid6 F m)
    by (destruct (frame_ret_assert (switch_ret_assert (case_post6 F m)) (lift0 (hdr_tok F m))); reflexivity) end end.

Ltac ra_red6 F m := destruct (frame_ret_assert (switch_ret_assert (case_post6 F m)) (lift0 (hdr_tok F m))); cbn [RA_normal].

Lemma SL6_cm_comment: forall F m c ln bf Hd,
  SL6 F (crc_if (cm_loop m ln bf) (inbytes (cm_loop m ln bf) c)) Hd = SL6 F (nm_comment m c ln bf) Hd.
Proof. intros. unfold nm_comment, cm_loop. rewrite !crc_if_eq. reflexivity. Qed.

Lemma cc6_COMMENT: forall s h, i_mode s = IM.COMMENT -> cc6 s h = i_length s.
Proof. intros s h E. unfold cc6. rewrite E. reflexivity. Qed.

Lemma case_COMMENT6 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_ok6 F IM.HCRC 8 -> case_ok6 F IM.COMMENT 7.
Proof.
  intros [FOK FR] HY m n HM HL [W W2] HD HH HP. pose proof FOK as (HWS & HWH & HRG & HRT).
  apply (case_fallthrough6 F m n IM.HCRC 7); [lia | reflexivity | rewrite HM; reflexivity | exact HP | exact HY | ].
  case_body_stmt.
  apply semax_seq with (Q := comm_mid6 F m).
  2:{ unfold comm_mid6. apply extract_exists_pre. intros m1.
      apply semax_extract_prop. intros (E & L1 & W1 & HD1 & T1 & H1).
      eapply ConseqFacts.semax_post''; [ | apply (semax_mode6_T F m1 IM.HCRC (hdr_tok F m * hd6 F (fin_c m1)))].
      unfold overridePost, fall_post6. cbn [RA_normal].
      apply andp_left2. rewrite exp_sepcon1. Exists (fin_c m1).
      rewrite sepcon_andp_prop'. apply andp_right.
      { apply prop_right. split; [exact E | ]. split; [reflexivity | ]. split; [exact L1 | ].
        split; [exact W1 | ]. split; [exact HD1 | ]. split; [exact T1 | exact H1]. }
      intros rho. simpl. cancel. }
  rewrite ls6_split. unfold PP, LL, SL6.
  change (fun _ : environ => hdr_tok F m) with (lift0 (hdr_tok F m)).
  abbreviate_semax.
  forward.
  forward_if.
  { (* FCOMMENT *)
    assert (F1: Z.land (i_flags (m_s m)) 4096 <> 0)
      by (intro X; apply (int_and_zero _ 4096 ltac:(rep_lia)) in X; contradiction).
    pose proof (mwf_have m W) as HVR.
    fif_prop (m_have m <> 0).
    - exfalso. apply (hpass_noleave_set _ n m m HP); [rewrite HM; reflexivity | ].
      rewrite (stepf2_COMMENT _ _ _ m HM). apply c_COMMENT2_have0; auto.
    - forward. ra_red6 F m. entailer!.
    - Intros. rename H2 into HV1.
      forward.
      rewrite hd6_open. Intros vt vtm vxf vos vxl vhc lx ln0 lc.
      rename H2 into HI. rename H3 into HPR.
      pose proof (mw_h _ W) as HW. pose proof (mw_s _ W) as SW. pose proof (mw_inp _ W) as INP.
      pose proof (mw_nx _ W) as NX.
      assert (HMs: i_mode (m_s m) = IM.COMMENT) by exact HM.
      destruct HI as (I1 & I2 & I3 & I4 & I5) eqn:HIe. clear HIe.
      destruct (I5 HMs) as (L0R & _ & _).
      pose proof HPR as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
      rewrite (cc6_COMMENT _ _ HMs) in P8. destruct P8 as (LN0 & _ & S0).
      destruct (zstr_f (Z.to_nat (m_have m)) (name_bytes m) (m_have m) (i_length (m_s m)) (h_comm_max (m_h m))
                  (andb (i_head (m_s m)) (h_cp (m_h m))) (h_cbuf (m_h m)) 0) as [[[c b] ln] bf] eqn:ZS.
      pose proof (zstr_f_ok (Z.to_nat (m_have m)) (name_bytes m) (m_have m) (i_length (m_s m))
                    (h_comm_max (m_h m)) (andb (i_head (m_s m)) (h_cp (m_h m))) (h_cbuf (m_h m)) 0) as ZOK.
      rewrite ZS in ZOK.
      assert (BB: bytes_ok (name_bytes m)) by (unfold name_bytes; apply Forall_sublist; apply INP).
      destruct ZOK as (Z1 & Z2 & Z3 & Z4).
      { exact BB. }
      { unfold name_bytes, m_have. rewrite Zlength_sublist; lia. }
      { lia. }
      { apply (sw_length _ SW). }
      { rewrite (proj1 (hw_cbuf _ HW)). lia. }
      { apply (hw_cbuf _ HW). }
      assert (HC: 0 <= c <= m_have m) by lia.
      assert (RLn: urange ln).
      { pose proof (sw_length _ SW). pose proof (hw_comm_max _ HW). unfold urange in *.
        destruct (Z.max_spec (i_length (m_s m)) (h_comm_max (m_h m))) as [[_ E] | [_ E]]; rewrite E in Z2; rep_lia. }
      assert (LBf: Zlength bf = h_comm_max (m_h m)) by (rewrite Z3; apply (hw_cbuf _ HW)).
      pose proof (mwf_cm_loop m ln bf W HM RLn LBf Z4) as Wl.
      pose proof (c_COMMENT2_str m c b ln bf F1 HV1 ZS) as Ecase.
      eapply semax_seq'.
      { eapply semax_pre; [ | apply (semax_comm_loop6 F m c b ln bf vt vtm vxf vos vxl vhc lx ln0 lc
                                       FOK W HD HH HV1 L0R LN0 S0 ZS)].
        unfold PP, LL, SL6. entailer!. }
      Intros lc1. rename H2 into HL1.
      eapply semax_seq'.
      { apply (semax_comm_crc6 F (cm_loop m ln bf) c b (hopen6 F (m_h m) vt vtm vxf vos vxl vhc lx ln0 lc1)
                 FOK Wl HV1 HC). }
      rewrite SL6_cm_comment.
      change (PP F (cm_loop m ln bf)) with (PP F m). change (LL F (cm_loop m ln bf)) with (LL F m).
      assert (W3: mwf3 (fin_c (nm_comment m c ln bf))).
      { apply mwf3_fin_c; [apply mwf_cm_comment; auto | rewrite cm_comment_mode; exact HM]. }
      assert (L3: m_leave (nm_comment m c ln bf) = 0) by (rewrite cm_comment_leave; exact HL).
      assert (HD3: hd_ok F (fin_c (nm_comment m c ln bf))) by (apply cm_comment_hd; exact HD).
      assert (T3: hdr_tok F (nm_comment m c ln bf) = hdr_tok F m) by apply cm_comment_tok.
      assert (HH3: i_head (m_s (fin_c (nm_comment m c ln bf))) = true) by (rewrite cm_comment_eq; exact HH).
      set (m3 := nm_comment m c ln bf) in *.
      unfold PP, LL.
      destruct (f_ib F) as [ | ish ip ilo inn icont] eqn:IB.
      { exfalso. unfold in_ok in H. unfold m_have in HV1. rewrite H, Zlength_nil in HV1, NX. lia. }
      cbn [in_ptr] in *.
      assert (IP: isptr ip) by (destruct H as (_ & X & _); exact X).
      unfold SL6.
      forward. forward.
      forward_if.
      + assert (Hb: b <> 0) by (intro X; subst b; contradiction).
        exfalso. apply (hpass_noleave_set _ n m m3 HP); [rewrite HM; reflexivity | ].
        rewrite (stepf2_COMMENT _ _ _ m HM), Ecase. rewrite (proj2 (Z.eqb_neq _ _) Hb). reflexivity.
      + assert (Hb: b = 0).
        { match goal with X: Int.repr b = Int.zero |- _ =>
            apply (f_equal Int.unsigned) in X; rewrite Int.unsigned_repr in X by (pose proof (zstr_f_brange _ _ _ _ _ _ _ _ _ _ _ _ BB ZS); rep_lia); exact X end. }
        forward.
        assert (NPc: h_cp (m_h m) = true -> sublist 0 ln lc1 = byte_vals (sublist 0 ln bf) /\
                       Z.min (fz bf + 1) (h_comm_max (m_h m)) <= ln <= h_comm_max (m_h m)).
        { intros NPt. rewrite HH, NPt in ZS. cbn [andb] in ZS. subst b.
          destruct (zstr_f_cn (name_bytes m) (m_have m) (i_length (m_s m)) (h_comm_max (m_h m)) (h_cbuf (m_h m)) c ln bf ltac:(lia) L0R (proj1 (hw_cbuf _ HW)) ZS) as (A & B & C).
          split; [exact H3 | lia]. }
        sep_apply (hd6_comm_fin F m c ln bf vt vtm vxf vos vxl vhc lx ln0 lc lc1 HM HW HI HPR HL1 LBf NPc).
        ra_red6 F m. unfold comm_mid6. Exists m3.
        apply andp_right.
        { apply prop_right. split; [ | exact (conj L3 (conj W3 (conj HD3 (conj T3 HH3))))].
          rewrite (stepf2_COMMENT _ _ _ m HM), Ecase. rewrite Hb. cbn [Z.eqb negb].
          symmetry. exact (stepf2_HCRC (f_flush F) lenfix_list distfix_list (fin_c m3) eq_refl). }
        rewrite <- T3, ls6_split. unfold PP, LL, SL6, m3. rewrite cm_comment_eq. unfold cm3. rewrite IB.
        mnorm_goal.
        fin_tac. }
  (* no FCOMMENT: head->comment = Z_NULL *)
  assert (F0: Z.land (i_flags (m_s m)) 4096 = 0) by (apply int_and_zero; [rep_lia | assumption]).
  set (m1 := upd_h m (fun h => set_h_cp h false)).
  assert (E0: stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list (fin_c m1)).
  { rewrite (stepf2_COMMENT _ _ _ m HM), (c_COMMENT2_none _ F0), HH. symmetry.
    exact (stepf2_HCRC (f_flush F) lenfix_list distfix_list (fin_c m1) eq_refl). }
  assert (HM1: m_mode m1 = COMMENT) by exact HM.
  assert (L1: m_leave m1 = 0) by exact HL.
  assert (W0: mwf3 (fin_c m1)).
  { apply mwf3_fin_c; [ | exact HM1]. pose proof (mwf_cp_false m W) as X. rewrite HH in X. exact X. }
  assert (HD0: hd_ok F (fin_c m1)).
  { pose proof (hd_ok_cp_false F m HD) as X. rewrite HH in X. exact X. }
  assert (T0: hdr_tok F m1 = hdr_tok F m) by reflexivity.
  assert (T0': hdr_tok F (fin_c m1) = hdr_tok F m) by reflexivity.
  assert (HH1: i_head (m_s m1) = true) by exact HH.
  pose proof (mw_h _ W) as HW.
  rewrite hd6_open. Intros vt vtm vxf vos vxl vhc lx ln0 lc.
  match goal with X: hinv6 _ _ |- _ => rename X into HI6 end.
  match goal with X: hprops6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename X into HPR6 end.
  unfold hopen6, hstr6. rewrite HH. Intros.
  forward.
  forward_if.
  + forward. forward.
    post_midc6. unfold comm_mid6. Exists m1.
    apply andp_right; [apply prop_right; exact (conj E0 (conj L1 (conj W0 (conj HD0 (conj T0' HH1))))) | ].
    rewrite <- T0, ls6_split. unfold PP, LL, SL6, m1. rewrite mem_rep_nc_upd_h.
    entailer!.
    replace (i_head (m_s (upd_h m (fun h => set_h_cp h false)))) with true by (symmetry; exact HH).
    cancel.
    eapply derives_trans; [ | apply (hd6_comm_none F m vt vtm vxf vos vxl vhc lx ln0 lc HM HW HI6 HPR6)].
    unfold hopen6, hstr6. cbn [h_cp set_h_cp h_xp h_cp h_extra_max h_comm_max h_comm_max h_done]. cancel; apply derives_refl.
  + assert_PROP (isptr (f_headp F)) by entailer!.
    match goal with X: f_headp F = nullval |- _ => rewrite X in *; contradiction end.
Qed.
