(* RT-H: case EXTRA (index 5) of inflate() with the partial header hd6 framed (RTHCase.case_ok6):
   with FEXTRA copy = min(length, have) input bytes, the part below extra_max memcpy'd into head->extra at
   extra_len - length (the defined prefix grows), crc, length -= copy; then length = 0, mode NAME, falls into NAME. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHEx6Kit.
Require Import Zlib.proof.roundtrip.RTHEXTRA6Mb.
Require Import Zlib.proof.roundtrip.RTHEXTRA6Cpy.
Require Import Zlib.proof.inflate.ExtraKit5.
Require Import Zlib.proof.inflate.ExtraBody5.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the header from EXTRA (all of the field copied, or no FEXTRA) to NAME *)
Lemma hd6_extra_fin: forall F m1, i_mode (m_s m1) = IM.EXTRA -> hwf (m_h m1) ->
  (i_length (m_s m1) = 0 \/ fextra (m_s m1) = false) ->
  hd6 F m1 |-- hd6 F (extra_fin m1).
Proof.
  intros F m1 HM HW HL. unfold hd6, head_rep6.
  apply derives_extract_prop. intros HI.
  pose proof HI as (I1 & I2 & I3 & I4 & I5).
  assert (XF: h_xp (m_h m1) = true -> fextra (m_s m1) = true) by (apply I2; rewrite HM; reflexivity).
  assert (E: hph (m_s (extra_fin m1)) = hph (m_s m1) /\ fextra (m_s (extra_fin m1)) = fextra (m_s m1) /\
             cx6 (m_s (extra_fin m1)) (m_h (extra_fin m1)) = cx6 (m_s m1) (m_h m1) /\
             cn6 (m_s (extra_fin m1)) (m_h (extra_fin m1)) = cn6 (m_s m1) (m_h m1) /\
             cc6 (m_s (extra_fin m1)) (m_h (extra_fin m1)) = cc6 (m_s m1) (m_h m1)).
  { unfold hph, cx6, cn6, cc6, extra_fin, set_mode, upd_s. cbn [m_s m_h set_m_s set_i_mode set_i_length i_mode i_length].
    rewrite HM. unfold fextra in *. cbn [i_flags set_i_mode set_i_length].
    split; [reflexivity | split; [reflexivity | ]].
    split; [ | split; reflexivity].
    cbn. destruct (h_xp (m_h m1)) eqn:X; [ | reflexivity].
    destruct HL as [HL | HL]; [rewrite HL; f_equal; lia | ].
    specialize (XF eq_refl). unfold fextra in XF. congruence. }
  destruct E as (E1 & E2 & E3 & E4 & E5).
  change (m_h (extra_fin m1)) with (m_h m1) in *.
  rewrite E1, E2, E3, E4, E5.
  apply andp_right; [ | apply derives_refl].
  apply prop_right.
  pose proof (hw_name_max _ HW) as NM.
  unfold hinv6, extra_fin, set_mode, upd_s, fextra in *. cbn [m_s m_h set_m_s set_i_mode set_i_length i_mode i_length i_flags] in *.
  rewrite HM in I2.
  split; [exact I1 | ]. split; [intros _; exact (I2 eq_refl) | ].
  split; [intros E; discriminate E | ].
  split; [intros _; split; [lia | split; [reflexivity | rewrite sublist_nil; constructor]] | ].
  intros E; discriminate E.
Qed.

Lemma ex_fall_ok6: forall F m mf,
  stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list mf ->
  m_mode mf = IM.NAME -> m_leave mf = 0 -> mwf3 mf -> hd_ok F mf -> hdr_tok F mf = hdr_tok F m ->
  i_head (m_s mf) = true ->
  PROPx (PPx F mf) (LOCALx (LLx F mf) (SEPx (SLx6 F mf (hdr_tok F m))))
  |-- fall_post6 F m IM.NAME * lift0 (hdr_tok F m).
Proof.
  intros F m mf E HM HL W HD HT HH. unfold fall_post6. rewrite exp_sepcon1. Exists mf.
  rewrite sepcon_andp_prop'. apply andp_right; [apply prop_right; tauto | ].
  change (lift0 (hdr_tok F m)) with (fun _ : environ => hdr_tok F m).
  rewrite <- ls_ex_tok6. intros rho. simpl. cancel.
Qed.

Ltac fix_post :=
  match goal with |- context [RA_normal (match ?R with _ => _ end)] =>
    destruct R as [r1 r2 r3 r4]; cbn [RA_normal] end.

Lemma extra_body6 {Espec: OracleKind} (F: frame) (m: mst) (n: nat):
  frame_ok5 F -> m_mode m = IM.EXTRA -> m_leave m = 0 -> mwf3 m -> hd_ok F m -> i_head (m_s m) = true ->
  hpass (f_flush F) (S n) m ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m)) (case_body 5)
    (overridePost (fall_post6 F m IM.NAME * (fun _ => hdr_tok F m))
       (frame_ret_assert (switch_ret_assert (case_post6 F m)) (fun _ => hdr_tok F m))).
Proof.
  intros [FOK FR] HM HL [W W3] HD Hh HP.
  pose proof (step_extra (f_flush F) m HM) as [SB SF]. cbv zeta in SB, SF.
  pose proof (mwf_extra_upd m W HM) as (WU & HMU & HLU).
  pose proof (sw_flags _ (mw_s _ W)) as RF.
  assert (HDM: hdr_mode (m_mode m) = true) by (rewrite HM; reflexivity).
  rewrite ls_ex_tok6.
  change (fun _ : environ => hdr_tok F m) with (lift0 (hdr_tok F m)).
  case_body_stmt.
  unfold PPx, LLx, SLx6.
  abbreviate_semax.
  forward.
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq.
  forward_if.
  - assert (Hf: Z.land (i_flags (m_s m)) 1024 <> 0).
    { match goal with H: Int.and _ _ <> Int.zero |- _ => apply Z.eqb_neq; apply (exc_flagbit _ _ H) end. }
    rewrite (proj2 (Z.eqb_neq _ _) Hf) in SB, SF.
    pose proof (sw_length _ (mw_s _ W)) as LN. pose proof (mwf_have m W) as HV.
    unfold urange in LN.
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx (temp _copy _ :: ?Q) (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _copy (Vint (Int.repr (Z.min (i_length (m_s m)) (m_have m)))) :: Q) (SEPx R))) end.
    + forward. fix_post. entailer!. rewrite Z.min_r by lia. reflexivity.
    + forward. fix_post. entailer!. rewrite Z.min_l by lia. reflexivity.
    + remember (Z.min (i_length (m_s m)) (m_have m)) as c eqn:Hc.
      destruct (extra_upd_io m) as [EI EA].
      forward_if (PROPx (PPx F (extra_upd m)) (LOCALx (temp _copy (Vint (Int.repr c)) :: LLx F (extra_upd m))
                    (SEPx (SLx6 F (extra_upd m) (hdr_tok F m))))).
      * assert (Hn: c <> 0) by (intro E; subst c; rewrite E in *; contradiction).
        unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS.
        eapply semax_pre; [ | eapply ConseqFacts.semax_post''; [ | apply (semax_extra_cpy6 F m c FOK W HD Hh HM Hc Hn)]].
        { unfold PPx, LLx, SLx6. entailer!. }
        unfold abbreviate in POSTCONDITION. subst POSTCONDITION. unfold overridePost. fix_post.
        unfold PPx. rewrite EI, EA. apply andp_left2. apply derives_refl.
      * assert (Hz: c = 0).
        { match goal with H: Int.repr c = Int.zero |- _ =>
            apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; exact H end. }
        forward.
        try (unfold abbreviate in POSTCONDITION; subst POSTCONDITION).
        try unfold overridePost. try fix_post.
        rewrite (extra_upd_zero m) by congruence.
        unfold PPx, LLx, SLx6. entailer!.
      * assert (HK: hkey (extra_fin (extra_upd m)) = hkey m) by (rewrite hkey_extra_fin; apply hkey_extra_upd).
        pose proof (mwf3_extra_fin (extra_upd m) WU HMU) as [WF LF].
        pose proof (sw_length _ (mw_s _ WU)) as LN1. unfold urange in LN1.
        assert (LZ: i_length (m_s (extra_upd m)) = 0).
        { destruct (Z.eq_dec (i_length (m_s (extra_upd m))) 0) as [E | E]; [exact E | exfalso].
          pose proof (hpass_brk _ n m _ HDM HP (SB E Hf)) as B. discriminate B. }
        specialize (SF (or_introl LZ)).
        assert (HWU: hwf (m_h (extra_upd m))) by apply (mw_h _ WU).
        assert (HHU: i_head (m_s (extra_upd m)) = true).
        { unfold hkey in HK. injection HK as K1 _. change (i_head (m_s (extra_upd m)) = true).
          change (i_head (m_s (extra_fin (extra_upd m)))) with (i_head (m_s (extra_upd m))) in K1. congruence. }
        set (m1 := extra_upd m) in *. clearbody m1.
        unfold PPx, LLx, SLx6.
        forward.
        unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq.
        forward_if.
        -- exfalso. match goal with H: Int.repr _ <> Int.zero |- _ => apply H end. rewrite LZ. reflexivity.
        -- forward. forward.
           try (unfold abbreviate in POSTCONDITION; subst POSTCONDITION).
           try unfold overridePost. repeat fix_post.
           eapply derives_trans; [ | apply (ex_fall_ok6 F m (extra_fin m1) SF eq_refl
               ltac:(rewrite LF, HLU; exact HL) WF (hkey_hd_ok F m _ HK HD) (hkey_hdr_tok F m _ HK) HHU)].
           unfold PPx, LLx, SLx6.
           sep_apply (hd6_extra_fin F m1 HMU HWU (or_introl LZ)).
           change (mem_x F (extra_fin m1)) with (mem_x F m1).
           change (m_have (extra_fin m1)) with (m_have m1). change (m_left (extra_fin m1)) with (m_left m1).
           cbn [extra_fin set_mode upd_s set_m_s m_s m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
                set_i_mode set_i_length i_mode i_wrap i_flags i_check i_head i_length].
           unfold IM.NAME.
           entailer!.
  - assert (Hf: Z.land (i_flags (m_s m)) 1024 = 0).
    { match goal with H: Int.and _ _ = Int.zero |- _ => apply Z.eqb_eq; apply (exc_flagbit0 _ _ H); rep_lia end. }
    rewrite (proj2 (Z.eqb_eq _ _) Hf) in SF.
    specialize (SF (or_intror Hf)).
    pose proof (mwf3_extra_fin m W HM) as [WF LF].
    assert (FXF: fextra (m_s m) = false) by (unfold fextra; rewrite Hf; reflexivity).
    forward. forward.
    destruct (frame_ret_assert (switch_ret_assert (case_post6 F m)) (lift0 (hdr_tok F m))) as [r1 r2 r3 r4].
    cbn [RA_normal].
    eapply derives_trans; [ | apply (ex_fall_ok6 F m (extra_fin m) SF eq_refl ltac:(rewrite LF; exact HL) WF
        (hkey_hd_ok F m _ (hkey_extra_fin m) HD) (hkey_hdr_tok F m _ (hkey_extra_fin m)) Hh)].
    unfold PPx, LLx, SLx6.
    sep_apply (hd6_extra_fin F m HM (mw_h _ W) (or_intror FXF)).
    change (mem_x F (extra_fin m)) with (mem_x F m).
    change (m_have (extra_fin m)) with (m_have m). change (m_left (extra_fin m)) with (m_left m).
    cbn [extra_fin set_mode upd_s set_m_s m_s m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
         set_i_mode set_i_length i_mode i_wrap i_flags i_check i_head i_length].
    unfold IM.NAME.
    entailer!.
Qed.

Lemma rth_extra6 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_ok6 F IM.NAME 6 -> case_ok6 F IM.EXTRA 5.
Proof.
  intros FOK HY m n HM HL W HD Hh HP.
  apply (case_fallthrough6 F m n IM.NAME 5); [lia | reflexivity | rewrite HM; reflexivity | exact HP | exact HY | ].
  apply (extra_body6 F m n); auto.
Qed.
