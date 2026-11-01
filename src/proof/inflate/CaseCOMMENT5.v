(* inflate(), case COMMENT (7) in Delta_cases5 (v5: Model2.v, header tokens): if (flags & 0x1000) { the do-while
   storing the comment into head->comment (zstr_f), crc32, leave when the input ran out } else
   head->comment = Z_NULL; state->mode = HCRC; falls into HCRC (no `state->length = 0`: Model2.v c_COMMENT2) *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.NCKit5.
Require Import Zlib.proof.inflate.NCLoop5.
Require Import Zlib.proof.inflate.NCCrc5.
Require Import Zlib.proof.inflate.NCMach5.
Require Import Zlib.proof.inflate.CaseNAME5.
Require Import Zlib.proof.inflate.ModeKit5.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition fin_c (m1: mst) : mst := set_mode m1 HCRC.

Lemma hdr_tok_fin_c: forall F m1, hdr_tok F (fin_c m1) = hdr_tok F m1.
Proof. reflexivity. Qed.

(* `state->mode = md;` with the tokens framed *)
Lemma semax_mode_T {Espec: OracleKind} (F: frame) (m: mst) (md: Z) (T: mpred):
  semax Delta_cases5 (loop_state F m * (fun _ => T))
    (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                       (Tstruct _inflate_state noattr)) _mode tint)
       (Econst_int (Int.repr md) tint))
    (normal_ret_assert (loop_state F (set_mode m md) * (fun _ => T))).
Proof.
  rewrite <- frame_normal. apply semax_frame; [ | apply semax_store_mode5].
  intros rho te _. reflexivity.
Qed.

Lemma mwf_cm_comment: forall m c ln bf,
  mwf m -> m_mode m = COMMENT -> urange ln -> Zlength bf = h_comm_max (m_h m) -> bytes_ok bf ->
  0 <= c <= m_have m -> mwf (nm_comment m c ln bf).
Proof.
  intros m c ln bf W HM RL LB BB C. unfold nm_comment.
  assert (W1: mwf (crc_if m (inbytes m c))).
  { apply mwf_crc_if'; auto. unfold inbytes. apply Forall_sublist. apply (mw_inp _ W). }
  rewrite crc_if_eq in *.
  eapply mwf_hdr; [exact W1 | | | | | | ..]; cbn; try reflexivity.
  - right. exact HM.
  - unfold m_mode in HM. rewrite HM. unfold HEAD, COMMENT, TYPEDO; lia.
  - apply swf_length; [apply (mw_s _ W1) | exact RL].
  - apply hwf_cbuf; [apply (mw_h _ W) | exact LB | exact BB].
  - pose proof (mw_nx _ W). unfold m_have in C. lia.
Qed.

Lemma mwf3_fin_c: forall m1, mwf m1 -> m_mode m1 = COMMENT -> mwf3 (fin_c m1).
Proof.
  intros m1 W HM. unfold fin_c. split.
  - eapply mwf_hdr; [exact W | right; exact HM | | | | | ..]; cbn; try reflexivity.
    + unfold HEAD, HCRC, TYPEDO; lia.
    + apply swf_mode; [apply (mw_s _ W) | unfold HEAD, HCRC, SYNC; lia].
    + apply (mw_h _ W).
    + apply (mw_nx _ W).
  - apply swf3_hdr. cbn. unfold FLAGS, HCRC, TYPEDO; lia.
Qed.

Lemma mwf_cp_false: forall m,
  mwf m -> mwf (if i_head (m_s m) then upd_h m (fun h => set_h_cp h false) else m).
Proof.
  intros m W. destruct (i_head (m_s m)); [ | exact W].
  destruct W; constructor; auto. apply hwf_cp; auto.
Qed.

Lemma hdr_tok_cp_false: forall F m,
  hdr_tok F (if i_head (m_s m) then upd_h m (fun h => set_h_cp h false) else m) = hdr_tok F m.
Proof. intros. destruct (i_head (m_s m)); reflexivity. Qed.

Lemma cm_comment_mode: forall m c ln bf, m_mode (nm_comment m c ln bf) = m_mode m.
Proof. intros. unfold nm_comment. rewrite crc_if_eq. reflexivity. Qed.
Lemma cm_comment_leave: forall m c ln bf, m_leave (nm_comment m c ln bf) = m_leave m.
Proof. intros. unfold nm_comment. rewrite crc_if_eq. reflexivity. Qed.
Lemma cm_comment_tok: forall F m c ln bf, hdr_tok F (nm_comment m c ln bf) = hdr_tok F m.
Proof. intros. unfold nm_comment. rewrite crc_if_eq. reflexivity. Qed.
Lemma cm_comment_hd: forall F m c ln bf, hd_ok F m -> hd_ok F (fin_c (nm_comment m c ln bf)).
Proof. intros. unfold fin_c, nm_comment. rewrite crc_if_eq. exact H. Qed.

Lemma mwf_cm_loop: forall m ln bf,
  mwf m -> m_mode m = COMMENT -> urange ln -> Zlength bf = h_comm_max (m_h m) -> bytes_ok bf ->
  mwf (cm_loop m ln bf).
Proof.
  intros m ln bf W HM RL LB BB. unfold cm_loop.
  eapply mwf_hdr; [exact W | | | | | | ..]; cbn; try reflexivity.
  - right. exact HM.
  - unfold m_mode in HM. rewrite HM. unfold HEAD, COMMENT, TYPEDO; lia.
  - apply swf_length; [apply (mw_s _ W) | exact RL].
  - apply hwf_cbuf; [apply (mw_h _ W) | exact LB | exact BB].
  - apply (mw_nx _ W).
Qed.

Definition cm3 (m: mst) (c ln: Z) (bf: list Z) : mst :=
  set_m_nx (set_m_h (set_m_s m (set_i_length (set_i_check (m_s m) (crc_val (m_s m) (inbytes m c))) ln))
                    (set_h_cbuf (m_h m) bf)) (m_nx m + c).

Lemma cm_comment_eq: forall m c ln bf, nm_comment m c ln bf = cm3 m c ln bf.
Proof. intros. unfold nm_comment, cm3. rewrite crc_if_eq. reflexivity. Qed.

Lemma SL_cm_comment: forall F m c ln bf,
  SL F (crc_if (cm_loop m ln bf) (inbytes (cm_loop m ln bf) c)) = SL F (nm_comment m c ln bf).
Proof. intros. unfold nm_comment, cm_loop. rewrite !crc_if_eq. reflexivity. Qed.

Lemma hd_ok_cp_false: forall F m, hd_ok F m -> hd_ok F (if i_head (m_s m) then upd_h m (fun h => set_h_cp h false) else m).
Proof.
  intros F m H. unfold hd_ok in *. destruct (i_head (m_s m)) eqn:E; cbn; intro X.
  - destruct (H eq_refl) as (A & B & C). split; [exact A | split; [exact B | discriminate]].
  - rewrite E in X. discriminate.
Qed.

(* the machine before the tail: m1 with `mode = HCRC` the fallthrough machine *)
Definition comm_mid (F: frame) (m: mst) : environ -> mpred :=
  EX m1: mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list (fin_c m1) /\
        m_leave m1 = 0 /\ mwf3 (fin_c m1) /\ hd_ok F (fin_c m1) /\ hdr_tok F (fin_c m1) = hdr_tok F m) &&
    (loop_state F m1 * (fun _ => hdr_tok F m)).

Ltac post_midc := match goal with |- context [RA_normal ?X] =>
  match X with context [case_post2 ?F ?m] =>
  replace (RA_normal X) with (comm_mid F m)
    by (destruct (frame_ret_assert (switch_ret_assert (case_post2 F m)) (lift0 (hdr_tok F m))); reflexivity) end end.

Lemma case_COMMENT5 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_ok5 F HCRC 8 -> case_okT5 F COMMENT 7.
Proof.
  intros [FOK FR] HY m HM HL [W W2] HD. pose proof FOK as (HWS & HWH & HRG & HRT).
  apply (case_fallthroughT5 F m HCRC 7); [lia | apply case_okT5_of_ok5; exact HY | ].
  case_body_stmt.
  apply semax_seq with (Q := comm_mid F m).
  2:{ unfold comm_mid. apply extract_exists_pre. intros m1.
      apply semax_extract_prop. intros (E & L1 & W1 & HD1 & T1).
      eapply ConseqFacts.semax_post''; [ | apply semax_mode_T].
      unfold overridePost, fall_postT5. cbn [RA_normal].
      apply andp_left2. rewrite exp_sepcon1. Exists (fin_c m1).
      rewrite sepcon_andp_prop'. apply andp_right; [ | apply derives_refl].
      apply prop_right. split; [exact E | ]. split; [reflexivity | ]. split; [exact L1 | ].
      split; [exact W1 | ]. split; [exact HD1 | exact T1]. }
  rewrite ls_tok_split. unfold PP, LL, SL.
  change (fun _ : environ => hdr_tok F m) with (lift0 (hdr_tok F m)).
  abbreviate_semax.
  forward.
  forward_if.
  { (* FCOMMENT *)
    assert (F1: Z.land (i_flags (m_s m)) 4096 <> 0)
      by (intro X; apply (int_and_zero _ 4096 ltac:(rep_lia)) in X; contradiction).
    pose proof (mwf_have m W) as HVR.
    fif_prop (m_have m <> 0).
    - forward. forward.
      brk_red F m. rewrite exp_sepcon1. Exists (set_leave m). rewrite sepcon_andp_prop'.
      apply andp_right.
      { apply prop_right. rewrite (stepf2_COMMENT _ _ _ m HM). apply c_COMMENT2_have0; auto. }
      change (hdr_tok F m) with (hdr_tok F (set_leave m)).
      rewrite ls_tok_split'. unfold PP, LL, SL. cbn [set_leave set_m_leave m_s m_h m_leave m_inp m_aout m_nx m_ow].
      entailer!. apply derives_refl.
    - forward. ra_red F m. entailer!.
    - Intros. rename H2 into HV1.
      forward.
      destruct (zstr_f (Z.to_nat (m_have m)) (name_bytes m) (m_have m) (i_length (m_s m)) (h_comm_max (m_h m))
                  (andb (i_head (m_s m)) (h_cp (m_h m))) (h_cbuf (m_h m)) 0) as [[[c b] ln] bf] eqn:ZS.
      pose proof (mw_h _ W) as HW. pose proof (mw_s _ W) as SW. pose proof (mw_inp _ W) as INP.
      pose proof (mw_nx _ W) as NX.
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
      pose proof (zstr_f_brange _ _ _ _ _ _ _ _ _ _ _ _ BB ZS) as BR.
      assert (HC: 0 <= c <= m_have m) by lia.
      assert (RLn: urange ln).
      { pose proof (sw_length _ SW). pose proof (hw_comm_max _ HW). unfold urange in *.
        destruct (Z.max_spec (i_length (m_s m)) (h_comm_max (m_h m))) as [[_ E] | [_ E]]; rewrite E in Z2; rep_lia. }
      assert (LBf: Zlength bf = h_comm_max (m_h m)) by (rewrite Z3; apply (hw_cbuf _ HW)).
      pose proof (mwf_cm_loop m ln bf W HM RLn LBf Z4) as Wl.
      pose proof (c_COMMENT2_str m c b ln bf F1 HV1 ZS) as Ecase.
      eapply semax_seq'.
      { eapply semax_pre; [ | apply (semax_comm_loop_m F m c b ln bf FOK W HD HV1 ZS)].
        unfold PP, LL, SL. entailer!. }
      eapply semax_seq'.
      { apply (semax_comm_crc_m F (cm_loop m ln bf) c b FOK Wl HV1 HC). }
      rewrite SL_cm_comment.
      change (PP F (cm_loop m ln bf)) with (PP F m). change (LL F (cm_loop m ln bf)) with (LL F m).
      assert (W3: mwf3 (fin_c (nm_comment m c ln bf))).
      { apply mwf3_fin_c; [apply mwf_cm_comment; auto | rewrite cm_comment_mode; exact HM]. }
      assert (L3: m_leave (nm_comment m c ln bf) = 0) by (rewrite cm_comment_leave; exact HL).
      assert (HD3: hd_ok F (fin_c (nm_comment m c ln bf))) by (apply cm_comment_hd; exact HD).
      assert (T3: hdr_tok F (nm_comment m c ln bf) = hdr_tok F m) by apply cm_comment_tok.
      set (m3 := nm_comment m c ln bf) in *.
      unfold PP, LL.
      destruct (f_ib F) as [ | ish ip ilo inn icont] eqn:IB.
      { exfalso. unfold in_ok in H. unfold m_have in HV1. rewrite H, Zlength_nil in HV1, NX. lia. }
      cbn [in_ptr] in *.
      assert (IP: isptr ip) by (destruct H as (_ & X & _); exact X).
      unfold SL.
      forward. forward.
      forward_if.
      + assert (Hb: b <> 0) by (intro X; subst b; contradiction).
        forward. forward.
        brk_red F m. rewrite exp_sepcon1. Exists (set_leave m3). rewrite sepcon_andp_prop'.
        apply andp_right.
        { apply prop_right. rewrite (stepf2_COMMENT _ _ _ m HM), Ecase.
          rewrite (proj2 (Z.eqb_neq _ _) Hb). reflexivity. }
        replace (hdr_tok F m) with (hdr_tok F (set_leave m3)) by exact T3.
        rewrite ls_tok_split'. unfold PP, LL, SL, m3. rewrite cm_comment_eq. unfold cm3. rewrite IB.
        mnorm_goal.
        fin_tac.
      + assert (Hb: b = 0).
        { match goal with X: Int.repr b = Int.zero |- _ =>
            apply (f_equal Int.unsigned) in X; rewrite Int.unsigned_repr in X by rep_lia; exact X end. }
        forward. ra_red F m. unfold comm_mid. Exists m3.
        apply andp_right.
        { apply prop_right. split; [ | exact (conj L3 (conj W3 (conj HD3 T3)))].
          rewrite (stepf2_COMMENT _ _ _ m HM), Ecase. rewrite Hb. cbn [Z.eqb negb].
          symmetry. exact (stepf2_HCRC (f_flush F) lenfix_list distfix_list (fin_c m3) eq_refl). }
        rewrite <- T3, ls_tok_split. unfold PP, LL, SL, m3. rewrite cm_comment_eq. unfold cm3. rewrite IB.
        mnorm_goal.
        fin_tac. }
  (* no FCOMMENT: head->comment = Z_NULL *)
  assert (F0: Z.land (i_flags (m_s m)) 4096 = 0) by (apply int_and_zero; [rep_lia | assumption]).
  set (m1 := if i_head (m_s m) then upd_h m (fun h => set_h_cp h false) else m).
  assert (E0: stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list (fin_c m1)).
  { rewrite (stepf2_COMMENT _ _ _ m HM), (c_COMMENT2_none _ F0). symmetry.
    exact (stepf2_HCRC (f_flush F) lenfix_list distfix_list (fin_c m1) eq_refl). }
  assert (HM1: m_mode m1 = COMMENT) by (unfold m1; destruct (i_head (m_s m)); exact HM).
  assert (L1: m_leave m1 = 0) by (unfold m1; destruct (i_head (m_s m)); exact HL).
  assert (W0: mwf3 (fin_c m1)) by (apply mwf3_fin_c; [apply mwf_cp_false; exact W | exact HM1]).
  assert (HD0: hd_ok F (fin_c m1)) by exact (hd_ok_cp_false F m HD).
  assert (T0: hdr_tok F m1 = hdr_tok F m) by apply hdr_tok_cp_false.
  assert (T0': hdr_tok F (fin_c m1) = hdr_tok F m) by (rewrite hdr_tok_fin_c; exact T0).
  destruct (bool_dec4 (i_head (m_s m))) as [HH | HH].
  - rewrite HH. unfold hp. rewrite head_rep_hstruct. unfold hstruct. Intros.
    forward.
    forward_if.
    + forward. forward.
      post_midc. unfold comm_mid. Exists m1.
      apply andp_right; [apply prop_right; exact (conj E0 (conj L1 (conj W0 (conj HD0 T0')))) | ].
      rewrite <- T0, ls_tok_split. unfold PP, LL, SL, hp, m1. rewrite HH. rewrite mem_rep_nc_upd_h.
      rewrite head_rep_hstruct. unfold hstruct.
      nc_simpl. rewrite HH. entailer!; apply derives_refl.
    + assert_PROP (isptr (f_headp F)) by entailer!.
      match goal with X: f_headp F = nullval |- _ => rewrite X in *; contradiction end.
  - rewrite HH. unfold hp.
    forward.
    forward_if.
    + match goal with X: false = true |- _ => discriminate X end.
    + forward.
      post_midc. unfold comm_mid. Exists m1.
      apply andp_right; [apply prop_right; exact (conj E0 (conj L1 (conj W0 (conj HD0 T0')))) | ].
      rewrite <- T0, ls_tok_split. unfold PP, LL, SL, hp, m1. rewrite HH. cbv iota. rewrite HH.
      entailer!.
Qed.
