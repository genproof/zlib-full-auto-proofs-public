(* Bodies of inflate.c's API functions, version 3: api_reset_stmt (Bodies5.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.ResetSplit5.
Require Import Zlib.proof.inflate_api.ResetKit5.
Require Import Zlib.proof.inflate_api.Body5_end.
#[local] Existing Instance Zlib.units.Inflate.CS.

Local Open Scope logic.

Lemma fc_strm_codes: forall sp, field_compatible t_state (DOT _strm) sp -> field_compatible t_state (DOT _codes) sp.
Proof.
  intros sp (A & B & C & D & E). repeat split; auto. simpl. unfold in_members. simpl. tauto.
Qed.

Lemma codes_at0: forall sp, field_compatible t_state (DOT _strm) sp -> codes_at sp 0 = offset_val 1368 sp.
Proof.
  intros. rewrite <- codes_addr0 by (apply fc_strm_codes; auto).
  unfold field_address. rewrite if_true by (apply fc_strm_codes; auto). reflexivity.
Qed.

Lemma zf_ok_keep: forall z s, zf_ok z -> 0 <= i_wrap s <= 15 -> zf_ok (reset_keep_z z s).
Proof.
  intros z s (A & B & C & D & F & G) W. unfold reset_keep_z, zf_ok. cbn [zf_ai zf_ao zf_tin zf_tout zf_dt zf_adler].
  assert (0 <= Z.land (i_wrap s) 1 <= 1).
  { pose proof (Z.land_ones (i_wrap s) 1 ltac:(lia)) as E1. change (Z.ones 1) with 1 in E1. rewrite E1.
    change (2 ^ 1) with 2. pose proof (Z.mod_pos_bound (i_wrap s) 2). lia. }
  destruct (i_wrap s =? 0); rep_lia.
Qed.

Lemma wrap_and1: forall w, 0 <= w <= 15 ->
  Int64.repr (Int.signed (Int.and (Int.repr w) (Int.repr 1))) = Int64.repr (Z.land w 1).
Proof.
  intros. f_equal. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia.
  assert (0 <= Z.land w 1 <= 1).
  { pose proof (Z.land_ones w 1 ltac:(lia)) as E1. change (Z.ones 1) with 1 in E1. rewrite E1.
    change (2 ^ 1) with 2. pose proof (Z.mod_pos_bound w 2). lia. }
  rewrite Int.signed_repr by rep_lia. reflexivity.
Qed.

(* inflateReset with bit 3 of wrap set (patch F8): the window freed and wbits = 0, then the plain reset; live
   because bit 3 comes only with bit 0 or 1 (Inv.wrap_land8: a wrapped stream before its header) *)
Lemma live_reset_hdr_ok: forall L, live_ok L -> Z.land (i_wrap (l_s L)) 8 <> 0 ->
  live_ok (set_l_s L (reset_s (set_i_wbits (set_i_win (l_s L) false) 0))).
Proof.
  intros [sp winp s h headp hsh xb nb cb] (P & W & M & HW & W3 & HS & WB0 & HD & WF) H8.
  cbn [l_s l_sp l_h l_hsh l_xb l_nb l_cb set_l_s] in *.
  pose proof (wrap_land8 _ (sw_wrap _ W) H8) as H3.
  split; [exact P | ]. split; [ | split; [ | split; [exact HW | split; [ | split; [exact HS | ]]]]].
  - destruct W. constructor; rs_simpl; auto;
      try (unfold HEAD, SYNC, srange, urange, lrange, tref_ok, ENOUGH_CODES in *; rep_lia).
    split; [reflexivity | constructor].
  - constructor; rs_simpl; repeat split; intros; exfalso;
      try (apply head_not_decode; assumption);
      unfold HEAD, LENLENS, CODELENS, LENEXT, DISTEXT, MATCH, DIST in *; lia.
  - destruct W3. constructor; rs_simpl; auto; intros HM;
      try (exfalso; apply head_not_decode; exact HM);
      try (unfold HEAD, LENEXT, DISTEXT in *; lia).
  - rs_simpl. split; [intros _; split; [exact H3 | reflexivity] | ]. split; [intro; discriminate | ].
    intros _ _. split; [reflexivity | left; reflexivity].
Qed.

Lemma live_reset : live_reset_stmt.
Proof.
  intros z L H. unfold reset_f, thd3. cbv zeta. cbn [snd]. unfold reset_full_s, reset_hdr_s.
  destruct (Z.eqb_spec (Z.land (i_wrap (l_s L)) 8) 0) as [E | E].
  - exact (live_reset_ok L H).
  - exact (live_reset_hdr_ok L H E).
Qed.

Lemma body_inflateResetKeep {E: OracleKind}:
  semax_body Vprog_inflate Gp_resetkeep f_inflateResetKeep inflateResetKeep_spec.
Proof.
  start_function.
  unfold rstream_opt.
  destruct (eq_dec strmp nullval) as [Hn | Hn].
  - subst strmp.
    forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
    { simpl. cancel. }
    forward_if; [forward | discriminate].
  - destruct r as [ | L vl vd vn vs | L rf vl vd vn vs].
    { unfold rstream, istream, zstrm_at, strm_rep. Intros.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (nullval, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), nullval, 0, false, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval); [contradiction | ].
    forward_if.
    { forward. unfold reset_ret, reset_post, rs_live, rstream_opt, rstream, istream, zstrm_at, strm_rep.
      rewrite !if_false by auto. entailer!. }
    { match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. } }
    2: {
    destruct L as [sp winp s h headp hsh xb nb cb].
    unfold reset_pre, rs_live in H. rewrite if_false in H by auto.
    specialize (H eq_refl). unfold thd3, reset_keep_f in H. cbn [snd] in H.
    unfold rstream. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_v_keep. Intros.
    pose proof H as LOK.
    destruct H as (Hsp & SW & MW & HW & SW3 & HS & WW). cbn [l_sp l_s l_h set_l_s] in Hsp, SW, MW, HW, SW3, HS, WW.
    pose proof (sw_wrap _ SW) as HWR. unfold reset_keep_s in HWR. cbn [i_wrap set_i_mode set_i_last set_i_havedict set_i_flags set_i_dmax set_i_head set_i_hold set_i_bits set_i_lencode set_i_distcode set_i_next set_i_sane set_i_back set_i_total] in HWR.
    clear SW MW HW SW3 HS WW.
    unfold raw_strm.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (rf_ni rf, (rf_ai rf, (rf_tin rf, (rf_no rf, (rf_ao rf, (rf_tout rf, (nullval, (sp, (zca, (zcf,
      (nullval, (rf_dt rf, (rf_adler rf, rf_res rf))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    match goal with H: HEAD <= i_mode s <= SYNC |- _ => rename H into HMD end.
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    forward. (* t'8 = strm->state *)
    forward. (* state = cast *)
    forward. (* t'2 = 0 *)
    forward. (* state->total *)
    forward. (* t'3 *)
    forward. (* strm->total_out *)
    forward. (* strm->total_in *)
    forward. (* strm->msg *)
    forward. (* strm->data_type *)
    forward. (* t'6 = state->wrap *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx (data_at ?sh ?t (?a1,(?a2,(?a3,(?a4,(?a5,(?a6,(?a7,(?a8,(?a9,(?a10,(?a11,(?a12,(?a13,?a14))))))))))))) ?p :: ?R)))) _ _ =>
      forward_if (PROPx P (LOCALx Q (SEPx (data_at sh t (a1,(a2,(a3,(a4,(a5,(a6,(a7,(a8,(a9,(a10,(a11,(a12,
        ((if i_wrap s =? 0 then a13 else lv (Z.land (i_wrap s) 1)), a14))))))))))))) p :: R))))
    end.
    { forward. forward.
      assert (HW0: i_wrap s <> 0) by (match goal with H: i_wrap s <> 0 |- _ => exact H end).
      rewrite (proj2 (Z.eqb_neq _ _) HW0). rewrite wrap_and1 by lia. entailer!. }
    { forward.
      assert (HW0: i_wrap s = 0).
      { match goal with H: Int.repr (i_wrap s) = Int.zero |- _ =>
          apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; exact H end. }
      rewrite (proj2 (Z.eqb_eq _ _) HW0). entailer!. }
    forward. (* mode *)
    forward. (* last *)
    forward. (* havedict *)
    forward. (* flags *)
    forward. (* dmax *)
    forward. (* head *)
    forward. (* hold *)
    forward. (* bits *)
    assert_PROP (field_compatible t_state (DOT _strm) sp) by entailer!.
    forward. (* t'4 = state->codes *)
    forward. (* next *)
    forward. (* t'5 *)
    forward. (* distcode *)
    forward. (* lencode *)
    forward. (* sane *)
    forward. (* back *)
    forward. (* return *)
    unfold reset_ret, reset_post, rs_live; rewrite if_false by auto.
    unfold reset_keep_f, fst3, snd3, thd3. cbn [fst snd]. rewrite Z.eqb_refl.
    unfold istream_raw, raw_strm, raw_after_init, state_mem. cbn [l_sp l_winp l_s l_h l_headp set_l_s] in *.
    rewrite state_rep_v_eq, state_rep_v_keep.
    match goal with |- context [U_keep ?g ?a ?b ?c (reset_keep_s s) ?x1 ?x2 ?x3 ?x4] =>
      change (U_keep g a b c (reset_keep_s s) x1 x2 x3 x4) with (U_keep g a b c s vl vd vn vs) end.
    change (win_rep winp (reset_keep_s s)) with (win_rep winp s).
    rk_simpl. cbn [rf_ni rf_ai rf_tin rf_no rf_ao rf_tout rf_dt rf_adler rf_res tref_val].
    rewrite codes_at0 by auto.
    entailer!.
    (* RRAW-END *) }
    destruct L as [sp winp s h headp hsh xb nb cb].
    unfold reset_pre, rs_live in H. rewrite if_false in H by auto.
    specialize (H eq_refl). unfold thd3, reset_keep_f in H. cbn [snd] in H.
    unfold rstream. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_v_keep. Intros.
    pose proof H as LOK.
    destruct H as (Hsp & SW & MW & HW & SW3 & HS & WW). cbn [l_sp l_s l_h set_l_s] in Hsp, SW, MW, HW, SW3, HS, WW.
    pose proof (sw_wrap _ SW) as HWR. unfold reset_keep_s in HWR. cbn [i_wrap set_i_mode set_i_last set_i_havedict set_i_flags set_i_dmax set_i_head set_i_hold set_i_bits set_i_lencode set_i_distcode set_i_next set_i_sane set_i_back set_i_total] in HWR.
    clear SW MW HW SW3 HS WW.
    unfold zstrm_at, strm_rep.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (sp, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    match goal with H: HEAD <= i_mode s <= SYNC |- _ => rename H into HMD end.
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    forward. (* t'8 = strm->state *)
    forward. (* state = cast *)
    forward. (* t'2 = 0 *)
    forward. (* state->total *)
    forward. (* t'3 *)
    forward. (* strm->total_out *)
    forward. (* strm->total_in *)
    forward. (* strm->msg *)
    forward. (* strm->data_type *)
    forward. (* t'6 = state->wrap *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx (data_at ?sh ?t (?a1,(?a2,(?a3,(?a4,(?a5,(?a6,(?a7,(?a8,(?a9,(?a10,(?a11,(?a12,(?a13,?a14))))))))))))) ?p :: ?R)))) _ _ =>
      forward_if (PROPx P (LOCALx Q (SEPx (data_at sh t (a1,(a2,(a3,(a4,(a5,(a6,(a7,(a8,(a9,(a10,(a11,(a12,
        (lv (if i_wrap s =? 0 then zf_adler z else Z.land (i_wrap s) 1), a14))))))))))))) p :: R))))
    end.
    { forward. forward.
      assert (HW0: i_wrap s <> 0) by (match goal with H: i_wrap s <> 0 |- _ => exact H end).
      rewrite (proj2 (Z.eqb_neq _ _) HW0). rewrite wrap_and1 by lia. entailer!. }
    { forward.
      assert (HW0: i_wrap s = 0).
      { match goal with H: Int.repr (i_wrap s) = Int.zero |- _ =>
          apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; exact H end. }
      rewrite (proj2 (Z.eqb_eq _ _) HW0). entailer!. }
    forward. (* mode *)
    forward. (* last *)
    forward. (* havedict *)
    forward. (* flags *)
    forward. (* dmax *)
    forward. (* head *)
    forward. (* hold *)
    forward. (* bits *)
    assert_PROP (field_compatible t_state (DOT _strm) sp) by entailer!.
    forward. (* t'4 = state->codes *)
    forward. (* next *)
    forward. (* t'5 *)
    forward. (* distcode *)
    forward. (* lencode *)
    forward. (* sane *)
    forward. (* back *)
    forward. (* return *)
    assert (ZOK: zf_ok (reset_keep_z z s)) by (apply zf_ok_keep; [assumption | lia]).
    unfold reset_ret, reset_post, rs_live; rewrite if_false by auto.
    unfold reset_keep_f, fst3, snd3, thd3. cbn [fst snd]. rewrite Z.eqb_refl.
    unfold istream, zstrm_at, strm_rep, state_mem. cbn [l_sp l_winp l_s l_h l_headp set_l_s] in *.
    rewrite state_rep_v_eq, state_rep_v_keep.
    match goal with |- context [U_keep ?g ?a ?b ?c (reset_keep_s s) ?x1 ?x2 ?x3 ?x4] =>
      change (U_keep g a b c (reset_keep_s s) x1 x2 x3 x4) with (U_keep g a b c s vl vd vn vs) end.
    change (win_rep winp (reset_keep_s s)) with (win_rep winp s).
    revert ZOK. unfold reset_keep_z. rk_simpl. cbn [zf_ni zf_ai zf_no zf_ao zf_tin zf_tout zf_msg zf_dt zf_adler zf_res msg_val tref_val]. intro ZOK.
    rewrite codes_at0 by auto.
    entailer!.
Qed.

(* inflateReset empties the window, then calls inflateResetKeep *)
Definition wclear (s: istate) : istate := set_i_wdata (set_i_wnext (set_i_whave (set_i_wsize s 0) 0) 0) [].

Lemma win_clear: forall winp s, win_rep winp s |-- win_rep winp (wclear s).
Proof.
  intros. unfold win_rep, wclear. cbn [i_win i_wbits i_wdata set_i_wsize set_i_whave set_i_wnext set_i_wdata].
  destruct (i_win s); [ | apply derives_refl].
  sep_apply data_at_data_at_. unfold byte_vals. simpl map. rewrite app_nil_l, Zlength_nil, Z.sub_0_r.
  rewrite sepcon_comm. apply derives_refl.
Qed.

Lemma zfuncs_isptr: forall gv zcf, zcf = gv _zcfree -> zfuncs gv |-- !! isptr zcf.
Proof.
  intros. subst. unfold zfuncs, func_ptr'.
  eapply derives_trans; [apply sepcon_derives; apply andp_left1; apply func_ptr_isptr | ].
  rewrite sepcon_prop_prop. apply prop_derives. tauto.
Qed.

(* inflateReset's test of bit 3 of wrap *)
Lemma wrap_and8: forall w, 0 <= w <= 15 ->
  Int.and (Int.repr w) (Int.repr 8) = Int.repr (Z.land w 8) /\ 0 <= Z.land w 8 <= 8.
Proof.
  intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. split; [reflexivity | ].
  assert (C: w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/
            w = 10 \/ w = 11 \/ w = 12 \/ w = 13 \/ w = 14 \/ w = 15) by lia.
  destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]];
    cbv; intuition congruence.
Qed.

Lemma wrap_reset_full: forall s, i_wrap (reset_full_s s) = i_wrap s.
Proof. intros. unfold reset_full_s, reset_hdr_s. destruct (Z.land (i_wrap s) 8 =? 0); reflexivity. Qed.

Lemma U_rst3_hdr: forall gv sp headp winp s vl vd vn vs,
  U_rst3 gv sp headp winp (reset_hdr_s s) vl vd vn vs = U_rst3 gv sp headp winp s vl vd vn vs.
Proof. intros. unfold reset_hdr_s. destruct (Z.land (i_wrap s) 8 =? 0); reflexivity. Qed.

Lemma body_inflateReset {E: OracleKind}:
  semax_body Vprog_inflate Gp_reset f_inflateReset inflateReset_spec.
Proof.
  start_function.
  unfold rstream_opt.
  destruct (eq_dec strmp nullval) as [Hn | Hn].
  - subst strmp.
    forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
    { simpl. cancel. }
    forward_if; [forward; cancel | discriminate].
  - destruct r as [ | L vl vd vn vs | L rf vl vd vn vs].
    { unfold rstream, istream, zstrm_at, strm_rep. Intros.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (nullval, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), nullval, 0, false, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval); [contradiction | ].
    forward_if.
    { forward. unfold reset_ret, reset_post, rs_live, rstream_opt, rstream, istream, zstrm_at, strm_rep.
      rewrite !if_false by auto. entailer!. }
    { match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. } }
    2: {
    destruct L as [sp winp s h headp hsh xb nb cb].
    assert (HWR: 0 <= i_wrap s <= 15).
    { unfold reset_pre, rs_live in H. rewrite if_false in H by auto. specialize (H eq_refl).
      destruct H as (_ & SW & _). pose proof (sw_wrap _ SW) as X. cbn [thd3 snd l_s set_l_s] in X.
      unfold thd3, reset_f in X. cbn [snd l_s set_l_s] in X. rewrite wrap_reset_full in X. lia. }
    unfold rstream. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_v_rst3. Intros.
    unfold raw_strm.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (rf_ni rf, (rf_ai rf, (rf_tin rf, (rf_no rf, (rf_ao rf, (rf_tout rf, (nullval, (sp, (zca, (zcf,
      (nullval, (rf_dt rf, (rf_adler rf, rf_res rf))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    match goal with H: HEAD <= i_mode s <= SYNC |- _ => rename H into HMD end.
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    forward. (* t'8 = strm->state *)
    forward. (* state = cast *)
    forward. (* t'3 = state->wrap *)
    destruct (wrap_and8 (i_wrap s) HWR) as [EA RA].
    set (s1 := reset_hdr_s s). (* bit 3 of wrap, raw stream *)
    freeze [1;2;4;5;7;8;9;11;13] FR.
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx (?F0 :: ?A :: ?D :: _ :: _ :: _ :: ?N :: nil)))) _ _ =>
      forward_if (PROPx [] (LOCALx Q (SEPx [F0; A; D;
        field_at Ews t_state (DOT _wbits) (zv (i_wbits s1)) sp;
        field_at Ews t_state (DOT _window) (if i_win s1 then winp else nullval) sp;
        win_rep winp s1; N]))) end.
    { (* bit 3: the window freed, wbits = 0 *)
      match goal with Hc: Int.and _ _ <> Int.zero |- _ => rewrite EA in Hc; rename Hc into Hc8 end.
      assert (H8: Z.land (i_wrap s) 8 <> 0) by (intro X; rewrite X in Hc8; contradiction).
      assert (Es1: s1 = set_i_wbits (set_i_win s false) 0)
        by (subst s1; unfold reset_hdr_s; rewrite (proj2 (Z.eqb_neq _ _) H8); reflexivity).
      forward. (* t'4 = state->window *)
      { unfold win_rep; destruct (i_win s); entailer!. }
      destruct (i_win s) eqn:EW.
      - unfold win_rep at 1. rewrite EW. Intros.
        assert_PROP (isptr winp) by entailer!.
        match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx (?F0 :: ?A :: ?D :: ?G :: _ :: _ :: _ :: ?N :: nil)))) _ _ =>
          forward_if (PROPx [] (LOCALx Q (SEPx [F0; A; D; G;
            field_at Ews t_state (DOT _window) nullval sp; N]))) end.
        2: { exfalso. destruct winp; try contradiction. match goal with Hc: _ = nullval |- _ => inversion Hc end. }
        assert_PROP (isptr zcf).
        { go_lower. rewrite (add_andp (zfuncs gv) _ (zfuncs_isptr gv zcf Hzcf)). normalize; try (apply prop_right; auto). }
        forward. forward. forward.
        unfold zfuncs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.
        forward_call (tarray tuchar (2 ^ i_wbits s), winp, gv, nullval).
        { rewrite if_false by (destruct winp; try contradiction; discriminate).
          sep_apply (data_at_data_at_ Ews (tarray tuchar (2 ^ i_wbits s))). cancel. }
        forward. unfold zfuncs. rewrite <- Hzcf, <- Hzca. entailer!.
        forward.
        rewrite Es1. unfold win_rep. cbn [i_win i_wbits set_i_win set_i_wbits]. entailer!.
      - match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
          forward_if (PROPx [] (LOCALx Q (SEPx R))) end.
        { discriminate. }
        { forward. entailer!. }
        forward.
        rewrite Es1. unfold win_rep. rewrite EW. cbn [i_win i_wbits set_i_win set_i_wbits]. entailer!. }
    { (* bit 3 clear: nothing *)
      match goal with Hc: Int.and _ _ = Int.zero |- _ => rewrite EA in Hc; rename Hc into Hc8 end.
      assert (H8: Z.land (i_wrap s) 8 = 0).
      { apply (f_equal Int.unsigned) in Hc8. rewrite Int.unsigned_repr in Hc8 by rep_lia. exact Hc8. }
      assert (Es1: s1 = s) by (subst s1; unfold reset_hdr_s; rewrite (proj2 (Z.eqb_eq _ _) H8); reflexivity).
      forward. rewrite Es1. entailer!. }
    thaw FR.
    assert (Ms1: i_mode s1 = i_mode s /\ i_wrap s1 = i_wrap s /\ i_wsize s1 = i_wsize s /\
                 i_whave s1 = i_whave s /\ i_wnext s1 = i_wnext s /\ 0 <= i_wbits s1 <= 23)
      by (subst s1; unfold reset_hdr_s; destruct (_ =? 0); cbn; repeat split; auto; lia).
    destruct Ms1 as (M1 & M2 & M3 & M4 & M5 & M6).
    forward. (* wsize *)
    forward. (* whave *)
    forward. (* wnext *)
    set (L' := Live sp winp (wclear s1) h headp hsh xb nb cb).
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      apply semax_pre with (PROPx P (LOCALx Q (SEPx [rstream_opt gv shs strmp z (RRaw L' rf vl vd vn vs); mem_mgr gv; zfuncs gv]))) end.
    { unfold rstream_opt; rewrite if_false by auto.
      unfold rstream, raw_strm, L'. cbn [l_sp l_winp l_s l_h l_headp].
      rewrite state_rep_v_rst3.
      change (U_rst3 gv sp headp winp (wclear s1) vl vd vn vs) with (U_rst3 gv sp headp winp (reset_hdr_s s) vl vd vn vs).
      rewrite U_rst3_hdr.
      sep_apply (win_clear winp s1).
      rewrite <- Hzca, <- Hzcf. unfold wclear.
      cbn [i_mode i_wrap i_wbits i_win i_wsize i_whave i_wnext set_i_wsize set_i_whave set_i_wnext set_i_wdata].
      rewrite M1, M2. entailer!. }
    forward_call (gv, shs, strmp, z, RRaw L' rf vl vd vn vs).
    { unfold reset_pre, rs_live in H |- *. rewrite if_false in H |- * by auto. exact H. }
    forward.
    unfold reset_ret, reset_post, rs_live. rewrite !if_false by auto. subst L' s1.
    unfold reset_keep_f, reset_f, fst3, snd3, thd3, reset_full_s, reset_s, wclear, set_l_s.
    cbn [fst snd l_s l_sp l_winp l_h l_headp l_hsh l_xb l_nb l_cb]. rewrite Z.eqb_refl. entailer!.
    (* RRAW-END *) }
    destruct L as [sp winp s h headp hsh xb nb cb].
    assert (HWR: 0 <= i_wrap s <= 15).
    { unfold reset_pre, rs_live in H. rewrite if_false in H by auto. specialize (H eq_refl).
      destruct H as (_ & SW & _). pose proof (sw_wrap _ SW) as X. cbn [thd3 snd l_s set_l_s] in X.
      unfold thd3, reset_f in X. cbn [snd l_s set_l_s] in X. rewrite wrap_reset_full in X. lia. }
    unfold rstream. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_v_rst3. Intros.
    unfold zstrm_at, strm_rep.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (sp, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    match goal with H: HEAD <= i_mode s <= SYNC |- _ => rename H into HMD end.
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    forward. (* t'8 = strm->state *)
    forward. (* state = cast *)
    forward. (* t'3 = state->wrap *)
    destruct (wrap_and8 (i_wrap s) HWR) as [EA RA].
    set (s1 := reset_hdr_s s). (* bit 3 of wrap, live stream *)
    freeze [1;2;4;5;7;8;9;11;13] FR.
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx (?F0 :: ?A :: ?D :: _ :: _ :: _ :: ?N :: nil)))) _ _ =>
      forward_if (PROPx [] (LOCALx Q (SEPx [F0; A; D;
        field_at Ews t_state (DOT _wbits) (zv (i_wbits s1)) sp;
        field_at Ews t_state (DOT _window) (if i_win s1 then winp else nullval) sp;
        win_rep winp s1; N]))) end.
    { (* bit 3: the window freed, wbits = 0 *)
      match goal with Hc: Int.and _ _ <> Int.zero |- _ => rewrite EA in Hc; rename Hc into Hc8 end.
      assert (H8: Z.land (i_wrap s) 8 <> 0) by (intro X; rewrite X in Hc8; contradiction).
      assert (Es1: s1 = set_i_wbits (set_i_win s false) 0)
        by (subst s1; unfold reset_hdr_s; rewrite (proj2 (Z.eqb_neq _ _) H8); reflexivity).
      forward. (* t'4 = state->window *)
      { unfold win_rep; destruct (i_win s); entailer!. }
      destruct (i_win s) eqn:EW.
      - unfold win_rep at 1. rewrite EW. Intros.
        assert_PROP (isptr winp) by entailer!.
        match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx (?F0 :: ?A :: ?D :: ?G :: _ :: _ :: _ :: ?N :: nil)))) _ _ =>
          forward_if (PROPx [] (LOCALx Q (SEPx [F0; A; D; G;
            field_at Ews t_state (DOT _window) nullval sp; N]))) end.
        2: { exfalso. destruct winp; try contradiction. match goal with Hc: _ = nullval |- _ => inversion Hc end. }
        assert_PROP (isptr zcf).
        { go_lower. rewrite (add_andp (zfuncs gv) _ (zfuncs_isptr gv zcf Hzcf)). normalize; try (apply prop_right; auto). }
        forward. forward. forward.
        unfold zfuncs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.
        forward_call (tarray tuchar (2 ^ i_wbits s), winp, gv, nullval).
        { rewrite if_false by (destruct winp; try contradiction; discriminate).
          sep_apply (data_at_data_at_ Ews (tarray tuchar (2 ^ i_wbits s))). cancel. }
        forward. unfold zfuncs. rewrite <- Hzcf, <- Hzca. entailer!.
        forward.
        rewrite Es1. unfold win_rep. cbn [i_win i_wbits set_i_win set_i_wbits]. entailer!.
      - match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
          forward_if (PROPx [] (LOCALx Q (SEPx R))) end.
        { discriminate. }
        { forward. entailer!. }
        forward.
        rewrite Es1. unfold win_rep. rewrite EW. cbn [i_win i_wbits set_i_win set_i_wbits]. entailer!. }
    { (* bit 3 clear: nothing *)
      match goal with Hc: Int.and _ _ = Int.zero |- _ => rewrite EA in Hc; rename Hc into Hc8 end.
      assert (H8: Z.land (i_wrap s) 8 = 0).
      { apply (f_equal Int.unsigned) in Hc8. rewrite Int.unsigned_repr in Hc8 by rep_lia. exact Hc8. }
      assert (Es1: s1 = s) by (subst s1; unfold reset_hdr_s; rewrite (proj2 (Z.eqb_eq _ _) H8); reflexivity).
      forward. rewrite Es1. entailer!. }
    thaw FR.
    assert (Ms1: i_mode s1 = i_mode s /\ i_wrap s1 = i_wrap s /\ i_wsize s1 = i_wsize s /\
                 i_whave s1 = i_whave s /\ i_wnext s1 = i_wnext s /\ 0 <= i_wbits s1 <= 23)
      by (subst s1; unfold reset_hdr_s; destruct (_ =? 0); cbn; repeat split; auto; lia).
    destruct Ms1 as (M1 & M2 & M3 & M4 & M5 & M6).
    forward. (* wsize *)
    forward. (* whave *)
    forward. (* wnext *)
    set (L' := Live sp winp (wclear s1) h headp hsh xb nb cb).
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      apply semax_pre with (PROPx P (LOCALx Q (SEPx [rstream_opt gv shs strmp z (RLive L' vl vd vn vs); mem_mgr gv; zfuncs gv]))) end.
    { unfold rstream_opt; rewrite if_false by auto.
      unfold rstream, zstrm_at, strm_rep, L'. cbn [l_sp l_winp l_s l_h l_headp].
      rewrite state_rep_v_rst3.
      change (U_rst3 gv sp headp winp (wclear s1) vl vd vn vs) with (U_rst3 gv sp headp winp (reset_hdr_s s) vl vd vn vs).
      rewrite U_rst3_hdr.
      sep_apply (win_clear winp s1).
      rewrite <- Hzca, <- Hzcf. unfold wclear.
      cbn [i_mode i_wrap i_wbits i_win i_wsize i_whave i_wnext set_i_wsize set_i_whave set_i_wnext set_i_wdata].
      rewrite M1, M2. entailer!. }
    forward_call (gv, shs, strmp, z, RLive L' vl vd vn vs).
    { unfold reset_pre, rs_live in H |- *. rewrite if_false in H |- * by auto. exact H. }
    forward.
    unfold reset_ret, reset_post, rs_live. rewrite !if_false by auto. subst L' s1.
    unfold reset_keep_f, reset_f, fst3, snd3, thd3, reset_full_s, reset_s, wclear, set_l_s.
    cbn [fst snd l_s l_sp l_winp l_h l_headp l_hsh l_xb l_nb l_cb]. rewrite Z.eqb_refl. entailer!.
Qed.

(* inflateReset2's windowBits after the sign test: the wrap and the window bits it computes *)
Definition wrap0 (w: Z) : Z := if w <? 0 then 0 else Z.shiftr w 4 + 5.
Definition wb0 (w: Z) : Z := if w <? 0 then - w else if w <? 48 then Z.land w 15 else w.
Definition wb_bad (w: Z) : bool := negb (orb (wb0 w =? 0) (andb (8 <=? wb0 w) (wb0 w <=? 15))).

Lemma reset2_wb_eq: forall w, -15 <= w ->
  reset2_wb w = if wb_bad w then None else Some (wrap0 w, wb0 w).
Proof.
  intros w Hw. unfold reset2_wb, wb_bad, wrap0, wb0.
  destruct (w <? 0) eqn:E.
  - rewrite (proj2 (Z.ltb_ge w (-15)) Hw). apply Z.ltb_lt in E.
    rewrite (proj2 (Z.eqb_neq (-w) 0)) by lia. simpl. destruct (andb (8 <=? - w) (- w <=? 15)); reflexivity.
  - destruct ((if w <? 48 then Z.land w 15 else w) =? 0 ); simpl; [reflexivity | ].
    destruct (andb (8 <=? (if w <? 48 then Z.land w 15 else w)) ((if w <? 48 then Z.land w 15 else w) <=? 15)); reflexivity.
Qed.

Lemma shr4_eq: forall w, 0 <= w <= Int.max_signed ->
  Int.shr (Int.repr w) (Int.repr 4) = Int.repr (Z.shiftr w 4) /\ 0 <= Z.shiftr w 4 < 134217728.
Proof.
  intros. unfold Int.shr. rewrite Int.signed_repr, (Int.unsigned_repr 4) by rep_lia.
  split; [reflexivity | ]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; rep_lia].
Qed.

Lemma and15_eq: forall w, 0 <= w <= Int.max_signed ->
  Int.and (Int.repr w) (Int.repr 15) = Int.repr (Z.land w 15) /\ 0 <= Z.land w 15 <= 15.
Proof.
  intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. split; [reflexivity | ].
  pose proof (Z.land_ones w 4 ltac:(lia)) as E1. change (Z.ones 4) with 15 in E1. rewrite E1.
  change (2 ^ 4) with 16. pose proof (Z.mod_pos_bound w 16). lia.
Qed.

Lemma wb0_range: forall w, -15 <= w <= Int.max_signed ->
  0 <= wb0 w <= Int.max_signed /\ (w < 48 -> 0 <= wb0 w <= 15).
Proof.
  intros. unfold wb0. destruct (w <? 0) eqn:E1; [apply Z.ltb_lt in E1; rep_lia | apply Z.ltb_ge in E1].
  destruct (w <? 48) eqn:E2; [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2; rep_lia].
  pose proof (proj2 (and15_eq w ltac:(rep_lia))). rep_lia.
Qed.

Lemma wb_bad_spec: forall w, wb_bad w = true <-> (wb0 w <> 0 /\ (wb0 w < 8 \/ 15 < wb0 w)).
Proof.
  intros. unfold wb_bad.
  destruct (Z.eqb_spec (wb0 w) 0); destruct (Z.leb_spec 8 (wb0 w)); destruct (Z.leb_spec (wb0 w) 15); simpl;
  split; intro HH; first [reflexivity | discriminate | lia | (exfalso; lia)].
Qed.

Lemma wb_ok_facts: forall w, -15 <= w <= Int.max_signed -> wb_bad w = false ->
  (wb0 w = 0 \/ 8 <= wb0 w <= 15) /\ w < 48 /\ 0 <= wrap0 w <= 7.
Proof.
  intros w Hw EB. assert (V: wb0 w = 0 \/ 8 <= wb0 w <= 15).
  { destruct (wb_bad w) eqn:E; [discriminate | ]. unfold wb_bad in E.
    destruct (Z.eqb_spec (wb0 w) 0); destruct (Z.leb_spec 8 (wb0 w)); destruct (Z.leb_spec (wb0 w) 15);
      simpl in E; try discriminate; lia. }
  split; [exact V | ].
  assert (W48: w < 48) by (unfold wb0 in V; destruct (w <? 0) eqn:E1; [apply Z.ltb_lt in E1; lia | ];
    destruct (w <? 48) eqn:E2; [apply Z.ltb_lt in E2; lia | apply Z.ltb_ge in E2; lia]).
  split; [exact W48 | ]. unfold wrap0. destruct (w <? 0) eqn:E1; [lia | apply Z.ltb_ge in E1].
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  assert (0 <= w / 16 < 3) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
Qed.

(* the window after inflateReset2's test (freed when its size changes) *)
Definition wfree (wb: Z) (s: istate) : istate :=
  if andb (i_win s) (negb (i_wbits s =? wb)) then set_i_win s false else s.

Lemma wfree_win: forall wb s, i_win (wfree wb s) = true -> i_wbits (wfree wb s) = wb.
Proof.
  intros. unfold wfree in *. destruct (i_win s) eqn:EW; simpl in *; [ | rewrite EW in H; discriminate].
  destruct (Z.eqb_spec (i_wbits s) wb); simpl in *; auto. discriminate.
Qed.

Lemma U_rst2_wfree: forall gv sp headp winp s wr wb vl vd vn vs,
  U_rst2 gv sp headp winp (set_i_wbits (set_i_wrap (wfree wb s) wr) wb) vl vd vn vs =
  U_rst2 gv sp headp winp s vl vd vn vs.
Proof. intros. unfold wfree. destruct (andb (i_win s) (negb (i_wbits s =? wb))); reflexivity. Qed.

Lemma mode_wfree: forall wb s, i_mode (wfree wb s) = i_mode s.
Proof. intros. unfold wfree. destruct (andb (i_win s) (negb (i_wbits s =? wb))); reflexivity. Qed.

Lemma win_rep_set_wbits: forall winp s wr wb, (i_win s = true -> i_wbits s = wb) ->
  win_rep winp s |-- win_rep winp (set_i_wbits (set_i_wrap s wr) wb).
Proof.
  intros. unfold win_rep. cbn [i_win i_wbits i_wdata set_i_wbits set_i_wrap].
  destruct (i_win s) eqn:E; [rewrite H by auto | ]; apply derives_refl.
Qed.


(* the error return of inflateReset2 (reset2_wb w = None): the stream unchanged *)
Ltac fin_err EN :=
  unfold reset_ret, reset_post, rs_live; rewrite !if_false by auto;
  unfold reset2_f, fst3; rewrite EN; cbn [fst snd];
  replace (Z_STREAM_ERROR =? Z_OK) with false by reflexivity;
  unfold rstream_opt, rstream; rewrite if_false by auto; cbn [l_sp l_winp l_s l_h l_headp];
  rewrite state_rep_v_rst2; unfold zstrm_at, strm_rep, raw_strm; entailer!.

Ltac fix_neg15 := try change (Int.signed (Int.neg (Int.repr 15))) with (-15) in *;
  try change (Int.signed (Int.repr (- (15)))) with (-15) in *.

(* inflateReset2's wrap |= 8 (patch F8) *)
Lemma or8_eq: forall x, 0 <= x <= 7 -> Int.or (Int.repr x) (Int.repr 8) = Int.repr (Z.lor x 8).
Proof. intros. unfold Int.or. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma body_inflateReset2 {E: OracleKind}:
  semax_body Vprog_inflate Gp_reset2 f_inflateReset2 inflateReset2_spec.
Proof.
  start_function.
  unfold rstream_opt.
  destruct (eq_dec strmp nullval) as [Hn | Hn].
  - subst strmp.
    forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
    { simpl. cancel. }
    forward_if; [forward; cancel | discriminate].
  - destruct r as [ | L vl vd vn vs | L rf vl vd vn vs].
    { unfold rstream, istream, zstrm_at, strm_rep. Intros.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (nullval, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), nullval, 0, false, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval); [contradiction | ].
    forward_if.
    { forward. unfold reset_ret, reset_post, rs_live, rstream_opt, rstream, istream, zstrm_at, strm_rep.
      rewrite !if_false by auto. entailer!. }
    { match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. } }
    2: {
    destruct L as [sp winp s h headp hsh xb nb cb].
    unfold rstream. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_v_rst2. Intros.
    unfold raw_strm.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (rf_ni rf, (rf_ai rf, (rf_tin rf, (rf_no rf, (rf_ao rf, (rf_tout rf, (nullval, (sp, (zca, (zcf,
      (nullval, (rf_dt rf, (rf_adler rf, rf_res rf))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    match goal with H: HEAD <= i_mode s <= SYNC |- _ => rename H into HMD end.
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    forward. (* t'10 = strm->state *)
    forward. (* state = cast *)
    destruct (Z_lt_dec w (-15)) as [Hlt | Hge].
    { (* windowBits < -15 *)
      assert (EN: reset2_wb w = None) by (unfold reset2_wb; rewrite !(proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
      forward_if False.
      { forward_if False; [ | fix_neg15; exfalso; lia].
        forward. fin_err EN. }
      { exfalso; lia. } }
    match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
      forward_if (PROP () LOCAL (temp _state sp; temp _strm strmp; gvars gv;
        temp _wrap (Vint (Int.repr (wrap0 w))); temp _windowBits (Vint (Int.repr (wb0 w)))) (SEPx R)) end.
    { forward_if (-15 <= w); [fix_neg15; exfalso; lia | forward; entailer! | ].
      Intros. forward. forward.
      { entailer!. rewrite Int.signed_zero. rep_lia. }
      unfold wrap0, wb0. rewrite (proj2 (Z.ltb_lt w 0)) by lia. rewrite Int.neg_repr. entailer!. }
    { destruct (shr4_eq w ltac:(rep_lia)) as [ES RS].
      forward.
      { entailer!. rewrite ES, Int.signed_repr by rep_lia. rep_lia. }
      rewrite ES, add_repr.
      forward_if.
      - forward. destruct (and15_eq w ltac:(rep_lia)) as [EA RA]. rewrite EA.
        unfold wrap0, wb0. rewrite (proj2 (Z.ltb_ge w 0)), (proj2 (Z.ltb_lt w 48)) by lia. entailer!.
      - forward. unfold wrap0, wb0. rewrite (proj2 (Z.ltb_ge w 0)), (proj2 (Z.ltb_ge w 48)) by lia. entailer!. }
    destruct (wb0_range w ltac:(lia)) as [RW RW48].
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'2 (Vint (Int.repr (if wb_bad w then 1 else 0))) :: Q) (SEPx R))) end.
    { forward_if.
      - forward. entailer!.
        rewrite (proj2 (wb_bad_spec w)) by lia. reflexivity.
      - forward. forward. entailer!.
        destruct (zlt 15 (wb0 w)); [rewrite (proj2 (wb_bad_spec w)) by lia; reflexivity | ].
        destruct (wb_bad w) eqn:EB; [apply wb_bad_spec in EB; lia | reflexivity]. }
    { forward. entailer!.
      assert (wb0 w = 0).
      { match goal with H: Int.repr (wb0 w) = Int.zero |- _ =>
          apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; exact H end. }
      destruct (wb_bad w) eqn:EB; [apply wb_bad_spec in EB; lia | reflexivity]. }
    destruct (wb_bad w) eqn:EB.
    { assert (EN: reset2_wb w = None) by (rewrite reset2_wb_eq by lia; rewrite EB; reflexivity).
      forward_if False.
      { forward. fin_err EN. }
      { match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. } }
    assert (ES: reset2_wb w = Some (wrap0 w, wb0 w)) by (rewrite reset2_wb_eq by lia; rewrite EB; reflexivity).
    destruct (wb_ok_facts w ltac:(rep_lia) EB) as (WBV & W48 & WRP).
    forward_if True.
    { match goal with H: Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end. }
    { forward. entailer!. }
    Intros.
    forward. (* t'8 = state->window (raw stream) *)
    { unfold win_rep; destruct (i_win s); entailer!. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'3 (Vint (Int.repr (if andb (i_win s) (negb (i_wbits s =? wb0 w)) then 1 else 0))) :: Q) (SEPx R))) end.
    { unfold win_rep; destruct (i_win s); entailer!. }
    { destruct (i_win s) eqn:EW; [ | contradiction].
      forward. forward. entailer!.
      simpl andb. destruct (Z.eqb_spec (i_wbits s) (wb0 w)); destruct (zeq (i_wbits s) (wb0 w)); try lia; reflexivity. }
    { destruct (i_win s) eqn:EW.
      - assert_PROP (isptr winp) by (unfold win_rep; rewrite EW; entailer!). subst; contradiction.
      - forward. entailer!. }
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: ?Q) (SEPx (?A :: ?B :: ?C :: ?D :: ?E2 :: ?F :: ?G :: _ :: ?I :: _ :: ?K :: ?L :: nil)))) _ _ =>
      forward_if (PROPx [] (LOCALx Q (SEPx [A; B; C; D; E2; F; G;
        field_at Ews t_state (DOT _window) (if i_win (wfree (wb0 w) s) then winp else nullval) sp;
        I; win_rep winp (wfree (wb0 w) s); K; L]))) end.
    { (* free the window *)
      destruct (i_win s) eqn:EW;
        [ | match goal with H: (if _ then 1 else 0) <> 0 |- _ => exfalso; apply H; reflexivity end].
      destruct (Z.eqb_spec (i_wbits s) (wb0 w));
        [match goal with H: (if _ then 1 else 0) <> 0 |- _ => exfalso; apply H; reflexivity end | ].
      unfold win_rep at 1. rewrite EW. Intros.
      assert_PROP (isptr zcf).
      { go_lower. rewrite (add_andp (zfuncs gv) _ (zfuncs_isptr gv zcf Hzcf)). normalize; try (apply prop_right; auto). }
      forward. forward. forward.
      assert_PROP (isptr winp) by entailer!.
      unfold zfuncs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.
      forward_call (tarray tuchar (2 ^ i_wbits s), winp, gv, nullval).
      { rewrite if_false by (destruct winp; try contradiction; discriminate).
        sep_apply (data_at_data_at_ Ews (tarray tuchar (2 ^ i_wbits s))). cancel. }
      forward.
      unfold wfree. rewrite EW. destruct (Z.eqb_spec (i_wbits s) (wb0 w)); [lia | ].
      unfold win_rep, zfuncs. cbn [i_win set_i_win andb negb]. rewrite <- Hzcf, <- Hzca. entailer!. }
    { forward. unfold wfree. destruct (i_win s) eqn:EW; cbn [andb].
      - destruct (Z.eqb_spec (i_wbits s) (wb0 w)).
        + cbn [negb]. rewrite EW. entailer!.
        + match goal with H: Int.repr (if _ then 1 else 0) = Int.zero |- _ => simpl in H; discriminate end.
      - rewrite EW. entailer!. }
    (* windowBits 0 (the size of the header): bit 3 of wrap *)
    match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
      forward_if (PROP () LOCAL (temp _state sp; temp _strm strmp; gvars gv;
        temp _wrap (Vint (Int.repr (reset2_wrap (wrap0 w) (wb0 w)))); temp _windowBits (Vint (Int.repr (wb0 w))))
        (SEPx R)) end.
    { forward.
      assert (E0: wb0 w = 0).
      { first [assumption | match goal with H: Int.repr (wb0 w) = Int.repr 0 |- _ =>
          apply (f_equal Int.unsigned) in H; rewrite !Int.unsigned_repr in H by rep_lia; exact H end]. }
      unfold reset2_wrap. rewrite E0, Z.eqb_refl. rewrite or8_eq by lia. entailer!. }
    { forward.
      assert (E0: wb0 w <> 0) by (first [assumption | intro X; rewrite X in *; contradiction]).
      unfold reset2_wrap. rewrite (proj2 (Z.eqb_neq _ _) E0). entailer!. }
    forward. (* state->wrap = wrap *)
    forward. (* state->wbits = windowBits *)
    set (s2 := set_i_wbits (set_i_wrap (wfree (wb0 w) s) (reset2_wrap (wrap0 w) (wb0 w))) (wb0 w)).
    set (L1 := Live sp winp s2 h headp hsh xb nb cb).
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      apply semax_pre with (PROPx P (LOCALx Q (SEPx [rstream_opt gv shs strmp z (RRaw L1 rf vl vd vn vs); mem_mgr gv; zfuncs gv]))) end.
    { unfold rstream_opt; rewrite if_false by auto.
      unfold rstream, raw_strm, L1. cbn [l_sp l_winp l_s l_h l_headp].
      rewrite state_rep_v_rst2. subst s2. rewrite U_rst2_wfree.
      sep_apply (win_rep_set_wbits winp (wfree (wb0 w) s) (reset2_wrap (wrap0 w) (wb0 w)) (wb0 w) (wfree_win (wb0 w) s)).
      cbn [i_mode i_wrap i_wbits i_win set_i_wbits set_i_wrap]. rewrite mode_wfree.
      rewrite <- Hzca, <- Hzcf. entailer!. }
    forward_call (gv, shs, strmp, z, RRaw L1 rf vl vd vn vs).
    { unfold reset_pre, rs_live in H0 |- *. rewrite if_false in H0 |- * by auto.
      unfold reset2_f in H0. rewrite ES in H0. exact H0. }
    forward.
    unfold reset_ret, reset_post, rs_live. rewrite !if_false by auto. unfold reset2_f. rewrite ES.
    subst L1 s2. unfold reset_f, fst3, snd3, thd3, reset2_s, wfree, set_l_s.
    cbn [fst snd l_s l_sp l_winp l_h l_headp l_hsh l_xb l_nb l_cb]. rewrite Z.eqb_refl. entailer!.
    (* RRAW-END *) }
    destruct L as [sp winp s h headp hsh xb nb cb].
    unfold rstream. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_v_rst2. Intros.
    unfold zstrm_at, strm_rep.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (sp, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    match goal with H: HEAD <= i_mode s <= SYNC |- _ => rename H into HMD end.
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    forward. (* t'10 = strm->state *)
    forward. (* state = cast *)
    destruct (Z_lt_dec w (-15)) as [Hlt | Hge].
    { (* windowBits < -15 *)
      assert (EN: reset2_wb w = None) by (unfold reset2_wb; rewrite !(proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
      forward_if False.
      { forward_if False; [ | fix_neg15; exfalso; lia].
        forward. fin_err EN. }
      { exfalso; lia. } }
    match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
      forward_if (PROP () LOCAL (temp _state sp; temp _strm strmp; gvars gv;
        temp _wrap (Vint (Int.repr (wrap0 w))); temp _windowBits (Vint (Int.repr (wb0 w)))) (SEPx R)) end.
    { forward_if (-15 <= w); [fix_neg15; exfalso; lia | forward; entailer! | ].
      Intros. forward. forward.
      { entailer!. rewrite Int.signed_zero. rep_lia. }
      unfold wrap0, wb0. rewrite (proj2 (Z.ltb_lt w 0)) by lia. rewrite Int.neg_repr. entailer!. }
    { destruct (shr4_eq w ltac:(rep_lia)) as [ES RS].
      forward.
      { entailer!. rewrite ES, Int.signed_repr by rep_lia. rep_lia. }
      rewrite ES, add_repr.
      forward_if.
      - forward. destruct (and15_eq w ltac:(rep_lia)) as [EA RA]. rewrite EA.
        unfold wrap0, wb0. rewrite (proj2 (Z.ltb_ge w 0)), (proj2 (Z.ltb_lt w 48)) by lia. entailer!.
      - forward. unfold wrap0, wb0. rewrite (proj2 (Z.ltb_ge w 0)), (proj2 (Z.ltb_ge w 48)) by lia. entailer!. }
    destruct (wb0_range w ltac:(lia)) as [RW RW48].
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'2 (Vint (Int.repr (if wb_bad w then 1 else 0))) :: Q) (SEPx R))) end.
    { forward_if.
      - forward. entailer!.
        rewrite (proj2 (wb_bad_spec w)) by lia. reflexivity.
      - forward. forward. entailer!.
        destruct (zlt 15 (wb0 w)); [rewrite (proj2 (wb_bad_spec w)) by lia; reflexivity | ].
        destruct (wb_bad w) eqn:EB; [apply wb_bad_spec in EB; lia | reflexivity]. }
    { forward. entailer!.
      assert (wb0 w = 0).
      { match goal with H: Int.repr (wb0 w) = Int.zero |- _ =>
          apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; exact H end. }
      destruct (wb_bad w) eqn:EB; [apply wb_bad_spec in EB; lia | reflexivity]. }
    destruct (wb_bad w) eqn:EB.
    { assert (EN: reset2_wb w = None) by (rewrite reset2_wb_eq by lia; rewrite EB; reflexivity).
      forward_if False.
      { forward. fin_err EN. }
      { match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. } }
    assert (ES: reset2_wb w = Some (wrap0 w, wb0 w)) by (rewrite reset2_wb_eq by lia; rewrite EB; reflexivity).
    destruct (wb_ok_facts w ltac:(rep_lia) EB) as (WBV & W48 & WRP).
    forward_if True.
    { match goal with H: Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end. }
    { forward. entailer!. }
    Intros.
    forward. (* t'8 = state->window (live stream) *)
    { unfold win_rep; destruct (i_win s); entailer!. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'3 (Vint (Int.repr (if andb (i_win s) (negb (i_wbits s =? wb0 w)) then 1 else 0))) :: Q) (SEPx R))) end.
    { unfold win_rep; destruct (i_win s); entailer!. }
    { destruct (i_win s) eqn:EW; [ | contradiction].
      forward. forward. entailer!.
      simpl andb. destruct (Z.eqb_spec (i_wbits s) (wb0 w)); destruct (zeq (i_wbits s) (wb0 w)); try lia; reflexivity. }
    { destruct (i_win s) eqn:EW.
      - assert_PROP (isptr winp) by (unfold win_rep; rewrite EW; entailer!). subst; contradiction.
      - forward. entailer!. }
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: ?Q) (SEPx (?A :: ?B :: ?C :: ?D :: ?E2 :: ?F :: ?G :: _ :: ?I :: _ :: ?K :: ?L :: nil)))) _ _ =>
      forward_if (PROPx [] (LOCALx Q (SEPx [A; B; C; D; E2; F; G;
        field_at Ews t_state (DOT _window) (if i_win (wfree (wb0 w) s) then winp else nullval) sp;
        I; win_rep winp (wfree (wb0 w) s); K; L]))) end.
    { (* free the window *)
      destruct (i_win s) eqn:EW;
        [ | match goal with H: (if _ then 1 else 0) <> 0 |- _ => exfalso; apply H; reflexivity end].
      destruct (Z.eqb_spec (i_wbits s) (wb0 w));
        [match goal with H: (if _ then 1 else 0) <> 0 |- _ => exfalso; apply H; reflexivity end | ].
      unfold win_rep at 1. rewrite EW. Intros.
      assert_PROP (isptr zcf).
      { go_lower. rewrite (add_andp (zfuncs gv) _ (zfuncs_isptr gv zcf Hzcf)). normalize; try (apply prop_right; auto). }
      forward. forward. forward.
      assert_PROP (isptr winp) by entailer!.
      unfold zfuncs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.
      forward_call (tarray tuchar (2 ^ i_wbits s), winp, gv, nullval).
      { rewrite if_false by (destruct winp; try contradiction; discriminate).
        sep_apply (data_at_data_at_ Ews (tarray tuchar (2 ^ i_wbits s))). cancel. }
      forward.
      unfold wfree. rewrite EW. destruct (Z.eqb_spec (i_wbits s) (wb0 w)); [lia | ].
      unfold win_rep, zfuncs. cbn [i_win set_i_win andb negb]. rewrite <- Hzcf, <- Hzca. entailer!. }
    { forward. unfold wfree. destruct (i_win s) eqn:EW; cbn [andb].
      - destruct (Z.eqb_spec (i_wbits s) (wb0 w)).
        + cbn [negb]. rewrite EW. entailer!.
        + match goal with H: Int.repr (if _ then 1 else 0) = Int.zero |- _ => simpl in H; discriminate end.
      - rewrite EW. entailer!. }
    (* windowBits 0 (the size of the header): bit 3 of wrap *)
    match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
      forward_if (PROP () LOCAL (temp _state sp; temp _strm strmp; gvars gv;
        temp _wrap (Vint (Int.repr (reset2_wrap (wrap0 w) (wb0 w)))); temp _windowBits (Vint (Int.repr (wb0 w))))
        (SEPx R)) end.
    { forward.
      assert (E0: wb0 w = 0).
      { first [assumption | match goal with H: Int.repr (wb0 w) = Int.repr 0 |- _ =>
          apply (f_equal Int.unsigned) in H; rewrite !Int.unsigned_repr in H by rep_lia; exact H end]. }
      unfold reset2_wrap. rewrite E0, Z.eqb_refl. rewrite or8_eq by lia. entailer!. }
    { forward.
      assert (E0: wb0 w <> 0) by (first [assumption | intro X; rewrite X in *; contradiction]).
      unfold reset2_wrap. rewrite (proj2 (Z.eqb_neq _ _) E0). entailer!. }
    forward. (* state->wrap = wrap *)
    forward. (* state->wbits = windowBits *)
    set (s2 := set_i_wbits (set_i_wrap (wfree (wb0 w) s) (reset2_wrap (wrap0 w) (wb0 w))) (wb0 w)).
    set (L1 := Live sp winp s2 h headp hsh xb nb cb).
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      apply semax_pre with (PROPx P (LOCALx Q (SEPx [rstream_opt gv shs strmp z (RLive L1 vl vd vn vs); mem_mgr gv; zfuncs gv]))) end.
    { unfold rstream_opt; rewrite if_false by auto.
      unfold rstream, zstrm_at, strm_rep, L1. cbn [l_sp l_winp l_s l_h l_headp].
      rewrite state_rep_v_rst2. subst s2. rewrite U_rst2_wfree.
      sep_apply (win_rep_set_wbits winp (wfree (wb0 w) s) (reset2_wrap (wrap0 w) (wb0 w)) (wb0 w) (wfree_win (wb0 w) s)).
      cbn [i_mode i_wrap i_wbits i_win set_i_wbits set_i_wrap]. rewrite mode_wfree.
      rewrite <- Hzca, <- Hzcf. entailer!. }
    forward_call (gv, shs, strmp, z, RLive L1 vl vd vn vs).
    { unfold reset_pre, rs_live in H0 |- *. rewrite if_false in H0 |- * by auto.
      unfold reset2_f in H0. rewrite ES in H0. exact H0. }
    forward.
    unfold reset_ret, reset_post, rs_live. rewrite !if_false by auto. unfold reset2_f. rewrite ES.
    subst L1 s2. unfold reset_f, fst3, snd3, thd3, reset2_s, wfree, set_l_s.
    cbn [fst snd l_s l_sp l_winp l_h l_headp l_hsh l_xb l_nb l_cb]. rewrite Z.eqb_refl. entailer!.
Qed.

Lemma api5_reset : api_reset_stmt.
Proof.
  split; [exact live_reset | ]. intros Espec.
  split; [apply body_inflateResetKeep | ].
  split; [apply body_inflateReset | ].
  split; [apply body_inflateReset2 | apply body5_inflateEnd].
Qed.
