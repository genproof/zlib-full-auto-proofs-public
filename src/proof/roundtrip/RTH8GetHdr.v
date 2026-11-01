(* inflateGetHeader's body against RTH8Spec.inflateGetHeader_spec8: the proof of RTHGetHeader.rth_getheader
   (against RTHSpec.inflateGetHeader_spec6) with header buffers of any uInt size (hwf8, live_ok8). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH8W.
Require Import Zlib.proof.inflate_api.Misc5Kit.
Require Zlib.proof.inflate_api.Body5_misc.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* Misc5Kit.live_head with hwf8: attaching the application's gz_header keeps live_ok8 *)
Lemma live_head8: forall L h headp hsh xb nb cb, live_ok8 L -> hwf8 h -> writable_share hsh ->
  (h_xp h = true -> xb <> nullval) -> (h_np h = true -> nb <> nullval) -> (h_cp h = true -> cb <> nullval) ->
  live_ok8 (set_l_head (set_l_s L (set_i_head (l_s L) true)) (set_h_done h 0) headp hsh xb nb cb).
Proof.
  intros [sp winp s hh headp0 hsh0 xb0 nb0 cb0] h headp hsh xb nb cb (P & W & M & HW & W3 & HS & W0 & HP & WW) Hh Hs X N C.
  ms_simpl.
  split; [exact P | ]. split; [ | split; [ | split; [ | split; [ | split; [exact Hs | ]]]]].
  - destruct W. constructor; ms_simpl; auto.
  - destruct M. constructor; ms_simpl; auto.
    all: try (intro D; destruct (md_tables0 D); split; eapply tv_codes; eauto).
  - unfold hwf8 in Hh |- *. cbn [l_h set_l_head set_l_s set_h_done h_text h_time h_xflags h_os h_extra_len
      h_extra_max h_name_max h_comm_max h_xbuf h_nbuf h_cbuf h_hcrc h_done].
    destruct Hh as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
    repeat split; try tauto; unfold srange, lrange, urange in *; rep_lia.
  - destruct W3. constructor; ms_simpl; auto.
    all: try (intro D; eapply tvl_codes; [ | apply s3_len0; exact D]; reflexivity).
  - split; [exact W0 | split; [ | exact WW]]. intros _. auto.
Qed.

(* RTHGetHeader.hraw6_head_rep6 for any buffer sizes: the raw header given to a stream in mode HEAD or FLAGS is
   a partial header of phase 0 *)
Lemma hraw6_head_rep6_8: forall hsh headp xb nb cb s h vt vtm vxf vos vxl vhc lx ln lc,
  (i_mode s = IM.HEAD \/ i_mode s = IM.FLAGS) ->
  Zlength lx = h_extra_max h -> Zlength ln = h_name_max h -> Zlength lc = h_comm_max h ->
  data_at hsh t_head
     (vt, (vtm, (vxf, (vos,
      ((if h_xp h then xb else nullval), (vxl, (zv (h_extra_max h),
      ((if h_np h then nb else nullval), (zv (h_name_max h),
      ((if h_cp h then cb else nullval), (zv (h_comm_max h), (vhc, zv 0))))))))))))
     headp *
   hbuf6 xb (h_extra_max h) lx * hbuf6 nb (h_name_max h) ln * hbuf6 cb (h_comm_max h) lc
  |-- head_rep6 hsh headp xb nb cb s (set_h_done h 0).
Proof.
  intros hsh headp xb nb cb s h vt vtm vxf vos vxl vhc lx ln lc HM LX LN LC.
  assert (P0: hph s = 0 /\ cx6 s (set_h_done h 0) = 0 /\ cn6 s (set_h_done h 0) = 0 /\ cc6 s (set_h_done h 0) = 0).
  { unfold hph, cx6, cn6, cc6. destruct HM as [E | E]; rewrite E; repeat split; reflexivity. }
  destruct P0 as (P1 & P2 & P3 & P4).
  unfold head_rep6, head_rep6p. rewrite P1, P2, P3, P4.
  apply andp_right.
  { apply prop_right. unfold hinv6.
    split; [reflexivity | ].
    destruct HM as [E | E]; rewrite E; unfold IM.HEAD, IM.FLAGS, IM.EXTRA, IM.NAME, IM.COMMENT, IM.HCRC;
      repeat split; intros; try discriminate; try lia. }
  Exists vt vtm vxf vos vxl vhc lx ln lc.
  cbn [set_h_done h_text h_time h_xflags h_os h_xp h_extra_len h_extra_max h_xbuf h_np h_name_max
    h_nbuf h_cp h_comm_max h_cbuf h_hcrc h_done].
  pose proof (Zlength_nonneg lx). pose proof (Zlength_nonneg ln). pose proof (Zlength_nonneg lc).
  apply andp_right; [ | cancel].
  apply prop_right. unfold bufok6. rewrite !sublist_nil. repeat split; try lia; auto.
Qed.

Lemma rth8_gethdr : gethdr8_stmt.
Proof.
  intros E.
  start_function.
  rename SH into HSH, H into HWF, H0 into HAT.
  unfold istream8_opt.
  destruct (eq_dec strmp nullval) as [Hn | Hn].
  - subst strmp.
    forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
    { simpl. cancel. }
    forward_if; [forward; unfold is_live; rewrite if_true by auto; cancel | discriminate].
  - destruct st as [L | ].
    2: { unfold istream8, zstrm_at, strm_rep. Intros.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (nullval, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), nullval, 0, false, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval); [contradiction | ].
    forward_if.
    { forward. unfold is_live, istream8_opt. rewrite !if_false by auto. unfold istream8, zstrm_at, strm_rep. entailer!. }
    { match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. } }
    destruct L as [sp winp s h0 headp0 hsh0 xb0 nb0 cb0].
    unfold istream8, state_mem, zstrm_at, strm_rep. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_misc. Intros.
    match goal with H: live_ok8 _ |- _ => pose proof H as LOK; destruct H as (Hsp & SW & MW & HW & SW3 & HS & WW) end.
    cbn [l_sp l_s l_h] in Hsp, SW, MW, HW, SW3, HS, WW.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (sp, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { pose proof (sw_mode _ SW). split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    pose proof (sw_mode _ SW) as HMD.
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    forward. forward. forward. (* t'2 = wrap *)
    pose proof (sw_wrap_range _ SW) as HWR. destruct (Zlib.proof.inflate_api.Body5_misc.wrap_and2 _ HWR) as [A2 R2].
    forward_if.
    { forward.
      assert (E2: Z.land (i_wrap s) 2 = 0).
      { match goal with H: Int.and _ _ = Int.repr 0 |- _ => rewrite A2 in H; apply repr_inj_unsigned in H; rep_lia end. }
      unfold is_live, istream8_opt. rewrite !if_false by auto. cbn [l_s]. rewrite E2. cbn [Z.eqb].
      unfold istream8, state_mem, zstrm_at, strm_rep. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_misc.
      entailer!. }
    assert (E2: Z.land (i_wrap s) 2 <> 0).
    { intro X. match goal with H: Int.and _ _ <> Int.repr 0 |- _ => apply H; rewrite A2, X; reflexivity end. }
    assert (HM: i_mode s = IM.HEAD \/ i_mode s = IM.FLAGS).
    { unfold hattach_ok, is_live in HAT. rewrite if_false in HAT by auto. exact (HAT E2). }
    unfold hraw6. Intros vt vtm vxf vos vxl vhc vd lx ln lc.
    forward. (* state->head = head *)
    forward. (* head->done = 0 *)
    forward.
    pose proof (live_head8 _ h headp hsh xb nb cb LOK HWF HSH ltac:(assumption) ltac:(assumption) ltac:(assumption)) as LOK'.
    unfold is_live, istream8_opt. rewrite !if_false by auto. cbn [l_s]. rewrite (proj2 (Z.eqb_neq _ _) E2).
    unfold istream8, state_mem, zstrm_at, strm_rep, head_mem8.
    cbn [set_l_head set_l_s l_sp l_winp l_s l_h l_headp l_hsh l_xb l_nb l_cb] in LOK' |- *.
    rewrite state_rep_misc.
    match goal with |- context [U_misc ?g ?a ?b (set_i_head ?s0 ?w)] =>
      change (U_misc g a b (set_i_head s0 w)) with (U_misc g a b s0) end;
    match goal with |- context [win_rep ?a (set_i_head ?s0 ?w)] =>
      change (win_rep a (set_i_head s0 w)) with (win_rep a s0) end.
    cbn [i_head set_i_head].
    assert (HDM: hdr_mode (i_mode (set_i_head s true)) = true).
    { cbn [i_mode set_i_head]. unfold hdr_mode. destruct HM as [X | X]; rewrite X; reflexivity. }
    sep_apply (hraw6_head_rep6_8 hsh headp xb nb cb (set_i_head s true) h vt vtm vxf vos vxl vhc lx ln lc HM
                 ltac:(assumption) ltac:(assumption) ltac:(assumption)).
    unfold hdr_btoks.
    cbn [h_extra_max h_name_max h_comm_max set_h_done].
    entailer!.
    apply orp_right1. apply orp_right2. apply andp_right; [apply prop_right; exact HDM | apply derives_refl].
Qed.
