(* Body of inflateSync, last segment (Body5_sync_kit.v): after the pattern was found and state->wrap,
   state->wbits were fixed, from `flags = state->flags` to the end: state->wrap with bit 3 hidden around the call
   of inflateReset (patch F8), then the counters, flags, wrap and mode restored. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.Body5_sync_kit.
#[local] Existing Instance Zlib.units.Inflate.CS.

Local Open Scope logic.

(* inflateReset keeps state->wrap *)
Lemma reset_s_wrap_eq (x: istate) : i_wrap (reset_s x) = i_wrap x.
Proof. destruct x; reflexivity. Qed.

(* the fields of a state that a change of wrap does not touch; rewriting with them instead of cbn keeps the kernel
   from unfolding the state reset_s (sync_fix ..) at Qed *)
Lemma set_wrap_fields (x: istate) (w: Z) : i_wbits (set_i_wrap x w) = i_wbits x /\
  i_hold (set_i_wrap x w) = i_hold x /\ i_bits (set_i_wrap x w) = i_bits x /\ i_have (set_i_wrap x w) = i_have x.
Proof. destruct x; repeat split. Qed.

Lemma sync_part5 : sync_seg5.
Proof.
  intros E gv shs strmp z sp winp s h headp hsh xb nb cb ish ip ilo ilen ic inp v_buf s1 bc len.
  intros HY LOK1 M1 SS GL SG.
  destruct HY as (HIN & NI & H2 & ZOK & H4 & Hn).
  destruct HIN as (ISH & IP & ILO & ILEN & IC & IMAX & ISUB & IBY).
  pose proof ZOK as (ZAI & ZAO & ZTIN & ZTOUT & ZDT & ZADL).
  set (L := Live sp winp s h headp hsh xb nb cb) in LOK1.
  destruct (have_fields s1 4) as (HM & HW & HF & HB & HH & HBI & HG).
  pose proof (live_sync_have (set_l_s L s1) 4 LOK1 M1 ltac:(lia)) as LOK2.
  set (L1 := set_l_s (set_l_s L s1) (set_i_have (l_s (set_l_s L s1)) 4)) in LOK2.
  set (s1g := set_i_have s1 4) in *.
  assert (EL1: l_s L1 = s1g) by reflexivity.
  set (s2 := sync_fix s1g) in *.
  destruct (sync_fix_ww s1g) as [W2 B2]. fold s2 in W2, B2.
  destruct (sync_fix_fields s1g) as (M2 & F2 & H2' & B2' & G2'). fold s2 in M2, F2, H2', B2', G2'.
  assert (SW1: swf s1) by (destruct LOK1 as (_ & X & _); exact X).
  assert (Hsp: isptr sp) by (destruct LOK1 as (X & _); exact X).
  sync_seg_start.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    assert (US2: U_sync gv sp headp winp s2 = U_sync gv sp headp winp s1)
      by (unfold s2, s1g; rewrite U_sync_fix, U_sync_have; reflexivity).
    assert (WS2: win_rep winp s2 = win_rep winp s1).
    { pose proof (win_rep_fix L1 winp LOK2) as X. rewrite EL1 in X. unfold s2. rewrite X. unfold s1g. apply win_rep_have. }
    assert (MS1: HEAD <= i_mode s1 <= SYNC) by (rewrite M1; unfold HEAD, SYNC; lia).
    assert (WB2: 0 <= i_wbits s2 <= 23).
    { rewrite B2, HF, HB. pose proof (sw_wbits _ SW1). destruct (i_flags s1 =? -1); [destruct (i_wbits s1 =? 0) | ]; lia. }
    set (z1 := set_zf_in z (in_ptr (InBuf ish ip ilo ilen ic) len) (Zlength inp - len) (u64 (zf_tin z + len))).
    assert (Z1OK: zf_ok z1) by (apply zf_ok_in; auto; rep_lia).
    assert (WR2: 0 <= i_wrap s2 <= 15).
    { rewrite W2, HF, HW. destruct (i_flags s1 =? -1); [lia | ].
      exact (wrap_range _ (wrap_clear4 _ (sw_wrap _ SW1))). }
    set (s2' := set_i_wrap s2 (Z.land (i_wrap s2) (Z.lnot 8))).
    set (L2 := Live sp winp s2' h headp hsh xb nb cb).
    forward. (* flags *)
    forward. (* wrap = state->wrap *)
    forward. (* state->wrap = wrap & ~8 *)
    rewrite (and_not8 (i_wrap s2) WR2).
    forward. forward. (* in, out *)
    match goal with |- semax _ (PROPx _ (LOCALx ?Q _)) _ _ =>
      apply semax_pre with (PROPx [] (LOCALx Q (SEPx [rstream_opt gv shs strmp z1 (rst_of gv (Some L2)); mem_mgr gv; zfuncs gv;
         data_at ish (tarray tuchar ilen) ic ip; data_at Tsh (tarray tuchar 4) bc v_buf])))
    end.
    { unfold rstream_opt, rstream, rst_of. rewrite if_false by auto. cbn [l_sp l_winp l_s l_headp L2].
      rewrite <- state_rep_v_eq, state_rep_sync. unfold zstrm_at, strm_rep.
      unfold s2'. rewrite U_sync_wrap, win_rep_wrap. cbn [i_mode i_flags i_hold i_bits i_have i_wbits i_wrap set_i_wrap].
      rewrite US2, WS2, M2, HM, F2, HF, H2', HH, B2', HBI, G2', HG.
      unfold z1. cbn [set_zf_in zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt zf_adler zf_res].
      rewrite <- Hzca, <- Hzcf. entailer!. }
    assert (RF: reset_full_s s2' = reset_s s2') by (apply reset_full_clear8; unfold s2'; cbn [i_wrap set_i_wrap]; apply land_not8_8).
    forward_call (gv, shs, strmp, z1, rst_of gv (Some L2)).
    { unfold reset_pre, rs_live. rewrite if_false by auto. intros _.
      pose proof (live_fixreset L1 LOK2) as X. rewrite EL1 in X.
      change (live_ok (set_l_s L2 (reset_full_s s2'))). rewrite RF. unfold s2'.
      exact (live_wrap8 _ _ X). }
    unfold reset_post, rs_live. rewrite if_false by auto. unfold rst_of. cbv iota.
    change (fst3 (reset_f z1 L2)) with Z_OK. rewrite Z.eqb_refl.
    change (snd3 (reset_f z1 L2)) with (reset_keep_z z1 (reset_full_s s2')).
    change (thd3 (reset_f z1 L2)) with (set_l_s L2 (reset_full_s s2')). rewrite RF.
    unfold istream, state_mem, zstrm_at, strm_rep.
    cbn [l_sp l_winp l_s l_headp set_l_s L2]. rewrite state_rep_sync.
    set (r := reset_s s2) in *.
    assert (WRr: i_wrap r = i_wrap s2) by (unfold r; apply reset_s_wrap_eq).
    assert (Er: reset_s s2' = set_i_wrap r (Z.land (i_wrap s2) (Z.lnot 8))) by (unfold s2', r; apply reset_s_wrap).
    rewrite Er. rewrite U_sync_wrap, win_rep_wrap.
    set (z2 := reset_keep_z z1 (set_i_wrap r (Z.land (i_wrap s2) (Z.lnot 8)))) in *. Intros.
    rewrite <- Hzca, <- Hzcf. forward. forward. forward. forward. forward. forward.
    clear W2 B2 ISUB IBY.
    set (s1g := set_i_have s1 4) in *.
    unfold on_live, is_live, fst3, snd3, thd3, sync_f. rewrite if_false by auto. cbn [l_s].
    rewrite SG. cbn [fst snd]. cbv zeta. fold z1.
    unfold istream_opt. rewrite if_false by auto.
    unfold istream, state_mem, zstrm_at, strm_rep, in_rep.
    pose proof (live_fin L1 LOK2) as LF. rewrite EL1 in LF.
    change (sync_fin s1g) with (set_i_mode (set_i_flags r (i_flags s2)) Zlib.proof.inflate.Model.TYPE) in *.
    destruct (mf_fields r (i_flags s2) Zlib.proof.inflate.Model.TYPE) as (FM1 & FM2 & FM3 & FM4 & FM5 & FM6 & FM7).
    rewrite (reset_keep_z_wrap z1 (set_i_wrap (set_i_mode (set_i_flags r (i_flags s2)) Zlib.proof.inflate.Model.TYPE) _)
               (set_i_wrap r (Z.land (i_wrap s2) (Z.lnot 8)))) by (cbn [i_wrap set_i_wrap]; rewrite FM2, WRr; reflexivity).
    fold z2.
    cbn [set_zf_counters set_l_s l_sp l_winp l_s l_h l_headp zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt
         zf_adler zf_res].
    assert (PZ: zf_ok (set_zf_counters z2 (zf_tin z1) (zf_tout z1))).
    { apply zf_ok_counters; [assumption | | ]; unfold lrange, z1, u64; cbn [zf_tin zf_tout set_zf_in].
      all: try (pose proof (Z.mod_pos_bound (zf_tin z + len) (2 ^ 64) ltac:(lia))); rep_lia. }
    rewrite (prop_true_andp (Vint (Int.repr 0) = Vint (Int.repr Z_OK))) by reflexivity.
    rewrite (prop_true_andp (_ /\ _)) by auto.
    rewrite (prop_true_andp (live_ok _)) by exact LF.
    rewrite state_rep_sync, FM1, FM2, FM3, FM4, FM5, FM6, FM7, U_sync_mf, win_rep_mf, F2, HF.
    destruct (set_wrap_fields r (Z.land (i_wrap s2) (Z.lnot 8))) as (WF1 & WF2 & WF3 & WF4).
    rewrite WF1, WF2, WF3, WF4.
    change (zf_tin z1) with (u64 (zf_tin z + len)). change (zf_tout z1) with (zf_tout z).
    change (Int.repr Zlib.proof.inflate.Model.TYPE) with (Int.repr 16191).
    rewrite WRr.
    sep_apply (data_at_data_at_ Tsh (tarray tuchar 4) bc v_buf). cancel.
Qed.
