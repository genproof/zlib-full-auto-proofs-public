(* Law inflate_dict, theory part: inflateInit2_'s state, inflateSetDictionary (raw right after the
   init; zlib after Z_NEED_DICT: the wrong dictionary is rejected, the right one sets the window). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_dict.ITTheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* updatewindow on an empty window                                                                *)

Lemma itd_uw_keep: forall s d,
  let s' := updatewindow s d in
  i_mode s' = i_mode s /\ i_last s' = i_last s /\ i_wrap s' = i_wrap s /\ i_havedict s' = i_havedict s /\
  i_flags s' = i_flags s /\ i_check s' = i_check s /\ i_total s' = i_total s /\ i_head s' = i_head s /\
  i_wbits s' = i_wbits s /\ i_hold s' = i_hold s /\ i_bits s' = i_bits s /\ i_win s' = i_win s.
Proof.
  intros s d. unfold updatewindow. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; simpl; auto 20.
Qed.

Lemma itd_uw_empty: forall s d, i_wsize s = 0 -> i_wdata s = [] -> 0 <= i_wbits s ->
  let s' := updatewindow s d in
  i_wsize s' = 2 ^ i_wbits s /\ i_whave s' = Z.min (Zlength d) (2 ^ i_wbits s) /\ wstruct s' /\
  (forall k, 1 <= k <= i_whave s' -> win_at s' k = Znth (Zlength d - k) d).
Proof.
  intros s d Hs Hw Hb. cbv zeta.
  assert (P: 0 < 2 ^ i_wbits s) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Zlength_nonneg d) as Ld.
  unfold updatewindow. rewrite Hs. cbv zeta. rewrite Z.eqb_refl.
  cbn [i_wsize i_wnext i_whave i_wdata i_wbits set_i_whave set_i_wnext set_i_wsize set_i_wdata].
  rewrite Hw. set (ws := 2 ^ i_wbits s) in *.
  destruct (Z.leb_spec ws (Zlength d)) as [Le | Gt].
  - cbn [i_wsize i_wnext i_whave i_wdata set_i_whave set_i_wnext set_i_wsize set_i_wdata].
    split; [reflexivity | split; [lia | split]].
    + unfold wstruct; cbn [i_wsize i_wnext i_whave i_wdata set_i_whave set_i_wnext set_i_wsize set_i_wdata].
      rewrite Zlength_sublist by lia. repeat split; lia.
    + intros k Hk. unfold win_at;
        cbn [i_wsize i_wnext i_whave i_wdata set_i_whave set_i_wnext set_i_wsize set_i_wdata] in *.
      destruct (Z.leb_spec k 0); [lia | ].
      rewrite Znth_sublist by lia. f_equal. lia.
  - rewrite !Z.sub_0_r, Z.min_r by lia.
    replace (Zlength d - Zlength d =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    rewrite (proj2 (Z.ltb_lt 0 ws)) by lia.
    replace (0 + Zlength d =? ws) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb].
    rewrite sublist_nil, Zlength_nil, (sublist_nil_gen _ (0 + Zlength d)) by lia.
    rewrite sublist_same by lia. rewrite app_nil_l, ?app_nil_r, Z.add_0_l.
    cbn [i_wsize i_wnext i_whave i_wdata set_i_whave set_i_wnext set_i_wsize set_i_wdata].
    split; [reflexivity | split; [lia | split]].
    + unfold wstruct; cbn [i_wsize i_wnext i_whave i_wdata set_i_whave set_i_wnext set_i_wsize set_i_wdata].
      repeat split; lia.
    + intros k Hk. unfold win_at;
        cbn [i_wsize i_wnext i_whave i_wdata set_i_whave set_i_wnext set_i_wsize set_i_wdata] in *.
      destruct (Z.leb_spec k (Zlength d)); [ | lia]. try (f_equal; lia).
Qed.

Lemma itd_sd_fields: forall s d, i_wsize s = 0 -> i_wdata s = [] -> 0 <= i_wbits s ->
  let s' := setdict_s s d in
  i_mode s' = i_mode s /\ i_last s' = i_last s /\ i_wrap s' = i_wrap s /\ i_havedict s' = 1 /\
  i_flags s' = i_flags s /\ i_check s' = i_check s /\ i_total s' = i_total s /\ i_head s' = i_head s /\
  i_wbits s' = i_wbits s /\ i_hold s' = i_hold s /\ i_bits s' = i_bits s /\ i_win s' = true /\
  i_wsize s' = 2 ^ i_wbits s /\ i_whave s' = Z.min (Zlength d) (2 ^ i_wbits s) /\ wstruct s' /\
  (forall k, 1 <= k <= i_whave s' -> win_at s' k = Znth (Zlength d - k) d).
Proof.
  intros s d A B C. cbv zeta.
  destruct (itd_uw_keep s d) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
  destruct (itd_uw_empty s d A B C) as (E1 & E2 & E3 & E4).
  unfold setdict_s, wstruct, win_at in *.
  cbn [i_mode i_last i_wrap i_havedict i_flags i_check i_total i_head i_wbits i_hold i_bits i_win
       i_wsize i_whave i_wnext i_wdata set_i_havedict set_i_win].
  repeat split; auto; tauto.
Qed.

Lemma itd_reset2_raw: forall wb, 8 <= wb <= 15 -> reset2_wb (- wb) = Some (0, wb).
Proof.
  intros wb H. unfold reset2_wb.
  destruct (Z.ltb_spec (- wb) 0); [ | lia]. destruct (Z.ltb_spec (- wb) (-15)); [lia | ].
  rewrite Z.opp_involutive. destruct (Z.leb_spec 8 wb); [ | lia]. destruct (Z.leb_spec wb 15); [ | lia].
  reflexivity.
Qed.

(* the state after inflateInit2_ for an accepted windowBits (wrap 0..7 from reset2_wb): wrap has bit 3 set when
   wb = 0 (patch F8), the other fields are those of the plain reset *)
Lemma itd_init_fields: forall wrap wb, 0 <= wrap <= 7 -> let s := init_s wrap wb in
  i_mode s = HEAD /\ i_wrap s = reset2_wrap wrap wb /\ i_wbits s = wb /\ i_head s = false /\ i_last s = 0 /\
  i_havedict s = 0 /\ i_total s = 0 /\ i_wsize s = 0 /\ i_whave s = 0 /\ i_wnext s = 0 /\
  i_win s = false /\ i_wdata s = [] /\ i_hold s = 0 /\ i_bits s = 0.
Proof.
  intros wrap wb H. unfold init_s, reset2_s, reset_full_s, reset_hdr_s, reset2_wrap. cbv zeta.
  assert (C: wrap = 0 \/ wrap = 1 \/ wrap = 2 \/ wrap = 3 \/ wrap = 4 \/ wrap = 5 \/ wrap = 6 \/ wrap = 7) by lia.
  destruct (Z.eqb_spec wb 0) as [E | E];
    [subst wb; destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]] | ];
    cbn; try (repeat split; reflexivity).
  destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; cbn; repeat split; reflexivity.
Qed.

Lemma itd_wrap: forall G w b, reset2_wb (g_iw G) = Some (w, b) -> it_wrap G = reset2_wrap w b /\ it_wb0 G = b.
Proof. intros G w b E. unfold it_wrap, it_wb0. rewrite E. auto. Qed.

Lemma itd_out0: forall G, it_out G 0 = g_dict G.
Proof. intros. unfold it_out. rewrite sublist_nil, app_nil_r. reflexivity. Qed.

Lemma itd_produced0: forall G, produced (itd G) (g_dict G) = [].
Proof. intros. unfold produced. cbn [dc_hist itd]. apply sublist_nil. Qed.

Lemma itd_winst: forall G s d, i_wbits s = g_wb G -> i_wsize s = 2 ^ g_wb G -> i_win s = true -> wstruct s ->
  i_whave s = Z.min (Zlength d) (2 ^ g_wb G) ->
  (forall k, 1 <= k <= i_whave s -> win_at s k = Znth (Zlength d - k) d) ->
  win_st G s d /\ win_ok (itd G) s d.
Proof.
  intros G s d A B C D E F.
  assert (W: win_ok (itd G) s d).
  { right. split; [rewrite A, B; reflexivity | split; [rewrite B; exact E | exact F]]. }
  split; [ | exact W]. unfold win_st. split; [exact A | split; [exact B | split; [exact C | split; [exact D | exact W]]]].
Qed.

Lemma itd_bpos0: forall G, g_zlib G = true -> bpos (itd G) 0 = 48.
Proof.
  intros G Hz. unfold bpos, D0. cbn [dc_w dc_bs itd]. unfold it_wrapper. rewrite Hz.
  simpl epos. unfold hdr_bytes. rewrite Zlength_app. unfold be_bytes. rewrite Zlength_rev.
  destruct (g_bs G); reflexivity.
Qed.

Lemma itd_src6: forall G, g_zlib G = true -> 6 <= Zlength (it_src G).
Proof.
  intros G Hz. unfold it_src, it_wrapper. rewrite Hz. unfold stream_bytes.
  rewrite !Zlength_app. unfold be_bytes. rewrite !Zlength_rev.
  pose proof (Zlength_nonneg (deflate_bytes (g_bs G))).
  change (Zlength (zlib_hdr (g_wb G) (Z.land (g_flevel G) 3) true)) with 2.
  change (Zlength (le_bytes (it_dictid G) 4)) with 4.
  change (Zlength (le_bytes (ref_adler32 1 (data (g_dict G) (g_bs G))) 4)) with 4.
  lia.
Qed.

(* the wrong dictionary has another Adler-32 *)
Lemma itd_fold_lo: forall d x y, 0 <= x < ADLER_BASE ->
  fst (fold_left adler_ref_step d (x, y)) = (x + fold_right Z.add 0 d) mod ADLER_BASE.
Proof.
  induction d as [|a d IH]; intros x y H; simpl.
  - rewrite Z.add_0_r, Z.mod_small; auto.
  - unfold adler_ref_step at 2. simpl. rewrite IH by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma itd_lo: forall d, adler_lo (ref_adler32 1 d) = (1 + fold_right Z.add 0 d) mod ADLER_BASE.
Proof.
  intros d. unfold ref_adler32.
  change (adler_lo 1) with 1. change (adler_hi 1) with 0.
  destruct (adler_ref_fold_range d (1, 0)) as [A B]; simpl; try (unfold ADLER_BASE; lia).
  unfold adler_pack. rewrite adler_lo_pack by (unfold ADLER_BASE in *; lia).
  apply itd_fold_lo. unfold ADLER_BASE; lia.
Qed.

Lemma itd_lxor1: forall b, Z.lxor b 1 = b + 1 \/ Z.lxor b 1 = b - 1.
Proof.
  intros b.
  assert (D: Z.div2 (Z.lxor b 1) = Z.div2 b).
  { rewrite !Z.div2_spec, Z.shiftr_lxor. change (Z.shiftr 1 1) with 0. apply Z.lxor_0_r. }
  assert (O: Z.odd (Z.lxor b 1) = negb (Z.odd b)).
  { rewrite <- !Z.bit0_odd, Z.lxor_spec. change (Z.testbit 1 0) with true. apply xorb_true_r. }
  pose proof (Z.div2_odd (Z.lxor b 1)) as E1. pose proof (Z.div2_odd b) as E2.
  rewrite D, O in E1. destruct (Z.odd b); simpl in *; lia.
Qed.

Lemma itd_adler1: adler_valid 1.
Proof. unfold adler_valid. change (adler_lo 1) with 1. change (adler_hi 1) with 0. unfold ADLER_BASE. lia. Qed.

Lemma itd_bad_ne: forall G, ref_adler32 1 (it_bad G) <> ref_adler32 1 (g_dict G).
Proof.
  intros G. unfold it_bad. destruct (g_dict G) as [|b r].
  - vm_compute. discriminate.
  - intro E. apply (f_equal adler_lo) in E. rewrite !itd_lo in E. simpl in E.
    unfold ADLER_BASE in E. destruct (itd_lxor1 b) as [X|X]; rewrite X in E; rewrite !Z.mod_eq in E by lia; lia.
Qed.

Lemma itd_facts :
  (forall G sp, it_ok G -> g_zlib G = true -> wbits_ok (g_iw G) = true ->
     pre_st G 0 (l_s (init_live sp (g_iw G)))) /\
  (forall G sp, it_ok G -> g_zlib G = false -> wbits_ok (g_iw G) = true ->
     let s := l_s (init_live sp (g_iw G)) in
     setdict_check s (g_dict G) = SDUpdate /\ i_win s = false /\ post_st G 0 0 0 (setdict_s s (g_dict G))) /\
  (forall G s, it_ok G -> g_zlib G = true -> nd_st G s -> setdict_check s (it_bad G) = SDData) /\
  (forall G s, it_ok G -> g_zlib G = true -> wbits_ok (g_iw G) = true -> nd_st G s ->
     setdict_check s (g_dict G) = SDUpdate /\ d1_st G 0 (setdict_s s (g_dict G))).
Proof.
  split; [ | split; [ | split]].
  - (* (1) the state after inflateInit2_ (zlib) *)
    intros G sp HG Hz Hw. unfold init_live; cbn [l_s]. unfold wbits_ok in Hw.
    destruct (reset2_wb (g_iw G)) as [[w b] | ] eqn:E; [ | discriminate].
    destruct (itd_wrap G w b E) as [W B].
    assert (R: 0 <= w <= 7) by (destruct (reset2_wb_cases _ _ _ E); lia).
    destruct (itd_init_fields w b R) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14).
    unfold pre_st, pre_common. rewrite W, B.
    split; [repeat split; assumption | ].
    left. split; [exact F1 | split; [exact F3 | split; [lia | split; [rewrite F14; reflexivity | ]]]].
    rewrite F13. reflexivity.
  - (* (2) raw: inflateSetDictionary right after inflateInit2_ *)
    intros G sp HG Hz Hw s.
    destruct HG as (Wb & _ & _ & _ & _ & _ & _ & Iw). rewrite Hz in Iw.
    assert (E: reset2_wb (g_iw G) = Some (0, g_wb G)) by (rewrite Iw; apply itd_reset2_raw; lia).
    assert (Hs: s = init_s 0 (g_wb G)) by (unfold s, init_live; cbn [l_s]; rewrite E; reflexivity).
    clearbody s. subst s.
    destruct (itd_init_fields 0 (g_wb G) ltac:(lia)) as
      (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14).
    assert (R0: reset2_wrap 0 (g_wb G) = 0) by (unfold reset2_wrap; destruct (Z.eqb_spec (g_wb G) 0); [lia | reflexivity]).
    rewrite R0 in F2.
    assert (Hraw: it_wrapper G = WRaw) by (unfold it_wrapper; rewrite Hz; reflexivity).
    split; [unfold setdict_check; rewrite F1, F2; reflexivity | split; [exact F11 | ]].
    set (s0 := init_s 0 (g_wb G)) in *.
    destruct (itd_sd_fields s0 (g_dict G) F8 F12 ltac:(lia)) as
      (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16).
    set (s' := setdict_s s0 (g_dict G)) in *.
    rewrite F3 in S13, S14.
    destruct (itd_winst G s' (g_dict G) ltac:(congruence) S13 S12 S15 S14 S16) as [WS WO].
    unfold post_st. rewrite itd_out0.
    split; [split; [lia | apply Zlength_nonneg] | split; [ | exact WS]].
    unfold dinv. split; [ | split; [ | split; [ | split]]].
    + unfold at_mode. rewrite S10, S11, F13, F14. split.
      * unfold hold_ok. split; [lia | split; [apply Zlength_nonneg | reflexivity]].
      * left. split; [congruence | ].
        unfold at_head. cbn [dc_hist dc_w itd]. rewrite Hraw.
        repeat split; try lia; try congruence; intros; discriminate.
    + unfold glob_ok. cbn [dc_iw dc_w dc_wb itd]. rewrite Hraw.
      split; [exists (g_wb G); rewrite (init_wrap_wb_of _ _ _ E), S3, F2, R0; split; [reflexivity | intros; congruence] | ].
      split; [congruence | split; [intros X; rewrite S1, F1 in X; congruence | ]].
      unfold wrapped. cbn [dc_w itd]. rewrite Hraw. discriminate.
    + intros _. exact WO.
    + unfold chk_ok, wrapped. cbn [dc_w itd]. rewrite Hraw. discriminate.
    + rewrite itd_produced0. reflexivity.
  - (* (3) the wrong dictionary *)
    intros G s HG Hz (PC & Md & _ & _ & _ & _ & Ck).
    unfold setdict_check. rewrite Md, Z.eqb_refl. cbn [negb]. rewrite andb_false_r.
    rewrite adler32_z_val_ref by exact itd_adler1. rewrite Ck. unfold it_dictid.
    destruct (Z.eqb_spec (ref_adler32 1 (it_bad G)) (ref_adler32 1 (g_dict G))) as [X | X].
    + exfalso. exact (itd_bad_ne G X).
    + reflexivity.
  - (* (4) the right dictionary *)
    intros G s HG Hz Hw ((W & Hd & La & Hv & To & Ws & Wh & Wn & Wi & Wd) & Md & Wb & Fl & Ho & Bi & Ck).
    pose proof HG as (Wr & _ & _ & _ & _ & _ & _ & _).
    unfold wbits_ok in Hw.
    destruct (reset2_wb (g_iw G)) as [[w b] | ] eqn:E; [ | discriminate].
    destruct (itd_wrap G w b E) as [WW _].
    assert (Hzl: it_wrapper G = WZlib (g_wb G) (Z.land (g_flevel G) 3) (Some (it_dictid G)))
      by (unfold it_wrapper; rewrite Hz; reflexivity).
    split.
    { unfold setdict_check. rewrite Md, Z.eqb_refl. cbn [negb]. rewrite andb_false_r.
      rewrite adler32_z_val_ref by exact itd_adler1. rewrite Ck. unfold it_dictid.
      rewrite Z.eqb_refl. reflexivity. }
    destruct (itd_sd_fields s (g_dict G) Ws Wd ltac:(lia)) as
      (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16).
    set (s' := setdict_s s (g_dict G)) in *.
    rewrite Wb in S13, S14.
    set (t := d1_ty s').
    assert (T: i_mode t = Zlib.proof.inflate.Model.TYPE /\ i_check t = 1 /\ i_last t = i_last s' /\
      i_wrap t = i_wrap s' /\ i_flags t = i_flags s' /\ i_total t = i_total s' /\ i_head t = i_head s' /\
      i_wbits t = i_wbits s' /\ i_hold t = i_hold s' /\ i_bits t = i_bits s' /\ i_win t = i_win s' /\
      i_wsize t = i_wsize s' /\ i_whave t = i_whave s' /\ i_wnext t = i_wnext s' /\ i_wdata t = i_wdata s')
      by (unfold t, d1_ty; cbn; repeat split; reflexivity).
    destruct T as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15).
    assert (WSt: wstruct t) by (unfold wstruct in *; rewrite T12, T13, T14, T15; exact S15).
    assert (WAt: forall k, 1 <= k <= i_whave t -> win_at t k = Znth (Zlength (g_dict G) - k) (g_dict G)).
    { intros k Hk. unfold win_at. rewrite T12, T14, T15. rewrite T13 in Hk. apply S16 in Hk.
      unfold win_at in Hk. exact Hk. }
    destruct (itd_winst G t (g_dict G) ltac:(congruence) ltac:(congruence) ltac:(congruence) WSt
      ltac:(congruence) WAt) as [WS WO].
    unfold d1_st. split; [exact Hz | split; [congruence | split; [exact S4 | ]]].
    fold t. unfold post_st. rewrite itd_out0.
    split; [split; [lia | apply Zlength_nonneg] | split; [ | exact WS]].
    unfold dinv. split; [ | split; [ | split; [ | split]]].
    + unfold at_mode. rewrite T9, T10, S10, S11, Ho, Bi. split.
      * unfold hold_ok. cbn [dc_src itd]. pose proof (itd_src6 G Hz).
        split; [lia | split; [lia | rewrite sublist_nil' by lia; reflexivity]].
      * right; right; left. split; [left; exact T1 | ].
        unfold at_type. exists 0. split; [unfold nblk; pose proof (Zlength_nonneg (dc_bs (itd G))); lia | ].
        split; [rewrite itd_bpos0 by exact Hz; reflexivity | ].
        split; [reflexivity | split; [lia | ]].
        rewrite T3, S2, La. reflexivity.
    + unfold glob_ok. cbn [dc_iw dc_w dc_wb itd]. rewrite Hzl.
      split; [exists b; rewrite (init_wrap_wb_of _ _ _ E), T4, S3, W, WW; split; [reflexivity | rewrite T1; intros X; discriminate X] | ].
      split; [rewrite T7, S8; exact Hd | ].
      split; [intros _; rewrite T8, S9, Wb; lia | ].
      intros _ _ _. rewrite T5, S5. exact Fl.
    + intros _. exact WO.
    + unfold chk_ok. intros _ _ _ _ _. rewrite T1. cbn [Z.eqb orb].
      change ((Zlib.proof.inflate.Model.TYPE =? LENGTH) || (Zlib.proof.inflate.Model.TYPE =? DONE)) with false.
      cbv iota. rewrite itd_produced0, T2, T6, S7, To.
      unfold chkv. cbn [dc_w itd]. rewrite Hzl.
      split; [reflexivity | split; [reflexivity | exists []; rewrite app_nil_r; reflexivity]].
    + rewrite itd_produced0. reflexivity.
Qed.
