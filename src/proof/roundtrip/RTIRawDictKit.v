(* RT-I: facts for RTIRawDict.rti_rawdict (raw stream, inflateSetDictionary right after
   inflateInit2): the decode context, and the state after the dictionary satisfies the decode invariant.
   Adapted from harness/inflate_dict/ITDict.v (itd_uw_keep, itd_uw_empty, itd_sd_fields, raw part of itd_facts)
   and ITCtx.v (itc_pack_ok). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.rfc1951.Decode.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* updatewindow on an empty window                                                                *)

Lemma rrd_uw_keep: forall s d,
  let s' := updatewindow s d in
  i_mode s' = i_mode s /\ i_last s' = i_last s /\ i_wrap s' = i_wrap s /\ i_havedict s' = i_havedict s /\
  i_flags s' = i_flags s /\ i_check s' = i_check s /\ i_total s' = i_total s /\ i_head s' = i_head s /\
  i_wbits s' = i_wbits s /\ i_hold s' = i_hold s /\ i_bits s' = i_bits s /\ i_win s' = i_win s.
Proof.
  intros s d. unfold updatewindow. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; simpl; auto 20.
Qed.

Lemma rrd_uw_empty: forall s d, i_wsize s = 0 -> i_wdata s = [] -> 0 <= i_wbits s ->
  let s' := updatewindow s d in
  i_wsize s' = 2 ^ i_wbits s /\ i_whave s' = Z.min (Zlength d) (2 ^ i_wbits s) /\
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
    split; [reflexivity | split; [lia | ]].
    intros k Hk. unfold win_at;
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
    split; [reflexivity | split; [lia | ]].
    intros k Hk. unfold win_at;
      cbn [i_wsize i_wnext i_whave i_wdata set_i_whave set_i_wnext set_i_wsize set_i_wdata] in *.
    destruct (Z.leb_spec k (Zlength d)); [ | lia]. try (f_equal; lia).
Qed.

Lemma rrd_sd_fields: forall s d, i_wsize s = 0 -> i_wdata s = [] -> 0 <= i_wbits s ->
  let s' := setdict_s s d in
  i_mode s' = i_mode s /\ i_last s' = i_last s /\ i_wrap s' = i_wrap s /\
  i_total s' = i_total s /\ i_head s' = i_head s /\
  i_wbits s' = i_wbits s /\ i_hold s' = i_hold s /\ i_bits s' = i_bits s /\
  i_wsize s' = 2 ^ i_wbits s /\ i_whave s' = Z.min (Zlength d) (2 ^ i_wbits s) /\
  (forall k, 1 <= k <= i_whave s' -> win_at s' k = Znth (Zlength d - k) d).
Proof.
  intros s d A B C. cbv zeta.
  destruct (rrd_uw_keep s d) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
  destruct (rrd_uw_empty s d A B C) as (E1 & E2 & E4).
  unfold setdict_s, win_at in *.
  cbn [i_mode i_last i_wrap i_havedict i_flags i_check i_total i_head i_wbits i_hold i_bits i_win
       i_wsize i_whave i_wnext i_wdata set_i_havedict set_i_win].
  repeat split; auto.
Qed.

Lemma rrd_reset2_raw: forall wb, 8 <= wb <= 15 -> reset2_wb (- wb) = Some (0, wb).
Proof.
  intros wb H. unfold reset2_wb.
  destruct (Z.ltb_spec (- wb) 0); [ | lia]. destruct (Z.ltb_spec (- wb) (-15)); [lia | ].
  rewrite Z.opp_involutive. destruct (Z.leb_spec 8 wb); [ | lia]. destruct (Z.leb_spec wb 15); [ | lia].
  reflexivity.
Qed.

(* the state after inflateInit2_ with a wrapper in 0..7 and a window size from the caller (wb <> 0): with fix F8,
   bit 3 of wrap is set only for wb = 0, so here the stored wrap is wrap itself and inflateReset keeps wbits *)
Lemma rrd_init_fields: forall wrap wb, 0 <= wrap <= 7 -> wb <> 0 -> let s := init_s wrap wb in
  i_mode s = HEAD /\ i_wrap s = wrap /\ i_wbits s = wb /\ i_head s = false /\ i_last s = 0 /\
  i_havedict s = 0 /\ i_total s = 0 /\ i_wsize s = 0 /\ i_whave s = 0 /\ i_wnext s = 0 /\
  i_win s = false /\ i_wdata s = [] /\ i_hold s = 0 /\ i_bits s = 0.
Proof.
  intros wrap wb Hw Hb. cbv zeta.
  assert (L: Z.land wrap 8 = 0).
  { assert (C: wrap = 0 \/ wrap = 1 \/ wrap = 2 \/ wrap = 3 \/ wrap = 4 \/ wrap = 5 \/ wrap = 6 \/ wrap = 7) by lia.
    destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; reflexivity. }
  unfold init_s, reset2_s, reset_full_s, reset_hdr_s, reset2_wrap.
  rewrite (proj2 (Z.eqb_neq wb 0) Hb). cbn [zero_s i_win i_wbits i_wrap set_i_wbits set_i_wrap andb orb].
  rewrite L. cbn. repeat split.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the decode context                                                                             *)

Lemma rrd_bval_range l : 0 <= bval l < 2 ^ Zlength l.
Proof.
  induction l as [|b r IH]; simpl.
  - rewrite ?Zlength_nil. simpl. lia.
  - rewrite Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg r); lia).
    destruct b; simpl; lia.
Qed.

Lemma rrd_pack_ok bs : bytes_ok (pack bs).
Proof.
  unfold bytes_ok, pack. apply Forall_map, Forall_forall. intros k _.
  set (l := sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs). pose proof (rrd_bval_range l).
  assert (Zlength l <= 8).
  { unfold l, sublist. rewrite Zlength_correct, length_skipn, length_firstn. lia. }
  assert (2 ^ Zlength l <= 2 ^ 8) by (apply Z.pow_le_mono_r; [lia | pose proof (Zlength_nonneg l); lia]).
  unfold Basics.compose; cbv beta; fold l. change (2 ^ 8) with 256 in *. rep_lia.
Qed.

Lemma rrd_ctx_ok wb dict bs O :
  8 <= wb <= 15 -> wf (2 ^ wb) dict bs -> O = deflate_bytes bs -> Zlength O <= 2 ^ 31 - 1 ->
  dctx_ok (DCtx WRaw wb dict bs (- wb) O).
Proof.
  intros Hwb Hwf HO HL.
  assert (Hb: bytes_ok O) by (subst O; apply rrd_pack_ok).
  unfold dctx_ok, slen, accepts; cbn [dc_w dc_wb dc_hist dc_bs dc_iw dc_src stream_bytes].
  rewrite <- HO.
  split; [unfold stream_ok; cbn; tauto | ].
  split; [reflexivity | ].
  split; [intros ? E; discriminate E | ].
  split; [intros ? ? ? E; discriminate E | ].
  split; [lia | ]. split; [exact HL | ]. split; [exact Hb | ].
  apply sublist_same; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the state after inflateInit2(-wb) and inflateSetDictionary                                     *)

Lemma rrd_setdict_check wb sp dict : 8 <= wb <= 15 ->
  l_s (init_live sp (- wb)) = init_s 0 wb /\
  setdict_check (init_s 0 wb) dict = SDUpdate /\ i_win (init_s 0 wb) = false.
Proof.
  intros Hwb. split; [unfold init_live; cbn [l_s]; rewrite rrd_reset2_raw by lia; reflexivity | ].
  destruct (rrd_init_fields 0 wb ltac:(lia) ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14).
  split; [ | exact F11].
  unfold setdict_check. rewrite F1, F2. reflexivity.
Qed.

Lemma rrd_dinv wb dict bs O :
  8 <= wb <= 15 ->
  dinv (DCtx WRaw wb dict bs (- wb) O) 0 dict (setdict_s (init_s 0 wb) dict) 0.
Proof.
  intros Hwb.
  set (G := DCtx WRaw wb dict bs (- wb) O).
  destruct (rrd_init_fields 0 wb ltac:(lia) ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14).
  set (s0 := init_s 0 wb) in *.
  destruct (rrd_sd_fields s0 dict F8 F12 ltac:(lia)) as
    (S1 & S2 & S3 & S7 & S8 & S9 & S10 & S11 & S13 & S14 & S16).
  set (s' := setdict_s s0 dict) in *.
  rewrite F3 in S13, S14.
  unfold dinv. split; [ | split; [ | split; [ | split]]].
  - unfold at_mode. rewrite S10, S11, F13, F14. split.
    + unfold hold_ok. split; [lia | split; [apply Zlength_nonneg | reflexivity]].
    + left. split; [congruence | ].
      unfold at_head. cbn [dc_hist dc_w G].
      repeat split; try lia; try congruence; intros; discriminate.
  - unfold glob_ok. cbn [dc_iw dc_w dc_wb G].
    (* inflateInit2_ on a raw windowBits: wrap 0 and no bit 3 (wb <> 0) *)
    split; [exists wb; rewrite (init_wrap_wb_of _ 0 wb (rrd_reset2_raw wb Hwb)); unfold reset2_wrap;
            rewrite (proj2 (Z.eqb_neq wb 0)) by lia; rewrite S3, F2; split; [reflexivity | intros; congruence] | ].
    split; [congruence | split; [intros X; rewrite S1, F1 in X; congruence | ]].
    unfold wrapped. cbn [dc_w G]. discriminate.
  - intros _. right. rewrite S9, F3. split; [exact S13 | split; [rewrite S13; exact S14 | exact S16]].
  - unfold chk_ok, wrapped. cbn [dc_w G]. discriminate.
  - unfold produced. cbn [dc_hist G]. rewrite sublist_nil. reflexivity.
Qed.
