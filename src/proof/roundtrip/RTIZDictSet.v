(* RT-I, part rti_zdict: inflateSetDictionary at DICT (after Z_NEED_DICT) with the right
   dictionary: the window update, and the decode invariant of the state's TYPE version at pos 6. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIZDictDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the window's shape (copy of harness/inflate_dict/ITTheoryDefs.v wstruct) *)
Definition rtzs_wstruct (s: istate) : Prop :=
  0 <= i_whave s <= i_wsize s /\ 0 <= i_wnext s < i_wsize s /\
  (i_whave s < i_wsize s -> i_wnext s = i_whave s) /\ Zlength (i_wdata s) = i_whave s.

Lemma rtzs_uw_keep: forall s d,
  let s' := updatewindow s d in
  i_mode s' = i_mode s /\ i_last s' = i_last s /\ i_wrap s' = i_wrap s /\ i_havedict s' = i_havedict s /\
  i_flags s' = i_flags s /\ i_check s' = i_check s /\ i_total s' = i_total s /\ i_head s' = i_head s /\
  i_wbits s' = i_wbits s /\ i_hold s' = i_hold s /\ i_bits s' = i_bits s /\ i_win s' = i_win s.
Proof.
  intros s d. unfold updatewindow. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; simpl; auto 20.
Qed.

Lemma rtzs_uw_empty: forall s d, i_wsize s = 0 -> i_wdata s = [] -> 0 <= i_wbits s ->
  let s' := updatewindow s d in
  i_wsize s' = 2 ^ i_wbits s /\ i_whave s' = Z.min (Zlength d) (2 ^ i_wbits s) /\ rtzs_wstruct s' /\
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
    + unfold rtzs_wstruct; cbn [i_wsize i_wnext i_whave i_wdata set_i_whave set_i_wnext set_i_wsize set_i_wdata].
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
    + unfold rtzs_wstruct; cbn [i_wsize i_wnext i_whave i_wdata set_i_whave set_i_wnext set_i_wsize set_i_wdata].
      repeat split; lia.
    + intros k Hk. unfold win_at;
        cbn [i_wsize i_wnext i_whave i_wdata set_i_whave set_i_wnext set_i_wsize set_i_wdata] in *.
      destruct (Z.leb_spec k (Zlength d)); [ | lia]. try (f_equal; lia).
Qed.

Lemma rtzs_sd_fields: forall s d, i_wsize s = 0 -> i_wdata s = [] -> 0 <= i_wbits s ->
  let s' := setdict_s s d in
  i_mode s' = i_mode s /\ i_last s' = i_last s /\ i_wrap s' = i_wrap s /\ i_havedict s' = 1 /\
  i_flags s' = i_flags s /\ i_check s' = i_check s /\ i_total s' = i_total s /\ i_head s' = i_head s /\
  i_wbits s' = i_wbits s /\ i_hold s' = i_hold s /\ i_bits s' = i_bits s /\ i_win s' = true /\
  i_wsize s' = 2 ^ i_wbits s /\ i_whave s' = Z.min (Zlength d) (2 ^ i_wbits s) /\ rtzs_wstruct s' /\
  (forall k, 1 <= k <= i_whave s' -> win_at s' k = Znth (Zlength d - k) d).
Proof.
  intros s d A B C. cbv zeta.
  destruct (rtzs_uw_keep s d) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
  destruct (rtzs_uw_empty s d A B C) as (E1 & E2 & E3 & E4).
  unfold setdict_s, rtzs_wstruct, win_at in *.
  cbn [i_mode i_last i_wrap i_havedict i_flags i_check i_total i_head i_wbits i_hold i_bits i_win
       i_wsize i_whave i_wnext i_wdata set_i_havedict set_i_win].
  repeat split; auto; tauto.
Qed.

Lemma rtzs_adler1: Zlib.proof.adler32.Model.adler_valid 1.
Proof.
  unfold Zlib.proof.adler32.Model.adler_valid.
  change (Zlib.proof.adler32.Model.adler_lo 1) with 1. change (Zlib.proof.adler32.Model.adler_hi 1) with 0.
  unfold Zlib.proof.adler32.Model.ADLER_BASE. lia.
Qed.

Lemma rtzs_bpos0: forall wb dict bs, bpos (zd_ctx wb dict bs) 0 = 48.
Proof.
  intros. unfold bpos, D0. cbn [dc_w dc_bs zd_ctx]. unfold zd_w.
  simpl epos. unfold hdr_bytes. rewrite Zlength_app. unfold be_bytes. rewrite Zlength_rev.
  destruct bs; reflexivity.
Qed.

Lemma rtzs_src6: forall wb dict bs, 6 <= Zlength (dc_src (zd_ctx wb dict bs)).
Proof.
  intros. cbn [dc_src zd_ctx]. unfold zd_w, stream_bytes.
  rewrite !Zlength_app. unfold be_bytes. rewrite !Zlength_rev.
  pose proof (Zlength_nonneg (deflate_bytes bs)).
  change (Zlength (zlib_hdr wb 0 true)) with 2.
  change (Zlength (le_bytes (Zlib.proof.adler32.Model.ref_adler32 1 dict) 4)) with 4.
  change (Zlength (le_bytes (Zlib.proof.adler32.Model.ref_adler32 1 (data dict bs)) 4)) with 4.
  lia.
Qed.

Lemma rtzs_produced0: forall wb dict bs, produced (zd_ctx wb dict bs) dict = [].
Proof. intros. unfold produced. cbn [dc_hist zd_ctx]. apply sublist_nil. Qed.

Lemma rtz_set : forall wb dict bs s,
  9 <= wb <= 15 -> wf (2 ^ wb) dict bs -> dict <> [] -> Zlength dict <= 32768 ->
  zd_nd wb (Zlib.proof.adler32.Model.ref_adler32 1 dict) s ->
  setdict_check s dict = SDUpdate /\
  dinv (zd_ctx wb dict bs) 6 dict (d1_ty (setdict_s s dict)) 0.
Proof.
  intros wb dict bs s Wbr Hwf Hne Hlen
    (Md & W & Hd & La & Hv & To & Ws & Wh & Wn & Wi & Wd & Wb & Fl & Ho & Bi & Ck).
  split.
  { unfold setdict_check. rewrite Md, Z.eqb_refl. cbn [negb]. rewrite andb_false_r.
    rewrite Zlib.proof.adler32.Model.adler32_z_val_ref by exact rtzs_adler1. rewrite Ck.
    rewrite Z.eqb_refl. reflexivity. }
  destruct (rtzs_sd_fields s dict Ws Wd ltac:(lia)) as
    (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16).
  set (s' := setdict_s s dict) in *.
  rewrite Wb in S13, S14.
  set (t := d1_ty s').
  assert (T: i_mode t = Zlib.proof.inflate.Model.TYPE /\ i_check t = 1 /\ i_last t = i_last s' /\
    i_wrap t = i_wrap s' /\ i_flags t = i_flags s' /\ i_total t = i_total s' /\ i_head t = i_head s' /\
    i_wbits t = i_wbits s' /\ i_hold t = i_hold s' /\ i_bits t = i_bits s' /\ i_win t = i_win s' /\
    i_wsize t = i_wsize s' /\ i_whave t = i_whave s' /\ i_wnext t = i_wnext s' /\ i_wdata t = i_wdata s')
    by (unfold t, d1_ty; cbn; repeat split; reflexivity).
  destruct T as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15).
  assert (WAt: forall k, 1 <= k <= i_whave t -> win_at t k = Znth (Zlength dict - k) dict).
  { intros k Hk. unfold win_at. rewrite T12, T14, T15. rewrite T13 in Hk. apply S16 in Hk.
    unfold win_at in Hk. exact Hk. }
  assert (WO: win_ok (zd_ctx wb dict bs) t dict).
  { right. split; [rewrite T8, T12, S9, S13, Wb; reflexivity | ].
    split; [rewrite T13, T12, S13, S14; reflexivity | exact WAt]. }
  unfold dinv. split; [ | split; [ | split; [ | split]]].
  + unfold at_mode. rewrite T9, T10, S10, S11, Ho, Bi. split.
    * unfold hold_ok. pose proof (rtzs_src6 wb dict bs).
      split; [lia | split; [lia | rewrite sublist_nil' by lia; reflexivity]].
    * right; right; left. split; [left; exact T1 | ].
      unfold at_type. exists 0. split; [unfold nblk; pose proof (Zlength_nonneg (dc_bs (zd_ctx wb dict bs))); lia | ].
      split; [rewrite rtzs_bpos0; reflexivity | ].
      split; [unfold outk; cbn [dc_hist zd_ctx]; reflexivity | split; [lia | ]].
      rewrite T3, S2, La. reflexivity.
  + unfold glob_ok. cbn [dc_iw dc_w dc_wb zd_ctx]. unfold zd_w.
    split; [exists 0; rewrite T4, S3, W; split; [reflexivity | rewrite T1; intros X; discriminate X] | ].
    split; [rewrite T7, S8; exact Hd | ].
    split; [intros _; rewrite T8, S9, Wb; lia | ].
    intros _ _ _. rewrite T5, S5. exact Fl.
  + intros _. exact WO.
  + unfold chk_ok. intros _ _ _ _ _. rewrite T1. cbn [Z.eqb orb].
    change ((Zlib.proof.inflate.Model.TYPE =? LENGTH) || (Zlib.proof.inflate.Model.TYPE =? DONE)) with false.
    cbv iota. rewrite rtzs_produced0, T2, T6, S7, To.
    unfold chkv. cbn [dc_w zd_ctx]. unfold zd_w.
    split; [reflexivity | split; [reflexivity | exists []; rewrite app_nil_r; reflexivity]].
  + rewrite rtzs_produced0. reflexivity.
Qed.
