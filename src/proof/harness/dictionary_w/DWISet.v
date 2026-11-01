(* The laws rt_dictionary and api_dict_id: inflateSetDictionary at DICT (after Z_NEED_DICT) with the right
   dictionary, of any length: the window holds the last min(|dict|, 2^wb) bytes of it, and the state's TYPE
   version satisfies the decode invariant at pos 6, in the decode context [dw_ctx] of the stream (inflateInit2's
   windowBits being the stream's window bits wb, 9..15).  Port of round 1's dictionary/DictISet.v, whose
   context had inflateInit2's windowBits 0. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIZDictDefs.
Require Import Zlib.proof.roundtrip.RTIZDictSet.
Require Import Zlib.proof.harness.dictionary_w.DWIFirst.
Import ListNotations.
Local Open Scope Z_scope.

(* the decode context of the stream after the dictionary: Format's zlib stream (FLEVEL 0, the header bytes
   are never read again), inflateInit2's windowBits wb *)
Definition dw_ctx (wb: Z) (dict: list Z) (bs: list block) : dctx :=
  DCtx (zd_w dict wb) wb dict bs wb (stream_bytes (zd_w dict wb) dict bs).

(* inflateInit2(strm, wb), 9 <= wb <= 15: the zlib wrapper (wrap 5), window bits wb *)
Lemma dwi_reset2_wb wb : 9 <= wb <= 15 -> reset2_wb wb = Some (5, wb).
Proof.
  intros Hwb. unfold reset2_wb.
  replace (wb <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.shiftr wb 4) with 0
    by (symmetry; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; change (2 ^ 4) with 16; lia).
  replace (wb <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (Z.land wb 15) with wb
    by (symmetry; change 15 with (Z.ones 4); rewrite Z.land_ones by lia; apply Z.mod_small; change (2 ^ 4) with 16; lia).
  replace (wb =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((8 <=? wb) && (wb <=? 15)) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  reflexivity.
Qed.

(* its wrapper after F8's inflateReset2: wrap 5, bit 3 only with windowBits 0 *)
Lemma dwi_init_wrap_wb wb : 9 <= wb <= 15 -> init_wrap_wb wb = Some (5, wb).
Proof.
  intros Hwb. rewrite (init_wrap_wb_of wb 5 wb (dwi_reset2_wb wb Hwb)). unfold reset2_wrap.
  replace (wb =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma dwi_bpos0 wb dict bs : bpos (dw_ctx wb dict bs) 0 = 48.
Proof. exact (rtzs_bpos0 wb dict bs). Qed.

Lemma dwi_src6 wb dict bs : 6 <= Zlength (dc_src (dw_ctx wb dict bs)).
Proof. exact (rtzs_src6 wb dict bs). Qed.

Lemma dwi_produced0 wb dict bs : produced (dw_ctx wb dict bs) dict = [].
Proof. exact (rtzs_produced0 wb dict bs). Qed.

Lemma dwi_set : forall wb dict bs s,
  9 <= wb <= 15 -> wf (2 ^ wb) dict bs -> dict <> [] ->
  dw_nd wb (Zlib.proof.adler32.Model.ref_adler32 1 dict) s ->
  setdict_check s dict = SDUpdate /\
  dinv (dw_ctx wb dict bs) 6 dict (d1_ty (setdict_s s dict)) 0.
Proof.
  intros wb dict bs s Wbr Hwf Hne
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
  assert (WO: win_ok (dw_ctx wb dict bs) t dict).
  { right. split; [rewrite T8, T12, S9, S13, Wb; reflexivity | ].
    split; [rewrite T13, T12, S13, S14; reflexivity | exact WAt]. }
  unfold dinv. split; [ | split; [ | split; [ | split]]].
  + unfold at_mode. rewrite T9, T10, S10, S11, Ho, Bi. split.
    * unfold hold_ok. pose proof (dwi_src6 wb dict bs).
      split; [lia | split; [lia | rewrite sublist_nil' by lia; reflexivity]].
    * right; right; left. split; [left; exact T1 | ].
      unfold at_type. exists 0. split; [unfold nblk; pose proof (Zlength_nonneg (dc_bs (dw_ctx wb dict bs))); lia | ].
      split; [rewrite dwi_bpos0; reflexivity | ].
      split; [unfold outk; cbn [dc_hist dw_ctx]; reflexivity | split; [lia | ]].
      rewrite T3, S2, La. reflexivity.
  + unfold glob_ok. cbn [dc_iw dc_w dc_wb dw_ctx]. unfold zd_w.
    split; [exists wb; rewrite T4, S3, W; split; [apply dwi_init_wrap_wb; lia | rewrite T1; intros X; discriminate X] | ].
    split; [rewrite T7, S8; exact Hd | ].
    split; [intros _; rewrite T8, S9, Wb; lia | ].
    intros _ _ _. rewrite T5, S5. exact Fl.
  + intros _. exact WO.
  + unfold chk_ok. intros _ _ _ _ _. rewrite T1. cbn [Z.eqb orb].
    change ((Zlib.proof.inflate.Model.TYPE =? LENGTH) || (Zlib.proof.inflate.Model.TYPE =? DONE)) with false.
    cbv iota. rewrite dwi_produced0, T2, T6, S7, To.
    unfold chkv. cbn [dc_w dw_ctx]. unfold zd_w.
    split; [reflexivity | split; [reflexivity | exists []; rewrite app_nil_r; reflexivity]].
  + rewrite dwi_produced0. reflexivity.
Qed.
