(* Bodies of inflate.c's API functions, version 5: api_dict_stmt (Bodies5.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Arguments stream_ok_val : simpl never.

Ltac one_zero := exfalso; match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end.

Local Open Scope logic.

Definition rest_g (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp *
  field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
  field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp *
  field_at Ews t_state (DOT _lencode) (tref_val gv sp (i_lencode s)) sp *
  field_at Ews t_state (DOT _distcode) (tref_val gv sp (i_distcode s)) sp *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp *
  field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp *
  field_at Ews t_state (DOT _ncode) (zv (i_ncode s)) sp *
  field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp *
  field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp *
  field_at Ews t_state (DOT _have) (zv (i_have s)) sp *
  field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp *
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

Lemma rest_g_rearr: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 : mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a1 * a2 * a13 * a14 * a15 * (a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma rest_g_split gv sp strmp headp winp s: state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _whave) (zv (i_whave s)) sp *
  field_at Ews t_state (DOT _wnext) (zv (i_wnext s)) sp *
  field_at Ews t_state (DOT _window) (if i_win s then winp else nullval) sp *
  rest_g gv sp strmp headp winp s.
Proof. unfold state_rep, rest_g. apply rest_g_rearr. Qed.

Definition rest_s (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
  field_at Ews t_state (DOT _whave) (zv (i_whave s)) sp *
  field_at Ews t_state (DOT _wnext) (zv (i_wnext s)) sp *
  field_at Ews t_state (DOT _window) (if i_win s then winp else nullval) sp *
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp *
  field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
  field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp *
  field_at Ews t_state (DOT _lencode) (tref_val gv sp (i_lencode s)) sp *
  field_at Ews t_state (DOT _distcode) (tref_val gv sp (i_distcode s)) sp *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp *
  field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp *
  field_at Ews t_state (DOT _ncode) (zv (i_ncode s)) sp *
  field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp *
  field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp *
  field_at Ews t_state (DOT _have) (zv (i_have s)) sp *
  field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp *
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

Lemma rest_s_rearr: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 : mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a1 * a2 * a4 * a5 * a8 * (a3 * a6 * a7 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma rest_s_split gv sp strmp headp winp s: state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  rest_s gv sp strmp headp winp s.
Proof. unfold state_rep, rest_s. apply rest_s_rearr. Qed.


Lemma fa0_tuchar n k p: 0 <= k <= n -> field_compatible (tarray tuchar n) [] p ->
  field_address0 (Tarray tuchar n noattr) [ArraySubsc k] p = offset_val k p.
Proof.
  intros. rewrite field_address0_offset by auto with field_compatible.
  simpl. f_equal. lia.
Qed.

Lemma arr3_split sh n a b (v: list val) p: 0 <= a <= b -> b <= n -> Zlength v = n ->
  data_at sh (tarray tuchar n) v p |--
  !! field_compatible (tarray tuchar n) [] p &&
  (data_at sh (tarray tuchar a) (sublist 0 a v) p *
   data_at sh (tarray tuchar (b - a)) (sublist a b v) (offset_val a p) *
   data_at sh (tarray tuchar (n - b)) (sublist b n v) (offset_val b p)).
Proof.
  intros. subst n. saturate_local. apply andp_right; [apply prop_right; auto|].
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh (Zlength v) a b) by lia.
  rewrite !fa0_tuchar by (auto; lia). auto.
Qed.

Lemma arr3_join sh n a b (v1 v2 v3: list val) p: 0 <= a <= b -> b <= n ->
  Zlength v1 = a -> Zlength v2 = b - a -> Zlength v3 = n - b ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar a) v1 p *
  data_at sh (tarray tuchar (b - a)) v2 (offset_val a p) *
  data_at sh (tarray tuchar (n - b)) v3 (offset_val b p) |--
  data_at sh (tarray tuchar n) (v1 ++ v2 ++ v3) p.
Proof.
  intros. unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a b) by list_solve.
  rewrite !fa0_tuchar by (auto; lia).
  autorewrite with sublist. cancel.
Qed.



Lemma arr2_split sh m a (v: list val) q: 0 <= a <= m -> Zlength v = m ->
  data_at sh (tarray tuchar m) v q |--
  !! field_compatible (tarray tuchar m) [] q &&
  (data_at sh (tarray tuchar a) (sublist 0 a v) q *
   data_at sh (tarray tuchar (m - a)) (sublist a m v) (offset_val a q)).
Proof.
  intros. subst m. saturate_local. apply andp_right; [apply prop_right; auto|].
  unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh (Zlength v) a) by lia.
  rewrite fa0_tuchar by (auto; lia). auto.
Qed.

Lemma arr2_join sh m a (v1 v2: list val) q: 0 <= a <= m -> Zlength v1 = a -> Zlength v2 = m - a ->
  field_compatible (tarray tuchar m) [] q ->
  data_at sh (tarray tuchar a) v1 q * data_at sh (tarray tuchar (m - a)) v2 (offset_val a q) |--
  data_at sh (tarray tuchar m) (v1 ++ v2) q.
Proof.
  intros. unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh m a) by list_solve.
  rewrite fa0_tuchar by (auto; lia). autorewrite with sublist. cancel.
Qed.


Lemma fc_sub n lo m p: 0 <= lo -> 0 <= m -> lo + m <= n -> field_compatible (tarray tuchar n) [] p ->
  field_compatible (tarray tuchar m) [] (offset_val lo p).
Proof.
  intros.
  destruct (proj1 (field_compatible_Tarray_split tuchar lo n p ltac:(lia)) H2) as [_ F].
  unfold tarray at 2 in F. rewrite fa0_tuchar in F by (auto; lia).
  destruct (proj1 (field_compatible_Tarray_split tuchar m (n - lo) (offset_val lo p) ltac:(lia)) F) as [F2 _].
  exact F2.
Qed.

Lemma arr2_join' sh a k (v1 v2: list val) q: 0 <= a -> 0 <= k -> Zlength v1 = a -> Zlength v2 = k ->
  field_compatible (tarray tuchar (a + k)) [] q ->
  data_at sh (tarray tuchar a) v1 q * data_at sh (tarray tuchar k) v2 (offset_val a q) |--
  data_at sh (tarray tuchar (a + k)) (v1 ++ v2) q.
Proof.
  intros. pose proof (arr2_join sh (a + k) a v1 v2 q) as J.
  replace (a + k - a) with k in J by lia. apply J; auto; lia.
Qed.

Lemma arr3_join' sh a k r (v1 v2 v3: list val) p: 0 <= a -> 0 <= k -> 0 <= r ->
  Zlength v1 = a -> Zlength v2 = k -> Zlength v3 = r ->
  field_compatible (tarray tuchar (a + k + r)) [] p ->
  data_at sh (tarray tuchar a) v1 p *
  data_at sh (tarray tuchar k) v2 (offset_val a p) *
  data_at sh (tarray tuchar r) v3 (offset_val (a + k) p) |--
  data_at sh (tarray tuchar (a + k + r)) (v1 ++ v2 ++ v3) p.
Proof.
  intros. pose proof (arr3_join sh (a + k + r) a (a + k) v1 v2 v3 p) as J.
  replace (a + k - a) with k in J by lia. replace (a + k + r - (a + k)) with r in J by lia.
  apply J; auto; lia.
Qed.


Lemma arr_valid sh n lo (c: list val) p: readable_share sh -> 0 <= lo < n -> Zlength c = n ->
  data_at sh (tarray tuchar n) c p |-- valid_pointer (offset_val lo p).
Proof.
  intros. sep_apply (arr3_split sh n lo n c p ltac:(lia) ltac:(lia) H1). Intros.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
  apply data_at_valid_ptr; [auto | simpl; rewrite Z.max_r by lia; lia].
Qed.

Lemma gd_pre sh n lo (c: list val) p W wd wh wn winp:
  0 <= lo -> lo + wh <= n -> Zlength c = n -> 0 <= wn <= wh -> wh <= W -> Zlength wd = wh ->
  data_at sh (tarray tuchar n) c p * data_at Ews (tarray tuchar W) (byte_vals wd ++ Zrepeat Vundef (W - wh)) winp |--
  !! (field_compatible (tarray tuchar n) [] p /\ field_compatible (tarray tuchar W) [] winp) &&
  (data_at sh (tarray tuchar lo) (sublist 0 lo c) p *
   data_at sh (tarray tuchar (wh - wn)) (sublist lo (lo + (wh - wn)) c) (offset_val lo p) *
   data_at sh (tarray tuchar wn) (sublist (lo + (wh - wn)) (lo + wh) c) (offset_val (lo + (wh - wn)) p) *
   data_at sh (tarray tuchar (n - (lo + wh))) (sublist (lo + wh) n c) (offset_val (lo + wh) p) *
   data_at Ews (tarray tuchar wn) (byte_vals (sublist 0 wn wd)) winp *
   data_at Ews (tarray tuchar (wh - wn)) (byte_vals (sublist wn wh wd)) (offset_val wn winp) *
   data_at Ews (tarray tuchar (W - wh)) (Zrepeat Vundef (W - wh)) (offset_val wh winp)).
Proof.
  intros.
  sep_apply (arr3_split sh n lo (lo + wh) c p ltac:(lia) ltac:(lia) ltac:(auto)).
  sep_apply (arr3_split Ews W wn wh (byte_vals wd ++ Zrepeat Vundef (W - wh)) winp ltac:(lia) ltac:(lia)
    ltac:(rewrite Zlength_app, Zlength_byte_vals, Zlength_Zrepeat; lia)).
  Intros.
  replace (lo + wh - lo) with wh by lia.
  sep_apply (arr2_split sh wh (wh - wn) (sublist lo (lo + wh) c) (offset_val lo p) ltac:(lia)
    ltac:(rewrite Zlength_sublist by lia; lia)).
  Intros. apply andp_right; [apply prop_right; auto|].
  rewrite offset_offset_val. replace (wh - (wh - wn)) with wn by lia.
  rewrite !sublist_sublist by lia. replace (0 + lo) with lo by lia.
  replace (wh - wn + lo) with (lo + (wh - wn)) by lia. replace (wh + lo) with (lo + wh) by lia.
  rewrite sublist_app1 by (rewrite ?Zlength_byte_vals; lia).
  rewrite sublist_app1 by (rewrite ?Zlength_byte_vals; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_byte_vals; lia).
  rewrite !sublist_byte_vals. rewrite Zlength_byte_vals.
  replace (wh - Zlength wd) with 0 by lia. replace (W - Zlength wd) with (W - wh) by lia.
  rewrite (sublist_same 0 (W - wh) (Zrepeat Vundef (W - wh))) by list_solve.
  cancel.
Qed.

Lemma gd_post sh n lo (c: list val) p W wd wh wn winp (b1 b2: list Z):
  0 <= lo -> lo + wh <= n -> Zlength c = n -> 0 <= wn <= wh -> wh <= W -> Zlength wd = wh ->
  Zlength b1 = wh - wn -> Zlength b2 = wn ->
  field_compatible (tarray tuchar n) [] p -> field_compatible (tarray tuchar W) [] winp ->
  data_at sh (tarray tuchar lo) (sublist 0 lo c) p *
  data_at sh (tarray tuchar (wh - wn)) (byte_vals b1) (offset_val lo p) *
  data_at sh (tarray tuchar wn) (byte_vals b2) (offset_val (lo + (wh - wn)) p) *
  data_at sh (tarray tuchar (n - (lo + wh))) (sublist (lo + wh) n c) (offset_val (lo + wh) p) *
  data_at Ews (tarray tuchar wn) (byte_vals (sublist 0 wn wd)) winp *
  data_at Ews (tarray tuchar (wh - wn)) (byte_vals (sublist wn wh wd)) (offset_val wn winp) *
  data_at Ews (tarray tuchar (W - wh)) (Zrepeat Vundef (W - wh)) (offset_val wh winp) |--
  data_at sh (tarray tuchar n) (sublist 0 lo c ++ byte_vals (b1 ++ b2) ++ sublist (lo + wh) n c) p *
  data_at Ews (tarray tuchar W) (byte_vals wd ++ Zrepeat Vundef (W - wh)) winp.
Proof.
  intros.
  assert (FCm: field_compatible (tarray tuchar (wh - wn + wn)) [] (offset_val lo p))
    by (apply (fc_sub n); auto; lia).
  replace (offset_val (lo + (wh - wn)) p) with (offset_val (wh - wn) (offset_val lo p))
    by (rewrite offset_offset_val; f_equal; lia).
  sep_apply (arr2_join' sh (wh - wn) wn (byte_vals b1) (byte_vals b2) (offset_val lo p) ltac:(lia) ltac:(lia)
    ltac:(rewrite Zlength_byte_vals; lia) ltac:(rewrite Zlength_byte_vals; lia) FCm).
  replace (wh - wn + wn) with wh by lia.
  sep_apply (arr3_join' sh lo wh (n - (lo + wh)) (sublist 0 lo c) (byte_vals b1 ++ byte_vals b2)
    (sublist (lo + wh) n c) p ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite Zlength_sublist by lia; lia)
    ltac:(rewrite Zlength_app, !Zlength_byte_vals; lia)
    ltac:(rewrite Zlength_sublist by lia; lia)
    ltac:(replace (lo + wh + (n - (lo + wh))) with n by lia; auto)).
  replace (offset_val wh winp) with (offset_val (wn + (wh - wn)) winp) by (f_equal; lia).
  sep_apply (arr3_join' Ews wn (wh - wn) (W - wh) (byte_vals (sublist 0 wn wd)) (byte_vals (sublist wn wh wd))
    (Zrepeat Vundef (W - wh)) winp ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite Zlength_byte_vals, Zlength_sublist by lia; lia)
    ltac:(rewrite Zlength_byte_vals, Zlength_sublist by lia; lia)
    ltac:(rewrite Zlength_Zrepeat by lia; lia)
    ltac:(replace (wn + (wh - wn) + (W - wh)) with W by lia; auto)).
  replace (lo + wh + (n - (lo + wh))) with n by lia.
  replace (wn + (wh - wn) + (W - wh)) with W by lia.
  rewrite app_assoc, <- !byte_vals_app, sublist_rejoin by lia.
  rewrite sublist_same by lia. cancel.
Qed.

Lemma win_facts s: swf s ->
  0 <= i_wnext s <= i_whave s /\ i_whave s <= 2 ^ 23 /\ Zlength (i_wdata s) = i_whave s /\
  (0 < i_whave s -> i_win s = true /\ i_whave s <= 2 ^ i_wbits s) /\
  (i_whave s = 0 -> dict_bytes s = []).
Proof.
  intros W.
  pose proof (sw_wbits _ W). pose proof (sw_whave _ W) as sw_whave0. pose proof (sw_wnext _ W).
  pose proof (sw_wsize _ W) as sw_wsize0. pose proof (sw_wvalid _ W) as sw_wvalid0.
  assert (2 ^ i_wbits s <= 2 ^ 23) by (apply Z.pow_le_mono_r; lia).
  destruct (sw_wdata _ W) as [Hl _].
  split; [|split; [|split; [auto|split]]].
  - destruct sw_wsize0 as [E|[_ E]]; [lia|].
    destruct (Z.eq_dec (i_whave s) (i_wsize s)); [lia|]. assert (i_wnext s = i_whave s) by (apply sw_wvalid0; lia). lia.
  - destruct sw_wsize0 as [E|[_ E]]; lia.
  - intros. destruct sw_wsize0 as [E|[A E]]; [lia|]. split; auto; lia.
  - intros E. unfold dict_bytes. assert (Hd: i_wdata s = []) by (apply Zlength_nil_inv; lia).
    rewrite Hd. rewrite !sublist_of_nil. reflexivity.
Qed.

Ltac getdict_fin :=
  rewrite !if_false by auto; apply andp_right; [apply prop_right; reflexivity|];
  unfold istream_opt, istream, zstrm_at, strm_rep, state_mem; rewrite if_false by auto; rewrite rest_g_split;
  rewrite !prop_true_andp by (first [assumption | split; assumption | unfold live_ok; auto 6]);
  unfold len_rep; try rewrite if_false by auto; try rewrite if_true by auto; cancel.

Lemma body_getdict {E: OracleKind} :
  semax_body Vprog_inflate Gp_getdict f_inflateGetDictionary inflateGetDictionary_spec.
Proof.
  start_function.
  unfold istream_opt.
  destruct (eq_dec strmp nullval) as [Hn|Hn].
  { subst strmp.
    forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
    { rewrite if_true by auto. cancel. }
    rewrite !if_true by auto.
    forward_if. 2: { one_zero. }
    forward.
    unfold is_live; rewrite if_true by auto. entailer!. }
  unfold is_live in *; rewrite if_false in * by auto.
  destruct st as [L|].
  2: { unfold istream, zstrm_at, strm_rep. Intros.
    match goal with |- context [data_at shs t_strm ?v strmp] => remember v as sv eqn:Hsv end.
    assert (Hok: stream_ok_val gv sv nullval) by (subst sv; split3; reflexivity).
    forward_call (strmp, shs, sv, nullval, 0, false, gv).
    { rewrite if_false by auto. cancel. }
    rewrite !if_false by auto.
    forward_if. 2: { one_zero. }
    forward.
    rewrite !if_false by auto. unfold istream_opt, istream, zstrm_at, strm_rep. rewrite if_false by auto.
    apply andp_right; [apply prop_right; reflexivity|]. rewrite prop_true_andp by auto. cancel. }
  unfold istream, zstrm_at, strm_rep, state_mem. rewrite rest_g_split. Intros.
  pose proof H2 as HL. destruct H2 as [Hsp [Hswf [Hmwf [Hhwf Hswf2]]]].
  pose proof (sw_mode _ Hswf) as Hmode.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
  forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z,
     (Vint (Int.repr (zf_ao z)), (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (l_sp L, (zca, (zcf,
     (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)), zf_res z))))))))))))),
     l_sp L, i_mode (l_s L), true, gv).
  { rewrite if_false by auto. cancel. }
  { unfold HEAD, SYNC in Hmode. split; [right; split; [auto | unfold stream_ok_val; auto] |]. all: try (intros; auto); rep_lia. }
  rewrite !if_false by auto.
  replace ((HEAD <=? i_mode (l_s L)) && (i_mode (l_s L) <=? SYNC))%bool with true
    by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
  forward_if. { exfalso. auto. }
  Intros. forward. forward. forward.
  freeze FR := (data_at shs t_strm _ strmp) (field_at Ews t_state (DOT _strm) _ _)
    (field_at Ews t_state (DOT _mode) _ _) (zfuncs gv) (malloc_token Ews t_state _) (rest_g _ _ _ _ _ _) (state_pad _).
  pose proof (win_facts _ Hswf) as Hwf.
  destruct d as [|dsh p lo n c].
  { (* no dictionary buffer *)
    forward_if (temp _t'2 (Vint Int.zero)).
    { forward. entailer!. }
    { forward. entailer!. }
    forward_if (temp _t'2 (Vint Int.zero)). { exfalso; auto. } { forward. entailer!. }
    unfold len_rep at 1; destruct (eq_dec lp nullval) as [Hlp|Hlp].
    { forward_if True.
      { subst lp; exfalso; auto. }
      { forward; entailer!. }
      forward. thaw FR. getdict_fin. }
    { forward_if (PROP () LOCAL ()
        SEP (FRZL FR; field_at Ews t_state (DOT _whave) (Vint (Int.repr (i_whave (l_s L)))) (l_sp L);
             field_at Ews t_state (DOT _wnext) (Vint (Int.repr (i_wnext (l_s L)))) (l_sp L);
             field_at Ews t_state (DOT _window) (if i_win (l_s L) then l_winp L else nullval) (l_sp L);
             win_rep (l_winp L) (l_s L); dict_rep DNull None;
             data_at Tsh tuint (Vint (Int.repr (i_whave (l_s L)))) lp)).
      { forward; forward; entailer!. }
      { exfalso; auto. }
      forward. thaw FR. getdict_fin. } }
  simpl dict_ptr in *. destruct H as (Hdsh & Hp & Hlo & Hlon & Hc & Hnmax).
  destruct Hwf as (Hwn & Hwh23 & Hwl & Hwpos & Hw0).
  destruct (Z.eq_dec (i_whave (l_s L)) 0) as [E0|E0].
  { (* empty window *)
    assert (ED: dict_rep (DBuf dsh p lo n c) (Some (dict_bytes (l_s L))) = dict_rep (DBuf dsh p lo n c) None).
    { simpl. rewrite (Hw0 E0). simpl. rewrite Z.add_0_r, sublist_rejoin, sublist_same by lia. reflexivity. }
    forward_if (temp _t'2 (Vint Int.zero)).
    { exfalso. rewrite E0 in *. auto. }
    { forward. entailer!. }
    forward_if (temp _t'2 (Vint Int.zero)). { exfalso; auto. } { forward. entailer!. }
    rewrite <- ED.
    unfold len_rep at 1; destruct (eq_dec lp nullval) as [Hlp|Hlp].
    { forward_if True.
      { subst lp; exfalso; auto. }
      { forward; entailer!. }
      forward. thaw FR. getdict_fin. }
    { forward_if (PROP () LOCAL ()
        SEP (FRZL FR; field_at Ews t_state (DOT _whave) (Vint (Int.repr (i_whave (l_s L)))) (l_sp L);
             field_at Ews t_state (DOT _wnext) (Vint (Int.repr (i_wnext (l_s L)))) (l_sp L);
             field_at Ews t_state (DOT _window) (if i_win (l_s L) then l_winp L else nullval) (l_sp L);
             win_rep (l_winp L) (l_s L); dict_rep (DBuf dsh p lo n c) (Some (dict_bytes (l_s L)));
             data_at Tsh tuint (Vint (Int.repr (i_whave (l_s L)))) lp)).
      { forward; forward; entailer!. }
      { exfalso; auto. }
      forward. thaw FR. getdict_fin. } }
  (* copy *)
  assert (Hpos: 0 < i_whave (l_s L)) by lia. destruct (Hwpos Hpos) as [Hwin Hwb].
  assert (HV: data_at dsh (tarray tuchar n) c p |-- valid_pointer (offset_val lo p))
    by (apply arr_valid; auto; lia).
  forward_if (temp _t'2 (Vint Int.one)).
  { forward. entailer!. destruct p; try contradiction; reflexivity. }
  { exfalso. apply E0. rewrite <- (Int.unsigned_repr (i_whave (l_s L))) by rep_lia.
    match goal with H: Int.repr _ = Int.zero |- _ => rewrite H end. reflexivity. }
  destruct (sw_wdata _ Hswf) as [_ Hbo].
  forward_if (PROP () LOCAL (temp _state (l_sp L); temp _dictLength lp)
     SEP (FRZL FR; field_at Ews t_state (DOT _whave) (Vint (Int.repr (i_whave (l_s L)))) (l_sp L);
          field_at Ews t_state (DOT _wnext) (Vint (Int.repr (i_wnext (l_s L)))) (l_sp L);
          field_at Ews t_state (DOT _window) (if i_win (l_s L) then l_winp L else nullval) (l_sp L);
          win_rep (l_winp L) (l_s L); dict_rep (DBuf dsh p lo n c) (Some (dict_bytes (l_s L))); len_rep lp None)).
  2: { exfalso. apply Int.one_not_zero. auto. }
  { unfold win_rep. rewrite Hwin. Intros. rewrite Hwl. unfold dict_rep.
    sep_apply (gd_pre dsh n lo c p (2 ^ i_wbits (l_s L)) (i_wdata (l_s L)) (i_whave (l_s L))
       (i_wnext (l_s L)) (l_winp L) ltac:(lia) ltac:(lia) ltac:(auto) ltac:(lia) ltac:(lia) ltac:(lia)).
    Intros.
    forward. forward. forward. forward.
    forward_call (dsh, offset_val lo p, Ews, offset_val (i_wnext (l_s L)) (l_winp L),
                  sublist (i_wnext (l_s L)) (i_whave (l_s L)) (i_wdata (l_s L))).
    { entailer!. simpl. rewrite Zlength_sublist by lia. rewrite Int.unsigned_repr by rep_lia. reflexivity. }
    { rewrite Zlength_sublist by lia. cancel. }
    { split; [apply Forall_sublist; auto | rewrite Zlength_sublist by lia; rep_lia]. }
    rewrite !Zlength_sublist by lia.
    forward. forward. forward. forward.
    forward_call (dsh, offset_val (lo + (i_whave (l_s L) - i_wnext (l_s L))) p, Ews, l_winp L,
                  sublist 0 (i_wnext (l_s L)) (i_wdata (l_s L))).
    { entailer!. simpl. clear - Hwn Hwh23 Hlo Hp Hwl. destruct p; try contradiction.
      rewrite Zlength_sublist by lia. rewrite Int.unsigned_repr by rep_lia. simpl.
      unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia. rewrite Z.sub_0_r.
      f_equal. f_equal. rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
      rewrite Ptrofs.mul_commut, Ptrofs.mul_one, Ptrofs.neg_repr, ptrofs_add_repr. f_equal; lia. }
    { rewrite Zlength_sublist by lia. rewrite Z.sub_0_r. cancel. }
    { split; [apply Forall_sublist; auto | rewrite Zlength_sublist by lia; rep_lia]. }
    rewrite !Zlength_sublist by lia. rewrite !Z.sub_0_r.
    sep_apply (gd_post dsh n lo c p (2 ^ i_wbits (l_s L)) (i_wdata (l_s L)) (i_whave (l_s L))
       (i_wnext (l_s L)) (l_winp L) (sublist (i_wnext (l_s L)) (i_whave (l_s L)) (i_wdata (l_s L)))
       (sublist 0 (i_wnext (l_s L)) (i_wdata (l_s L))) ltac:(lia) ltac:(lia) ltac:(auto) ltac:(lia) ltac:(lia)
       ltac:(lia) ltac:(rewrite Zlength_sublist by lia; lia) ltac:(rewrite Zlength_sublist by lia; lia) H3 H4).
    unfold win_rep, dict_rep. rewrite Hwin, Hwl.
    assert (ZD: Zlength (dict_bytes (l_s L)) = i_whave (l_s L))
      by (unfold dict_bytes; rewrite Zlength_app, !Zlength_sublist by lia; lia).
    rewrite ZD. unfold dict_bytes.
    entailer!. }
  unfold len_rep at 1; destruct (eq_dec lp nullval) as [Hlp|Hlp].
  { forward_if True.
    { subst lp; exfalso; auto. }
    { forward; entailer!. }
    forward. thaw FR. getdict_fin. }
  { forward_if (PROP () LOCAL ()
      SEP (FRZL FR; field_at Ews t_state (DOT _whave) (Vint (Int.repr (i_whave (l_s L)))) (l_sp L);
           field_at Ews t_state (DOT _wnext) (Vint (Int.repr (i_wnext (l_s L)))) (l_sp L);
           field_at Ews t_state (DOT _window) (if i_win (l_s L) then l_winp L else nullval) (l_sp L);
           win_rep (l_winp L) (l_s L); dict_rep (DBuf dsh p lo n c) (Some (dict_bytes (l_s L)));
           data_at Tsh tuint (Vint (Int.repr (i_whave (l_s L)))) lp)).
    { forward; forward; entailer!. }
    { exfalso; auto. }
    forward. thaw FR. getdict_fin. }
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* inflateSetDictionary: the state after the window update                                       *)

(* the fields that the window update does not touch *)
Definition wfree (s: istate) :=
  (i_mode s, i_last s, i_wrap s, i_flags s, i_dmax s, i_check s, i_total s, i_head s, i_wbits s,
   i_hold s, i_bits s, i_length s, i_offset s, i_extra s, i_lencode s, i_distcode s, i_lenbits s,
   i_distbits s, i_ncode s, i_nlen s, i_ndist s, i_have s, i_next s, i_lens s, i_codes s, i_sane s,
   i_back s, i_was s).

Lemma wfree_wdata s v: wfree (set_i_wdata s v) = wfree s. Proof. reflexivity. Qed.
Lemma wfree_whave s v: wfree (set_i_whave s v) = wfree s. Proof. reflexivity. Qed.
Lemma wfree_wnext s v: wfree (set_i_wnext s v) = wfree s. Proof. reflexivity. Qed.
Lemma wfree_wsize s v: wfree (set_i_wsize s v) = wfree s. Proof. reflexivity. Qed.
Lemma wfree_win s v: wfree (set_i_win s v) = wfree s. Proof. reflexivity. Qed.
Lemma wfree_havedict s v: wfree (set_i_havedict s v) = wfree s. Proof. reflexivity. Qed.

Lemma wfree_uw s data: wfree (updatewindow s data) = wfree s.
Proof.
  unfold updatewindow. cbv zeta.
  destruct (i_wsize s =? 0);
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  rewrite ?wfree_wdata, ?wfree_whave, ?wfree_wnext, ?wfree_wsize; reflexivity.
Qed.

Lemma modewf_wfree s s': wfree s' = wfree s -> modewf s -> modewf s'.
Proof.
  intros E M. destruct s, s'. unfold wfree in E; cbn in E. injection E; intros; subst.
  destruct M; constructor; assumption.
Qed.

Lemma uw_window s data: swf s -> bytes_ok data ->
  let s' := updatewindow s data in
  i_wsize s' = 2 ^ i_wbits s /\ 0 <= i_whave s' <= i_wsize s' /\
  0 <= i_wnext s' < i_wsize s' /\ (i_whave s' < i_wsize s' -> i_wnext s' = i_whave s') /\
  Zlength (i_wdata s') = i_whave s' /\ bytes_ok (i_wdata s').
Proof.
  intros W B. cbv zeta.
  pose proof (sw_wbits _ W). pose proof (sw_whave _ W). pose proof (sw_wnext _ W).
  pose proof (sw_wsize _ W). pose proof (sw_wvalid _ W). destruct (sw_wdata _ W) as [Hl Hb].
  assert (P: 0 < 2 ^ i_wbits s) by (apply Z.pow_pos_nonneg; lia).
  set (s1 := if i_wsize s =? 0 then set_i_whave (set_i_wnext (set_i_wsize s (2 ^ i_wbits s)) 0) 0 else s).
  assert (S1: i_wsize s1 = 2 ^ i_wbits s /\ 0 <= i_whave s1 <= i_wsize s1 /\
              0 <= i_wnext s1 < i_wsize s1 /\ (i_whave s1 < i_wsize s1 -> i_wnext s1 = i_whave s1) /\
              Zlength (i_wdata s1) = i_whave s1 /\ bytes_ok (i_wdata s1)).
  { subst s1. destruct (Z.eqb_spec (i_wsize s) 0) as [E|E]; cbn.
    - assert (Zlength (i_wdata s) = 0) by lia. repeat split; auto; lia.
    - destruct H2 as [E'|[_ E']]; [lia|]. repeat split; auto; lia. }
  replace (updatewindow s data) with
    (let copy := Zlength data in
     let ws := i_wsize s1 in
     let w := i_wdata s1 in
     if ws <=? copy then
       set_i_wdata (set_i_whave (set_i_wnext s1 0) ws) (sublist (copy - ws) copy data)
     else
       let dist := Z.min (ws - i_wnext s1) copy in
       let src1 := sublist 0 dist data in
       let full := sublist 0 (i_wnext s1) w ++ src1 ++ sublist (i_wnext s1 + dist) (Zlength w) w in
       let copy' := copy - dist in
       if negb (copy' =? 0) then
         let src2 := sublist dist copy data in
         set_i_wdata (set_i_whave (set_i_wnext s1 copy') ws) (src2 ++ sublist copy' (Zlength full) full)
       else
         let wn := i_wnext s1 + dist in
         let wh := if i_whave s1 <? ws then i_whave s1 + dist else i_whave s1 in
         set_i_wdata (set_i_whave (set_i_wnext s1 (if wn =? ws then 0 else wn)) wh) full)
    by reflexivity.
  clearbody s1. cbv zeta.
  destruct S1 as (A1 & A2 & A3 & A4 & A5 & A6).
  destruct s1 as [m1 l1 wr1 hd1 fl1 dm1 ck1 tt1 hh1 wb1 ws wh wn wi1 w ho1 bi1 le1 of1 ex1 lc1 dc1 lb1 db1
                  nc1 nl1 nd1 hv1 nx1 ls1 cd1 sa1 ba1 wa1].
  cbn in A1, A2, A3, A4, A5, A6. cbn [i_wsize i_whave i_wnext i_wdata].
  remember (Zlength data) as copy eqn:Ecopy.
  assert (0 <= copy) by (subst copy; apply Zlength_nonneg).
  destruct (Z.leb_spec ws copy).
  { cbn [i_wsize i_whave i_wnext i_wdata set_i_wdata set_i_whave set_i_wnext]. rewrite A1.
    repeat split; try lia.
    - rewrite Zlength_sublist by lia. lia.
    - apply Forall_sublist; auto. }
  remember (Z.min (ws - wn) copy) as dist eqn:Edist.
  assert (D: 0 <= dist <= ws - wn /\ dist <= copy) by (subst dist; lia).
  assert (LF: Zlength (sublist 0 wn w ++ sublist 0 dist data ++ sublist (wn + dist) (Zlength w) w) =
              if wh <? ws then wh + dist else ws).
  { destruct (Z.ltb_spec wh ws).
    - rewrite A4 in * by lia. rewrite !Zlength_app, !Zlength_sublist by lia.
      rewrite (sublist_nil_gen w) by lia. rewrite Zlength_nil. lia.
    - rewrite !Zlength_app, !Zlength_sublist by lia. lia. }
  assert (BF: bytes_ok (sublist 0 wn w ++ sublist 0 dist data ++ sublist (wn + dist) (Zlength w) w)).
  { apply Forall_app; split; [|apply Forall_app; split]; apply Forall_sublist; auto. }
  remember (sublist 0 wn w ++ sublist 0 dist data ++ sublist (wn + dist) (Zlength w) w) as full eqn:Efull.
  destruct (Z.eqb_spec (copy - dist) 0) as [C0|C0];
    cbn [negb i_wsize i_whave i_wnext i_wdata set_i_wdata set_i_whave set_i_wnext].
  - rewrite LF.
    repeat match goal with
      | |- context [if (?a <? ?b) then _ else _] => destruct (Z.ltb_spec a b)
      | |- context [if (?a =? ?b) then _ else _] => destruct (Z.eqb_spec a b) end;
    repeat split; auto; lia.
  - assert (dist = ws - wn) by lia.
    assert (LF': Zlength full = ws) by (rewrite LF; destruct (Z.ltb_spec wh ws); [specialize (A4 ltac:(lia))|]; lia).
    repeat split; try lia.
    + rewrite Zlength_app, !Zlength_sublist by lia. lia.
    + apply Forall_app; split; apply Forall_sublist; auto.
Qed.


Lemma swf_setdict s dict: swf s -> bytes_ok dict -> swf (setdict_s s dict).
Proof.
  intros W B. pose proof (uw_window s dict W B) as U. cbv zeta in U.
  pose proof (wfree_uw s dict) as E. unfold setdict_s.
  remember (updatewindow s dict) as s2 eqn:Hs2. clear Hs2.
  destruct s, s2. unfold wfree in E; cbn in E, U. injection E; intros; subst.
  destruct W; cbn in *.
  destruct U as (U1 & U2 & U3 & U4 & U5 & U6).
  constructor; cbn; auto; try lia.
Qed.

Lemma modewf_setdict s dict: modewf s -> modewf (setdict_s s dict).
Proof.
  intros M. apply (modewf_wfree s); auto. unfold setdict_s.
  rewrite wfree_havedict, wfree_win. apply wfree_uw.
Qed.

Lemma setdict_keep s dict:
  i_wbits (setdict_s s dict) = i_wbits s /\ i_wrap (setdict_s s dict) = i_wrap s /\
  i_mode (setdict_s s dict) = i_mode s /\ i_head (setdict_s s dict) = i_head s /\
  i_flags (setdict_s s dict) = i_flags s.
Proof.
  pose proof (wfree_uw s dict) as E. unfold setdict_s.
  remember (updatewindow s dict) as s2 eqn:Hs2. clear Hs2.
  destruct s, s2. unfold wfree in E; cbn in E. injection E; intros; subst. cbn. auto.
Qed.

Lemma swf3_setdict s dict: swf3 s -> (i_mode s = HEAD -> i_wrap s = 0) -> swf3 (setdict_s s dict).
Proof.
  intros W HW. pose proof (wfree_uw s dict) as E. unfold setdict_s.
  remember (updatewindow s dict) as s2 eqn:Hs2. clear Hs2.
  destruct s, s2. unfold wfree in E; cbn in E. injection E; intros; subst.
  destruct W; constructor; cbn in *; try assumption.
  intros A B C. exfalso. apply C, HW, A.
Qed.

Lemma setdict_update s dict: setdict_check s dict = SDUpdate -> i_wrap s = 0 \/ i_mode s = DICT.
Proof.
  unfold setdict_check. destruct (Z.eqb_spec (i_wrap s) 0); auto.
  destruct (Z.eqb_spec (i_mode s) DICT); auto. cbn. discriminate.
Qed.

Lemma live_setdict L dict w: live_ok L -> bytes_ok dict -> setdict_check (l_s L) dict = SDUpdate ->
  live_ok (Live (l_sp L) w (setdict_s (l_s L) dict) (l_h L) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
Proof.
  intros (A & B & C & D & E & F & G & H & I) Hb U. apply setdict_update in U.
  destruct (setdict_keep (l_s L) dict) as (K1 & K2 & K3 & K4 & K5).
  assert (WB: i_wbits (l_s L) <> 0).
  { intro W0. destruct (G W0) as [G1 _]. destruct U as [U|U]; [exact (land3_wrap _ G1 U)|].
    destruct (I W0 (land3_wrap _ G1)) as [_ M]. rewrite U in M. clear - M. cbv in M. repeat destruct M as [M|M]; discriminate. }
  unfold live_ok; cbn [l_sp l_s l_h l_hsh l_xb l_nb l_cb].
  split; [auto|]. split; [apply swf_setdict; auto|]. split; [apply modewf_setdict; auto|].
  split; [auto|]. split.
  { apply swf3_setdict; auto. intros Hh. destruct U as [U|U]; auto. rewrite Hh in U. discriminate. }
  split; [auto|].
  split; [intros Hw; rewrite K1 in Hw; exfalso; exact (WB Hw)|].
  split; [rewrite K4; exact H|].
  intros Hw; rewrite K1 in Hw; exfalso; exact (WB Hw).
Qed.

Lemma live_mem L: live_ok L -> live_ok (set_l_s L (set_i_mode (l_s L) MEM)).
Proof.
  intros (A & W & M & D & W3 & F & G & H & I).
  assert (NM: forall P: Prop, decode_mode MEM \/ MEM = LENLENS \/ MEM = CODELENS \/ MEM = LENEXT \/
                MEM = DISTEXT \/ MEM = DIST \/ MEM = MATCH \/ MEM = HEAD -> P).
  { intros P X. exfalso. clear - X. cbv in X. repeat destruct X as [X|X]; discriminate. }
  unfold live_ok, set_l_s; cbn [l_sp l_s l_h l_hsh].
  split; [auto|]. split; [|split; [|split; [auto|split; [|split; [auto|split; [|split]]]]]].
  - destruct W; constructor; cbn [set_i_mode i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was] in *; try assumption.
    clear. cbv; split; discriminate.
  - constructor; cbn [set_i_mode i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was]; intros; try (apply NM; tauto).
    split; [|split]; intros; apply NM; tauto.
  - destruct W3; constructor; cbn [set_i_mode i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was] in *; try assumption; intros; apply NM; tauto.
  - cbn [set_i_mode i_win i_wbits i_wrap]. exact G.
  - cbn [set_i_mode i_head]. exact H.
  - cbn [set_i_mode i_wbits i_wrap i_flags i_mode]. intros W0 W1. split; [apply (I W0 W1)|]. auto.
Qed.


Lemma neq_dict_val m: HEAD <= m <= SYNC ->
  Vint (if m =? DICT then Int.zero else Int.one) = bool2val (negb (Int.eq (Int.repr m) (Int.repr 16190))).
Proof.
  intros. unfold DICT. destruct (Z.eqb_spec m 16190). { subst; reflexivity. }
  rewrite Int.eq_false; [reflexivity|]. intro X. apply repr_inj_signed in X; [lia | |];
  unfold HEAD, SYNC in *; rep_lia.
Qed.

Lemma repr_zero_u x: 0 <= x <= Int.max_unsigned -> Int.repr x = Int.zero -> x = 0.
Proof. intros. apply repr_inj_unsigned in H0; rep_lia. Qed.

Lemma sd_stream s dict:
  (if i_wrap s =? 0 then Int.repr 0 else if i_mode s =? DICT then Int.repr 0 else Int.one) <> Int.zero ->
  setdict_check s dict = SDStream.
Proof.
  unfold setdict_check. destruct (i_wrap s =? 0), (i_mode s =? DICT); cbn; intro H; try reflexivity;
  exfalso; apply H; reflexivity.
Qed.

Lemma sd_nstream s dict:
  Vint (if i_wrap s =? 0 then Int.zero else if i_mode s =? DICT then Int.zero else Int.one) = Vint Int.zero ->
  setdict_check s dict <> SDStream.
Proof.
  unfold setdict_check. destruct (i_wrap s =? 0), (i_mode s =? DICT); cbn;
  try (destruct (adler32_z_val 1 dict =? i_check s); cbn; congruence); try congruence.
  intro X. inversion X.
Qed.


Lemma sd_update_nd s d: setdict_check s d <> SDStream -> i_mode s <> DICT -> setdict_check s d = SDUpdate.
Proof.
  unfold setdict_check. destruct (Z.eqb_spec (i_mode s) DICT); [congruence|].
  destruct (i_wrap s =? 0); cbn; auto; congruence.
Qed.

Lemma sd_update_d s d: i_mode s = DICT -> adler32_z_val 1 d = i_check s -> setdict_check s d = SDUpdate.
Proof.
  intros M A. unfold setdict_check. rewrite M, A, Z.eqb_refl, Z.eqb_refl. cbn.
  rewrite andb_false_r. reflexivity.
Qed.

Lemma sd_data s d: i_mode s = DICT -> adler32_z_val 1 d <> i_check s -> setdict_check s d = SDData.
Proof.
  intros M A. unfold setdict_check. rewrite M, Z.eqb_refl. apply Z.eqb_neq in A. rewrite A. cbn.
  rewrite andb_false_r. reflexivity.
Qed.

Lemma state_rep_winp gv sp strmp headp winp s:
  state_rep gv sp strmp headp winp s = state_rep gv sp strmp headp (if i_win s then winp else nullval) s.
Proof. unfold state_rep. destruct (i_win s); reflexivity. Qed.

Lemma win_rep_winp winp s: win_rep winp s = win_rep (if i_win s then winp else nullval) s.
Proof. unfold win_rep. destruct (i_win s); reflexivity. Qed.

Lemma ptr_add_dict p lo k: isptr p -> 0 <= lo -> 0 <= k -> lo + k <= Ptrofs.max_unsigned -> k <= Int.max_unsigned ->
  force_val (sem_add_ptr_int tuchar Unsigned (offset_val lo p) (Vint (Int.repr k))) = offset_val (lo + k) p.
Proof.
  intros P L K M I. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int.
  rewrite Int.unsigned_repr by lia. rewrite Ptrofs.mul_commut, Ptrofs.mul_one, ptrofs_add_repr. reflexivity.
Qed.

Ltac sd_same HS :=
  unfold on_live, is_live, fst3, snd3, thd3; rewrite !if_false by auto; unfold setdict_f; rewrite HS;
  cbn [fst snd]; unfold istream_opt, istream, zstrm_at, strm_rep, state_mem; rewrite if_false by auto;
  rewrite rest_s_split; apply andp_right; [apply prop_right; reflexivity|];
  rewrite !prop_true_andp by (first [assumption | split; assumption]); cancel.

(* the calls of adler32 (Adler32.CS): its byte arrays are moved to its compspecs by da_cs/mt_cs before the
   call; Floyd's change_compspecs (on the whole precondition) does not terminate in reasonable time here *)
Lemma da_cs sh n (c: list val) p:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) c p = @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) c p.
Proof.
  assert (E: @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) c = @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) c).
  { apply data_at_change_composite; [apply JMeq_refl | prove_cs_preserve_type]. }
  rewrite E. reflexivity.
Qed.

Lemma mt_cs sh n p:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) p = @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) p.
Proof.
  assert (E: @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) = @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n)).
  { apply malloc_token_change_composite; prove_cs_preserve_type. }
  rewrite E. reflexivity.
Qed.

Ltac change_compspecs cs ::= idtac.

(* Floyd's simplify_remove_localdef_temp (simpl on ident_eq of the large $"..." idents) does not finish
   here: remove the temp by rewriting instead *)
Lemma rlt_nil i: remove_localdef_temp i [] = [].
Proof. reflexivity. Qed.
Lemma rlt_gvars i g l: remove_localdef_temp i (gvars g :: l) = gvars g :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rlt_same i v l: remove_localdef_temp i (temp i v :: l) = remove_localdef_temp i l.
Proof. simpl. unfold rlt_ident_eq. rewrite if_true by auto. reflexivity. Qed.
Lemma rlt_cons i j v l: i <> j -> remove_localdef_temp i (temp j v :: l) = temp j v :: remove_localdef_temp i l.
Proof. intros. simpl. unfold rlt_ident_eq. rewrite if_false by auto. reflexivity. Qed.

Ltac simplify_remove_localdef_temp ::=
  repeat first [ rewrite rlt_nil | rewrite rlt_gvars | rewrite rlt_same
               | rewrite rlt_cons by (let X := fresh in intro X; discriminate X) ].

Lemma state_rep_fold gv sp strmp headp winp s:
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  rest_s gv sp strmp headp winp s |-- state_rep gv sp strmp headp winp s.
Proof. rewrite rest_s_split. cancel. Qed.

Lemma rest_g_mode gv sp strmp headp winp s m:
  rest_g gv sp strmp headp winp (set_i_mode s m) = rest_g gv sp strmp headp winp s.
Proof. reflexivity. Qed.

Lemma state_rep_hd gv sp strmp headp winp s v: state_rep gv sp strmp headp winp (set_i_havedict s v) =
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _havedict) (zv v) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  rest_s gv sp strmp headp winp s.
Proof. rewrite rest_s_split. reflexivity. Qed.

Lemma win_rep_hd winp s v: win_rep winp (set_i_havedict s v) = win_rep winp s.
Proof. reflexivity. Qed.

Lemma body_setdict {E: OracleKind} :
  semax_body Vprog_inflate Gp_setdict f_inflateSetDictionary inflateSetDictionary_spec.
Proof.
  start_function.
  unfold istream_opt.
  destruct (eq_dec strmp nullval) as [Hn|Hn].
  { subst strmp.
    forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
    { rewrite if_true by auto. cancel. }
    rewrite !if_true by auto.
    forward_if. 2: { one_zero. }
    forward.
    Exists false nullval. unfold on_live, is_live; rewrite ?if_true by auto. entailer!. }
  destruct st as [L|].
  2: { unfold istream, zstrm_at, strm_rep. Intros.
    match goal with |- context [data_at shs t_strm ?v strmp] => remember v as sv eqn:Hsv end.
    assert (Hok: stream_ok_val gv sv nullval) by (subst sv; split3; reflexivity).
    forward_call (strmp, shs, sv, nullval, 0, false, gv).
    { rewrite if_false by auto. cancel. }
    rewrite !if_false by auto.
    forward_if. 2: { one_zero. }
    forward.
    Exists false nullval.
    unfold on_live, is_live, fst3, snd3, thd3. rewrite !if_false by auto. cbn [fst snd].
    unfold istream_opt, istream, zstrm_at, strm_rep. rewrite if_false by auto.
    apply andp_right; [apply prop_right; reflexivity|]. rewrite prop_true_andp by auto. cancel. }
  unfold istream, zstrm_at, strm_rep, state_mem. rewrite rest_s_split. Intros.
  match goal with H: live_ok L |- _ => pose proof H as HL; destruct H as [Hsp [Hswf [Hmwf [Hhwf Hswf2]]]] end.
  pose proof (sw_mode _ Hswf) as Hmode. pose proof (sw_wrap_range _ Hswf) as Hwrap.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
  forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z,
     (Vint (Int.repr (zf_ao z)), (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (l_sp L, (zca, (zcf,
     (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)), zf_res z))))))))))))),
     l_sp L, i_mode (l_s L), true, gv).
  { rewrite if_false by auto. cancel. }
  { unfold HEAD, SYNC in Hmode. split; [right; split; [auto | unfold stream_ok_val; auto] |]. all: try (intros; auto); rep_lia. }
  rewrite !if_false by auto.
  replace ((HEAD <=? i_mode (l_s L)) && (i_mode (l_s L) <=? SYNC))%bool with true
    by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
  forward_if. { exfalso. auto. }
  Intros. forward. forward. forward.
  forward_if (temp _t'2 (Vint (if i_wrap (l_s L) =? 0 then Int.zero
                               else if i_mode (l_s L) =? DICT then Int.zero else Int.one))).
  { assert (W0: i_wrap (l_s L) <> 0)
      by (first [assumption | lia]).
    forward. forward. entailer!. rewrite (proj2 (Z.eqb_neq _ _) W0). apply neq_dict_val; auto. }
  { assert (W0: i_wrap (l_s L) = 0)
      by (first [assumption | lia]).
    forward. entailer!. rewrite W0. reflexivity. }
  forward_if (setdict_check (l_s L) dict <> SDStream).
  { assert (HS: setdict_check (l_s L) dict = SDStream)
      by (apply sd_stream; match goal with H: (if _ then _ else _) <> Int.zero |- _ => exact H end).
    forward. Exists false nullval. sd_same HS. }
  { forward. entailer!. match goal with H: (if _ then _ else _) = Int.zero, H2: setdict_check _ _ = SDStream |- _ => exact (sd_nstream _ _ (f_equal Vint H) H2) end. }
  Intros. forward.
  forward_if (setdict_check (l_s L) dict = SDUpdate).
  { assert (HD: i_mode (l_s L) = DICT).
    { match goal with X: Int.repr (i_mode _) = Int.repr 16190 |- _ => apply repr_inj_signed in X end;
        [unfold DICT; lia | unfold HEAD, SYNC in *; rep_lia | rep_lia]. }
    freeze FA := (data_at shs t_strm _ _) (field_at _ _ (DOT _strm) _ _) (field_at _ _ (DOT _mode) _ _)
      (zfuncs _) (malloc_token Ews t_state _) (field_at _ _ (DOT _wrap) _ _).
    freeze FB := (field_at _ _ (DOT _havedict) _ _) (rest_s _ _ _ _ _ _) (win_rep _ _) (state_pad _) (mem_mgr _).
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      apply semax_pre with (PROPx P (LOCALx Q (SEPx (emp :: emp :: R)))); [entailer! |] end.
    forward_call (0, nullval, 0, true, dsh, p, lo, n, c, @nil Z, false, Ews).
    rewrite da_cs, mt_cs.
    forward_call (1, offset_val lo p, Zlength dict, false, dsh, p, lo, n, c, dict, tok, Ews).
    { split; [unfold cbuf_ok; repeat split; auto; lia|].
      intros _ T. destruct (zlt 0 n); auto.
      assert (n = 0) by (pose proof (Zlength_nonneg c); lia). rewrite H3 in T by auto. discriminate. }
    rewrite <- da_cs, <- mt_cs. thaw FB. thaw FA.
    pose proof (adler32_z_val_range 1 dict H7) as AR. pose proof (sw_check _ Hswf) as CR.
    forward.
    forward_if (adler32_z_val 1 dict = i_check (l_s L)).
    { assert (HS: setdict_check (l_s L) dict = SDData).
      { apply sd_data; auto. intro X. rewrite X in *. contradiction. }
      forward. Exists false nullval. sd_same HS. }
    { forward. entailer!.
      match goal with X: Int64.eq _ _ = true |- _ => apply Int64.same_if_eq in X;
        apply repr_inj_unsigned64 in X; [exact X | rep_lia | unfold lrange in CR; rep_lia] end. }
    entailer!. apply sd_update_d; auto. }
  { forward. entailer!. apply sd_update_nd; auto. intro X.
    match goal with Y: Int.repr (i_mode _) <> _ |- _ => apply Y; rewrite X; reflexivity end. }
  Intros. match goal with X: setdict_check _ _ = SDUpdate |- _ => rename X into HU end.
  sep_apply (state_rep_fold gv (l_sp L) strmp (l_headp L) (l_winp L) (l_s L)).
  rewrite (state_rep_winp gv (l_sp L) strmp (l_headp L) (l_winp L)), (win_rep_winp (l_winp L)).
  change (let (l_sp, _, _, _, _, _, _, _, _) := L in l_sp) with (l_sp L).
  match goal with |- context [data_at shs t_strm ?v strmp] =>
    forward_call (gv, shs, strmp, v, l_sp L, l_headp L, (if i_win (l_s L) then l_winp L else nullval),
                  l_s L, dsh, p, n, c, lo + Zlength dict, dict) end.
  { subst zca zcf. split; [unfold stream_ok_val2; auto|].
    split; [replace (lo + Zlength dict - Zlength dict) with lo by lia; exact H6|].
    intros W; rewrite W; reflexivity. }
  Intros vret. destruct vret as [r winp']. cbn [fst snd] in *.
  match goal with X: (r = 0 /\ _) \/ _ |- _ => destruct X as [[R0 HW] | (R1 & HW & HN)] end.
  - subst r. rewrite Z.eqb_refl.
    match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ => forward_if (PROPx [] (LOCALx Q (SEPx R))) end.
    { exfalso. match goal with X: Int.repr 0 <> Int.zero |- _ => apply X; reflexivity end. }
    { forward. entailer!. }
    rewrite (rest_s_split gv (l_sp L) strmp (l_headp L) winp' (set_i_win (updatewindow (l_s L) dict) true)).
    Intros.
    forward. forward.
    Exists true winp'.
    unfold on_live, is_live, fst3, snd3, thd3; rewrite !if_false by auto; unfold setdict_f; rewrite HU.
    destruct (i_win (l_s L)) eqn:HW0; cbn [fst snd].
    + specialize (HW eq_refl). subst winp'.
      unfold istream_opt, istream, zstrm_at, strm_rep, state_mem; rewrite if_false by auto.
      unfold set_l_s; cbn [l_sp l_winp l_s l_headp l_h l_hsh l_xb l_nb l_cb].
      apply andp_right; [apply prop_right; reflexivity|].
      rewrite !prop_true_andp by (first [split; assumption | apply live_setdict; auto]).
      unfold setdict_s. rewrite state_rep_hd, win_rep_hd. entailer!.
    + unfold istream_opt, istream, zstrm_at, strm_rep, state_mem; rewrite if_false by auto.
      unfold set_l_winp, set_l_s; cbn [l_sp l_winp l_s l_headp l_h l_hsh l_xb l_nb l_cb].
      apply andp_right; [apply prop_right; reflexivity|].
      rewrite !prop_true_andp by (first [split; assumption | apply live_setdict; auto]).
      unfold setdict_s. rewrite state_rep_hd, win_rep_hd. entailer!.
  - subst r winp'. rewrite (proj2 (Z.eqb_neq 1 0)) by lia.
    forward_if (PROP (False) LOCAL () SEP ()).
    { rewrite (rest_g_split gv (l_sp L) strmp (l_headp L) nullval (l_s L)). Intros.
      forward. forward.
      Exists false nullval.
      unfold on_live, is_live, fst3, snd3, thd3; rewrite !if_false by auto; unfold setdict_f; rewrite HU, HW.
      cbn [fst snd].
      unfold istream_opt, istream, zstrm_at, strm_rep, state_mem; rewrite if_false by auto.
      unfold set_l_s; cbn [l_sp l_winp l_s l_headp l_h l_hsh l_xb l_nb l_cb].
      rewrite (rest_g_split gv (l_sp L) strmp (l_headp L) (l_winp L) (set_i_mode (l_s L) MEM)).
      rewrite rest_g_mode. unfold win_rep. cbn [i_whave i_wnext i_win i_mode set_i_mode]. rewrite HW.
      apply andp_right; [apply prop_right; reflexivity|].
      rewrite !prop_true_andp by (first [split; assumption | exact (live_mem L HL)]).
      unfold win_rep in *. rewrite ?HW. entailer!; unfold rest_g; apply derives_refl. }
    { exfalso. match goal with X: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact X end. }
Qed.

Lemma api5_dict : api_dict_stmt.
Proof. intros E. split; [apply body_getdict | apply body_setdict]. Qed.
