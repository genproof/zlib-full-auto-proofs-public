(** * fill_window, fragment S_slide (FWKit.v) against its model step. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.FWKit.
Require Import Zlib.proof.zutil.Libc.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** Window slices (after StoredWinKit.v of deflate_stored's proof) *)
Lemma mb_definedb_spec b lo hi : lo <= hi -> mb_definedb b lo hi = true ->
  0 <= lo /\ hi <= Zlength (mb_val b) /\ forall i, lo <= i < hi -> Znth i (mb_def b) = true.
Proof.
  unfold mb_definedb. intros Hle H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1, H2. split; [lia|split; [lia|]].
  intros i Hi. rewrite forallb_forall in H3. apply (H3 i).
  replace i with (lo + Z.of_nat (Z.to_nat (i - lo))) at 1 by lia.
  apply (in_map (fun k : nat => lo + Z.of_nat k)). apply in_seq. lia.
Qed.

(** A block read of the window: the bytes, defined, in range. *)
Lemma mb_read_vals b lo n bytes : mb_ok b -> mb_read b lo n = Some bytes ->
  bytes = sublist lo (lo + n) (mb_val b) /\ Zlength bytes = n /\ 0 <= lo /\ 0 <= n /\
  lo + n <= Zlength (mb_val b) /\
  sublist lo (lo + n) (mb_vals b) = map vi bytes /\ Forall (fun x => 0 <= x < 256) bytes.
Proof.
  intros [Hl Hd] H. unfold mb_read in H.
  destruct (0 <=? n) eqn:E0; [|discriminate]. apply Z.leb_le in E0.
  destruct (mb_definedb b lo (lo + n)) eqn:E; [|discriminate]. cbn in H. inversion H; subst; clear H.
  apply mb_definedb_spec in E as (E1 & E2 & E3); [|lia].
  rewrite Zlength_sublist by lia.
  split; [reflexivity|split; [lia|split; [lia|split; [lia|split; [lia|]]]]].
  split.
  - unfold mb_vals. rewrite <- pb_vals_sublist by auto.
    apply Znth_eq_ext.
    + rewrite Zlength_pb_vals, Zlength_map by (rewrite !Zlength_sublist; lia). reflexivity.
    + intros i Hi. rewrite Zlength_pb_vals in Hi by (rewrite !Zlength_sublist; lia).
      rewrite Zlength_sublist in Hi by lia.
      rewrite Znth_pb_vals by (rewrite ?Zlength_sublist; lia).
      rewrite Znth_map by (rewrite Zlength_sublist; lia).
      rewrite (Znth_sublist _ _ _ (mb_def b)) by lia. rewrite E3 by lia. reflexivity.
  - apply Forall_forall. intros x Hx. apply In_Znth in Hx. destruct Hx as [i [Hi Hx]]. subst x.
    rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia.
    apply Hd; [lia|]. apply E3. lia.
Qed.

(** ** Byte arrays: slices *)

Lemma tuchar_offset0 n j p:
  field_compatible (tarray tuchar n) [] p -> 0 <= j <= n ->
  field_address0 (Tarray tuchar n noattr) [ArraySubsc j] p = offset_val j p.
Proof.
  intros. rewrite field_address0_offset.
  - simpl. f_equal. lia.
  - eapply field_compatible0_cons_Tarray; [reflexivity | auto | lia].
Qed.

Lemma data_at_tuchar_split3 sh n a b (v: list val) p:
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= b -> b <= n -> Zlength v = n ->
  @data_at DCS.CS sh (tarray tuchar n) v p =
  (@data_at DCS.CS sh (tarray tuchar a) (sublist 0 a v) p *
   @data_at DCS.CS sh (tarray tuchar (b - a)) (sublist a b v) (offset_val a p) *
   @data_at DCS.CS sh (tarray tuchar (n - b)) (sublist b n v) (offset_val b p))%logic.
Proof.
  intros FC A B L.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a b v p) by (first [exact L | lia]).
  rewrite !tuchar_offset0 by (auto; lia). reflexivity.
Qed.

Lemma data_at_tuchar_split2 sh n a (v: list val) p:
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= n -> Zlength v = n ->
  @data_at DCS.CS sh (tarray tuchar n) v p =
  (@data_at DCS.CS sh (tarray tuchar a) (sublist 0 a v) p *
   @data_at DCS.CS sh (tarray tuchar (n - a)) (sublist a n v) (offset_val a p))%logic.
Proof.
  intros FC A L.
  unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh n a v p) by (first [exact L | lia]).
  rewrite !tuchar_offset0 by (auto; lia). reflexivity.
Qed.

Lemma fc_tuchar_tail L w p : field_compatible (tarray tuchar L) [] p -> 0 <= w <= L ->
  field_compatible (tarray tuchar (L - w)) [] (offset_val w p).
Proof.
  intros H Hw.
  pose proof (field_compatible0_nested_field_array (tarray tuchar L) [] w L p
                (arr_field_compatible0 tuchar L p w H ltac:(lia)) (arr_field_compatible0 tuchar L p L H ltac:(lia))
                ltac:(lia)) as H1.
  unfold nested_field_array_type in H1. simpl in H1.
  replace (0 + 1 * w) with w in H1 by lia. exact H1.
Qed.

(** memcpy from a separate object into [lo, lo + n) of the window. *)
Lemma win_split_in sh b wp lo n :
  Zlength (mb_def b) = Zlength (mb_val b) -> 0 <= lo -> 0 <= n -> lo + n <= Zlength (mb_val b) ->
  @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val b))) (mb_vals b) wp |--
  (@data_at DCS.CS sh (tarray tuchar lo) (sublist 0 lo (mb_vals b)) wp *
   @data_at_ DCS.CS sh (tarray tuchar n) (offset_val lo wp) *
   @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val b) - (lo + n)))
     (sublist (lo + n) (Zlength (mb_val b)) (mb_vals b)) (offset_val (lo + n) wp))%logic.
Proof.
  intros Hl H1 H2 H3. assert_PROP (field_compatible (tarray tuchar (Zlength (mb_val b))) [] wp) by entailer!.
  rewrite (data_at_tuchar_split3 sh _ lo (lo + n)) by (rewrite ?Zlength_mb_vals; auto; lia).
  replace (lo + n - lo) with n by lia. cancel.
Qed.

Lemma win_join_in sh b wp lo src b' :
  Zlength (mb_def b) = Zlength (mb_val b) -> mb_write b lo src = Some b' ->
  field_compatible (tarray tuchar (Zlength (mb_val b))) [] wp ->
  (@data_at DCS.CS sh (tarray tuchar lo) (sublist 0 lo (mb_vals b)) wp *
   @data_at DCS.CS sh (tarray tuchar (Zlength src)) (map vi src) (offset_val lo wp) *
   @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val b) - (lo + Zlength src)))
     (sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_vals b)) (offset_val (lo + Zlength src) wp))%logic |--
  @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val b'))) (mb_vals b') wp.
Proof.
  intros Hl Hw FC. destruct (mb_vals_write _ _ _ _ Hl Hw) as (E & L1 & L2 & H1 & H2).
  pose proof (Zlength_nonneg src). pose proof (Zlength_mb_vals b Hl).
  rewrite L1, (data_at_tuchar_split3 sh _ lo (lo + Zlength src) (mb_vals b') wp)
    by (rewrite ?L1 in *; rewrite ?Zlength_mb_vals; auto; lia).
  rewrite E.
  set (V := mb_vals b) in *. set (L := Zlength (mb_val b)) in *. set (n := Zlength src) in *.
  assert (A1 : sublist 0 lo (sublist 0 lo V ++ map vi src ++ sublist (lo + n) L V) = sublist 0 lo V) by list_solve.
  assert (A2 : sublist lo (lo + n) (sublist 0 lo V ++ map vi src ++ sublist (lo + n) L V) = map vi src) by list_solve.
  assert (A3 : sublist (lo + n) L (sublist 0 lo V ++ map vi src ++ sublist (lo + n) L V) = sublist (lo + n) L V)
    by list_solve.
  rewrite A1, A2, A3. replace (lo + n - lo) with n by lia. cancel.
Qed.

(** memcpy(window, window + w, n) with n <= w: the slices [0, n) (destination), [n, w), [w, w + n) (source),
    [w + n, L). *)
Lemma win_split_move sh b wp w n bytes :
  mb_ok b -> mb_read b w n = Some bytes -> n <= w ->
  @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val b))) (mb_vals b) wp |--
  (!! field_compatible (tarray tuchar (Zlength (mb_val b))) [] wp &&
  (@data_at_ DCS.CS sh (tarray tuchar n) wp *
   @data_at DCS.CS sh (tarray tuchar (w - n)) (sublist n w (mb_vals b)) (offset_val n wp) *
   @data_at DCS.CS sh (tarray tuchar n) (map vi bytes) (offset_val w wp) *
   @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val b) - (w + n)))
     (sublist (w + n) (Zlength (mb_val b)) (mb_vals b)) (offset_val (w + n) wp)))%logic.
Proof.
  intros Hok Hr Hn. destruct (mb_read_vals _ _ _ _ Hok Hr) as (Eb & Lb & H0 & H1 & H2 & Ev & Fb).
  pose proof (Zlength_mb_vals b (proj1 Hok)) as LV.
  assert_PROP (field_compatible (tarray tuchar (Zlength (mb_val b))) [] wp) by entailer!.
  apply andp_right; [apply prop_right; auto|].
  set (V := mb_vals b) in *. set (L := Zlength (mb_val b)) in *.
  rewrite (data_at_tuchar_split3 sh L n w V wp) by (auto; lia).
  assert_PROP (field_compatible (tarray tuchar (L - w)) [] (offset_val w wp)) by entailer!.
  rewrite (data_at_tuchar_split2 sh (L - w) n (sublist w L V) (offset_val w wp))
    by (auto; try lia; rewrite Zlength_sublist; lia).
  rewrite offset_offset_val. rewrite !sublist_sublist by lia.
  replace (0 + w) with w by lia. replace (n + w) with (w + n) by lia. replace (L - w + w) with L by lia.
  replace (L - w - n) with (L - (w + n)) by lia. rewrite Ev.
  sep_apply (data_at_data_at_ sh (tarray tuchar n) (sublist 0 n V) wp). cancel.
Qed.


Lemma byte_vals_vi l : byte_vals l = map vi l.
Proof. reflexivity. Qed.

Lemma ptr_add_uint b i w : 0 <= w <= Int.max_unsigned ->
  Vptr b (Ptrofs.add i (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr w)))) =
  Vptr b (Ptrofs.add i (Ptrofs.repr w)).
Proof.
  intros Hw. f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by lia.
  rewrite Ptrofs.mul_commut. change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.mul_one. reflexivity.
Qed.


Lemma win_join_write sh b wp w n bytes b' :
  mb_ok b -> mb_read b w n = Some bytes -> mb_write b 0 bytes = Some b' -> n <= w ->
  field_compatible (tarray tuchar (Zlength (mb_val b))) [] wp ->
  (@data_at DCS.CS sh (tarray tuchar n) (map vi bytes) wp *
   @data_at DCS.CS sh (tarray tuchar (w - n)) (sublist n w (mb_vals b)) (offset_val n wp) *
   @data_at DCS.CS sh (tarray tuchar n) (map vi bytes) (offset_val w wp) *
   @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val b) - (w + n)))
     (sublist (w + n) (Zlength (mb_val b)) (mb_vals b)) (offset_val (w + n) wp))%logic |--
  @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val b'))) (mb_vals b') wp.
Proof.
  intros Hok Hr Hm Hn FC.
  destruct (mb_read_vals _ _ _ _ Hok Hr) as (Eb & Lb & H0 & H1 & H2 & Ev & Fb).
  pose proof (Zlength_mb_vals b (proj1 Hok)) as LV.
  destruct (mb_vals_write _ _ _ _ (proj1 Hok) Hm) as (E & L1 & L2 & _ & _).
  set (V := mb_vals b) in *. set (L := Zlength (mb_val b)) in *.
  rewrite L1, (data_at_tuchar_split3 sh L n w (mb_vals b') wp)
    by (auto; try lia; rewrite Zlength_mb_vals by lia; lia).
  assert_PROP (field_compatible (tarray tuchar (L - w)) [] (offset_val w wp)).
  { apply prop_right. apply fc_tuchar_tail; auto; lia. }
  rewrite (data_at_tuchar_split2 sh (L - w) n (sublist w L (mb_vals b')) (offset_val w wp))
    by (auto; try lia; rewrite Zlength_sublist; rewrite ?Zlength_mb_vals; lia).
  rewrite offset_offset_val. rewrite !sublist_sublist by lia.
  replace (0 + w) with w by lia. replace (n + w) with (w + n) by lia. replace (L - w + w) with L by lia.
  replace (L - w - n) with (L - (w + n)) by lia.
  rewrite E. rewrite Lb.
  assert (A1 : sublist 0 n (sublist 0 0 V ++ map vi bytes ++ sublist (0 + n) L V) = map vi bytes) by list_solve.
  assert (A2 : sublist n w (sublist 0 0 V ++ map vi bytes ++ sublist (0 + n) L V) = sublist n w V) by list_solve.
  assert (A3 : sublist w (w + n) (sublist 0 0 V ++ map vi bytes ++ sublist (0 + n) L V) = map vi bytes).
  { rewrite <- Ev. list_solve. }
  assert (A4 : sublist (w + n) L (sublist 0 0 V ++ map vi bytes ++ sublist (0 + n) L V) = sublist (w + n) L V)
    by list_solve.
  rewrite A1, A2, A3, A4. cancel.
Qed.

Lemma bytes_ok_256 b : Forall (fun x => 0 <= x < 256) b -> bytes_ok b.
Proof. unfold bytes_ok. intros H. eapply Forall_impl; [|exact H]. cbn. intros; rep_lia. Qed.

Lemma vi_u32' x : vi (u32 x) = vi x.
Proof.
  unfold vi, u32. f_equal. change 4294967296 with Int.modulus.
  rewrite <- Int.unsigned_repr_eq. apply Int.repr_unsigned.
Qed.

Lemma u32_range' x : 0 <= u32 x <= Int.max_unsigned.
Proof. unfold u32. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)). rep_lia. Qed.

Lemma slide_cond st w : 0 <= st <= Int.max_unsigned ->
  (st >= Int.unsigned (Int.add (Int.repr w) (Int.repr (w - (258 + 3 + 1)))) <->
   (st >=? u32 (w + u32 (w - MIN_LOOKAHEAD))) = true).
Proof.
  intros Hst. rewrite add_repr32, Int.unsigned_repr_eq.
  unfold u32, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH. change Int.modulus with 4294967296.
  rewrite Zplus_mod_idemp_r. rewrite Z.geb_le. lia.
Qed.

(** The state handed to slide_hash. *)
Definition slid1 (s : dstate) (win : mbuf) : dstate :=
  let st1 := u32 (d_strstart s - d_w_size s) in
  set_d_insert
    (set_d_block_start
       (set_d_strstart (set_d_match_start (set_d_window s win) (u32 (d_match_start s - d_w_size s))) st1)
       (d_block_start s - d_w_size s))
    (if d_insert s >? st1 then st1 else d_insert s).

Ltac slid_simpl :=
  cbn [slid1 set_d_insert set_d_block_start set_d_strstart set_d_match_start set_d_window
       d_status d_po d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window
       d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_block_start
       d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length
       d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid
       d_pending_buf_size d_tr d_pbm] in *.

Lemma slid1_ranges s win : dstate_ranges s -> mb_ok win -> Zlength (mb_val win) = Zlength (mb_val (d_window s)) ->
  Int64.min_signed <= d_block_start s - d_w_size s <= Int64.max_signed -> dstate_ranges (slid1 s win).
Proof.
  intros Hr Hok Hl Hb.
  pose proof (u32_range' (d_strstart s - d_w_size s)). pose proof (u32_range' (d_match_start s - d_w_size s)).
  unfold dstate_ranges, u32_ok, s64_ok in *. slid_simpl. rewrite Hl.
  destruct (_ >? _); slid_simpl; tauto.
Qed.

Lemma fold_slid1 s win p gv ins :
  dstate_ranges (slid1 s win) -> ins = d_insert (slid1 s win) ->
  (trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv *
   @data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val win))) (mb_vals win) (p_window p) *
   @field_at DCS.CS Ews t_ds (DOT _window) (p_window p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _window_size) (vl (d_window_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _w_mask) (vi (d_w_mask s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _high_water) (vl (d_high_water s)) (p_s p) *
   hash_at s p *
   @field_at DCS.CS Ews t_ds (DOT _block_start) (vl (d_block_start s - d_w_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (u32 (d_strstart s - d_w_size s))) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (u32 (d_match_start s - d_w_size s))) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _insert) (vi ins) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p) *
   cfg_at s p * stat_at s p)%logic |-- dstate_at (slid1 s win) p gv.
Proof.
  intros Hr ->. unfold dstate_at.
  assert (E1 : d_trm (slid1 s win) = d_trm s) by reflexivity.
  assert (E2 : hash_at (slid1 s win) p = hash_at s p) by reflexivity.
  assert (E3 : cfg_at (slid1 s win) p = cfg_at s p) by reflexivity.
  assert (E4 : stat_at (slid1 s win) p = stat_at s p) by reflexivity.
  rewrite E1, E2, E3, E4. clear E1 E2 E3 E4.
  apply andp_right; [apply prop_right; exact Hr|].
  unfold win_at, match_at. slid_simpl. cancel.
Qed.

Lemma fw_slide : fw_slide_triple.
Proof.
  unfold fw_slide_triple; intros. show_fw_stmt. unfold dfull_in, dstate_at, match_at, win_at. Intros.
  forward. forward.
  unfold c_fw_slide in H0. cbv zeta in H0.
  assert (Hst : 0 <= d_strstart s <= Int.max_unsigned) by (unfold dstate_ranges, u32_ok in H4; tauto).
  destruct (d_strstart s >=? u32 (d_w_size s + u32 (d_w_size s - MIN_LOOKAHEAD))) eqn:Eg.
  2: { inversion H0; subst s' more'. forward_if.
       - exfalso. apply slide_cond in H5; [congruence|]. unfold dstate_ranges, u32_ok in H4; tauto.
       - forward. entailer!. }
  inv_bind H0. inv_bind H0. inv_bind H0. inv_bind H0. inv_bind H0.
  inversion H0; subst s' more'; clear H0.
  destruct x. apply guard_inv, Z.leb_le in Ha.
  forward_if.
  2: { exfalso. apply (proj2 (slide_cond _ _ Hst)) in Eg. lia. }
  match type of Ha3 with c_slide_hash ?S = _ =>
    replace S with (slid1 s x1) in Ha3 by (unfold slid1; destruct s; cbn; destruct (_ >? _); reflexivity) end.
  cbn [d_block_start set_d_strstart set_d_match_start set_d_window d_match_start d_strstart] in Ha2.
  destruct x2. apply guard_inv in Ha2. unfold in_long in Ha2. apply andb_prop in Ha2 as [Hb1 Hb2].
  apply Z.leb_le in Hb1, Hb2.
  assert (Hw : 0 <= d_w_size s <= Int.max_unsigned) by (unfold dstate_ranges, u32_ok in H4; tauto).
  assert (Hwok : mb_ok (d_window s)) by (unfold dstate_ranges in H4; tauto).
  destruct (mb_read_vals _ _ _ _ Hwok Ha0) as (Eb & Lb & R0 & R1 & R2 & Ev & Fb).
  forward. forward.
  sep_apply (win_split_move Ews (d_window s) (p_window p) (d_w_size s) (u32 (d_w_size s - more)) x0 Hwok Ha0 Ha).
  Intros.
  rewrite <- Lb. forward_call (Ews, p_window p, Ews, offset_val (d_w_size s) (p_window p), x0).
  { apply prop_right. destruct H5 as [Hp _]. destruct (p_window p); try contradiction. cbn.
    rewrite Lb, sub_repr32. unfold u32. rewrite ptr_add_uint by lia. rewrite Int.unsigned_repr_eq. reflexivity. }
  { apply bytes_ok_256; auto. }
  rewrite !byte_vals_vi. rewrite <- Lb in Ha0, Ha.
  sep_apply (win_join_write Ews (d_window s) (p_window p) (d_w_size s) (Zlength x0) x0 x1 Hwok Ha0 Ha1 Ha H5).
  assert (Hbs : Int64.min_signed <= d_block_start s <= Int64.max_signed) by (unfold dstate_ranges, s64_ok in H4; tauto).
  forward. forward. forward. forward. forward. forward.
  replace (Vint (Int.sub (Int.repr (d_strstart s)) (Int.repr (d_w_size s))))
    with (vi (u32 (d_strstart s - d_w_size s))) by (rewrite vi_u32'; unfold vi; rewrite sub_repr32; reflexivity).
  replace (Vint (Int.sub (Int.repr (d_match_start s)) (Int.repr (d_w_size s))))
    with (vi (u32 (d_match_start s - d_w_size s))) by (rewrite vi_u32'; unfold vi; rewrite sub_repr32; reflexivity).
  replace (Vlong (Int64.sub (Int64.repr (d_block_start s)) (Int64.repr (Int.unsigned (Int.repr (d_w_size s))))))
    with (vl (d_block_start s - d_w_size s)) by (rewrite Int.unsigned_repr by lia; unfold vl; rewrite sub64_repr; reflexivity).
  assert (Hr1 : dstate_ranges (slid1 s x1)).
  { apply slid1_ranges.
    - exact H4.
    - eapply mb_ok_write; eauto.
    - destruct (mb_vals_write _ _ _ _ (proj1 Hwok) Ha1) as (_ & L1 & _). exact L1.
    - unfold Int64.min_signed, Int64.max_signed; cbn; lia. }
  assert (Hins : 0 <= d_insert s <= Int.max_unsigned) by (unfold dstate_ranges, u32_ok in H4; tauto).
  pose proof (u32_range' (d_strstart s - d_w_size s)) as Hst1.
  forward. forward.
  apply semax_if_seq. forward_if.
  - forward. forward.
    sep_apply (fold_slid1 s x1 p gv (u32 (d_strstart s - d_w_size s)) Hr1).
    { unfold slid1; slid_simpl. rewrite ?Int.unsigned_repr in H6 by lia.
      destruct (d_insert s >? u32 (d_strstart s - d_w_size s)) eqn:Ei; [reflexivity|]. lia. }
    forward_call (slid1 s x1, p, x3, gv).
    forward.
    unfold dstate_at, match_at, win_at. Intros. entailer!. apply vi_u32'.
  - sep_apply (fold_slid1 s x1 p gv (d_insert s) Hr1).
    { unfold slid1; slid_simpl. rewrite ?Int.unsigned_repr in H6 by lia.
      destruct (d_insert s >? u32 (d_strstart s - d_w_size s)) eqn:Ei; [|reflexivity]. lia. }
    forward_call (slid1 s x1, p, x3, gv).
    forward.
    unfold dstate_at, match_at, win_at. Intros. entailer!. apply vi_u32'.
Qed.
