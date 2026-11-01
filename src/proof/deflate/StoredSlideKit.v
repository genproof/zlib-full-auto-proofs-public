(** * Kit for StoredTailSlide.v (a copy of StoredWinKit.v under another name): [dfull] opened into the fields the fragment touches
    and a folded frame; the state after the update as one setter chain [upd_win]; byte-array slices for the
    two memcpy patterns (input -> window, window -> window). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.StoredKit.
Require Zlib.trees.code.
Require Import Zlib.proof.zutil.Libc.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** trees.c's part, without the fields of sym_at / out_at / dtype_at (kept folded: trees.c's globals) *)
Definition trees_frame (cs : tstate * list bool) (sp : val) (gv : globals) : mpred :=
  (ltree_at (tr_ltree (fst cs)) sp * dtree_at (tr_dtree (fst cs)) sp * bltree_at (tr_bltree (fst cs)) sp *
   ldesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) sp) (tr_lmax (fst cs)) (gv Zlib.trees.code._static_l_desc) sp *
   ddesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) sp) (tr_dmax (fst cs)) (gv Zlib.trees.code._static_d_desc) sp *
   bldesc_at (field_address t_ds (DOT Zlib.trees.code._bl_tree) sp) (tr_blmax (fst cs)) (gv Zlib.trees.code._static_bl_desc) sp *
   work_at (tr_wk (fst cs)) sp * lvl_at (fst cs) sp)%logic.

Definition strm_zfuncs (strmp : val) (gv : globals) : mpred :=
  (@field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) strmp *
   @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) strmp)%logic.

Lemma trees_at_split cs sp pbp strmp gv :
  trees_at cs sp pbp strmp gv =
  (trees_frame cs sp gv * out_at (tr_out (fst cs)) (snd cs) sp pbp * sym_at (fst cs) sp pbp *
   dtype_at (fst cs) sp strmp)%logic.
Proof. unfold trees_at, trees_frame. apply pred_ext; cancel. Qed.

(** ** The frame: everything of [dfull] but the touched fields *)
Definition wframe (s : dstate) (z : strm) (p : dptrs) (pout : val) (rest : list val) (msgv : val)
    (gv : globals) : mpred :=
  (trees_frame (d_trm s) (p_s p) gv * out_at (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p) *
   @field_at DCS.CS Ews t_ds (DOT _sym_buf) (offset_val (tr_lit_bufsize (d_tr s)) (p_pbuf p)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) (vi (tr_lit_bufsize (d_tr s))) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _sym_next) (vi (tr_sym_next (d_tr s))) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi (tr_sym_end (d_tr s))) (p_s p) *
   @field_at DCS.CS Ews t_strm (DOT _data_type) (vi (tr_data_type (d_tr s))) (p_strm p) *
   @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _w_mask) (vi (d_w_mask s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _high_water) (vl (d_high_water s)) (p_s p) *
   hash_at s p * cfg_at s p * stat_at s p *
   @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p) *
   @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) pout) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _total_out) (vl (z_total_out z)) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _msg) msgv (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _state) (p_s p) (p_strm p) *
   strm_zfuncs (p_strm p) gv *
   @field_at DCS.CS Ews t_strm (DOT _opaque) nullval (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) (p_strm p) *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) (p_strm p) *
   out_space z pout rest)%logic.

(** The touched fields, with their values. *)
Definition wfields (s : dstate) (z : strm) (p : dptrs) (pin : val) (ish : share)
    (ma : Z) (win : mbuf) (st ins bs : Z) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _strm) (p_strm p) (p_s p) *
   @field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) (p_strm p) *
   in_obj ish z pin *
   @field_at DCS.CS Ews t_ds (DOT _window) (p_window p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _window_size) (vl (d_window_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p) *
   @data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val win))) (mb_vals win) (p_window p) *
   @field_at DCS.CS Ews t_ds (DOT _matches) (vi ma) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _strstart) (vi st) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _insert) (vi ins) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _block_start) (vl bs) (p_s p))%logic.

Definition win_pure (s : dstate) (z : strm) (msgv : val) (ish : share) : Prop :=
  dstate_ranges s /\ strm_ranges z /\ msg_ok (z_msg z) msgv /\ readable_share ish /\
  (0 <= tr_sym_next (d_tr s) <= Int.max_unsigned /\ 0 <= tr_sym_end (d_tr s) <= Int.max_unsigned /\
   0 <= tr_matches (d_tr s) <= Int.max_unsigned /\ 0 <= tr_lit_bufsize (d_tr s) <= Int.max_unsigned) /\
  Int.min_signed <= tr_data_type (d_tr s) <= Int.max_signed.

(** The state after the update. *)
Definition upd_win (s : dstate) (ma : Z) (win : mbuf) (st ins bs : Z) : dstate :=
  set_d_block_start (set_d_insert (set_d_strstart (set_d_window (set_d_matches s ma) win) st) ins) bs.

Lemma upd_win_id s : upd_win s (d_matches s) (d_window s) (d_strstart s) (d_insert s) (d_block_start s) = s.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [] ?]; reflexivity. Qed.

Lemma dfull_open s z p pin pout ish rest msgv gv :
  dfull s z p pin pout ish rest msgv gv |--
  (!! win_pure s z msgv ish &&
   (wframe s z p pout rest msgv gv *
    wfields s z p pin ish (d_matches s) (d_window s) (d_strstart s) (d_insert s) (d_block_start s)))%logic.
Proof.
  unfold dfull, dstate_at, trees_at, wframe, wfields, trees_frame, strm_zfuncs, win_at, match_at, sym_at,
    dtype_at, strm_at, d_matches, d_trm.
  cbn [fst snd]. Intros. apply andp_right; [apply prop_right; unfold win_pure; tauto|]. cancel.
Qed.

Lemma hash_at_upd s ma win st ins bs p : hash_at (upd_win s ma win st ins bs) p = hash_at s p.
Proof. reflexivity. Qed.
Lemma cfg_at_upd s ma win st ins bs p : cfg_at (upd_win s ma win st ins bs) p = cfg_at s p.
Proof. reflexivity. Qed.
Lemma stat_at_upd s ma win st ins bs p : stat_at (upd_win s ma win st ins bs) p = stat_at s p.
Proof. reflexivity. Qed.
Lemma trees_frame_upd s ma win st ins bs sp gv :
  trees_frame (d_trm (upd_win s ma win st ins bs)) sp gv = trees_frame (d_trm s) sp gv.
Proof. reflexivity. Qed.

Ltac upd_simpl :=
  cbn [upd_win set_d_block_start set_d_insert set_d_strstart set_d_window set_d_matches set_d_tr set_matches
       d_tr d_pbm d_w_size d_window d_window_size d_w_bits d_w_mask d_high_water d_block_start d_match_length
       d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length d_insert d_slid
       tr_out tr_lit_bufsize tr_sym_next tr_sym_end tr_matches tr_data_type fst snd] in *.

Lemma dfull_fold s z p pin pout ish rest msgv gv ma win st ins bs :
  win_pure s z msgv ish ->
  0 <= ma <= Int.max_unsigned -> mb_ok win -> Zlength (mb_val win) <= Int.max_unsigned ->
  0 <= st <= Int.max_unsigned -> 0 <= ins <= Int.max_unsigned ->
  Int64.min_signed <= bs <= Int64.max_signed ->
  (wframe s z p pout rest msgv gv * wfields s z p pin ish ma win st ins bs)%logic |--
  dfull (upd_win s ma win st ins bs) z p pin pout ish rest msgv gv.
Proof.
  intros (Hr & Hz & Hm & Hi & Hsym & Hdt) Hma Hw Hwl Hst Hins Hbs.
  unfold dfull, dstate_at. rewrite hash_at_upd, cfg_at_upd, stat_at_upd.
  rewrite trees_at_split, trees_frame_upd.
  unfold wframe, wfields, strm_zfuncs, win_at, match_at, sym_at, dtype_at, strm_at, d_trm.
  upd_simpl.
  assert (dstate_ranges (upd_win s ma win st ins bs)).
  { unfold dstate_ranges in *. upd_simpl. unfold u32_ok, s64_ok in *. tauto. }
  entailer!.
Qed.

(** ** Masked buffers *)

Lemma Zlength_mb_vals b : Zlength (mb_def b) = Zlength (mb_val b) -> Zlength (mb_vals b) = Zlength (mb_val b).
Proof. intros. unfold mb_vals. apply Zlength_pb_vals. auto. Qed.

Lemma pb_vals_app b1 b2 m1 m2 : Zlength m1 = Zlength b1 ->
  pb_vals (b1 ++ b2) (m1 ++ m2) = pb_vals b1 m1 ++ pb_vals b2 m2.
Proof.
  intros H. unfold pb_vals. rewrite combine_app' by lia.
  apply map_app.
Qed.

Lemma pb_vals_sublist lo hi b m : Zlength m = Zlength b ->
  pb_vals (sublist lo hi b) (sublist lo hi m) = sublist lo hi (pb_vals b m).
Proof.
  intros H. unfold pb_vals. rewrite sublist_map, sublist_combine. reflexivity.
Qed.

Lemma pb_vals_all_true b : pb_vals b (repeat true (Z.to_nat (Zlength b))) = map vi b.
Proof.
  unfold pb_vals. rewrite Zlength_correct, Nat2Z.id.
  induction b as [|x b IH]; [reflexivity|]. cbn. f_equal. exact IH.
Qed.

(** The contents of the window after [mb_write]: the old contents with [src] in place. *)
Lemma mb_vals_write b lo src b' :
  Zlength (mb_def b) = Zlength (mb_val b) ->
  mb_write b lo src = Some b' ->
  mb_vals b' = sublist 0 lo (mb_vals b) ++ map vi src ++
               sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_vals b) /\
  Zlength (mb_val b') = Zlength (mb_val b) /\ Zlength (mb_def b') = Zlength (mb_val b') /\
  0 <= lo /\ lo + Zlength src <= Zlength (mb_val b).
Proof.
  intros Hl H. unfold mb_write in H.
  destruct (andb (0 <=? lo) (lo + Zlength src <=? Zlength (mb_val b))) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  inversion H; subst; clear H. pose proof (Zlength_nonneg src).
  unfold mb_vals; cbn [mb_val mb_def].
  assert (Hlen : Zlength (sublist 0 lo (mb_val b) ++ src ++
                  sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_val b)) = Zlength (mb_val b)).
  { rewrite !Zlength_app, !Zlength_sublist by lia. lia. }
  assert (Hlen' : Zlength (sublist 0 lo (mb_def b) ++ repeat true (Z.to_nat (Zlength src)) ++
                  sublist (lo + Zlength src) (Zlength (mb_def b)) (mb_def b)) = Zlength (mb_val b)).
  { rewrite !Zlength_app, Zlength_repeat, !Zlength_sublist by lia. lia. }
  split; [|split; [exact Hlen|split; [lia|split; lia]]].
  rewrite !pb_vals_app.
  2: { rewrite Zlength_repeat; lia. }
  2: { rewrite !Zlength_sublist by lia. lia. }
  rewrite pb_vals_all_true. rewrite Hl.
  rewrite !pb_vals_sublist by auto. reflexivity.
Qed.

Lemma mb_ok_write b lo src b' :
  mb_ok b -> Forall (fun x => 0 <= x < 256) src -> mb_write b lo src = Some b' -> mb_ok b'.
Proof.
  intros [Hl Hd] Hs H. unfold mb_write in H.
  destruct (andb (0 <=? lo) (lo + Zlength src <=? Zlength (mb_val b))) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  inversion H; subst; clear H. pose proof (Zlength_nonneg src).
  split; cbn [mb_val mb_def].
  - rewrite !Zlength_app, Zlength_repeat, !Zlength_sublist by lia. lia.
  - intros i Hi Hdi. rewrite !Zlength_app, !Zlength_sublist in Hi by lia.
    destruct (Z_lt_dec i lo).
    + rewrite app_Znth1 in Hdi by (rewrite Zlength_sublist; lia).
      rewrite app_Znth1 by (rewrite Zlength_sublist; lia).
      rewrite Znth_sublist in Hdi by lia. rewrite Znth_sublist by lia.
      apply Hd; [lia|]. rewrite Z.add_0_r in *. auto.
    + rewrite app_Znth2 in Hdi by (rewrite Zlength_sublist; lia).
      rewrite app_Znth2 by (rewrite Zlength_sublist; lia).
      rewrite Zlength_sublist in Hdi by lia. rewrite Zlength_sublist by lia.
      destruct (Z_lt_dec (i - (lo - 0)) (Zlength src)).
      * rewrite app_Znth1 by lia. rewrite Forall_forall in Hs. apply Hs. apply Znth_In. lia.
      * rewrite app_Znth2 in Hdi by (rewrite ?Zlength_repeat; lia).
        rewrite app_Znth2 by (rewrite ?Zlength_repeat; lia).
        rewrite Zlength_repeat in Hdi by lia.
        rewrite Znth_sublist in Hdi by lia. rewrite Znth_sublist by lia. apply Hd; [lia|]. auto.
Qed.

Lemma mb_write_len b lo src b' : mb_write b lo src = Some b' -> Zlength (mb_val b') = Zlength (mb_val b).
Proof.
  intros H. unfold mb_write in H.
  destruct (andb (0 <=? lo) (lo + Zlength src <=? Zlength (mb_val b))) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  inversion H; subst; clear H. pose proof (Zlength_nonneg src). cbn [mb_val].
  rewrite !Zlength_app, !Zlength_sublist by lia. lia.
Qed.

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


Lemma win_join_move sh b wp w n b' :
  mb_ok b -> mb_move b 0 w n = Some b' -> n <= w ->
  field_compatible (tarray tuchar (Zlength (mb_val b))) [] wp ->
  exists bytes, mb_read b w n = Some bytes /\ Forall (fun x => 0 <= x < 256) bytes /\ Zlength bytes = n /\
  mb_ok b' /\ Zlength (mb_val b') = Zlength (mb_val b) /\
  (@data_at DCS.CS sh (tarray tuchar n) (map vi bytes) wp *
   @data_at DCS.CS sh (tarray tuchar (w - n)) (sublist n w (mb_vals b)) (offset_val n wp) *
   @data_at DCS.CS sh (tarray tuchar n) (map vi bytes) (offset_val w wp) *
   @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val b) - (w + n)))
     (sublist (w + n) (Zlength (mb_val b)) (mb_vals b)) (offset_val (w + n) wp))%logic |--
  @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val b'))) (mb_vals b') wp.
Proof.
  intros Hok Hm Hn FC. unfold mb_move in Hm.
  destruct (orb (0 + n <=? w) (w + n <=? 0)); [|discriminate]. cbn [guard bind] in Hm.
  destruct (mb_read b w n) as [bytes|] eqn:Hr; [|discriminate]. cbn [bind] in Hm.
  destruct (mb_read_vals _ _ _ _ Hok Hr) as (Eb & Lb & H0 & H1 & H2 & Ev & Fb).
  exists bytes. split; [reflexivity|]. split; [exact Fb|]. split; [exact Lb|].
  split; [eapply mb_ok_write; eauto|].
  pose proof (Zlength_mb_vals b (proj1 Hok)) as LV.
  destruct (mb_vals_write _ _ _ _ (proj1 Hok) Hm) as (E & L1 & L2 & _ & _).
  split; [exact L1|].
  set (V := mb_vals b) in *. set (L := Zlength (mb_val b)) in *.
  rewrite L1, (data_at_tuchar_split3 sh L n w (mb_vals b') wp)
    by (auto; try lia; rewrite Zlength_mb_vals by lia; lia).
  assert_PROP (field_compatible (tarray tuchar (L - w)) [] (offset_val w wp)).
  { (* from the slice at w (non-empty when n > 0) or else from the whole object *)
    apply prop_right. apply fc_tuchar_tail; auto; lia. }
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

Lemma byte_vals_vi l : byte_vals l = map vi l.
Proof. reflexivity. Qed.

(** The input object in three slices: [0, a), [a, a + k) (a memcpy source), [a + k, N). *)
Lemma in_obj_split ish z pin a k :
  field_compatible (tarray tuchar (Zlength (z_in z))) [] pin -> 0 <= a -> 0 <= k -> a + k <= Zlength (z_in z) ->
  in_obj ish z pin =
  (@data_at DCS.CS ish (tarray tuchar a) (sublist 0 a (map vi (z_in z))) pin *
   @data_at DCS.CS ish (tarray tuchar k) (map vi (sublist a (a + k) (z_in z))) (offset_val a pin) *
   @data_at DCS.CS ish (tarray tuchar (Zlength (z_in z) - (a + k)))
     (sublist (a + k) (Zlength (z_in z)) (map vi (z_in z))) (offset_val (a + k) pin))%logic.
Proof.
  intros FC H1 H2 H3. unfold in_obj.
  rewrite (data_at_tuchar_split3 ish _ a (a + k)) by (rewrite ?Zlength_map; auto; lia).
  replace (a + k - a) with k by lia. rewrite !sublist_map. reflexivity.
Qed.

(** ** Model facts *)

Lemma upd_win_bs s bs : upd_win s (d_matches s) (d_window s) (d_strstart s) (d_insert s) bs = set_d_block_start s bs.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [] ?]; reflexivity. Qed.

Lemma win_pure_ranges s z msgv ish : win_pure s z msgv ish ->
  0 <= d_w_size s <= Int.max_unsigned /\ mb_ok (d_window s) /\
  Zlength (mb_val (d_window s)) <= Int.max_unsigned /\ 0 <= d_window_size s <= Int64.max_unsigned /\
  Int64.min_signed <= d_block_start s <= Int64.max_signed /\ 0 <= d_strstart s <= Int.max_unsigned /\
  0 <= d_insert s <= Int.max_unsigned /\ 0 <= d_matches s <= Int.max_unsigned /\
  strm_ranges z /\ readable_share ish.
Proof.
  intros (Hr & Hz & Hm & Hi & Hsym & Hdt). unfold dstate_ranges, u32_ok, u64_ok, s64_ok in Hr. unfold d_matches.
  tauto.
Qed.

Lemma rds_inv l lo n b : rds l lo n = Some b ->
  0 <= lo /\ 0 <= n /\ lo + n <= Zlength l /\ b = sublist lo (lo + n) l /\ Zlength b = n.
Proof.
  unfold rds. intros H.
  destruct ((0 <=? lo) && (0 <=? n) && (lo + n <=? Zlength l))%bool eqn:E; [|discriminate].
  inversion H; subst. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1, E2, E3. rewrite Zlength_sublist by lia. repeat split; lia.
Qed.

Lemma rds_bytes_ok z lo n b : strm_ranges z -> rds (z_in z) lo n = Some b -> Forall (fun x => 0 <= x < 256) b.
Proof.
  intros Hz H. apply rds_inv in H as (H1 & H2 & H3 & -> & _).
  unfold strm_ranges in Hz. apply Forall_sublist. tauto.
Qed.

Lemma bytes_ok_256 b : Forall (fun x => 0 <= x < 256) b -> bytes_ok b.
Proof. unfold bytes_ok. intros H. eapply Forall_impl; [|exact H]. cbn. intros; rep_lia. Qed.

(** The input object around a memcpy source [a, a + Zlength b). *)
Lemma in_obj_split_b ish z pin a b :
  field_compatible (tarray tuchar (Zlength (z_in z))) [] pin -> rds (z_in z) a (Zlength b) = Some b ->
  in_obj ish z pin =
  (@data_at DCS.CS ish (tarray tuchar a) (sublist 0 a (map vi (z_in z))) pin *
   @data_at DCS.CS ish (tarray tuchar (Zlength b)) (map vi b) (offset_val a pin) *
   @data_at DCS.CS ish (tarray tuchar (Zlength (z_in z) - (a + Zlength b)))
     (sublist (a + Zlength b) (Zlength (z_in z)) (map vi (z_in z))) (offset_val (a + Zlength b) pin))%logic.
Proof.
  intros FC H. pose proof H as H'. apply rds_inv in H' as (H1 & H2 & H3 & E & _).
  rewrite (in_obj_split ish z pin a (Zlength b)) by auto. rewrite <- E. reflexivity.
Qed.

Lemma in_obj_join_b ish z pin a b :
  field_compatible (tarray tuchar (Zlength (z_in z))) [] pin -> rds (z_in z) a (Zlength b) = Some b ->
  (@data_at DCS.CS ish (tarray tuchar a) (sublist 0 a (map vi (z_in z))) pin *
   @data_at DCS.CS ish (tarray tuchar (Zlength b)) (map vi b) (offset_val a pin) *
   @data_at DCS.CS ish (tarray tuchar (Zlength (z_in z) - (a + Zlength b)))
     (sublist (a + Zlength b) (Zlength (z_in z)) (map vi (z_in z))) (offset_val (a + Zlength b) pin))%logic
  |-- in_obj ish z pin.
Proof. intros FC H. rewrite (in_obj_split_b ish z pin a b FC H). cancel. Qed.

Lemma vi_u32' x : vi (u32 x) = vi x.
Proof.
  unfold vi, u32. f_equal. change 4294967296 with Int.modulus.
  rewrite <- Int.unsigned_repr_eq. apply Int.repr_unsigned.
Qed.

Lemma u32_range' x : 0 <= u32 x <= Int.max_unsigned.
Proof. unfold u32. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)). rep_lia. Qed.

(** [p - w] for a C pointer [p] and an unsigned int [w]. *)
Lemma ptr_sub_uint b i n w : 0 <= w <= Int.max_unsigned ->
  Vptr b (Ptrofs.sub (Ptrofs.add i (Ptrofs.repr n))
            (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr w)))) =
  Vptr b (Ptrofs.add i (Ptrofs.repr (n - w))).
Proof.
  intros Hw. f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by lia.
  rewrite Ptrofs.mul_commut. change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.mul_one.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, <- Ptrofs.sub_add_opp.
  rewrite ptrofs_sub_repr. reflexivity.
Qed.

Lemma ptr_add_uint b i w : 0 <= w <= Int.max_unsigned ->
  Vptr b (Ptrofs.add i (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr w)))) =
  Vptr b (Ptrofs.add i (Ptrofs.repr w)).
Proof.
  intros Hw. f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by lia.
  rewrite Ptrofs.mul_commut. change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.mul_one. reflexivity.
Qed.

Lemma u64_sub_unsigned' a b :
  Int64.unsigned (Int64.sub (Int64.repr a) (Int64.repr b)) = u64 (a - b).
Proof. rewrite sub64_repr, Int64.unsigned_repr_eq. reflexivity. Qed.

Lemma mb_move_le b w n b' : 0 <= w -> 0 <= n -> mb_move b 0 w n = Some b' -> n <= w.
Proof.
  intros Hw Hn H. unfold mb_move in H.
  destruct (orb (0 + n <=? w) (w + n <=? 0)) eqn:E; [|discriminate].
  apply orb_prop in E as [E|E]; apply Z.leb_le in E; lia.
Qed.

Lemma slide_state s win1 :
  clamp_insert (incr_matches (set_d_window (set_d_strstart s (u32 (d_strstart s - d_w_size s))) win1)) =
  upd_win s (if d_matches s <? 2 then u32 (d_matches s + 1) else d_matches s) win1
    (u32 (d_strstart s - d_w_size s))
    (if d_insert s >? u32 (d_strstart s - d_w_size s) then u32 (d_strstart s - d_w_size s) else d_insert s)
    (d_block_start s).
Proof.
  destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [] ?].
  unfold clamp_insert, incr_matches, upd_win, d_matches. cbn.
  destruct (_ <? 2); destruct (_ >? _); reflexivity.
Qed.

Lemma upd_win_s1 s1 win st ins : 
  upd_win s1 (d_matches s1) win st ins (d_block_start s1) =
  set_d_insert (set_d_strstart (set_d_window s1 win) st) ins.
Proof. destruct s1 as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [] ?]; reflexivity. Qed.
