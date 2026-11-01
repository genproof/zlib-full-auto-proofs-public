(** * Parts of the body proof of deflateInit2_. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DSpec Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.deflate.InitKit Zlib.proof.deflate.InitKit2 Zlib.proof.deflate.InitFacts.
Require Zlib.proof.zutil.Libc Zlib.proof.deflate.ZeroBytes.
Local Open Scope logic.

(** The fields of deflate_state that deflateInit2_ never writes (still their zero value from zmemzero). *)
Definition zrest (sp : val) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _pending_out) (zero_val (nested_field_type t_ds (DOT _pending_out))) sp *
   @field_at DCS.CS Ews t_ds (DOT _pending) (zero_val (nested_field_type t_ds (DOT _pending))) sp *
   @field_at DCS.CS Ews t_ds (DOT _gzindex) (zero_val (nested_field_type t_ds (DOT _gzindex))) sp *
   @field_at DCS.CS Ews t_ds (DOT _last_flush) (zero_val (nested_field_type t_ds (DOT _last_flush))) sp *
   @field_at DCS.CS Ews t_ds (DOT _window_size) (zero_val (nested_field_type t_ds (DOT _window_size))) sp *
   @field_at DCS.CS Ews t_ds (DOT _ins_h) (zero_val (nested_field_type t_ds (DOT _ins_h))) sp *
   @field_at DCS.CS Ews t_ds (DOT _block_start) (zero_val (nested_field_type t_ds (DOT _block_start))) sp *
   @field_at DCS.CS Ews t_ds (DOT _match_length) (zero_val (nested_field_type t_ds (DOT _match_length))) sp *
   @field_at DCS.CS Ews t_ds (DOT _prev_match) (zero_val (nested_field_type t_ds (DOT _prev_match))) sp *
   @field_at DCS.CS Ews t_ds (DOT _match_available) (zero_val (nested_field_type t_ds (DOT _match_available))) sp *
   @field_at DCS.CS Ews t_ds (DOT _strstart) (zero_val (nested_field_type t_ds (DOT _strstart))) sp *
   @field_at DCS.CS Ews t_ds (DOT _match_start) (zero_val (nested_field_type t_ds (DOT _match_start))) sp *
   @field_at DCS.CS Ews t_ds (DOT _lookahead) (zero_val (nested_field_type t_ds (DOT _lookahead))) sp *
   @field_at DCS.CS Ews t_ds (DOT _prev_length) (zero_val (nested_field_type t_ds (DOT _prev_length))) sp *
   @field_at DCS.CS Ews t_ds (DOT _max_chain_length) (zero_val (nested_field_type t_ds (DOT _max_chain_length))) sp *
   @field_at DCS.CS Ews t_ds (DOT _max_lazy_match) (zero_val (nested_field_type t_ds (DOT _max_lazy_match))) sp *
   @field_at DCS.CS Ews t_ds (DOT _good_match) (zero_val (nested_field_type t_ds (DOT _good_match))) sp *
   @field_at DCS.CS Ews t_ds (DOT _nice_match) (zero_val (nested_field_type t_ds (DOT _nice_match))) sp *
   @field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (zero_val (nested_field_type t_ds (DOT _dyn_ltree))) sp *
   @field_at DCS.CS Ews t_ds (DOT _dyn_dtree) (zero_val (nested_field_type t_ds (DOT _dyn_dtree))) sp *
   @field_at DCS.CS Ews t_ds (DOT _bl_tree) (zero_val (nested_field_type t_ds (DOT _bl_tree))) sp *
   @field_at DCS.CS Ews t_ds (DOT _l_desc) (zero_val (nested_field_type t_ds (DOT _l_desc))) sp *
   @field_at DCS.CS Ews t_ds (DOT _d_desc) (zero_val (nested_field_type t_ds (DOT _d_desc))) sp *
   @field_at DCS.CS Ews t_ds (DOT _bl_desc) (zero_val (nested_field_type t_ds (DOT _bl_desc))) sp *
   @field_at DCS.CS Ews t_ds (DOT _bl_count) (zero_val (nested_field_type t_ds (DOT _bl_count))) sp *
   @field_at DCS.CS Ews t_ds (DOT _heap) (zero_val (nested_field_type t_ds (DOT _heap))) sp *
   @field_at DCS.CS Ews t_ds (DOT _heap_len) (zero_val (nested_field_type t_ds (DOT _heap_len))) sp *
   @field_at DCS.CS Ews t_ds (DOT _heap_max) (zero_val (nested_field_type t_ds (DOT _heap_max))) sp *
   @field_at DCS.CS Ews t_ds (DOT _depth) (zero_val (nested_field_type t_ds (DOT _depth))) sp *
   @field_at DCS.CS Ews t_ds (DOT _sym_next) (zero_val (nested_field_type t_ds (DOT _sym_next))) sp *
   @field_at DCS.CS Ews t_ds (DOT _opt_len) (zero_val (nested_field_type t_ds (DOT _opt_len))) sp *
   @field_at DCS.CS Ews t_ds (DOT _static_len) (zero_val (nested_field_type t_ds (DOT _static_len))) sp *
   @field_at DCS.CS Ews t_ds (DOT _matches) (zero_val (nested_field_type t_ds (DOT _matches))) sp *
   @field_at DCS.CS Ews t_ds (DOT _insert) (zero_val (nested_field_type t_ds (DOT _insert))) sp *
   @field_at DCS.CS Ews t_ds (DOT _bi_buf) (zero_val (nested_field_type t_ds (DOT _bi_buf))) sp *
   @field_at DCS.CS Ews t_ds (DOT _bi_valid) (zero_val (nested_field_type t_ds (DOT _bi_valid))) sp *
   @field_at DCS.CS Ews t_ds (DOT _bi_used) (zero_val (nested_field_type t_ds (DOT _bi_used))) sp *
   @field_at DCS.CS Ews t_ds (DOT _slid) (zero_val (nested_field_type t_ds (DOT _slid))) sp)%logic.

(** The fields it writes, as zmemzero left them. *)
Definition zset0 (sp : val) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _strm) (zero_val (nested_field_type t_ds (DOT _strm))) sp *
   @field_at DCS.CS Ews t_ds (DOT _status) (zero_val (nested_field_type t_ds (DOT _status))) sp *
   @field_at DCS.CS Ews t_ds (DOT _wrap) (zero_val (nested_field_type t_ds (DOT _wrap))) sp *
   @field_at DCS.CS Ews t_ds (DOT _gzhead) (zero_val (nested_field_type t_ds (DOT _gzhead))) sp *
   @field_at DCS.CS Ews t_ds (DOT _w_bits) (zero_val (nested_field_type t_ds (DOT _w_bits))) sp *
   @field_at DCS.CS Ews t_ds (DOT _w_size) (zero_val (nested_field_type t_ds (DOT _w_size))) sp *
   @field_at DCS.CS Ews t_ds (DOT _w_mask) (zero_val (nested_field_type t_ds (DOT _w_mask))) sp *
   @field_at DCS.CS Ews t_ds (DOT _hash_bits) (zero_val (nested_field_type t_ds (DOT _hash_bits))) sp *
   @field_at DCS.CS Ews t_ds (DOT _hash_size) (zero_val (nested_field_type t_ds (DOT _hash_size))) sp *
   @field_at DCS.CS Ews t_ds (DOT _hash_mask) (zero_val (nested_field_type t_ds (DOT _hash_mask))) sp *
   @field_at DCS.CS Ews t_ds (DOT _hash_shift) (zero_val (nested_field_type t_ds (DOT _hash_shift))) sp *
   @field_at DCS.CS Ews t_ds (DOT _window) (zero_val (nested_field_type t_ds (DOT _window))) sp *
   @field_at DCS.CS Ews t_ds (DOT _prev) (zero_val (nested_field_type t_ds (DOT _prev))) sp *
   @field_at DCS.CS Ews t_ds (DOT _head) (zero_val (nested_field_type t_ds (DOT _head))) sp *
   @field_at DCS.CS Ews t_ds (DOT _high_water) (zero_val (nested_field_type t_ds (DOT _high_water))) sp *
   @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) (zero_val (nested_field_type t_ds (DOT _lit_bufsize))) sp *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf) (zero_val (nested_field_type t_ds (DOT _pending_buf))) sp *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (zero_val (nested_field_type t_ds (DOT _pending_buf_size))) sp *
   @field_at DCS.CS Ews t_ds (DOT _sym_buf) (zero_val (nested_field_type t_ds (DOT _sym_buf))) sp *
   @field_at DCS.CS Ews t_ds (DOT _sym_end) (zero_val (nested_field_type t_ds (DOT _sym_end))) sp *
   @field_at DCS.CS Ews t_ds (DOT _level) (zero_val (nested_field_type t_ds (DOT _level))) sp *
   @field_at DCS.CS Ews t_ds (DOT _strategy) (zero_val (nested_field_type t_ds (DOT _strategy))) sp *
   @field_at DCS.CS Ews t_ds (DOT _method) (zero_val (nested_field_type t_ds (DOT _method))) sp)%logic.

(** The fields written only after the allocation check. *)
Definition zlate (sp : val) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _sym_buf) (zero_val (nested_field_type t_ds (DOT _sym_buf))) sp *
   @field_at DCS.CS Ews t_ds (DOT _sym_end) (zero_val (nested_field_type t_ds (DOT _sym_end))) sp *
   @field_at DCS.CS Ews t_ds (DOT _level) (zero_val (nested_field_type t_ds (DOT _level))) sp *
   @field_at DCS.CS Ews t_ds (DOT _strategy) (zero_val (nested_field_type t_ds (DOT _strategy))) sp *
   @field_at DCS.CS Ews t_ds (DOT _method) (zero_val (nested_field_type t_ds (DOT _method))) sp)%logic.

Lemma zds_split sp : zds sp = zset0 sp * zrest sp.
Proof. unfold zds, zset0, zrest. apply pred_ext; cancel. Qed.

(** The padding bytes (zeros) are the padding of [ds_pad]. *)
Lemma zpad_ds_pad sp : field_compatible t_ds [] sp -> zpad sp |-- ds_pad sp.
Proof.
  intros FC. unfold zpad, ds_pad, spacer. simpl. unfold at_offset.
  repeat match goal with |- context [@data_at DCS.CS Ews (tarray tuchar ?k) (zbytes ?k) ?q] =>
    sep_apply (@data_at_memory_block DCS.CS Ews (tarray tuchar k) (zbytes k) q) end.
  simpl sizeof. cancel.
Qed.

Lemma i_state_sizes level method wbits mem strategy :
  -15 <= wbits -> i_bad level method wbits mem strategy = false ->
  dsizes (i_state level method wbits mem strategy).
Proof.
  intros. pose proof (fun x => proj2 (Z.shiftl_nonneg 1 x) ltac:(lia)) as Hs.
  pose proof (Hs (i_wb9 wbits)). pose proof (Hs (mem + 7)). pose proof (Hs (mem + 6)).
  unfold dsizes, i_state, init_dstate, init_tstate. cbn.
  rewrite !Zlength_repeat'. unfold LIT_BUFS. repeat split; rewrite Z2Nat.id; lia.
Qed.

(** ** Helpers of [init_d0] *)

Lemma zv_td : @zero_val DCS.CS t_td = td_val (mkTD nullval 0 nullval).
Proof.
  apply JMeq_eq. rewrite zero_val_eq. eapply JMeq_trans; [apply fold_reptype_JMeq|]. simpl. unfold td_val; simpl.
  rewrite zero_val_Tpointer, zero_val_Tint, zero_val_Tpointer. apply JMeq_refl.
Qed.

(** The untouched fields with explicit values. *)
Lemma zrest_vals sp : zrest sp =
  (@field_at DCS.CS Ews t_ds (DOT _pending_out) (nullval) sp *
   @field_at DCS.CS Ews t_ds (DOT _pending) (vl 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _window_size) (vl 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _ins_h) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _block_start) (vl 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _match_length) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _match_available) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _strstart) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _match_start) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _max_chain_length) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _max_lazy_match) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _good_match) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _nice_match) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon (zero_tree HEAP_SIZE)) sp *
   @field_at DCS.CS Ews t_ds (DOT _dyn_dtree) (ct_canon (zero_tree (2 * D_CODES + 1))) sp *
   @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_canon (zero_tree (2 * BL_CODES + 1))) sp *
   @field_at DCS.CS Ews t_ds (DOT _l_desc) (td_val (mkTD nullval 0 nullval)) sp *
   @field_at DCS.CS Ews t_ds (DOT _d_desc) (td_val (mkTD nullval 0 nullval)) sp *
   @field_at DCS.CS Ews t_ds (DOT _bl_desc) (td_val (mkTD nullval 0 nullval)) sp *
   @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi (w_bl_count zero_work)) sp *
   @field_at DCS.CS Ews t_ds (DOT _heap) (map vi (w_heap zero_work)) sp *
   @field_at DCS.CS Ews t_ds (DOT _heap_len) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _heap_max) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _depth) (map vi (w_depth zero_work)) sp *
   @field_at DCS.CS Ews t_ds (DOT _sym_next) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _static_len) (vl 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _matches) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _insert) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _bi_buf) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _bi_valid) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _bi_used) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _slid) (vi 0) sp)%logic.
Proof.
  unfold zrest.
  change (nested_field_type t_ds (DOT _dyn_ltree)) with (tarray t_ct HEAP_SIZE).
  change (nested_field_type t_ds (DOT _dyn_dtree)) with (tarray t_ct (2 * D_CODES + 1)).
  change (nested_field_type t_ds (DOT _bl_tree)) with (tarray t_ct (2 * BL_CODES + 1)).
  rewrite !zv_tree by (unfold HEAP_SIZE, D_CODES, BL_CODES; lia).
  change (nested_field_type t_ds (DOT _l_desc)) with t_td.
  change (nested_field_type t_ds (DOT _d_desc)) with t_td.
  change (nested_field_type t_ds (DOT _bl_desc)) with t_td.
  rewrite !zv_td.
  change (nested_field_type t_ds (DOT _heap)) with (tarray tint 573).
  change (nested_field_type t_ds (DOT _depth)) with (tarray tuchar 573).
  change (nested_field_type t_ds (DOT _bl_count)) with (tarray tushort 16).
  rewrite !zero_val_tarray.
  rewrite !zero_val_eq.
  reflexivity.
Qed.

(** The parameters accepted by deflateInit2_'s checks. *)
Lemma i_bad_false level method wbits mem strategy : -15 <= wbits -> i_bad level method wbits mem strategy = false ->
  1 <= mem <= 9 /\ method = 8 /\ 9 <= i_wb9 wbits <= 15 /\ 0 <= i_lv level <= 9 /\ 0 <= strategy <= 4 /\
  0 <= i_wr wbits <= 2.
Proof.
  intros Hw Hb. unfold i_bad in Hb. repeat rewrite orb_false_iff in Hb. decompose [and] Hb; clear Hb.
  repeat match goal with
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (?a >? ?b) = false |- _ => rewrite Z.gtb_ltb in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  end.
  assert (0 <= i_wr wbits <= 2) by (unfold i_wr; destruct (wbits <? 0), (wbits >? 15); lia).
  assert (9 <= i_wb9 wbits <= 15) by (unfold i_wb9; destruct (i_wb wbits =? 8) eqn:E;
    [|apply Z.eqb_neq in E]; lia).
  repeat split; lia.
Qed.

Lemma shl_bounds k lo hi : 0 <= lo -> lo <= k <= hi -> 2 ^ lo <= Z.shiftl 1 k <= 2 ^ hi.
Proof.
  intros H0 Hk. rewrite Z.shiftl_1_l. split; apply Z.pow_le_mono_r; lia.
Qed.

Lemma Forall_repeat0 (P : Z -> Prop) n : P 0 -> Forall P (repeat 0 n).
Proof. intros HP. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. exact HP. Qed.

Lemma mb_ok_zero n : mb_ok (mkMB (repeat 0 n) (repeat false n)).
Proof.
  split; cbn [mb_val mb_def].
  - rewrite !Zlength_repeat'. reflexivity.
  - intros i Hi Hd. rewrite Zlength_repeat' in Hi. rewrite Znth_repeat' in Hd by lia. discriminate.
Qed.

Lemma tree_ok_zero n : 0 <= n -> tree_ok (zero_tree n) n.
Proof.
  intros Hn. unfold tree_ok, zero_tree. cbn [fc dl]. rewrite !Zlength_repeat', Z2Nat.id by lia.
  split; [reflexivity|]. split; [reflexivity|].
  intros i Hi. rewrite !Znth_repeat' by (rewrite Z2Nat.id; lia). lia.
Qed.

Lemma work_ok_zero : work_ok zero_work.
Proof.
  unfold work_ok, zero_work. cbn [w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len].
  rewrite !Zlength_repeat'.
  repeat split; try reflexivity; try rep_lia; apply Forall_repeat0; rep_lia.
Qed.

Lemma out_ok_zero n : Z.of_nat n <= Int.max_unsigned -> out_ok (mkOut (repeat 0 n) 0 0 0 0) (repeat false n).
Proof.
  intros Hn. unfold out_ok. cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
  rewrite !Zlength_repeat'. split; [apply mb_ok_zero|]. repeat split; rep_lia.
Qed.

Lemma i_state_ranges level method wbits mem strategy :
  -15 <= wbits -> i_bad level method wbits mem strategy = false ->
  dstate_ranges (i_state level method wbits mem strategy).
Proof.
  intros Hw Hb. destruct (i_bad_false _ _ _ _ _ Hw Hb) as (Hm & -> & Hwb & Hlv & Hst & Hwr).
  pose proof (shl_bounds (i_wb9 wbits) 9 15 ltac:(lia) Hwb) as HW.
  pose proof (shl_bounds (mem + 7) 8 16 ltac:(lia) ltac:(lia)) as HH.
  pose proof (shl_bounds (mem + 6) 7 15 ltac:(lia) ltac:(lia)) as HL.
  unfold dstate_ranges, i_state, init_dstate, init_tstate.
  cbn [d_status d_pending_buf_size d_po d_wrap d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask
       d_window mb_val d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift
       d_block_start d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead
       d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid
       set_d_method set_d_tr d_tr].
  unfold u32, u64, u8, s32_ok, u32_ok, u64_ok, s64_ok, INIT_STATE, MIN_MATCH.
  rewrite !Zlength_repeat', !Z2Nat.id by lia.
  repeat match goal with |- _ /\ _ => split end; try apply mb_ok_zero; try (apply Forall_repeat0; lia);
    try rep_lia;
    try (match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)) end; rep_lia);
    try (apply Z.div_pos; lia);
    try (apply Z.div_le_upper_bound; rep_lia).
Qed.

(** A fresh buffer (no byte written) as the masked buffer of zeros with an all-false mask. *)
Lemma undef_buf n m p : 0 <= m -> n = m ->
  @data_at_ DCS.CS Ews (tarray tuchar n) p |--
  @data_at DCS.CS Ews (tarray tuchar (Zlength (repeat 0 (Z.to_nat m))))
    (pb_vals (repeat 0 (Z.to_nat m)) (repeat false (Z.to_nat m))) p.
Proof.
  intros Hm ->. rewrite Zlength_repeat', Z2Nat.id by lia. rewrite data_at__tarray.
  replace (pb_vals _ _) with (Zrepeat (default_val tuchar) m); [apply derives_refl|].
  change (default_val tuchar) with Vundef.
  unfold pb_vals, Zrepeat. generalize (Z.to_nat m) as k. intros k. induction k; simpl; [reflexivity|f_equal; exact IHk].
Qed.

(** (b) The written fields, the untouched zero fields and the four fresh buffers are the level-0 representation of
    the model's state [i_state] (the state deflateInit2_ hands to deflateReset). *)
Lemma init_d0 (level method wbits mem strategy : Z) (strmp sp pw pp ph pb dt : val) (gv : globals) :
  -15 <= wbits -> i_bad level method wbits mem strategy = false -> s32_ok level -> s32_ok strategy ->
  s32_ok method -> s32_ok mem ->
  let s := i_state level method wbits mem strategy in
  let p := mkDP strmp sp pw pp ph pb nullval in
  @field_at DCS.CS Ews t_ds (DOT _strm) strmp sp *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) sp *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) sp *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) nullval sp *
  @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s)) sp *
  @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) sp *
  @field_at DCS.CS Ews t_ds (DOT _w_mask) (vi (d_w_mask s)) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_bits) (vi (d_hash_bits s)) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_mask) (vi (d_hash_mask s)) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_shift) (vi (d_hash_shift s)) sp *
  @field_at DCS.CS Ews t_ds (DOT _window) pw sp *
  @field_at DCS.CS Ews t_ds (DOT _prev) pp sp *
  @field_at DCS.CS Ews t_ds (DOT _head) ph sp *
  @field_at DCS.CS Ews t_ds (DOT _high_water) (vl (d_high_water s)) sp *
  @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) (vi (tr_lit_bufsize (d_tr s))) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pb sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_buf) (offset_val (tr_lit_bufsize (d_tr s)) pb) sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi (tr_sym_end (d_tr s))) sp *
  @field_at DCS.CS Ews t_ds (DOT _level) (vi (tr_level (d_tr s))) sp *
  @field_at DCS.CS Ews t_ds (DOT _strategy) (vi (tr_strategy (d_tr s))) sp *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) sp *
  zrest sp *
  @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp *
  @data_at_ DCS.CS Ews (tarray tuchar (2 * d_w_size s)) pw *
  @data_at DCS.CS Ews (tarray tushort (Zlength (d_prev s))) (map vi (d_prev s)) pp *
  @data_at_ DCS.CS Ews (tarray tushort (d_hash_size s)) ph *
  @data_at_ DCS.CS Ews (tarray tuchar (4 * tr_lit_bufsize (d_tr s))) pb
  |-- dstate_at_d0 s p gv.
Proof.
  intros Hw Hb Hl Hs Hme Hm s p.
  pose proof (i_state_ranges level method wbits mem strategy Hw Hb) as HR.
  destruct (i_bad_false _ _ _ _ _ Hw Hb) as (Hm1 & Em & Hwb & Hlv & Hst & Hwr).
  pose proof (shl_bounds (i_wb9 wbits) 9 15 ltac:(lia) Hwb) as HW.
  pose proof (shl_bounds (mem + 7) 8 16 ltac:(lia) ltac:(lia)) as HH.
  pose proof (shl_bounds (mem + 6) 7 15 ltac:(lia) ltac:(lia)) as HL.
  rewrite zrest_vals.
  unfold dstate_at_d0, trees_at_d0, stat_at_d0, win_at, hash_at_h0, match_at, cfg_at,
    ltree_at, dtree_at, bltree_at, ldesc_at, ddesc_at, bldesc_at, work_at, out_at, sym_at, lvl_at, mb_vals.
  subst s p. rewrite (prop_true_andp _ _ HR).
  cbn [p_s p_window p_prev p_head p_pbuf p_strm p_gzhead d_trm fst snd
       d_status d_pending_buf_size d_po d_wrap d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask
       d_window mb_val mb_def d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift
       d_block_start d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead
       d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid
       d_tr d_pbm set_d_method set_d_tr i_state init_dstate init_tstate
       tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk tr_out tr_sym_next tr_sym_end tr_matches
       tr_lit_bufsize tr_level tr_strategy tr_data_type o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
  sep_apply (undef_buf (2 * Z.shiftl 1 (i_wb9 wbits)) (2 * Z.shiftl 1 (i_wb9 wbits)) pw ltac:(lia) eq_refl).
  sep_apply (undef_buf (4 * Z.shiftl 1 (mem + 6)) (Z.shiftl 1 (mem + 6) * LIT_BUFS) pb
    ltac:(unfold LIT_BUFS; lia) ltac:(unfold LIT_BUFS; lia)).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_ds (DOT _pending_out) nullval sp).
  replace (Zlength (repeat 0 (Z.to_nat (Z.shiftl 1 (mem + 7))))) with (Z.shiftl 1 (mem + 7))
    by (rewrite Zlength_repeat', Z2Nat.id; lia).
  Exists nullval nullval nullval nullval nullval nullval.
  rewrite !prop_true_andp by first
    [ apply tree_ok_zero; unfold HEAP_SIZE, D_CODES, BL_CODES; lia
    | apply work_ok_zero
    | apply out_ok_zero; rewrite Z2Nat.id by (unfold LIT_BUFS; lia); unfold LIT_BUFS; rep_lia
    | unfold u32; match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)) end; rep_lia
    | rep_lia ].
  Exists dt.
  cancel.
Qed.

(** (c) The failure path: the written fields (any values), the zero fields, the buffers each NULL or allocated, the
    state's token and padding are what deflateEnd needs ([dend_at] of [i_end_state]). *)
Lemma init_end (wbits mem : Z) (strmp sp pw pp ph pb : val)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : val) :
  let s := i_end_state wbits mem in
  let p := mkDP strmp sp pw pp ph pb nullval in
  @field_at DCS.CS Ews t_ds (DOT _strm) strmp sp *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) sp *
  @field_at DCS.CS Ews t_ds (DOT _wrap) v1 sp *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) v2 sp *
  @field_at DCS.CS Ews t_ds (DOT _w_bits) v3 sp *
  @field_at DCS.CS Ews t_ds (DOT _w_size) v4 sp *
  @field_at DCS.CS Ews t_ds (DOT _w_mask) v5 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_bits) v6 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_size) v7 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_mask) v8 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_shift) v9 sp *
  @field_at DCS.CS Ews t_ds (DOT _window) pw sp *
  @field_at DCS.CS Ews t_ds (DOT _prev) pp sp *
  @field_at DCS.CS Ews t_ds (DOT _head) ph sp *
  @field_at DCS.CS Ews t_ds (DOT _high_water) v10 sp *
  @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) v11 sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pb sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) v12 sp *
  zlate sp * zrest sp *
  @malloc_token DCS.CS Ews t_ds sp *
  opt_alloc (tarray tuchar (4 * tr_lit_bufsize (d_tr s))) pb *
  opt_alloc (tarray tushort (d_hash_size s)) ph *
  opt_alloc (tarray tushort (d_w_size s)) pp *
  opt_alloc (tarray tuchar (2 * d_w_size s)) pw
  |-- dend_at s p.
Proof.
  intros s p. unfold zlate, zrest.
  eapply derives_trans.
  { repeat apply sepcon_derives;
    match goal with
    | |- @field_at _ _ _ (DOT ?f) _ _ |-- _ =>
        first [ constr_eq f _strm | constr_eq f _status | constr_eq f _window | constr_eq f _prev
              | constr_eq f _head | constr_eq f _pending_buf ];
        apply derives_refl
    | |- @field_at _ _ _ _ _ _ |-- _ => apply field_at_field_at_
    | |- _ => apply derives_refl
    end. }
  unfold dend_at. subst p. cbn [p_strm p_s p_pbuf p_head p_prev p_window].
  repeat match goal with
  | |- context [@field_at_ ?cs ?sh ?t ?gfs ?q] => generalize (@field_at_ cs sh t gfs q); intro
  | |- context [@field_at ?cs ?sh ?t ?gfs ?v ?q] => generalize (@field_at cs sh t gfs v q); intro
  | |- context [@malloc_token ?cs ?sh ?t ?q] => generalize (@malloc_token cs sh t q); intro
  | |- context [opt_alloc ?t ?q] => generalize (opt_alloc t q); intro
  end.
  cancel.
Qed.

(** The written fields as zmemzero left them, with explicit values. *)
Lemma zset0_vals sp : zset0 sp =
  (@field_at DCS.CS Ews t_ds (DOT _strm) nullval sp *
   @field_at DCS.CS Ews t_ds (DOT _status) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _wrap) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _gzhead) nullval sp *
   @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _w_size) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _w_mask) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _hash_bits) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _hash_mask) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _hash_shift) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _window) nullval sp *
   @field_at DCS.CS Ews t_ds (DOT _prev) nullval sp *
   @field_at DCS.CS Ews t_ds (DOT _head) nullval sp *
   @field_at DCS.CS Ews t_ds (DOT _high_water) (vl 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf) nullval sp *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _sym_buf) nullval sp *
   @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _level) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _strategy) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _method) (vi 0) sp)%logic.
Proof. unfold zset0. rewrite !zero_val_eq. reflexivity. Qed.

Lemma zlate_vals sp : zlate sp =
  (@field_at DCS.CS Ews t_ds (DOT _sym_buf) nullval sp *
   @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _level) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _strategy) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _method) (vi 0) sp)%logic.
Proof. unfold zlate. rewrite !zero_val_eq. reflexivity. Qed.

(** zmemzero(s->prev, w_size * sizeof(Pos)): the bytes as unsigned shorts. *)
Lemma prev_zero (n : Z) (p : val) : 0 <= n -> @field_compatible DCS.CS (tarray tushort n) [] p ->
  @data_at DCS.CS Ews (tarray tuchar (2 * n)) (Libc.byte_vals (repeat 0 (Z.to_nat (2 * n)))) p |--
  @data_at DCS.CS Ews (tarray tushort n) (map vi (repeat 0 (Z.to_nat n))) p.
Proof.
  intros Hn FC.
  replace (2 * n)%Z with (sizeof (tarray tushort n)) by (simpl; rewrite Z.max_r by lia; lia).
  sep_apply (ZeroBytes.data_at_zero_bytes Ews (tarray tushort n) p ltac:(auto) eq_refl eq_refl FC).
  rewrite zero_val_tarray. unfold Zrepeat. rewrite map_repeat. rewrite (zero_val_eq tushort). apply derives_refl.
Qed.

(** The failure path: everything deflateEnd needs, as [dstream_end]. *)
Lemma init_end_stream (wbits mem : Z) (strmp sp pw pp ph pb dt : val) (gv : globals)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : val) :
  field_compatible t_ds [] sp ->
  let W := Z.shiftl 1 (i_wb9 wbits) in
  let HS := Z.shiftl 1 (mem + 7) in
  let LB := Z.shiftl 1 (mem + 6) in
  @field_at DCS.CS Ews t_ds (DOT _strm) strmp sp *
  @field_at DCS.CS Ews t_ds (DOT _status) (Vint (Int.repr 666)) sp *
  @field_at DCS.CS Ews t_ds (DOT _wrap) v1 sp *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) v2 sp *
  @field_at DCS.CS Ews t_ds (DOT _w_bits) v3 sp *
  @field_at DCS.CS Ews t_ds (DOT _w_size) v4 sp *
  @field_at DCS.CS Ews t_ds (DOT _w_mask) v5 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_bits) v6 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_size) v7 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_mask) v8 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_shift) v9 sp *
  @field_at DCS.CS Ews t_ds (DOT _window) pw sp *
  @field_at DCS.CS Ews t_ds (DOT _prev) pp sp *
  @field_at DCS.CS Ews t_ds (DOT _head) ph sp *
  @field_at DCS.CS Ews t_ds (DOT _high_water) v10 sp *
  @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) v11 sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pb sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) v12 sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_buf) nullval sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi 0) sp *
  @field_at DCS.CS Ews t_ds (DOT _level) (vi 0) sp *
  @field_at DCS.CS Ews t_ds (DOT _strategy) (vi 0) sp *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi 0) sp *
  zrest sp * zpad sp * @malloc_token DCS.CS Ews t_ds sp *
  (if eq_dec pb nullval then emp else
     @malloc_token DCS.CS Ews (tarray tuchar (4 * LB)) pb * @data_at_ DCS.CS Ews (tarray tuchar (4 * LB)) pb) *
  (if eq_dec ph nullval then emp else
     @malloc_token DCS.CS Ews (tarray tushort HS) ph * @data_at_ DCS.CS Ews (tarray tushort HS) ph) *
  (if eq_dec pp nullval then emp else
     @malloc_token DCS.CS Ews (tarray tushort W) pp * @data_at_ DCS.CS Ews (tarray tushort W) pp) *
  (if eq_dec pw nullval then emp else
     @malloc_token DCS.CS Ews (tarray tuchar (2 * W)) pw * @data_at_ DCS.CS Ews (tarray tuchar (2 * W)) pw) *
  func_ptr' (snd Zlib.proof.zutil.Spec.zcalloc_spec) (gv _zcalloc) * func_ptr' (snd Zlib.proof.zutil.Spec.zcfree_spec) (gv _zcfree) *
  @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp *
  @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
  @field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) strmp *
  @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) strmp *
  @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp *
  @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp
  |-- dstream_end (Some (i_end_state wbits mem)) strmp gv.
Proof.
  intros FC W HS LB.
  sep_apply (zpad_ds_pad sp FC).
  assert (Z5 : @field_at DCS.CS Ews t_ds (DOT _sym_buf) nullval sp *
   @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _level) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _strategy) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _method) (vi 0) sp |-- zlate sp) by (rewrite zlate_vals; cancel).
  sep_apply Z5.
  unfold dstream_end, zfuncs. Exists (mkDP strmp sp pw pp ph pb nullval) dt. cbn [p_strm p_s].
  pose proof (init_end wbits mem strmp sp pw pp ph pb v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12) as IE.
  cbv zeta in IE. unfold opt_alloc in IE.
  change (tr_lit_bufsize (d_tr (i_end_state wbits mem))) with LB in IE.
  change (d_hash_size (i_end_state wbits mem)) with HS in IE.
  change (d_w_size (i_end_state wbits mem)) with W in IE.
  change (d_status (i_end_state wbits mem)) with 666 in IE.
  sep_apply IE.
  entailer!. change (d_status (i_end_state wbits mem)) with 666. rep_lia.
Qed.

Lemma vl_u64' x : vl (u64 x) = vl x.
Proof.
  unfold vl, u64. f_equal. apply Int64.eqm_samerepr. unfold Int64.eqm.
  apply Zbits.eqmod_sym. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma vi_u32' x : vi (u32 x) = vi x.
Proof.
  unfold vi, u32. f_equal. apply Int.eqm_samerepr. unfold Int.eqm.
  apply Zbits.eqmod_sym. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma vi_u8 x : 0 <= x < 256 -> vi (u8 x) = vi x.
Proof. intros. unfold u8. rewrite Z.mod_small by lia. reflexivity. Qed.

(** The success path: the state and the stream as [dstream] at level 0 (deflateReset's PRE). *)
Lemma init_ok_stream (level wbits mem strategy : Z) (strmp sp pw pp ph pb dt : val) (gv : globals) :
  -15 <= wbits -> i_bad level 8 wbits mem strategy = false -> s32_ok level -> s32_ok strategy -> s32_ok mem ->
  field_compatible t_ds [] sp ->
  let W := Z.shiftl 1 (i_wb9 wbits) in
  let HS := Z.shiftl 1 (mem + 7) in
  let LB := Z.shiftl 1 (mem + 6) in
  @field_at DCS.CS Ews t_ds (DOT _strm) strmp sp *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi 42) sp *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (i_wr wbits)) sp *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) nullval sp *
  @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (i_wb9 wbits)) sp *
  @field_at DCS.CS Ews t_ds (DOT _w_size) (vi W) sp *
  @field_at DCS.CS Ews t_ds (DOT _w_mask) (vi (W - 1)) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_bits) (vi (mem + 7)) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi HS) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_mask) (vi (HS - 1)) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_shift) (vi ((mem + 7 + 3 - 1) / 3)) sp *
  @field_at DCS.CS Ews t_ds (DOT _window) pw sp *
  @field_at DCS.CS Ews t_ds (DOT _prev) pp sp *
  @field_at DCS.CS Ews t_ds (DOT _head) ph sp *
  @field_at DCS.CS Ews t_ds (DOT _high_water) (vl 0) sp *
  @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) (vi LB) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pb sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (LB * 4)) sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_buf) (offset_val LB pb) sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi ((LB - 1) * 3)) sp *
  @field_at DCS.CS Ews t_ds (DOT _level) (vi (i_lv level)) sp *
  @field_at DCS.CS Ews t_ds (DOT _strategy) (vi strategy) sp *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi 8) sp *
  zrest sp * zpad sp *
  @data_at_ DCS.CS Ews (tarray tuchar (2 * W)) pw *
  @data_at DCS.CS Ews (tarray tushort W) (map vi (repeat 0 (Z.to_nat W))) pp *
  @data_at_ DCS.CS Ews (tarray tushort HS) ph *
  @data_at_ DCS.CS Ews (tarray tuchar (4 * LB)) pb *
  @malloc_token DCS.CS Ews t_ds sp *
  @malloc_token DCS.CS Ews (tarray tuchar (2 * W)) pw *
  @malloc_token DCS.CS Ews (tarray tushort W) pp *
  @malloc_token DCS.CS Ews (tarray tushort HS) ph *
  @malloc_token DCS.CS Ews (tarray tuchar (4 * LB)) pb *
  func_ptr' (snd Zlib.proof.zutil.Spec.zcalloc_spec) (gv _zcalloc) * func_ptr' (snd Zlib.proof.zutil.Spec.zcfree_spec) (gv _zcfree) *
  @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp *
  @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
  @field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) strmp *
  @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) strmp *
  @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp *
  @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp
  |-- dstream 0 (Some (i_state level 8 wbits mem strategy)) strmp nullval gv.
Proof.
  intros Hw Hb Hl Hs Hm FC W HS LB.
  pose proof (init_d0 level 8 wbits mem strategy strmp sp pw pp ph pb dt gv Hw Hb Hl Hs ltac:(unfold s32_ok; rep_lia) Hm) as IE.
  cbv zeta in IE.
  set (s := i_state level 8 wbits mem strategy) in *.
  change (d_w_size s) with W in IE. change (d_hash_size s) with HS in IE.
  change (tr_lit_bufsize (d_tr s)) with LB in IE.
  change (Zlength (d_prev s)) with (Zlength (repeat 0 (Z.to_nat W))) in IE.
  change (d_prev s) with (repeat 0 (Z.to_nat W)) in IE.
  assert (HW0 : 0 <= W) by (apply (proj2 (Z.shiftl_nonneg 1 (i_wb9 wbits))); lia).
  replace (Zlength (repeat 0 (Z.to_nat W))) with W in IE by (rewrite Zlength_repeat', Z2Nat.id; lia).
  change (d_status s) with 42 in IE. change (d_wrap s) with (i_wr wbits) in IE.
  change (d_w_bits s) with (i_wb9 wbits) in IE. change (d_w_mask s) with (u32 (W - 1)) in IE.
  change (d_hash_bits s) with (mem + 7) in IE. change (d_hash_mask s) with (u32 (HS - 1)) in IE.
  change (d_hash_shift s) with ((mem + 7 + 3 - 1) / 3) in IE. change (d_high_water s) with 0 in IE.
  change (d_pending_buf_size s) with (u64 (LB * 4)) in IE.
  change (tr_sym_end (d_tr s)) with (u32 ((LB - 1) * 3)) in IE.
  change (tr_level (d_tr s)) with (i_lv level) in IE. change (tr_strategy (d_tr s)) with strategy in IE.
  change (d_method s) with 8 in IE.
  rewrite !vi_u32', vl_u64' in IE.
  pose proof (i_state_sizes level 8 wbits mem strategy Hw Hb) as SZ. fold s in SZ.
  unfold dstream, dstate_at', zfuncs. cbn [Z.eqb Pos.eqb].
  Exists (mkDP strmp sp pw pp ph pb nullval). cbn [p_strm p_gzhead p_s].
  sep_apply IE. sep_apply (zpad_ds_pad sp FC).
  unfold dtokens. cbn [p_s p_window p_prev p_head p_pbuf].
  change (d_w_size s) with W. change (d_hash_size s) with HS. change (tr_lit_bufsize (d_tr s)) with LB.
  entailer!.
Qed.
