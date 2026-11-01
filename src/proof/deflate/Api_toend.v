(** * The conversion ob_dstream_to_end. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DSpec Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.deflate.ApiKit.

Lemma opt_alloc_intro (t : type) (q : val) :
  (@malloc_token DCS.CS Ews t q * @data_at_ DCS.CS Ews t q)%logic |-- opt_alloc t q.
Proof.
  unfold opt_alloc. destruct (eq_dec q nullval).
  - subst. entailer!.
  - cancel.
Qed.

Ltac fa_ f := sep_apply (@field_at_field_at_ DCS.CS Ews t_ds (DOT f)).

(** trees.c's field names (Zlib.trees.code) are other constants with the same values: [change] them to
    deflate.c's.  Each group of fields is converted by its own lemma (one big [cancel] makes Qed very slow);
    field_at etc. are opaque so that [cancel] matches syntactically. *)
Local Opaque field_at field_at_ data_at data_at_ malloc_token opt_alloc zfuncs.



Lemma work_end w sp :
  work_at w sp |--
  (   @field_at_ DCS.CS Ews t_ds (DOT _heap) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _heap_len) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _heap_max) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _depth) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _bl_count) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _opt_len) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _static_len) sp)%logic.
Proof.
  unfold work_at. Intros.
  change Zlib.trees.code._heap with Zlib.deflate.code._heap.
  change Zlib.trees.code._heap_len with Zlib.deflate.code._heap_len.
  change Zlib.trees.code._heap_max with Zlib.deflate.code._heap_max.
  change Zlib.trees.code._depth with Zlib.deflate.code._depth.
  change Zlib.trees.code._bl_count with Zlib.deflate.code._bl_count.
  change Zlib.trees.code._opt_len with Zlib.deflate.code._opt_len.
  change Zlib.trees.code._static_len with Zlib.deflate.code._static_len.
  fa_ Zlib.deflate.code._heap.
  fa_ Zlib.deflate.code._heap_len.
  fa_ Zlib.deflate.code._heap_max.
  fa_ Zlib.deflate.code._depth.
  fa_ Zlib.deflate.code._bl_count.
  fa_ Zlib.deflate.code._opt_len.
  fa_ Zlib.deflate.code._static_len.
  cancel.
Qed.

Lemma sym_end s sp pbp :
  sym_at s sp pbp |--
  (   @field_at_ DCS.CS Ews t_ds (DOT _sym_buf) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _lit_bufsize) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _sym_next) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _sym_end) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _matches) sp)%logic.
Proof.
  unfold sym_at. Intros.
  change Zlib.trees.code._sym_buf with Zlib.deflate.code._sym_buf.
  change Zlib.trees.code._lit_bufsize with Zlib.deflate.code._lit_bufsize.
  change Zlib.trees.code._sym_next with Zlib.deflate.code._sym_next.
  change Zlib.trees.code._sym_end with Zlib.deflate.code._sym_end.
  change Zlib.trees.code._matches with Zlib.deflate.code._matches.
  fa_ Zlib.deflate.code._sym_buf.
  fa_ Zlib.deflate.code._lit_bufsize.
  fa_ Zlib.deflate.code._sym_next.
  fa_ Zlib.deflate.code._sym_end.
  fa_ Zlib.deflate.code._matches.
  cancel.
Qed.

Lemma lvl_end s sp :
  lvl_at s sp |--
  (   @field_at_ DCS.CS Ews t_ds (DOT _level) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _strategy) sp)%logic.
Proof.
  unfold lvl_at. Intros.
  change Zlib.trees.code._level with Zlib.deflate.code._level.
  change Zlib.trees.code._strategy with Zlib.deflate.code._strategy.
  fa_ Zlib.deflate.code._level.
  fa_ Zlib.deflate.code._strategy.
  cancel.
Qed.

Lemma tr3_end s sp :
  (ltree_at (tr_ltree s) sp * dtree_at (tr_dtree s) sp * bltree_at (tr_bltree s) sp)%logic |--
  (   @field_at_ DCS.CS Ews t_ds (DOT _dyn_ltree) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _dyn_dtree) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _bl_tree) sp)%logic.
Proof.
  unfold ltree_at, dtree_at, bltree_at. Intros.
  change Zlib.trees.code._dyn_ltree with Zlib.deflate.code._dyn_ltree.
  change Zlib.trees.code._dyn_dtree with Zlib.deflate.code._dyn_dtree.
  change Zlib.trees.code._bl_tree with Zlib.deflate.code._bl_tree.
  fa_ Zlib.deflate.code._dyn_ltree.
  fa_ Zlib.deflate.code._dyn_dtree.
  fa_ Zlib.deflate.code._bl_tree.
  cancel.
Qed.

Lemma desc_end a b c d e f g h i sp :
  (ldesc_at a b c sp * ddesc_at d e f sp * bldesc_at g h i sp)%logic |--
  (   @field_at_ DCS.CS Ews t_ds (DOT _l_desc) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _d_desc) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _bl_desc) sp)%logic.
Proof.
  unfold ldesc_at, ddesc_at, bldesc_at. Intros.
  change Zlib.trees.code._l_desc with Zlib.deflate.code._l_desc.
  change Zlib.trees.code._d_desc with Zlib.deflate.code._d_desc.
  change Zlib.trees.code._bl_desc with Zlib.deflate.code._bl_desc.
  fa_ Zlib.deflate.code._l_desc.
  fa_ Zlib.deflate.code._d_desc.
  fa_ Zlib.deflate.code._bl_desc.
  cancel.
Qed.

Lemma out_end o m sp pbp :
  out_at o m sp pbp |--
  (@field_at DCS.CS Ews t_ds (DOT _pending_buf) pbp sp *
   @data_at_ DCS.CS Ews (tarray tuchar (Zlength (o_buf o))) pbp *
   @field_at_ DCS.CS Ews t_ds (DOT _pending) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _bi_buf) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _bi_valid) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _bi_used) sp)%logic.
Proof.
  unfold out_at. Intros.
  change Zlib.trees.code._pending with Zlib.deflate.code._pending.
  change Zlib.trees.code._bi_buf with Zlib.deflate.code._bi_buf.
  change Zlib.trees.code._bi_valid with Zlib.deflate.code._bi_valid.
  change Zlib.trees.code._bi_used with Zlib.deflate.code._bi_used.
  change Zlib.trees.code._pending_buf with Zlib.deflate.code._pending_buf.
  sep_apply (@data_at_data_at_ DCS.CS Ews (tarray tuchar (Zlength (o_buf o)))).
  fa_ Zlib.deflate.code._pending.
  fa_ Zlib.deflate.code._bi_buf.
  fa_ Zlib.deflate.code._bi_valid.
  fa_ Zlib.deflate.code._bi_used.
  cancel.
Qed.

Lemma dtype_end s sp strmp :
  dtype_at s sp strmp |--
  (@field_at DCS.CS Ews t_ds (DOT _strm) strmp sp *
   EX dt : val, @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp)%logic.
Proof.
  unfold dtype_at. Intros.
  change Zlib.trees.code._strm with Zlib.deflate.code._strm.
  change Zlib.trees.code._data_type with Zlib.deflate.code._data_type.
  Exists (vi (tr_data_type s)). cancel.
Qed.

Lemma win_end s p :
  win_at s p |--
  (@field_at DCS.CS Ews t_ds (DOT _window) (p_window p) (p_s p) *
   @data_at_ DCS.CS Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (p_window p) *
   @field_at_ DCS.CS Ews t_ds (DOT _window_size) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _w_size) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _w_bits) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _w_mask) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _high_water) (p_s p))%logic.
Proof.
  unfold win_at.
  sep_apply (@data_at_data_at_ DCS.CS Ews (tarray tuchar (Zlength (mb_val (d_window s))))).
  fa_ Zlib.deflate.code._window_size.
  fa_ Zlib.deflate.code._w_size.
  fa_ Zlib.deflate.code._w_bits.
  fa_ Zlib.deflate.code._w_mask.
  fa_ Zlib.deflate.code._high_water.
  cancel.
Qed.

Lemma hash_end s p :
  hash_at s p |--
  (@field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p) *
   @data_at_ DCS.CS Ews (tarray tushort (Zlength (d_prev s))) (p_prev p) *
   @data_at_ DCS.CS Ews (tarray tushort (Zlength (d_head s))) (p_head p) *
   @field_at_ DCS.CS Ews t_ds (DOT _ins_h) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _hash_size) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _hash_bits) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _hash_mask) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _hash_shift) (p_s p))%logic.
Proof.
  unfold hash_at.
  sep_apply (@data_at_data_at_ DCS.CS Ews (tarray tushort (Zlength (d_prev s)))).
  sep_apply (@data_at_data_at_ DCS.CS Ews (tarray tushort (Zlength (d_head s)))).
  fa_ Zlib.deflate.code._ins_h.
  fa_ Zlib.deflate.code._hash_size.
  fa_ Zlib.deflate.code._hash_bits.
  fa_ Zlib.deflate.code._hash_mask.
  fa_ Zlib.deflate.code._hash_shift.
  cancel.
Qed.

Lemma match_end s p :
  match_at s p |--
  (   @field_at_ DCS.CS Ews t_ds (DOT _block_start) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _match_length) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _prev_match) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _match_available) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _strstart) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _match_start) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _lookahead) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _prev_length) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _insert) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _slid) (p_s p))%logic.
Proof.
  unfold match_at.
  fa_ Zlib.deflate.code._block_start.
  fa_ Zlib.deflate.code._match_length.
  fa_ Zlib.deflate.code._prev_match.
  fa_ Zlib.deflate.code._match_available.
  fa_ Zlib.deflate.code._strstart.
  fa_ Zlib.deflate.code._match_start.
  fa_ Zlib.deflate.code._lookahead.
  fa_ Zlib.deflate.code._prev_length.
  fa_ Zlib.deflate.code._insert.
  fa_ Zlib.deflate.code._slid.
  cancel.
Qed.

Lemma cfg_end s p :
  cfg_at s p |--
  (   @field_at_ DCS.CS Ews t_ds (DOT _max_chain_length) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _max_lazy_match) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _good_match) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _nice_match) (p_s p))%logic.
Proof.
  unfold cfg_at.
  fa_ Zlib.deflate.code._max_chain_length.
  fa_ Zlib.deflate.code._max_lazy_match.
  fa_ Zlib.deflate.code._good_match.
  fa_ Zlib.deflate.code._nice_match.
  cancel.
Qed.

Lemma stat_end s p :
  stat_at s p |--
  (@field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _pending_buf_size) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _pending_out) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _wrap) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _gzhead) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _gzindex) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _method) (p_s p) *
   @field_at_ DCS.CS Ews t_ds (DOT _last_flush) (p_s p))%logic.
Proof.
  unfold stat_at.
  fa_ Zlib.deflate.code._pending_buf_size.
  fa_ Zlib.deflate.code._pending_out.
  fa_ Zlib.deflate.code._wrap.
  fa_ Zlib.deflate.code._gzhead.
  fa_ Zlib.deflate.code._gzindex.
  fa_ Zlib.deflate.code._method.
  fa_ Zlib.deflate.code._last_flush.
  cancel.
Qed.

Lemma dstream_to_end : ob_dstream_to_end.
Proof.
  unfold ob_dstream_to_end; intros. unfold dstream, dstream_end.
  destruct os as [s|].
  2:{ Intros za zf op dt. Exists za zf op dt. entailer!. }
  Intros p. Exists p. rewrite dstate_at'_2. unfold dstate_at, dtokens, trees_at. Intros.
  destruct H as [? [? [? ?]]]. destruct H1 as [Hw [Hp [Hh Hb]]].
  sep_apply win_end. sep_apply hash_end. sep_apply match_end. sep_apply cfg_end. sep_apply stat_end.
  sep_apply tr3_end. sep_apply desc_end. sep_apply work_end. sep_apply out_end. sep_apply sym_end.
  sep_apply lvl_end. sep_apply dtype_end. Intros dt.
  unfold d_trm; cbn [fst snd].
  rewrite Hw, Hp, Hh, Hb. unfold dend_at.
  sep_apply (opt_alloc_intro (tarray tuchar (4 * tr_lit_bufsize (d_tr s))) (p_pbuf p)).
  sep_apply (opt_alloc_intro (tarray tuchar (2 * d_w_size s)) (p_window p)).
  sep_apply (opt_alloc_intro (tarray tushort (d_w_size s)) (p_prev p)).
  sep_apply (opt_alloc_intro (tarray tushort (d_hash_size s)) (p_head p)).
  Exists dt.
  apply andp_right; [apply prop_right; split; [reflexivity | unfold dstate_ranges, s32_ok in H2; tauto] |].
  cancel.
Qed.
