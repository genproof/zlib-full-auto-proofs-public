(** * Kit for the body proof of deflateInit2_: the zmemzero'd deflate_state field by field. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.zutil.Libc.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.deflate.ZeroBytes.
Local Open Scope logic.

Definition zbytes (n : Z) : list val := Zrepeat (Vint Int.zero) n.

Lemma zbytes_byte_vals n : 0 <= n -> byte_vals (repeat 0 (Z.to_nat n)) = zbytes n.
Proof. intros. unfold byte_vals, zbytes, Zrepeat. rewrite map_repeat. reflexivity. Qed.

Lemma zbytes_split sh n k p : 0 <= k <= n -> field_compatible (tarray tuchar n) [] p ->
  @data_at DCS.CS sh (tarray tuchar n) (zbytes n) p =
  @data_at DCS.CS sh (tarray tuchar k) (zbytes k) p * @data_at DCS.CS sh (tarray tuchar (n - k)) (zbytes (n - k)) (offset_val k p).
Proof.
  intros. unfold zbytes.
  replace (Zrepeat (Vint Int.zero) n) with (Zrepeat (Vint Int.zero) k ++ Zrepeat (Vint Int.zero) (n - k))
    by (rewrite Zrepeat_app by lia; f_equal; lia).
  rewrite (split2_data_at_Tarray_app k n sh tuchar) by (rewrite Zlength_Zrepeat; lia).
  rewrite field_address0_offset.
  - simpl. rewrite Z.mul_1_l. reflexivity.
  - apply field_compatible_field_compatible0 in H0. auto with field_compatible.
Qed.

Lemma zpeel_pad n k o n' o' p : field_compatible t_ds [] p -> 0 <= o -> 0 <= k <= n ->
  o + n <= sizeof t_ds -> n' = n - k -> o' = o + k ->
  @data_at DCS.CS Ews (tarray tuchar n) (zbytes n) (offset_val o p) |--
  @data_at DCS.CS Ews (tarray tuchar k) (zbytes k) (offset_val o p) *
  @data_at DCS.CS Ews (tarray tuchar n') (zbytes n') (offset_val o' p).
Proof.
  intros FC Ho Hk Hn -> ->.
  assert_PROP (field_compatible (tarray tuchar n) [] (offset_val o p)) as FC2 by entailer!.
  rewrite (zbytes_split Ews n k) by auto. rewrite offset_offset_val. apply derives_refl.
Qed.

Lemma zpeel2 f n o p n' o' : field_compatible t_ds [] p ->
  in_members f (co_members (get_co _internal_state)) ->
  o = nested_field_offset t_ds (DOT f) ->
  complete_legal_cosu_type (nested_field_type t_ds (DOT f)) = true ->
  fully_nonvolatile (rank_type cenv_cs (nested_field_type t_ds (DOT f))) (nested_field_type t_ds (DOT f)) = true ->
  0 <= sizeof (nested_field_type t_ds (DOT f)) <= n ->
  o + n <= sizeof t_ds ->
  n' = n - sizeof (nested_field_type t_ds (DOT f)) ->
  o' = o + sizeof (nested_field_type t_ds (DOT f)) ->
  @data_at DCS.CS Ews (tarray tuchar n) (zbytes n) (offset_val o p) |--
  @field_at DCS.CS Ews t_ds (DOT f) (zero_val (nested_field_type t_ds (DOT f))) p *
  @data_at DCS.CS Ews (tarray tuchar n') (zbytes n') (offset_val o' p).
Proof.
  intros FC IM Ho HC HV Hn Hon -> ->.
  set (ft := nested_field_type t_ds (DOT f)) in *.
  assert_PROP (field_compatible (tarray tuchar n) [] (offset_val o p)) as FC2 by entailer!.
  rewrite (zbytes_split Ews n (sizeof ft)) by auto.
  rewrite offset_offset_val. apply sepcon_derives; [ | apply derives_refl].
  assert (FCf: field_compatible t_ds (DOT f) p).
  { apply field_compatible_cons; split; auto. }
  rewrite field_at_data_at. rewrite field_compatible_field_address by auto. rewrite <- Ho.
  rewrite <- zbytes_byte_vals by lia.
  apply data_at_zero_bytes; auto.
  subst o. apply field_compatible_nested_field. auto.
Qed.

Ltac sd := first [ reflexivity | split; vm_compute; congruence | vm_compute; congruence | cbv; tauto ].

Definition zds (sp : val) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _strm) (zero_val (nested_field_type t_ds (DOT _strm))) sp *
  @field_at DCS.CS Ews t_ds (DOT _status) (zero_val (nested_field_type t_ds (DOT _status))) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) (zero_val (nested_field_type t_ds (DOT _pending_buf))) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (zero_val (nested_field_type t_ds (DOT _pending_buf_size))) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_out) (zero_val (nested_field_type t_ds (DOT _pending_out))) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending) (zero_val (nested_field_type t_ds (DOT _pending))) sp *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (zero_val (nested_field_type t_ds (DOT _wrap))) sp *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (zero_val (nested_field_type t_ds (DOT _gzhead))) sp *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (zero_val (nested_field_type t_ds (DOT _gzindex))) sp *
  @field_at DCS.CS Ews t_ds (DOT _method) (zero_val (nested_field_type t_ds (DOT _method))) sp *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (zero_val (nested_field_type t_ds (DOT _last_flush))) sp *
  @field_at DCS.CS Ews t_ds (DOT _w_size) (zero_val (nested_field_type t_ds (DOT _w_size))) sp *
  @field_at DCS.CS Ews t_ds (DOT _w_bits) (zero_val (nested_field_type t_ds (DOT _w_bits))) sp *
  @field_at DCS.CS Ews t_ds (DOT _w_mask) (zero_val (nested_field_type t_ds (DOT _w_mask))) sp *
  @field_at DCS.CS Ews t_ds (DOT _window) (zero_val (nested_field_type t_ds (DOT _window))) sp *
  @field_at DCS.CS Ews t_ds (DOT _window_size) (zero_val (nested_field_type t_ds (DOT _window_size))) sp *
  @field_at DCS.CS Ews t_ds (DOT _prev) (zero_val (nested_field_type t_ds (DOT _prev))) sp *
  @field_at DCS.CS Ews t_ds (DOT _head) (zero_val (nested_field_type t_ds (DOT _head))) sp *
  @field_at DCS.CS Ews t_ds (DOT _ins_h) (zero_val (nested_field_type t_ds (DOT _ins_h))) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_size) (zero_val (nested_field_type t_ds (DOT _hash_size))) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_bits) (zero_val (nested_field_type t_ds (DOT _hash_bits))) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_mask) (zero_val (nested_field_type t_ds (DOT _hash_mask))) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_shift) (zero_val (nested_field_type t_ds (DOT _hash_shift))) sp *
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
  @field_at DCS.CS Ews t_ds (DOT _level) (zero_val (nested_field_type t_ds (DOT _level))) sp *
  @field_at DCS.CS Ews t_ds (DOT _strategy) (zero_val (nested_field_type t_ds (DOT _strategy))) sp *
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
  @field_at DCS.CS Ews t_ds (DOT _sym_buf) (zero_val (nested_field_type t_ds (DOT _sym_buf))) sp *
  @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) (zero_val (nested_field_type t_ds (DOT _lit_bufsize))) sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_next) (zero_val (nested_field_type t_ds (DOT _sym_next))) sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_end) (zero_val (nested_field_type t_ds (DOT _sym_end))) sp *
  @field_at DCS.CS Ews t_ds (DOT _opt_len) (zero_val (nested_field_type t_ds (DOT _opt_len))) sp *
  @field_at DCS.CS Ews t_ds (DOT _static_len) (zero_val (nested_field_type t_ds (DOT _static_len))) sp *
  @field_at DCS.CS Ews t_ds (DOT _matches) (zero_val (nested_field_type t_ds (DOT _matches))) sp *
  @field_at DCS.CS Ews t_ds (DOT _insert) (zero_val (nested_field_type t_ds (DOT _insert))) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_buf) (zero_val (nested_field_type t_ds (DOT _bi_buf))) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_valid) (zero_val (nested_field_type t_ds (DOT _bi_valid))) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_used) (zero_val (nested_field_type t_ds (DOT _bi_used))) sp *
  @field_at DCS.CS Ews t_ds (DOT _high_water) (zero_val (nested_field_type t_ds (DOT _high_water))) sp *
  @field_at DCS.CS Ews t_ds (DOT _slid) (zero_val (nested_field_type t_ds (DOT _slid))) sp)%logic.

Definition zpad (sp : val) : mpred :=
  (@data_at DCS.CS Ews (tarray tuchar 4) (zbytes 4) (offset_val 12 sp) *
  @data_at DCS.CS Ews (tarray tuchar 4) (zbytes 4) (offset_val 52 sp) *
  @data_at DCS.CS Ews (tarray tuchar 3) (zbytes 3) (offset_val 73 sp) *
  @data_at DCS.CS Ews (tarray tuchar 4) (zbytes 4) (offset_val 92 sp) *
  @data_at DCS.CS Ews (tarray tuchar 4) (zbytes 4) (offset_val 148 sp) *
  @data_at DCS.CS Ews (tarray tuchar 7) (zbytes 7) (offset_val 5881 sp) *
  @data_at DCS.CS Ews (tarray tuchar 4) (zbytes 4) (offset_val 5908 sp) *
  @data_at DCS.CS Ews (tarray tuchar 2) (zbytes 2) (offset_val 5938 sp) *
  @data_at DCS.CS Ews (tarray tuchar 4) (zbytes 4) (offset_val 5948 sp) *
  @data_at DCS.CS Ews (tarray tuchar 4) (zbytes 4) (offset_val 5964 sp))%logic.


(** The struct right after zmemzero: every field its zero value, and the padding (zero bytes). *)
Lemma zero_ds sp : field_compatible t_ds [] sp ->
  @data_at DCS.CS Ews (tarray tuchar 5968) (zbytes 5968) sp |-- zds sp * zpad sp.
Proof.
  intros FC.
  assert (E: sp = offset_val 0 sp) by (destruct sp; try (destruct FC; contradiction); simpl; rewrite Ptrofs.add_zero; auto).
  rewrite E at 1. clear E.
  sep_apply (zpeel2 _strm 5968 0 sp 5960 8 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _status 5960 8 sp 5956 12 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel_pad 5956 4 12 5952 16 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _pending_buf 5952 16 sp 5944 24 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _pending_buf_size 5944 24 sp 5936 32 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _pending_out 5936 32 sp 5928 40 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _pending 5928 40 sp 5920 48 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _wrap 5920 48 sp 5916 52 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel_pad 5916 4 52 5912 56 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _gzhead 5912 56 sp 5904 64 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _gzindex 5904 64 sp 5896 72 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _method 5896 72 sp 5895 73 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel_pad 5895 3 73 5892 76 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _last_flush 5892 76 sp 5888 80 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _w_size 5888 80 sp 5884 84 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _w_bits 5884 84 sp 5880 88 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _w_mask 5880 88 sp 5876 92 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel_pad 5876 4 92 5872 96 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _window 5872 96 sp 5864 104 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _window_size 5864 104 sp 5856 112 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _prev 5856 112 sp 5848 120 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _head 5848 120 sp 5840 128 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _ins_h 5840 128 sp 5836 132 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _hash_size 5836 132 sp 5832 136 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _hash_bits 5832 136 sp 5828 140 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _hash_mask 5828 140 sp 5824 144 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _hash_shift 5824 144 sp 5820 148 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel_pad 5820 4 148 5816 152 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _block_start 5816 152 sp 5808 160 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _match_length 5808 160 sp 5804 164 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _prev_match 5804 164 sp 5800 168 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _match_available 5800 168 sp 5796 172 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _strstart 5796 172 sp 5792 176 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _match_start 5792 176 sp 5788 180 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _lookahead 5788 180 sp 5784 184 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _prev_length 5784 184 sp 5780 188 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _max_chain_length 5780 188 sp 5776 192 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _max_lazy_match 5776 192 sp 5772 196 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _level 5772 196 sp 5768 200 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _strategy 5768 200 sp 5764 204 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _good_match 5764 204 sp 5760 208 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _nice_match 5760 208 sp 5756 212 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _dyn_ltree 5756 212 sp 3464 2504 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _dyn_dtree 3464 2504 sp 3220 2748 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _bl_tree 3220 2748 sp 3064 2904 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _l_desc 3064 2904 sp 3040 2928 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _d_desc 3040 2928 sp 3016 2952 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _bl_desc 3016 2952 sp 2992 2976 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _bl_count 2992 2976 sp 2960 3008 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _heap 2960 3008 sp 668 5300 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _heap_len 668 5300 sp 664 5304 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _heap_max 664 5304 sp 660 5308 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _depth 660 5308 sp 87 5881 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel_pad 87 7 5881 80 5888 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _sym_buf 80 5888 sp 72 5896 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _lit_bufsize 72 5896 sp 68 5900 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _sym_next 68 5900 sp 64 5904 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _sym_end 64 5904 sp 60 5908 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel_pad 60 4 5908 56 5912 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _opt_len 56 5912 sp 48 5920 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _static_len 48 5920 sp 40 5928 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _matches 40 5928 sp 36 5932 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _insert 36 5932 sp 32 5936 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _bi_buf 32 5936 sp 30 5938 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel_pad 30 2 5938 28 5940 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _bi_valid 28 5940 sp 24 5944 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _bi_used 24 5944 sp 20 5948 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel_pad 20 4 5948 16 5952 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _high_water 16 5952 sp 8 5960 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  sep_apply (zpeel2 _slid 8 5960 sp 4 5964 FC ltac:(sd) eq_refl ltac:(sd) ltac:(sd) ltac:(sd) ltac:(sd) eq_refl eq_refl).
  unfold zds, zpad. cancel.
Qed.
