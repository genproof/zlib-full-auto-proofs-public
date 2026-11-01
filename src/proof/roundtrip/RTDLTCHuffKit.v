(** * Kit for the deflate_huff part: definitions, part statements, small lemmas.

    deflate_huff is proved over the invariant [W s /\ huff_extra s]: [W] alone allows a huff state whose
    pending symbols are matches, and then a block can reach 65536 bytes with block_start >= 0 (fbo_pre and
    ev_ok need at most 65535); [huff_extra] says the pending block holds only literals (blk_len <= count).

    Parts (statements [*_stmt] below):
    - [hfbw_stmt]: FLUSH_BLOCK_ONLY at a huff state with the symbols [syms] ([HS0]);
    - [hlit_stmt]: the literal step ([hlit]);
    - [hrefill_stmt]: fill_window when lookahead = 0;
    - [hbflush_stmt]: [if (bflush) FLUSH_BLOCK(s, 0)] (c_bflush), from [hfbw_stmt];
    - [htail_stmt]: deflate_tail after the loop, from [hfbw_stmt].
    The glue (loop, final assembly) is in RTDLTCHuff2.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCSpecs2.
Require Zlib.proof.huffman.HuffAbs.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Projections of the setters: [autorewrite with hproj in *]
    ([cbn] does not reduce [d_F (set_d_G s x)] well: use these lemmas). *)
Lemma hk_status_po s x : d_status (set_d_po s x) = d_status s. Proof. reflexivity. Qed.
Lemma hk_po_po s x : d_po (set_d_po s x) = x. Proof. reflexivity. Qed.
Lemma hk_wrap_po s x : d_wrap (set_d_po s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma hk_gzhead_po s x : d_gzhead (set_d_po s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma hk_gzindex_po s x : d_gzindex (set_d_po s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma hk_method_po s x : d_method (set_d_po s x) = d_method s. Proof. reflexivity. Qed.
Lemma hk_last_flush_po s x : d_last_flush (set_d_po s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma hk_w_size_po s x : d_w_size (set_d_po s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma hk_w_bits_po s x : d_w_bits (set_d_po s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma hk_w_mask_po s x : d_w_mask (set_d_po s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma hk_window_po s x : d_window (set_d_po s x) = d_window s. Proof. reflexivity. Qed.
Lemma hk_window_size_po s x : d_window_size (set_d_po s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma hk_prev_po s x : d_prev (set_d_po s x) = d_prev s. Proof. reflexivity. Qed.
Lemma hk_head_po s x : d_head (set_d_po s x) = d_head s. Proof. reflexivity. Qed.
Lemma hk_ins_h_po s x : d_ins_h (set_d_po s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma hk_hash_size_po s x : d_hash_size (set_d_po s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma hk_hash_bits_po s x : d_hash_bits (set_d_po s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma hk_hash_mask_po s x : d_hash_mask (set_d_po s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma hk_hash_shift_po s x : d_hash_shift (set_d_po s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma hk_block_start_po s x : d_block_start (set_d_po s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma hk_match_length_po s x : d_match_length (set_d_po s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma hk_prev_match_po s x : d_prev_match (set_d_po s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma hk_match_available_po s x : d_match_available (set_d_po s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma hk_strstart_po s x : d_strstart (set_d_po s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma hk_match_start_po s x : d_match_start (set_d_po s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma hk_lookahead_po s x : d_lookahead (set_d_po s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma hk_prev_length_po s x : d_prev_length (set_d_po s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma hk_max_chain_length_po s x : d_max_chain_length (set_d_po s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma hk_max_lazy_match_po s x : d_max_lazy_match (set_d_po s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma hk_good_match_po s x : d_good_match (set_d_po s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma hk_nice_match_po s x : d_nice_match (set_d_po s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma hk_insert_po s x : d_insert (set_d_po s x) = d_insert s. Proof. reflexivity. Qed.
Lemma hk_high_water_po s x : d_high_water (set_d_po s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma hk_slid_po s x : d_slid (set_d_po s x) = d_slid s. Proof. reflexivity. Qed.
Lemma hk_pending_buf_size_po s x : d_pending_buf_size (set_d_po s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma hk_tr_po s x : d_tr (set_d_po s x) = d_tr s. Proof. reflexivity. Qed.
Lemma hk_pbm_po s x : d_pbm (set_d_po s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma hk_status_prev s x : d_status (set_d_prev s x) = d_status s. Proof. reflexivity. Qed.
Lemma hk_po_prev s x : d_po (set_d_prev s x) = d_po s. Proof. reflexivity. Qed.
Lemma hk_wrap_prev s x : d_wrap (set_d_prev s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma hk_gzhead_prev s x : d_gzhead (set_d_prev s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma hk_gzindex_prev s x : d_gzindex (set_d_prev s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma hk_method_prev s x : d_method (set_d_prev s x) = d_method s. Proof. reflexivity. Qed.
Lemma hk_last_flush_prev s x : d_last_flush (set_d_prev s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma hk_w_size_prev s x : d_w_size (set_d_prev s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma hk_w_bits_prev s x : d_w_bits (set_d_prev s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma hk_w_mask_prev s x : d_w_mask (set_d_prev s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma hk_window_prev s x : d_window (set_d_prev s x) = d_window s. Proof. reflexivity. Qed.
Lemma hk_window_size_prev s x : d_window_size (set_d_prev s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma hk_prev_prev s x : d_prev (set_d_prev s x) = x. Proof. reflexivity. Qed.
Lemma hk_head_prev s x : d_head (set_d_prev s x) = d_head s. Proof. reflexivity. Qed.
Lemma hk_ins_h_prev s x : d_ins_h (set_d_prev s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma hk_hash_size_prev s x : d_hash_size (set_d_prev s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma hk_hash_bits_prev s x : d_hash_bits (set_d_prev s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma hk_hash_mask_prev s x : d_hash_mask (set_d_prev s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma hk_hash_shift_prev s x : d_hash_shift (set_d_prev s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma hk_block_start_prev s x : d_block_start (set_d_prev s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma hk_match_length_prev s x : d_match_length (set_d_prev s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma hk_prev_match_prev s x : d_prev_match (set_d_prev s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma hk_match_available_prev s x : d_match_available (set_d_prev s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma hk_strstart_prev s x : d_strstart (set_d_prev s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma hk_match_start_prev s x : d_match_start (set_d_prev s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma hk_lookahead_prev s x : d_lookahead (set_d_prev s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma hk_prev_length_prev s x : d_prev_length (set_d_prev s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma hk_max_chain_length_prev s x : d_max_chain_length (set_d_prev s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma hk_max_lazy_match_prev s x : d_max_lazy_match (set_d_prev s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma hk_good_match_prev s x : d_good_match (set_d_prev s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma hk_nice_match_prev s x : d_nice_match (set_d_prev s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma hk_insert_prev s x : d_insert (set_d_prev s x) = d_insert s. Proof. reflexivity. Qed.
Lemma hk_high_water_prev s x : d_high_water (set_d_prev s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma hk_slid_prev s x : d_slid (set_d_prev s x) = d_slid s. Proof. reflexivity. Qed.
Lemma hk_pending_buf_size_prev s x : d_pending_buf_size (set_d_prev s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma hk_tr_prev s x : d_tr (set_d_prev s x) = d_tr s. Proof. reflexivity. Qed.
Lemma hk_pbm_prev s x : d_pbm (set_d_prev s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma hk_status_head s x : d_status (set_d_head s x) = d_status s. Proof. reflexivity. Qed.
Lemma hk_po_head s x : d_po (set_d_head s x) = d_po s. Proof. reflexivity. Qed.
Lemma hk_wrap_head s x : d_wrap (set_d_head s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma hk_gzhead_head s x : d_gzhead (set_d_head s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma hk_gzindex_head s x : d_gzindex (set_d_head s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma hk_method_head s x : d_method (set_d_head s x) = d_method s. Proof. reflexivity. Qed.
Lemma hk_last_flush_head s x : d_last_flush (set_d_head s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma hk_w_size_head s x : d_w_size (set_d_head s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma hk_w_bits_head s x : d_w_bits (set_d_head s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma hk_w_mask_head s x : d_w_mask (set_d_head s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma hk_window_head s x : d_window (set_d_head s x) = d_window s. Proof. reflexivity. Qed.
Lemma hk_window_size_head s x : d_window_size (set_d_head s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma hk_prev_head s x : d_prev (set_d_head s x) = d_prev s. Proof. reflexivity. Qed.
Lemma hk_head_head s x : d_head (set_d_head s x) = x. Proof. reflexivity. Qed.
Lemma hk_ins_h_head s x : d_ins_h (set_d_head s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma hk_hash_size_head s x : d_hash_size (set_d_head s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma hk_hash_bits_head s x : d_hash_bits (set_d_head s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma hk_hash_mask_head s x : d_hash_mask (set_d_head s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma hk_hash_shift_head s x : d_hash_shift (set_d_head s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma hk_block_start_head s x : d_block_start (set_d_head s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma hk_match_length_head s x : d_match_length (set_d_head s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma hk_prev_match_head s x : d_prev_match (set_d_head s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma hk_match_available_head s x : d_match_available (set_d_head s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma hk_strstart_head s x : d_strstart (set_d_head s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma hk_match_start_head s x : d_match_start (set_d_head s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma hk_lookahead_head s x : d_lookahead (set_d_head s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma hk_prev_length_head s x : d_prev_length (set_d_head s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma hk_max_chain_length_head s x : d_max_chain_length (set_d_head s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma hk_max_lazy_match_head s x : d_max_lazy_match (set_d_head s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma hk_good_match_head s x : d_good_match (set_d_head s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma hk_nice_match_head s x : d_nice_match (set_d_head s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma hk_insert_head s x : d_insert (set_d_head s x) = d_insert s. Proof. reflexivity. Qed.
Lemma hk_high_water_head s x : d_high_water (set_d_head s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma hk_slid_head s x : d_slid (set_d_head s x) = d_slid s. Proof. reflexivity. Qed.
Lemma hk_pending_buf_size_head s x : d_pending_buf_size (set_d_head s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma hk_tr_head s x : d_tr (set_d_head s x) = d_tr s. Proof. reflexivity. Qed.
Lemma hk_pbm_head s x : d_pbm (set_d_head s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma hk_status_ins_h s x : d_status (set_d_ins_h s x) = d_status s. Proof. reflexivity. Qed.
Lemma hk_po_ins_h s x : d_po (set_d_ins_h s x) = d_po s. Proof. reflexivity. Qed.
Lemma hk_wrap_ins_h s x : d_wrap (set_d_ins_h s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma hk_gzhead_ins_h s x : d_gzhead (set_d_ins_h s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma hk_gzindex_ins_h s x : d_gzindex (set_d_ins_h s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma hk_method_ins_h s x : d_method (set_d_ins_h s x) = d_method s. Proof. reflexivity. Qed.
Lemma hk_last_flush_ins_h s x : d_last_flush (set_d_ins_h s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma hk_w_size_ins_h s x : d_w_size (set_d_ins_h s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma hk_w_bits_ins_h s x : d_w_bits (set_d_ins_h s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma hk_w_mask_ins_h s x : d_w_mask (set_d_ins_h s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma hk_window_ins_h s x : d_window (set_d_ins_h s x) = d_window s. Proof. reflexivity. Qed.
Lemma hk_window_size_ins_h s x : d_window_size (set_d_ins_h s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma hk_prev_ins_h s x : d_prev (set_d_ins_h s x) = d_prev s. Proof. reflexivity. Qed.
Lemma hk_head_ins_h s x : d_head (set_d_ins_h s x) = d_head s. Proof. reflexivity. Qed.
Lemma hk_ins_h_ins_h s x : d_ins_h (set_d_ins_h s x) = x. Proof. reflexivity. Qed.
Lemma hk_hash_size_ins_h s x : d_hash_size (set_d_ins_h s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma hk_hash_bits_ins_h s x : d_hash_bits (set_d_ins_h s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma hk_hash_mask_ins_h s x : d_hash_mask (set_d_ins_h s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma hk_hash_shift_ins_h s x : d_hash_shift (set_d_ins_h s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma hk_block_start_ins_h s x : d_block_start (set_d_ins_h s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma hk_match_length_ins_h s x : d_match_length (set_d_ins_h s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma hk_prev_match_ins_h s x : d_prev_match (set_d_ins_h s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma hk_match_available_ins_h s x : d_match_available (set_d_ins_h s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma hk_strstart_ins_h s x : d_strstart (set_d_ins_h s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma hk_match_start_ins_h s x : d_match_start (set_d_ins_h s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma hk_lookahead_ins_h s x : d_lookahead (set_d_ins_h s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma hk_prev_length_ins_h s x : d_prev_length (set_d_ins_h s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma hk_max_chain_length_ins_h s x : d_max_chain_length (set_d_ins_h s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma hk_max_lazy_match_ins_h s x : d_max_lazy_match (set_d_ins_h s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma hk_good_match_ins_h s x : d_good_match (set_d_ins_h s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma hk_nice_match_ins_h s x : d_nice_match (set_d_ins_h s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma hk_insert_ins_h s x : d_insert (set_d_ins_h s x) = d_insert s. Proof. reflexivity. Qed.
Lemma hk_high_water_ins_h s x : d_high_water (set_d_ins_h s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma hk_slid_ins_h s x : d_slid (set_d_ins_h s x) = d_slid s. Proof. reflexivity. Qed.
Lemma hk_pending_buf_size_ins_h s x : d_pending_buf_size (set_d_ins_h s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma hk_tr_ins_h s x : d_tr (set_d_ins_h s x) = d_tr s. Proof. reflexivity. Qed.
Lemma hk_pbm_ins_h s x : d_pbm (set_d_ins_h s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma hk_status_block_start s x : d_status (set_d_block_start s x) = d_status s. Proof. reflexivity. Qed.
Lemma hk_po_block_start s x : d_po (set_d_block_start s x) = d_po s. Proof. reflexivity. Qed.
Lemma hk_wrap_block_start s x : d_wrap (set_d_block_start s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma hk_gzhead_block_start s x : d_gzhead (set_d_block_start s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma hk_gzindex_block_start s x : d_gzindex (set_d_block_start s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma hk_method_block_start s x : d_method (set_d_block_start s x) = d_method s. Proof. reflexivity. Qed.
Lemma hk_last_flush_block_start s x : d_last_flush (set_d_block_start s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma hk_w_size_block_start s x : d_w_size (set_d_block_start s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma hk_w_bits_block_start s x : d_w_bits (set_d_block_start s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma hk_w_mask_block_start s x : d_w_mask (set_d_block_start s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma hk_window_block_start s x : d_window (set_d_block_start s x) = d_window s. Proof. reflexivity. Qed.
Lemma hk_window_size_block_start s x : d_window_size (set_d_block_start s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma hk_prev_block_start s x : d_prev (set_d_block_start s x) = d_prev s. Proof. reflexivity. Qed.
Lemma hk_head_block_start s x : d_head (set_d_block_start s x) = d_head s. Proof. reflexivity. Qed.
Lemma hk_ins_h_block_start s x : d_ins_h (set_d_block_start s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma hk_hash_size_block_start s x : d_hash_size (set_d_block_start s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma hk_hash_bits_block_start s x : d_hash_bits (set_d_block_start s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma hk_hash_mask_block_start s x : d_hash_mask (set_d_block_start s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma hk_hash_shift_block_start s x : d_hash_shift (set_d_block_start s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma hk_block_start_block_start s x : d_block_start (set_d_block_start s x) = x. Proof. reflexivity. Qed.
Lemma hk_match_length_block_start s x : d_match_length (set_d_block_start s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma hk_prev_match_block_start s x : d_prev_match (set_d_block_start s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma hk_match_available_block_start s x : d_match_available (set_d_block_start s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma hk_strstart_block_start s x : d_strstart (set_d_block_start s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma hk_match_start_block_start s x : d_match_start (set_d_block_start s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma hk_lookahead_block_start s x : d_lookahead (set_d_block_start s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma hk_prev_length_block_start s x : d_prev_length (set_d_block_start s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma hk_max_chain_length_block_start s x : d_max_chain_length (set_d_block_start s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma hk_max_lazy_match_block_start s x : d_max_lazy_match (set_d_block_start s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma hk_good_match_block_start s x : d_good_match (set_d_block_start s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma hk_nice_match_block_start s x : d_nice_match (set_d_block_start s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma hk_insert_block_start s x : d_insert (set_d_block_start s x) = d_insert s. Proof. reflexivity. Qed.
Lemma hk_high_water_block_start s x : d_high_water (set_d_block_start s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma hk_slid_block_start s x : d_slid (set_d_block_start s x) = d_slid s. Proof. reflexivity. Qed.
Lemma hk_pending_buf_size_block_start s x : d_pending_buf_size (set_d_block_start s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma hk_tr_block_start s x : d_tr (set_d_block_start s x) = d_tr s. Proof. reflexivity. Qed.
Lemma hk_pbm_block_start s x : d_pbm (set_d_block_start s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma hk_status_match_length s x : d_status (set_d_match_length s x) = d_status s. Proof. reflexivity. Qed.
Lemma hk_po_match_length s x : d_po (set_d_match_length s x) = d_po s. Proof. reflexivity. Qed.
Lemma hk_wrap_match_length s x : d_wrap (set_d_match_length s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma hk_gzhead_match_length s x : d_gzhead (set_d_match_length s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma hk_gzindex_match_length s x : d_gzindex (set_d_match_length s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma hk_method_match_length s x : d_method (set_d_match_length s x) = d_method s. Proof. reflexivity. Qed.
Lemma hk_last_flush_match_length s x : d_last_flush (set_d_match_length s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma hk_w_size_match_length s x : d_w_size (set_d_match_length s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma hk_w_bits_match_length s x : d_w_bits (set_d_match_length s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma hk_w_mask_match_length s x : d_w_mask (set_d_match_length s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma hk_window_match_length s x : d_window (set_d_match_length s x) = d_window s. Proof. reflexivity. Qed.
Lemma hk_window_size_match_length s x : d_window_size (set_d_match_length s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma hk_prev_match_length s x : d_prev (set_d_match_length s x) = d_prev s. Proof. reflexivity. Qed.
Lemma hk_head_match_length s x : d_head (set_d_match_length s x) = d_head s. Proof. reflexivity. Qed.
Lemma hk_ins_h_match_length s x : d_ins_h (set_d_match_length s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma hk_hash_size_match_length s x : d_hash_size (set_d_match_length s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma hk_hash_bits_match_length s x : d_hash_bits (set_d_match_length s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma hk_hash_mask_match_length s x : d_hash_mask (set_d_match_length s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma hk_hash_shift_match_length s x : d_hash_shift (set_d_match_length s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma hk_block_start_match_length s x : d_block_start (set_d_match_length s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma hk_match_length_match_length s x : d_match_length (set_d_match_length s x) = x. Proof. reflexivity. Qed.
Lemma hk_prev_match_match_length s x : d_prev_match (set_d_match_length s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma hk_match_available_match_length s x : d_match_available (set_d_match_length s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma hk_strstart_match_length s x : d_strstart (set_d_match_length s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma hk_match_start_match_length s x : d_match_start (set_d_match_length s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma hk_lookahead_match_length s x : d_lookahead (set_d_match_length s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma hk_prev_length_match_length s x : d_prev_length (set_d_match_length s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma hk_max_chain_length_match_length s x : d_max_chain_length (set_d_match_length s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma hk_max_lazy_match_match_length s x : d_max_lazy_match (set_d_match_length s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma hk_good_match_match_length s x : d_good_match (set_d_match_length s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma hk_nice_match_match_length s x : d_nice_match (set_d_match_length s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma hk_insert_match_length s x : d_insert (set_d_match_length s x) = d_insert s. Proof. reflexivity. Qed.
Lemma hk_high_water_match_length s x : d_high_water (set_d_match_length s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma hk_slid_match_length s x : d_slid (set_d_match_length s x) = d_slid s. Proof. reflexivity. Qed.
Lemma hk_pending_buf_size_match_length s x : d_pending_buf_size (set_d_match_length s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma hk_tr_match_length s x : d_tr (set_d_match_length s x) = d_tr s. Proof. reflexivity. Qed.
Lemma hk_pbm_match_length s x : d_pbm (set_d_match_length s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma hk_status_strstart s x : d_status (set_d_strstart s x) = d_status s. Proof. reflexivity. Qed.
Lemma hk_po_strstart s x : d_po (set_d_strstart s x) = d_po s. Proof. reflexivity. Qed.
Lemma hk_wrap_strstart s x : d_wrap (set_d_strstart s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma hk_gzhead_strstart s x : d_gzhead (set_d_strstart s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma hk_gzindex_strstart s x : d_gzindex (set_d_strstart s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma hk_method_strstart s x : d_method (set_d_strstart s x) = d_method s. Proof. reflexivity. Qed.
Lemma hk_last_flush_strstart s x : d_last_flush (set_d_strstart s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma hk_w_size_strstart s x : d_w_size (set_d_strstart s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma hk_w_bits_strstart s x : d_w_bits (set_d_strstart s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma hk_w_mask_strstart s x : d_w_mask (set_d_strstart s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma hk_window_strstart s x : d_window (set_d_strstart s x) = d_window s. Proof. reflexivity. Qed.
Lemma hk_window_size_strstart s x : d_window_size (set_d_strstart s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma hk_prev_strstart s x : d_prev (set_d_strstart s x) = d_prev s. Proof. reflexivity. Qed.
Lemma hk_head_strstart s x : d_head (set_d_strstart s x) = d_head s. Proof. reflexivity. Qed.
Lemma hk_ins_h_strstart s x : d_ins_h (set_d_strstart s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma hk_hash_size_strstart s x : d_hash_size (set_d_strstart s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma hk_hash_bits_strstart s x : d_hash_bits (set_d_strstart s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma hk_hash_mask_strstart s x : d_hash_mask (set_d_strstart s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma hk_hash_shift_strstart s x : d_hash_shift (set_d_strstart s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma hk_block_start_strstart s x : d_block_start (set_d_strstart s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma hk_match_length_strstart s x : d_match_length (set_d_strstart s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma hk_prev_match_strstart s x : d_prev_match (set_d_strstart s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma hk_match_available_strstart s x : d_match_available (set_d_strstart s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma hk_strstart_strstart s x : d_strstart (set_d_strstart s x) = x. Proof. reflexivity. Qed.
Lemma hk_match_start_strstart s x : d_match_start (set_d_strstart s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma hk_lookahead_strstart s x : d_lookahead (set_d_strstart s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma hk_prev_length_strstart s x : d_prev_length (set_d_strstart s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma hk_max_chain_length_strstart s x : d_max_chain_length (set_d_strstart s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma hk_max_lazy_match_strstart s x : d_max_lazy_match (set_d_strstart s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma hk_good_match_strstart s x : d_good_match (set_d_strstart s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma hk_nice_match_strstart s x : d_nice_match (set_d_strstart s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma hk_insert_strstart s x : d_insert (set_d_strstart s x) = d_insert s. Proof. reflexivity. Qed.
Lemma hk_high_water_strstart s x : d_high_water (set_d_strstart s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma hk_slid_strstart s x : d_slid (set_d_strstart s x) = d_slid s. Proof. reflexivity. Qed.
Lemma hk_pending_buf_size_strstart s x : d_pending_buf_size (set_d_strstart s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma hk_tr_strstart s x : d_tr (set_d_strstart s x) = d_tr s. Proof. reflexivity. Qed.
Lemma hk_pbm_strstart s x : d_pbm (set_d_strstart s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma hk_status_match_start s x : d_status (set_d_match_start s x) = d_status s. Proof. reflexivity. Qed.
Lemma hk_po_match_start s x : d_po (set_d_match_start s x) = d_po s. Proof. reflexivity. Qed.
Lemma hk_wrap_match_start s x : d_wrap (set_d_match_start s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma hk_gzhead_match_start s x : d_gzhead (set_d_match_start s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma hk_gzindex_match_start s x : d_gzindex (set_d_match_start s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma hk_method_match_start s x : d_method (set_d_match_start s x) = d_method s. Proof. reflexivity. Qed.
Lemma hk_last_flush_match_start s x : d_last_flush (set_d_match_start s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma hk_w_size_match_start s x : d_w_size (set_d_match_start s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma hk_w_bits_match_start s x : d_w_bits (set_d_match_start s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma hk_w_mask_match_start s x : d_w_mask (set_d_match_start s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma hk_window_match_start s x : d_window (set_d_match_start s x) = d_window s. Proof. reflexivity. Qed.
Lemma hk_window_size_match_start s x : d_window_size (set_d_match_start s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma hk_prev_match_start s x : d_prev (set_d_match_start s x) = d_prev s. Proof. reflexivity. Qed.
Lemma hk_head_match_start s x : d_head (set_d_match_start s x) = d_head s. Proof. reflexivity. Qed.
Lemma hk_ins_h_match_start s x : d_ins_h (set_d_match_start s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma hk_hash_size_match_start s x : d_hash_size (set_d_match_start s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma hk_hash_bits_match_start s x : d_hash_bits (set_d_match_start s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma hk_hash_mask_match_start s x : d_hash_mask (set_d_match_start s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma hk_hash_shift_match_start s x : d_hash_shift (set_d_match_start s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma hk_block_start_match_start s x : d_block_start (set_d_match_start s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma hk_match_length_match_start s x : d_match_length (set_d_match_start s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma hk_prev_match_match_start s x : d_prev_match (set_d_match_start s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma hk_match_available_match_start s x : d_match_available (set_d_match_start s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma hk_strstart_match_start s x : d_strstart (set_d_match_start s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma hk_match_start_match_start s x : d_match_start (set_d_match_start s x) = x. Proof. reflexivity. Qed.
Lemma hk_lookahead_match_start s x : d_lookahead (set_d_match_start s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma hk_prev_length_match_start s x : d_prev_length (set_d_match_start s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma hk_max_chain_length_match_start s x : d_max_chain_length (set_d_match_start s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma hk_max_lazy_match_match_start s x : d_max_lazy_match (set_d_match_start s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma hk_good_match_match_start s x : d_good_match (set_d_match_start s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma hk_nice_match_match_start s x : d_nice_match (set_d_match_start s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma hk_insert_match_start s x : d_insert (set_d_match_start s x) = d_insert s. Proof. reflexivity. Qed.
Lemma hk_high_water_match_start s x : d_high_water (set_d_match_start s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma hk_slid_match_start s x : d_slid (set_d_match_start s x) = d_slid s. Proof. reflexivity. Qed.
Lemma hk_pending_buf_size_match_start s x : d_pending_buf_size (set_d_match_start s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma hk_tr_match_start s x : d_tr (set_d_match_start s x) = d_tr s. Proof. reflexivity. Qed.
Lemma hk_pbm_match_start s x : d_pbm (set_d_match_start s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma hk_status_lookahead s x : d_status (set_d_lookahead s x) = d_status s. Proof. reflexivity. Qed.
Lemma hk_po_lookahead s x : d_po (set_d_lookahead s x) = d_po s. Proof. reflexivity. Qed.
Lemma hk_wrap_lookahead s x : d_wrap (set_d_lookahead s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma hk_gzhead_lookahead s x : d_gzhead (set_d_lookahead s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma hk_gzindex_lookahead s x : d_gzindex (set_d_lookahead s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma hk_method_lookahead s x : d_method (set_d_lookahead s x) = d_method s. Proof. reflexivity. Qed.
Lemma hk_last_flush_lookahead s x : d_last_flush (set_d_lookahead s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma hk_w_size_lookahead s x : d_w_size (set_d_lookahead s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma hk_w_bits_lookahead s x : d_w_bits (set_d_lookahead s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma hk_w_mask_lookahead s x : d_w_mask (set_d_lookahead s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma hk_window_lookahead s x : d_window (set_d_lookahead s x) = d_window s. Proof. reflexivity. Qed.
Lemma hk_window_size_lookahead s x : d_window_size (set_d_lookahead s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma hk_prev_lookahead s x : d_prev (set_d_lookahead s x) = d_prev s. Proof. reflexivity. Qed.
Lemma hk_head_lookahead s x : d_head (set_d_lookahead s x) = d_head s. Proof. reflexivity. Qed.
Lemma hk_ins_h_lookahead s x : d_ins_h (set_d_lookahead s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma hk_hash_size_lookahead s x : d_hash_size (set_d_lookahead s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma hk_hash_bits_lookahead s x : d_hash_bits (set_d_lookahead s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma hk_hash_mask_lookahead s x : d_hash_mask (set_d_lookahead s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma hk_hash_shift_lookahead s x : d_hash_shift (set_d_lookahead s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma hk_block_start_lookahead s x : d_block_start (set_d_lookahead s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma hk_match_length_lookahead s x : d_match_length (set_d_lookahead s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma hk_prev_match_lookahead s x : d_prev_match (set_d_lookahead s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma hk_match_available_lookahead s x : d_match_available (set_d_lookahead s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma hk_strstart_lookahead s x : d_strstart (set_d_lookahead s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma hk_match_start_lookahead s x : d_match_start (set_d_lookahead s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma hk_lookahead_lookahead s x : d_lookahead (set_d_lookahead s x) = x. Proof. reflexivity. Qed.
Lemma hk_prev_length_lookahead s x : d_prev_length (set_d_lookahead s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma hk_max_chain_length_lookahead s x : d_max_chain_length (set_d_lookahead s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma hk_max_lazy_match_lookahead s x : d_max_lazy_match (set_d_lookahead s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma hk_good_match_lookahead s x : d_good_match (set_d_lookahead s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma hk_nice_match_lookahead s x : d_nice_match (set_d_lookahead s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma hk_insert_lookahead s x : d_insert (set_d_lookahead s x) = d_insert s. Proof. reflexivity. Qed.
Lemma hk_high_water_lookahead s x : d_high_water (set_d_lookahead s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma hk_slid_lookahead s x : d_slid (set_d_lookahead s x) = d_slid s. Proof. reflexivity. Qed.
Lemma hk_pending_buf_size_lookahead s x : d_pending_buf_size (set_d_lookahead s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma hk_tr_lookahead s x : d_tr (set_d_lookahead s x) = d_tr s. Proof. reflexivity. Qed.
Lemma hk_pbm_lookahead s x : d_pbm (set_d_lookahead s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma hk_status_insert s x : d_status (set_d_insert s x) = d_status s. Proof. reflexivity. Qed.
Lemma hk_po_insert s x : d_po (set_d_insert s x) = d_po s. Proof. reflexivity. Qed.
Lemma hk_wrap_insert s x : d_wrap (set_d_insert s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma hk_gzhead_insert s x : d_gzhead (set_d_insert s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma hk_gzindex_insert s x : d_gzindex (set_d_insert s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma hk_method_insert s x : d_method (set_d_insert s x) = d_method s. Proof. reflexivity. Qed.
Lemma hk_last_flush_insert s x : d_last_flush (set_d_insert s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma hk_w_size_insert s x : d_w_size (set_d_insert s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma hk_w_bits_insert s x : d_w_bits (set_d_insert s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma hk_w_mask_insert s x : d_w_mask (set_d_insert s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma hk_window_insert s x : d_window (set_d_insert s x) = d_window s. Proof. reflexivity. Qed.
Lemma hk_window_size_insert s x : d_window_size (set_d_insert s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma hk_prev_insert s x : d_prev (set_d_insert s x) = d_prev s. Proof. reflexivity. Qed.
Lemma hk_head_insert s x : d_head (set_d_insert s x) = d_head s. Proof. reflexivity. Qed.
Lemma hk_ins_h_insert s x : d_ins_h (set_d_insert s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma hk_hash_size_insert s x : d_hash_size (set_d_insert s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma hk_hash_bits_insert s x : d_hash_bits (set_d_insert s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma hk_hash_mask_insert s x : d_hash_mask (set_d_insert s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma hk_hash_shift_insert s x : d_hash_shift (set_d_insert s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma hk_block_start_insert s x : d_block_start (set_d_insert s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma hk_match_length_insert s x : d_match_length (set_d_insert s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma hk_prev_match_insert s x : d_prev_match (set_d_insert s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma hk_match_available_insert s x : d_match_available (set_d_insert s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma hk_strstart_insert s x : d_strstart (set_d_insert s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma hk_match_start_insert s x : d_match_start (set_d_insert s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma hk_lookahead_insert s x : d_lookahead (set_d_insert s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma hk_prev_length_insert s x : d_prev_length (set_d_insert s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma hk_max_chain_length_insert s x : d_max_chain_length (set_d_insert s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma hk_max_lazy_match_insert s x : d_max_lazy_match (set_d_insert s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma hk_good_match_insert s x : d_good_match (set_d_insert s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma hk_nice_match_insert s x : d_nice_match (set_d_insert s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma hk_insert_insert s x : d_insert (set_d_insert s x) = x. Proof. reflexivity. Qed.
Lemma hk_high_water_insert s x : d_high_water (set_d_insert s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma hk_slid_insert s x : d_slid (set_d_insert s x) = d_slid s. Proof. reflexivity. Qed.
Lemma hk_pending_buf_size_insert s x : d_pending_buf_size (set_d_insert s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma hk_tr_insert s x : d_tr (set_d_insert s x) = d_tr s. Proof. reflexivity. Qed.
Lemma hk_pbm_insert s x : d_pbm (set_d_insert s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma hk_status_tr s x : d_status (set_d_tr s x) = d_status s. Proof. reflexivity. Qed.
Lemma hk_po_tr s x : d_po (set_d_tr s x) = d_po s. Proof. reflexivity. Qed.
Lemma hk_wrap_tr s x : d_wrap (set_d_tr s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma hk_gzhead_tr s x : d_gzhead (set_d_tr s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma hk_gzindex_tr s x : d_gzindex (set_d_tr s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma hk_method_tr s x : d_method (set_d_tr s x) = d_method s. Proof. reflexivity. Qed.
Lemma hk_last_flush_tr s x : d_last_flush (set_d_tr s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma hk_w_size_tr s x : d_w_size (set_d_tr s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma hk_w_bits_tr s x : d_w_bits (set_d_tr s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma hk_w_mask_tr s x : d_w_mask (set_d_tr s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma hk_window_tr s x : d_window (set_d_tr s x) = d_window s. Proof. reflexivity. Qed.
Lemma hk_window_size_tr s x : d_window_size (set_d_tr s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma hk_prev_tr s x : d_prev (set_d_tr s x) = d_prev s. Proof. reflexivity. Qed.
Lemma hk_head_tr s x : d_head (set_d_tr s x) = d_head s. Proof. reflexivity. Qed.
Lemma hk_ins_h_tr s x : d_ins_h (set_d_tr s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma hk_hash_size_tr s x : d_hash_size (set_d_tr s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma hk_hash_bits_tr s x : d_hash_bits (set_d_tr s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma hk_hash_mask_tr s x : d_hash_mask (set_d_tr s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma hk_hash_shift_tr s x : d_hash_shift (set_d_tr s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma hk_block_start_tr s x : d_block_start (set_d_tr s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma hk_match_length_tr s x : d_match_length (set_d_tr s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma hk_prev_match_tr s x : d_prev_match (set_d_tr s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma hk_match_available_tr s x : d_match_available (set_d_tr s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma hk_strstart_tr s x : d_strstart (set_d_tr s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma hk_match_start_tr s x : d_match_start (set_d_tr s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma hk_lookahead_tr s x : d_lookahead (set_d_tr s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma hk_prev_length_tr s x : d_prev_length (set_d_tr s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma hk_max_chain_length_tr s x : d_max_chain_length (set_d_tr s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma hk_max_lazy_match_tr s x : d_max_lazy_match (set_d_tr s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma hk_good_match_tr s x : d_good_match (set_d_tr s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma hk_nice_match_tr s x : d_nice_match (set_d_tr s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma hk_insert_tr s x : d_insert (set_d_tr s x) = d_insert s. Proof. reflexivity. Qed.
Lemma hk_high_water_tr s x : d_high_water (set_d_tr s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma hk_slid_tr s x : d_slid (set_d_tr s x) = d_slid s. Proof. reflexivity. Qed.
Lemma hk_pending_buf_size_tr s x : d_pending_buf_size (set_d_tr s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma hk_tr_tr s x : d_tr (set_d_tr s x) = x. Proof. reflexivity. Qed.
Lemma hk_pbm_tr s x : d_pbm (set_d_tr s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma hk_status_pbm s x : d_status (set_d_pbm s x) = d_status s. Proof. reflexivity. Qed.
Lemma hk_po_pbm s x : d_po (set_d_pbm s x) = d_po s. Proof. reflexivity. Qed.
Lemma hk_wrap_pbm s x : d_wrap (set_d_pbm s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma hk_gzhead_pbm s x : d_gzhead (set_d_pbm s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma hk_gzindex_pbm s x : d_gzindex (set_d_pbm s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma hk_method_pbm s x : d_method (set_d_pbm s x) = d_method s. Proof. reflexivity. Qed.
Lemma hk_last_flush_pbm s x : d_last_flush (set_d_pbm s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma hk_w_size_pbm s x : d_w_size (set_d_pbm s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma hk_w_bits_pbm s x : d_w_bits (set_d_pbm s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma hk_w_mask_pbm s x : d_w_mask (set_d_pbm s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma hk_window_pbm s x : d_window (set_d_pbm s x) = d_window s. Proof. reflexivity. Qed.
Lemma hk_window_size_pbm s x : d_window_size (set_d_pbm s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma hk_prev_pbm s x : d_prev (set_d_pbm s x) = d_prev s. Proof. reflexivity. Qed.
Lemma hk_head_pbm s x : d_head (set_d_pbm s x) = d_head s. Proof. reflexivity. Qed.
Lemma hk_ins_h_pbm s x : d_ins_h (set_d_pbm s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma hk_hash_size_pbm s x : d_hash_size (set_d_pbm s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma hk_hash_bits_pbm s x : d_hash_bits (set_d_pbm s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma hk_hash_mask_pbm s x : d_hash_mask (set_d_pbm s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma hk_hash_shift_pbm s x : d_hash_shift (set_d_pbm s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma hk_block_start_pbm s x : d_block_start (set_d_pbm s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma hk_match_length_pbm s x : d_match_length (set_d_pbm s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma hk_prev_match_pbm s x : d_prev_match (set_d_pbm s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma hk_match_available_pbm s x : d_match_available (set_d_pbm s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma hk_strstart_pbm s x : d_strstart (set_d_pbm s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma hk_match_start_pbm s x : d_match_start (set_d_pbm s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma hk_lookahead_pbm s x : d_lookahead (set_d_pbm s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma hk_prev_length_pbm s x : d_prev_length (set_d_pbm s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma hk_max_chain_length_pbm s x : d_max_chain_length (set_d_pbm s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma hk_max_lazy_match_pbm s x : d_max_lazy_match (set_d_pbm s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma hk_good_match_pbm s x : d_good_match (set_d_pbm s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma hk_nice_match_pbm s x : d_nice_match (set_d_pbm s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma hk_insert_pbm s x : d_insert (set_d_pbm s x) = d_insert s. Proof. reflexivity. Qed.
Lemma hk_high_water_pbm s x : d_high_water (set_d_pbm s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma hk_slid_pbm s x : d_slid (set_d_pbm s x) = d_slid s. Proof. reflexivity. Qed.
Lemma hk_pending_buf_size_pbm s x : d_pending_buf_size (set_d_pbm s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma hk_tr_pbm s x : d_tr (set_d_pbm s x) = d_tr s. Proof. reflexivity. Qed.
Lemma hk_pbm_pbm s x : d_pbm (set_d_pbm s x) = x. Proof. reflexivity. Qed.
#[export] Hint Rewrite hk_status_po hk_po_po hk_wrap_po hk_gzhead_po hk_gzindex_po hk_method_po hk_last_flush_po hk_w_size_po hk_w_bits_po hk_w_mask_po hk_window_po hk_window_size_po hk_prev_po hk_head_po hk_ins_h_po hk_hash_size_po hk_hash_bits_po hk_hash_mask_po hk_hash_shift_po hk_block_start_po hk_match_length_po hk_prev_match_po hk_match_available_po hk_strstart_po hk_match_start_po hk_lookahead_po hk_prev_length_po hk_max_chain_length_po hk_max_lazy_match_po hk_good_match_po hk_nice_match_po hk_insert_po hk_high_water_po hk_slid_po hk_pending_buf_size_po hk_tr_po hk_pbm_po hk_status_prev hk_po_prev hk_wrap_prev hk_gzhead_prev hk_gzindex_prev hk_method_prev hk_last_flush_prev hk_w_size_prev hk_w_bits_prev hk_w_mask_prev hk_window_prev hk_window_size_prev hk_prev_prev hk_head_prev hk_ins_h_prev hk_hash_size_prev hk_hash_bits_prev hk_hash_mask_prev hk_hash_shift_prev hk_block_start_prev hk_match_length_prev hk_prev_match_prev hk_match_available_prev hk_strstart_prev hk_match_start_prev hk_lookahead_prev hk_prev_length_prev hk_max_chain_length_prev hk_max_lazy_match_prev hk_good_match_prev hk_nice_match_prev hk_insert_prev hk_high_water_prev hk_slid_prev hk_pending_buf_size_prev hk_tr_prev hk_pbm_prev hk_status_head hk_po_head hk_wrap_head hk_gzhead_head hk_gzindex_head hk_method_head hk_last_flush_head hk_w_size_head hk_w_bits_head hk_w_mask_head hk_window_head hk_window_size_head hk_prev_head hk_head_head hk_ins_h_head hk_hash_size_head hk_hash_bits_head hk_hash_mask_head hk_hash_shift_head hk_block_start_head hk_match_length_head hk_prev_match_head hk_match_available_head hk_strstart_head hk_match_start_head hk_lookahead_head hk_prev_length_head hk_max_chain_length_head hk_max_lazy_match_head hk_good_match_head hk_nice_match_head hk_insert_head hk_high_water_head hk_slid_head hk_pending_buf_size_head hk_tr_head hk_pbm_head hk_status_ins_h hk_po_ins_h hk_wrap_ins_h hk_gzhead_ins_h hk_gzindex_ins_h hk_method_ins_h hk_last_flush_ins_h hk_w_size_ins_h hk_w_bits_ins_h hk_w_mask_ins_h hk_window_ins_h hk_window_size_ins_h hk_prev_ins_h hk_head_ins_h hk_ins_h_ins_h hk_hash_size_ins_h hk_hash_bits_ins_h hk_hash_mask_ins_h hk_hash_shift_ins_h hk_block_start_ins_h hk_match_length_ins_h hk_prev_match_ins_h hk_match_available_ins_h hk_strstart_ins_h hk_match_start_ins_h hk_lookahead_ins_h hk_prev_length_ins_h hk_max_chain_length_ins_h hk_max_lazy_match_ins_h hk_good_match_ins_h hk_nice_match_ins_h hk_insert_ins_h hk_high_water_ins_h hk_slid_ins_h hk_pending_buf_size_ins_h hk_tr_ins_h hk_pbm_ins_h hk_status_block_start hk_po_block_start hk_wrap_block_start hk_gzhead_block_start hk_gzindex_block_start hk_method_block_start hk_last_flush_block_start hk_w_size_block_start hk_w_bits_block_start hk_w_mask_block_start hk_window_block_start hk_window_size_block_start hk_prev_block_start hk_head_block_start hk_ins_h_block_start hk_hash_size_block_start hk_hash_bits_block_start hk_hash_mask_block_start hk_hash_shift_block_start hk_block_start_block_start hk_match_length_block_start hk_prev_match_block_start hk_match_available_block_start hk_strstart_block_start hk_match_start_block_start hk_lookahead_block_start hk_prev_length_block_start hk_max_chain_length_block_start hk_max_lazy_match_block_start hk_good_match_block_start hk_nice_match_block_start hk_insert_block_start hk_high_water_block_start hk_slid_block_start hk_pending_buf_size_block_start hk_tr_block_start hk_pbm_block_start hk_status_match_length hk_po_match_length hk_wrap_match_length hk_gzhead_match_length hk_gzindex_match_length hk_method_match_length hk_last_flush_match_length hk_w_size_match_length hk_w_bits_match_length hk_w_mask_match_length hk_window_match_length hk_window_size_match_length hk_prev_match_length hk_head_match_length hk_ins_h_match_length hk_hash_size_match_length hk_hash_bits_match_length hk_hash_mask_match_length hk_hash_shift_match_length hk_block_start_match_length hk_match_length_match_length hk_prev_match_match_length hk_match_available_match_length hk_strstart_match_length hk_match_start_match_length hk_lookahead_match_length hk_prev_length_match_length hk_max_chain_length_match_length hk_max_lazy_match_match_length hk_good_match_match_length hk_nice_match_match_length hk_insert_match_length hk_high_water_match_length hk_slid_match_length hk_pending_buf_size_match_length hk_tr_match_length hk_pbm_match_length hk_status_strstart hk_po_strstart hk_wrap_strstart hk_gzhead_strstart hk_gzindex_strstart hk_method_strstart hk_last_flush_strstart hk_w_size_strstart hk_w_bits_strstart hk_w_mask_strstart hk_window_strstart hk_window_size_strstart hk_prev_strstart hk_head_strstart hk_ins_h_strstart hk_hash_size_strstart hk_hash_bits_strstart hk_hash_mask_strstart hk_hash_shift_strstart hk_block_start_strstart hk_match_length_strstart hk_prev_match_strstart hk_match_available_strstart hk_strstart_strstart hk_match_start_strstart hk_lookahead_strstart hk_prev_length_strstart hk_max_chain_length_strstart hk_max_lazy_match_strstart hk_good_match_strstart hk_nice_match_strstart hk_insert_strstart hk_high_water_strstart hk_slid_strstart hk_pending_buf_size_strstart hk_tr_strstart hk_pbm_strstart hk_status_match_start hk_po_match_start hk_wrap_match_start hk_gzhead_match_start hk_gzindex_match_start hk_method_match_start hk_last_flush_match_start hk_w_size_match_start hk_w_bits_match_start hk_w_mask_match_start hk_window_match_start hk_window_size_match_start hk_prev_match_start hk_head_match_start hk_ins_h_match_start hk_hash_size_match_start hk_hash_bits_match_start hk_hash_mask_match_start hk_hash_shift_match_start hk_block_start_match_start hk_match_length_match_start hk_prev_match_match_start hk_match_available_match_start hk_strstart_match_start hk_match_start_match_start hk_lookahead_match_start hk_prev_length_match_start hk_max_chain_length_match_start hk_max_lazy_match_match_start hk_good_match_match_start hk_nice_match_match_start hk_insert_match_start hk_high_water_match_start hk_slid_match_start hk_pending_buf_size_match_start hk_tr_match_start hk_pbm_match_start hk_status_lookahead hk_po_lookahead hk_wrap_lookahead hk_gzhead_lookahead hk_gzindex_lookahead hk_method_lookahead hk_last_flush_lookahead hk_w_size_lookahead hk_w_bits_lookahead hk_w_mask_lookahead hk_window_lookahead hk_window_size_lookahead hk_prev_lookahead hk_head_lookahead hk_ins_h_lookahead hk_hash_size_lookahead hk_hash_bits_lookahead hk_hash_mask_lookahead hk_hash_shift_lookahead hk_block_start_lookahead hk_match_length_lookahead hk_prev_match_lookahead hk_match_available_lookahead hk_strstart_lookahead hk_match_start_lookahead hk_lookahead_lookahead hk_prev_length_lookahead hk_max_chain_length_lookahead hk_max_lazy_match_lookahead hk_good_match_lookahead hk_nice_match_lookahead hk_insert_lookahead hk_high_water_lookahead hk_slid_lookahead hk_pending_buf_size_lookahead hk_tr_lookahead hk_pbm_lookahead hk_status_insert hk_po_insert hk_wrap_insert hk_gzhead_insert hk_gzindex_insert hk_method_insert hk_last_flush_insert hk_w_size_insert hk_w_bits_insert hk_w_mask_insert hk_window_insert hk_window_size_insert hk_prev_insert hk_head_insert hk_ins_h_insert hk_hash_size_insert hk_hash_bits_insert hk_hash_mask_insert hk_hash_shift_insert hk_block_start_insert hk_match_length_insert hk_prev_match_insert hk_match_available_insert hk_strstart_insert hk_match_start_insert hk_lookahead_insert hk_prev_length_insert hk_max_chain_length_insert hk_max_lazy_match_insert hk_good_match_insert hk_nice_match_insert hk_insert_insert hk_high_water_insert hk_slid_insert hk_pending_buf_size_insert hk_tr_insert hk_pbm_insert hk_status_tr hk_po_tr hk_wrap_tr hk_gzhead_tr hk_gzindex_tr hk_method_tr hk_last_flush_tr hk_w_size_tr hk_w_bits_tr hk_w_mask_tr hk_window_tr hk_window_size_tr hk_prev_tr hk_head_tr hk_ins_h_tr hk_hash_size_tr hk_hash_bits_tr hk_hash_mask_tr hk_hash_shift_tr hk_block_start_tr hk_match_length_tr hk_prev_match_tr hk_match_available_tr hk_strstart_tr hk_match_start_tr hk_lookahead_tr hk_prev_length_tr hk_max_chain_length_tr hk_max_lazy_match_tr hk_good_match_tr hk_nice_match_tr hk_insert_tr hk_high_water_tr hk_slid_tr hk_pending_buf_size_tr hk_tr_tr hk_pbm_tr hk_status_pbm hk_po_pbm hk_wrap_pbm hk_gzhead_pbm hk_gzindex_pbm hk_method_pbm hk_last_flush_pbm hk_w_size_pbm hk_w_bits_pbm hk_w_mask_pbm hk_window_pbm hk_window_size_pbm hk_prev_pbm hk_head_pbm hk_ins_h_pbm hk_hash_size_pbm hk_hash_bits_pbm hk_hash_mask_pbm hk_hash_shift_pbm hk_block_start_pbm hk_match_length_pbm hk_prev_match_pbm hk_match_available_pbm hk_strstart_pbm hk_match_start_pbm hk_lookahead_pbm hk_prev_length_pbm hk_max_chain_length_pbm hk_max_lazy_match_pbm hk_good_match_pbm hk_nice_match_pbm hk_insert_pbm hk_high_water_pbm hk_slid_pbm hk_pending_buf_size_pbm hk_tr_pbm hk_pbm_pbm : hproj.

(** ** The extra invariant of a huff state: the pending block holds only literals *)
Definition huff_extra (s : dstate) : Prop :=
  fn_of s = 3 -> 3 * (d_strstart s - d_block_start s) <= d_sym_next s.

(** deflate_huff's specification over [W /\ huff_extra]. *)
Definition huff_specX : Prop :=
  forall s z flush, compress_pre s z flush -> huff_extra s -> fn_of s = 3 ->
    exists s' z' bs evs, c_deflate_huff s z flush = Some (s', z', bs) /\
      cpost W s z flush s' z' bs evs /\ huff_extra s'.

(** ** What a piece of a compression call guarantees (cpost without the block_state part) *)
Definition hcrel (s : dstate) (z : strm) (flush : Z) (s' : dstate) (z' : strm) (evs : list dev) : Prop :=
  W s' /\ huff_extra s' /\ outok s' /\ same_prm s s' /\ api_eq s s' /\
  (exists k x, zstep (d_wrap s) z z' k x /\ bytes x /\ k + ub s = sum_len evs + ub s') /\
  ev_chain (Gb s (z_total_out z)) evs (Gb s' (z_total_out z')) /\
  Forall (ev_ok s flush) evs.

(** The block_state part of cpost. *)
Definition hbpost (s : dstate) (z : strm) (flush : Z) (s' : dstate) (z' : strm) (bs : bstate) (evs : list dev)
    : Prop :=
  match bs with
  | need_more =>
      Forall (fun e => ev_last e = 0) evs /\ d_bi_valid s' <= 7 /\
      (flush = Z_NO_FLUSH \/ z_avail_out z' = 0 \/ d_level s = 0)
  | block_done =>
      Forall (fun e => ev_last e = 0) evs /\ flush <> Z_NO_FLUSH /\ flush <> Z_FINISH /\
      z_avail_in z' = 0 /\ ub s' = 0 /\ quiet s' /\ d_sym_next s' = 0
  | finish_started =>
      last_ev evs /\ flush = Z_FINISH /\ z_avail_in z' = 0 /\ ub s' = 0 /\ d_sym_next s' = 0 /\
      d_bi_valid s' = 0 /\ z_avail_out z' = 0 /\ (d_level s <> 0 -> d_pending s' <> 0 \/ d_wrap s <> 0)
  | finish_done =>
      last_ev evs /\ flush = Z_FINISH /\ z_avail_in z' = 0 /\ ub s' = 0 /\ d_sym_next s' = 0 /\
      quiet s' /\ d_bi_valid s' = 0
  end.

(** The loop invariant between iterations: [s'], [z'] reached from the call's [s], [z], no block marked last,
    nothing pending, the stream sane (and the call's stream [z] sane: zstep_trans needs it). *)
Definition HFI (s : dstate) (z : strm) (flush : Z) (s' : dstate) (z' : strm) (evs : list dev) : Prop :=
  zall z /\ adler_ok (d_wrap s) (z_adler z) /\
  hcrel s z flush s' z' evs /\ quiet s' /\ zall z' /\ adler_ok (d_wrap s') (z_adler z') /\
  Forall (fun e => ev_last e = 0) evs.

(** A step inside one iteration that changes neither the stream nor the bit count nor ub. *)
Definition hfr (s s' : dstate) : Prop :=
  same_prm s s' /\ api_eq s s' /\ ub s' = ub s /\ (forall tout, Gb s' tout = Gb s tout).

(** A huff state with the symbols [syms] (at most L - 1 of them: a full sym_buf is allowed), all literals
    ([d_strstart - d_block_start <= Zlength syms]): [W] minus the L - 2 bound, plus outok, quiet. *)
Definition HS0 (s : dstate) (syms : list (Z * Z)) : Prop :=
  prm s /\ wstruct s /\ wpos s /\ wwin s /\ whash s /\ wmatch s /\
  tree_ok (d_tr s) (d_pbm s) syms /\ Zlength syms <= d_L s - 1 /\ Forall (sym_ok s) syms /\
  blk_len syms = d_strstart s - d_block_start s /\ d_strstart s - d_block_start s <= Zlength syms /\
  outok s /\ quiet s /\ fn_of s = 3.

(** The literal step of huff_body (after the refill) *)
Definition hlit (s : dstate) : option (dstate * bool) :=
  let s := set_d_match_length s 0 in
  let* c := mb_rd (d_window s) (d_strstart s) in
  let* (s, bflush) := c_dtally_lit s c in
  let s := set_d_lookahead s (u32 (d_lookahead s - 1)) in
  Some (set_d_strstart s (u32 (d_strstart s + 1)), bflush).

(** huff_body with its two pieces named. *)
Definition hrefill (flush : Z) (s : dstate) (z : strm) : option ((dstate * strm) + dexit) :=
  if d_lookahead s =? 0 then
    let* (s, z) := c_fill_window s z in
    if d_lookahead s =? 0 then
      (if flush =? Z_NO_FLUSH then Some (inr (s, z, Some need_more)) else Some (inr (s, z, None)))
    else Some (inl (s, z))
  else Some (inl (s, z)).

Lemma huff_body_eq flush s z :
  huff_body flush (s, z) =
  let* r := hrefill flush s z in
  match r with
  | inr e => Some (inr e)
  | inl (s, z) => let* (s, bf) := hlit s in c_bflush s z bf
  end.
Proof.
  assert (L : forall s z, (let s := set_d_match_length s 0 in
    let* c := mb_rd (d_window s) (d_strstart s) in
    let* (s, bflush) := c_dtally_lit s c in
    let s := set_d_lookahead s (u32 (d_lookahead s - 1)) in
    let s := set_d_strstart s (u32 (d_strstart s + 1)) in
    c_bflush s z bflush) = let* (s, bf) := hlit s in c_bflush s z bf).
  { intros s1 z1. unfold hlit. cbv zeta.
    destruct (mb_rd _ _) as [c|]; [|reflexivity]. cbn [bind].
    destruct (c_dtally_lit _ c) as [[s2 b]|]; reflexivity. }
  unfold huff_body, hrefill.
  destruct (d_lookahead s =? 0); [|cbn [bind]; apply L].
  destruct (c_fill_window s z) as [[s1 z1]|]; [|reflexivity]. cbn [bind].
  destruct (d_lookahead s1 =? 0); [destruct (flush =? Z_NO_FLUSH); reflexivity|]. cbn [bind]. apply L.
Qed.

(** ** The part statements *)

Definition hfbw_stmt : Prop :=
  forall s z flush syms last,
    HS0 s syms -> zall z -> adler_ok (d_wrap s) (z_adler z) -> 0 <= flush <= 5 -> 0 <= last <= 1 ->
    (last = 1 -> flush = Z_FINISH) ->
    (last = 0 -> Zlength syms = d_L s - 1 \/ (flush <> Z_NO_FLUSH /\ flush <> Z_FINISH)) ->
    exists s' z' e,
      c_flush_block_only s z last = Some (s', z') /\ hcrel s z flush s' z' [e] /\ ev_last e = last /\
      zall z' /\ z_adler z' = z_adler z /\ z_avail_in z' = z_avail_in z /\
      d_lookahead s' = d_lookahead s /\ d_strstart s' = d_strstart s /\ d_block_start s' = d_strstart s /\
      d_sym_next s' = 0 /\ d_bi_valid s' <= 7 /\ (last = 1 -> d_bi_valid s' = 0) /\
      (d_pending s' = 0 \/ z_avail_out z' = 0).

Definition hlit_stmt : Prop :=
  forall s,
    W s -> huff_extra s -> outok s -> quiet s -> fn_of s = 3 -> 1 <= d_lookahead s ->
    exists s3 bf syms3,
      hlit s = Some (s3, bf) /\ HS0 s3 syms3 /\ bf = (Zlength syms3 =? d_L s3 - 1) /\ hfr s s3 /\
      d_lookahead s3 = d_lookahead s - 1.

Definition hrefill_stmt : Prop :=
  forall s0 z0 flush s z evs,
    HFI s0 z0 flush s z evs -> fn_of s0 = 3 -> d_lookahead s = 0 ->
    exists s' z',
      c_fill_window s z = Some (s', z') /\ HFI s0 z0 flush s' z' evs /\
      z_avail_in z' + d_lookahead s' = z_avail_in z + d_lookahead s /\
      (d_lookahead s' = 0 -> z_avail_in z' = 0).

Definition hbflush_stmt : Prop :=
  forall s0 z0 flush s z evs s3 syms3 bf,
    HFI s0 z0 flush s z evs -> 0 <= flush <= 5 -> fn_of s0 = 3 ->
    HS0 s3 syms3 -> bf = (Zlength syms3 =? d_L s3 - 1) -> hfr s s3 ->
    exists r, c_bflush s3 z bf = Some r /\
    match r with
    | inl (s', z') =>
        (exists evs', HFI s0 z0 flush s' z' evs') /\ d_lookahead s' = d_lookahead s3 /\
        z_avail_in z' = z_avail_in z
    | inr (s', z', o) =>
        o = Some need_more /\ exists evs', hcrel s0 z0 flush s' z' evs' /\ hbpost s0 z0 flush s' z' need_more evs'
    end.

Definition htail_stmt : Prop :=
  forall s0 z0 flush s z evs,
    HFI s0 z0 flush s z evs -> 0 <= flush <= 5 -> fn_of s0 = 3 -> flush <> Z_NO_FLUSH ->
    d_lookahead s = 0 -> z_avail_in z = 0 ->
    exists s' z' bs evs',
      c_deflate_tail (set_d_insert s 0) z flush = Some (s', z', bs) /\
      hcrel s0 z0 flush s' z' evs' /\ hbpost s0 z0 flush s' z' bs evs'.

(** ** Helper lemmas *)

Lemma fn_of_huff s : prm s -> fn_of s = 3 -> d_level s <> 0 /\ d_strategy s = Z_HUFFMAN_ONLY.
Proof.
  intros Hp Hf. destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & _).
  unfold fn_of in Hf.
  destruct (Z.eqb_spec (d_level s) 0) as [E0|N0]; [discriminate|].
  destruct (Z.eqb_spec (d_strategy s) Z_HUFFMAN_ONLY) as [E1|N1]; [split; assumption|].
  destruct (Z.eqb_spec (d_strategy s) Z_RLE) as [E2|N2]; [discriminate|].
  exfalso.
  assert (H : d_level s = 1 \/ d_level s = 2 \/ d_level s = 3 \/ d_level s = 4 \/ d_level s = 5 \/
              d_level s = 6 \/ d_level s = 7 \/ d_level s = 8 \/ d_level s = 9) by lia.
  destruct H as [E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]; rewrite E in Hf; vm_compute in Hf; discriminate.
Qed.

Lemma fn_of_same_prm' s s' : same_prm s s' -> fn_of s' = fn_of s.
Proof.
  intros (_ & _ & _ & _ & _ & El & Es). unfold fn_of. rewrite El, Es. reflexivity.
Qed.

Lemma blk_len_nil : blk_len [] = 0.
Proof. reflexivity. Qed.

(** [W /\ huff_extra] from [HS0] when sym_buf is not full. *)
Lemma HS0_W s syms : HS0 s syms -> Zlength syms <= d_L s - 2 -> W s /\ huff_extra s.
Proof.
  intros (Hp & Hs & Hpos & Hw & Hh & Hm & Ht & HL & Hf & Hb & Hlit & Ho & Hq & Hfn) HL2.
  assert (Hlev := fn_of_huff s Hp Hfn).
  assert (Ha : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  split.
  - unfold W. split; [exact Hp|]. split; [exact Hs|]. split; [exact Hpos|]. split; [exact Hw|].
    split; [exact Hh|]. split; [exact Hm|]. split; [intros; lia|].
    exists syms. unfold wtrees. split; [exact Ht|]. split; [exact HL2|]. split; [exact Hf|].
    split; [intros; lia|]. intros _. rewrite Ha. lia.
  - intros _. destruct Ht as (_ & _ & T3 & _). unfold d_sym_next. rewrite T3. lia.
Qed.

(** [HS0] from [W /\ huff_extra]. *)
Lemma W_HS0 s : W s -> huff_extra s -> outok s -> quiet s -> fn_of s = 3 ->
  exists syms, HS0 s syms /\ Zlength syms <= d_L s - 2.
Proof.
  intros (Hp & Hs & Hpos & Hw & Hh & Hm & H0 & syms & Ht & HL & Hf & Hz & Hb) He Ho Hq Hfn.
  assert (Hlev := fn_of_huff s Hp Hfn).
  assert (Ha : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  exists syms. split; [|exact HL].
  specialize (He Hfn). destruct Ht as (T1 & T2 & T3 & Trest). unfold d_sym_next in He. rewrite T3 in He.
  unfold HS0. split; [exact Hp|]. split; [exact Hs|]. split; [exact Hpos|]. split; [exact Hw|].
  split; [exact Hh|]. split; [exact Hm|]. split; [exact (conj T1 (conj T2 (conj T3 Trest)))|].
  split; [lia|]. split; [exact Hf|].
  split; [rewrite Hb by lia; rewrite Ha; lia|]. split; [lia|]. split; [exact Ho|]. split; [exact Hq|].
  exact Hfn.
Qed.

(** fbo_spec does not bound the bytes written by avail_out; the model does (out_put's guard). *)
Lemma mb_read_len b lo len l : mb_read b lo len = Some l -> Zlength l = len.
Proof.
  unfold mb_read, mb_definedb. intros H.
  destruct (0 <=? len) eqn:E0; [|discriminate].
  destruct (0 <=? lo) eqn:E1; [|discriminate].
  destruct (lo + len <=? Zlength (mb_val b)) eqn:E2; [|discriminate]. cbn [andb] in H.
  destruct (forallb _ _); [|discriminate]. injection H as <-.
  apply Z.leb_le in E0. apply Z.leb_le in E1. apply Z.leb_le in E2.
  rewrite Zlength_sublist by lia. lia.
Qed.

Lemma flush_pending_avail s z s' z' :
  c_flush_pending s z = Some (s', z') -> 0 <= z_avail_out z -> 0 <= z_avail_out z'.
Proof.
  unfold c_flush_pending. intros H Hz.
  destruct (c_tr_flush_bits (d_out s)) as [o|]; [|discriminate]. cbn [bind] in H.
  set (len := if d_pending (set_d_out s o) >? z_avail_out z then z_avail_out z
              else u32 (d_pending (set_d_out s o))) in H.
  destruct (len =? 0); [injection H as _ <-; exact Hz|].
  destruct (mb_read _ _ len) as [l|] eqn:Er; [|discriminate]. cbn [bind] in H.
  apply mb_read_len in Er.
  unfold out_put in H. destruct (Zlength l <=? z_avail_out z) eqn:Eo; [|discriminate].
  apply Z.leb_le in Eo. cbn [bind] in H.
  destruct (d_pending _ =? 0); injection H as _ <-; cbn; lia.
Qed.

Lemma flush_block_only_avail s z last s' z' :
  c_flush_block_only s z last = Some (s', z') -> 0 <= z_avail_out z -> 0 <= z_avail_out z'.
Proof.
  unfold c_flush_block_only. intros H Hz.
  destruct (in_long _); [|discriminate]. cbn [guard bind] in H.
  destruct (if d_block_start s >=? 0 then _ else _) as [buf|]; [|discriminate]. cbn [bind] in H.
  destruct (c_tr_flush_block _ _ _ _) as [[t k]|]; [|discriminate]. cbn [bind] in H.
  exact (flush_pending_avail _ _ _ _ H Hz).
Qed.
