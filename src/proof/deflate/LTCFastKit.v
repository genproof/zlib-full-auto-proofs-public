(** * Kit for LTCFast2.v: deflate_fast on the checked model.

    The proof of [fast_ok2] is cut into parts (statements [*_stmt] below, one file each):
    - [refill_stmt] (LTCFastRefill.v): the top of the loop, c_refill with fill_window;
    - [search_stmt] (LTCFastSearch.v): INSERT_STRING at strstart and longest_match ([fsearch]);
    - [lit_stmt] (LTCFastLit2.v): the literal branch ([flit]);
    - [insloop_stmt] (LTCFastInsLoop.v): the insertion loop after a short match (df_insert_body);
    - [match_stmt] (LTCFastMatch2.v): the match branch ([fmatch]);
    - [fbw_stmt] (LTCFastFbw.v): FLUSH_BLOCK_ONLY at a state with the symbols [syms] ([TS0]);
    - [bflush_stmt] (LTCFastBflush.v): [if (bflush) FLUSH_BLOCK(s, 0)] (c_bflush);
    - [tail_stmt] (LTCFastTail.v): deflate_tail after the loop.
    The glue lemmas are in LTCFastGlue.v; LTCFast2.v assembles the parts (fast_ok2). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCLib.
Require Zlib.proof.huffman.HuffAbs.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Projections of the setters: [autorewrite with fproj in *]
    ([cbn] does not reduce [d_F (set_d_G s x)] well: use these lemmas). *)
Lemma fk_status_po s x : d_status (set_d_po s x) = d_status s. Proof. reflexivity. Qed.
Lemma fk_po_po s x : d_po (set_d_po s x) = x. Proof. reflexivity. Qed.
Lemma fk_wrap_po s x : d_wrap (set_d_po s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma fk_gzhead_po s x : d_gzhead (set_d_po s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma fk_gzindex_po s x : d_gzindex (set_d_po s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma fk_method_po s x : d_method (set_d_po s x) = d_method s. Proof. reflexivity. Qed.
Lemma fk_last_flush_po s x : d_last_flush (set_d_po s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma fk_w_size_po s x : d_w_size (set_d_po s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma fk_w_bits_po s x : d_w_bits (set_d_po s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma fk_w_mask_po s x : d_w_mask (set_d_po s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma fk_window_po s x : d_window (set_d_po s x) = d_window s. Proof. reflexivity. Qed.
Lemma fk_window_size_po s x : d_window_size (set_d_po s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma fk_prev_po s x : d_prev (set_d_po s x) = d_prev s. Proof. reflexivity. Qed.
Lemma fk_head_po s x : d_head (set_d_po s x) = d_head s. Proof. reflexivity. Qed.
Lemma fk_ins_h_po s x : d_ins_h (set_d_po s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma fk_hash_size_po s x : d_hash_size (set_d_po s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma fk_hash_bits_po s x : d_hash_bits (set_d_po s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma fk_hash_mask_po s x : d_hash_mask (set_d_po s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma fk_hash_shift_po s x : d_hash_shift (set_d_po s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma fk_block_start_po s x : d_block_start (set_d_po s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma fk_match_length_po s x : d_match_length (set_d_po s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma fk_prev_match_po s x : d_prev_match (set_d_po s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma fk_match_available_po s x : d_match_available (set_d_po s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma fk_strstart_po s x : d_strstart (set_d_po s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma fk_match_start_po s x : d_match_start (set_d_po s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma fk_lookahead_po s x : d_lookahead (set_d_po s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma fk_prev_length_po s x : d_prev_length (set_d_po s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma fk_max_chain_length_po s x : d_max_chain_length (set_d_po s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma fk_max_lazy_match_po s x : d_max_lazy_match (set_d_po s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma fk_good_match_po s x : d_good_match (set_d_po s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma fk_nice_match_po s x : d_nice_match (set_d_po s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma fk_insert_po s x : d_insert (set_d_po s x) = d_insert s. Proof. reflexivity. Qed.
Lemma fk_high_water_po s x : d_high_water (set_d_po s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma fk_slid_po s x : d_slid (set_d_po s x) = d_slid s. Proof. reflexivity. Qed.
Lemma fk_pending_buf_size_po s x : d_pending_buf_size (set_d_po s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma fk_tr_po s x : d_tr (set_d_po s x) = d_tr s. Proof. reflexivity. Qed.
Lemma fk_pbm_po s x : d_pbm (set_d_po s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma fk_status_prev s x : d_status (set_d_prev s x) = d_status s. Proof. reflexivity. Qed.
Lemma fk_po_prev s x : d_po (set_d_prev s x) = d_po s. Proof. reflexivity. Qed.
Lemma fk_wrap_prev s x : d_wrap (set_d_prev s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma fk_gzhead_prev s x : d_gzhead (set_d_prev s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma fk_gzindex_prev s x : d_gzindex (set_d_prev s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma fk_method_prev s x : d_method (set_d_prev s x) = d_method s. Proof. reflexivity. Qed.
Lemma fk_last_flush_prev s x : d_last_flush (set_d_prev s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma fk_w_size_prev s x : d_w_size (set_d_prev s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma fk_w_bits_prev s x : d_w_bits (set_d_prev s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma fk_w_mask_prev s x : d_w_mask (set_d_prev s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma fk_window_prev s x : d_window (set_d_prev s x) = d_window s. Proof. reflexivity. Qed.
Lemma fk_window_size_prev s x : d_window_size (set_d_prev s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma fk_prev_prev s x : d_prev (set_d_prev s x) = x. Proof. reflexivity. Qed.
Lemma fk_head_prev s x : d_head (set_d_prev s x) = d_head s. Proof. reflexivity. Qed.
Lemma fk_ins_h_prev s x : d_ins_h (set_d_prev s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma fk_hash_size_prev s x : d_hash_size (set_d_prev s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma fk_hash_bits_prev s x : d_hash_bits (set_d_prev s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma fk_hash_mask_prev s x : d_hash_mask (set_d_prev s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma fk_hash_shift_prev s x : d_hash_shift (set_d_prev s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma fk_block_start_prev s x : d_block_start (set_d_prev s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma fk_match_length_prev s x : d_match_length (set_d_prev s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma fk_prev_match_prev s x : d_prev_match (set_d_prev s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma fk_match_available_prev s x : d_match_available (set_d_prev s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma fk_strstart_prev s x : d_strstart (set_d_prev s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma fk_match_start_prev s x : d_match_start (set_d_prev s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma fk_lookahead_prev s x : d_lookahead (set_d_prev s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma fk_prev_length_prev s x : d_prev_length (set_d_prev s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma fk_max_chain_length_prev s x : d_max_chain_length (set_d_prev s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma fk_max_lazy_match_prev s x : d_max_lazy_match (set_d_prev s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma fk_good_match_prev s x : d_good_match (set_d_prev s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma fk_nice_match_prev s x : d_nice_match (set_d_prev s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma fk_insert_prev s x : d_insert (set_d_prev s x) = d_insert s. Proof. reflexivity. Qed.
Lemma fk_high_water_prev s x : d_high_water (set_d_prev s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma fk_slid_prev s x : d_slid (set_d_prev s x) = d_slid s. Proof. reflexivity. Qed.
Lemma fk_pending_buf_size_prev s x : d_pending_buf_size (set_d_prev s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma fk_tr_prev s x : d_tr (set_d_prev s x) = d_tr s. Proof. reflexivity. Qed.
Lemma fk_pbm_prev s x : d_pbm (set_d_prev s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma fk_status_head s x : d_status (set_d_head s x) = d_status s. Proof. reflexivity. Qed.
Lemma fk_po_head s x : d_po (set_d_head s x) = d_po s. Proof. reflexivity. Qed.
Lemma fk_wrap_head s x : d_wrap (set_d_head s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma fk_gzhead_head s x : d_gzhead (set_d_head s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma fk_gzindex_head s x : d_gzindex (set_d_head s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma fk_method_head s x : d_method (set_d_head s x) = d_method s. Proof. reflexivity. Qed.
Lemma fk_last_flush_head s x : d_last_flush (set_d_head s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma fk_w_size_head s x : d_w_size (set_d_head s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma fk_w_bits_head s x : d_w_bits (set_d_head s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma fk_w_mask_head s x : d_w_mask (set_d_head s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma fk_window_head s x : d_window (set_d_head s x) = d_window s. Proof. reflexivity. Qed.
Lemma fk_window_size_head s x : d_window_size (set_d_head s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma fk_prev_head s x : d_prev (set_d_head s x) = d_prev s. Proof. reflexivity. Qed.
Lemma fk_head_head s x : d_head (set_d_head s x) = x. Proof. reflexivity. Qed.
Lemma fk_ins_h_head s x : d_ins_h (set_d_head s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma fk_hash_size_head s x : d_hash_size (set_d_head s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma fk_hash_bits_head s x : d_hash_bits (set_d_head s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma fk_hash_mask_head s x : d_hash_mask (set_d_head s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma fk_hash_shift_head s x : d_hash_shift (set_d_head s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma fk_block_start_head s x : d_block_start (set_d_head s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma fk_match_length_head s x : d_match_length (set_d_head s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma fk_prev_match_head s x : d_prev_match (set_d_head s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma fk_match_available_head s x : d_match_available (set_d_head s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma fk_strstart_head s x : d_strstart (set_d_head s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma fk_match_start_head s x : d_match_start (set_d_head s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma fk_lookahead_head s x : d_lookahead (set_d_head s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma fk_prev_length_head s x : d_prev_length (set_d_head s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma fk_max_chain_length_head s x : d_max_chain_length (set_d_head s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma fk_max_lazy_match_head s x : d_max_lazy_match (set_d_head s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma fk_good_match_head s x : d_good_match (set_d_head s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma fk_nice_match_head s x : d_nice_match (set_d_head s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma fk_insert_head s x : d_insert (set_d_head s x) = d_insert s. Proof. reflexivity. Qed.
Lemma fk_high_water_head s x : d_high_water (set_d_head s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma fk_slid_head s x : d_slid (set_d_head s x) = d_slid s. Proof. reflexivity. Qed.
Lemma fk_pending_buf_size_head s x : d_pending_buf_size (set_d_head s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma fk_tr_head s x : d_tr (set_d_head s x) = d_tr s. Proof. reflexivity. Qed.
Lemma fk_pbm_head s x : d_pbm (set_d_head s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma fk_status_ins_h s x : d_status (set_d_ins_h s x) = d_status s. Proof. reflexivity. Qed.
Lemma fk_po_ins_h s x : d_po (set_d_ins_h s x) = d_po s. Proof. reflexivity. Qed.
Lemma fk_wrap_ins_h s x : d_wrap (set_d_ins_h s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma fk_gzhead_ins_h s x : d_gzhead (set_d_ins_h s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma fk_gzindex_ins_h s x : d_gzindex (set_d_ins_h s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma fk_method_ins_h s x : d_method (set_d_ins_h s x) = d_method s. Proof. reflexivity. Qed.
Lemma fk_last_flush_ins_h s x : d_last_flush (set_d_ins_h s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma fk_w_size_ins_h s x : d_w_size (set_d_ins_h s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma fk_w_bits_ins_h s x : d_w_bits (set_d_ins_h s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma fk_w_mask_ins_h s x : d_w_mask (set_d_ins_h s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma fk_window_ins_h s x : d_window (set_d_ins_h s x) = d_window s. Proof. reflexivity. Qed.
Lemma fk_window_size_ins_h s x : d_window_size (set_d_ins_h s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma fk_prev_ins_h s x : d_prev (set_d_ins_h s x) = d_prev s. Proof. reflexivity. Qed.
Lemma fk_head_ins_h s x : d_head (set_d_ins_h s x) = d_head s. Proof. reflexivity. Qed.
Lemma fk_ins_h_ins_h s x : d_ins_h (set_d_ins_h s x) = x. Proof. reflexivity. Qed.
Lemma fk_hash_size_ins_h s x : d_hash_size (set_d_ins_h s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma fk_hash_bits_ins_h s x : d_hash_bits (set_d_ins_h s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma fk_hash_mask_ins_h s x : d_hash_mask (set_d_ins_h s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma fk_hash_shift_ins_h s x : d_hash_shift (set_d_ins_h s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma fk_block_start_ins_h s x : d_block_start (set_d_ins_h s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma fk_match_length_ins_h s x : d_match_length (set_d_ins_h s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma fk_prev_match_ins_h s x : d_prev_match (set_d_ins_h s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma fk_match_available_ins_h s x : d_match_available (set_d_ins_h s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma fk_strstart_ins_h s x : d_strstart (set_d_ins_h s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma fk_match_start_ins_h s x : d_match_start (set_d_ins_h s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma fk_lookahead_ins_h s x : d_lookahead (set_d_ins_h s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma fk_prev_length_ins_h s x : d_prev_length (set_d_ins_h s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma fk_max_chain_length_ins_h s x : d_max_chain_length (set_d_ins_h s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma fk_max_lazy_match_ins_h s x : d_max_lazy_match (set_d_ins_h s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma fk_good_match_ins_h s x : d_good_match (set_d_ins_h s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma fk_nice_match_ins_h s x : d_nice_match (set_d_ins_h s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma fk_insert_ins_h s x : d_insert (set_d_ins_h s x) = d_insert s. Proof. reflexivity. Qed.
Lemma fk_high_water_ins_h s x : d_high_water (set_d_ins_h s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma fk_slid_ins_h s x : d_slid (set_d_ins_h s x) = d_slid s. Proof. reflexivity. Qed.
Lemma fk_pending_buf_size_ins_h s x : d_pending_buf_size (set_d_ins_h s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma fk_tr_ins_h s x : d_tr (set_d_ins_h s x) = d_tr s. Proof. reflexivity. Qed.
Lemma fk_pbm_ins_h s x : d_pbm (set_d_ins_h s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma fk_status_block_start s x : d_status (set_d_block_start s x) = d_status s. Proof. reflexivity. Qed.
Lemma fk_po_block_start s x : d_po (set_d_block_start s x) = d_po s. Proof. reflexivity. Qed.
Lemma fk_wrap_block_start s x : d_wrap (set_d_block_start s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma fk_gzhead_block_start s x : d_gzhead (set_d_block_start s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma fk_gzindex_block_start s x : d_gzindex (set_d_block_start s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma fk_method_block_start s x : d_method (set_d_block_start s x) = d_method s. Proof. reflexivity. Qed.
Lemma fk_last_flush_block_start s x : d_last_flush (set_d_block_start s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma fk_w_size_block_start s x : d_w_size (set_d_block_start s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma fk_w_bits_block_start s x : d_w_bits (set_d_block_start s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma fk_w_mask_block_start s x : d_w_mask (set_d_block_start s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma fk_window_block_start s x : d_window (set_d_block_start s x) = d_window s. Proof. reflexivity. Qed.
Lemma fk_window_size_block_start s x : d_window_size (set_d_block_start s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma fk_prev_block_start s x : d_prev (set_d_block_start s x) = d_prev s. Proof. reflexivity. Qed.
Lemma fk_head_block_start s x : d_head (set_d_block_start s x) = d_head s. Proof. reflexivity. Qed.
Lemma fk_ins_h_block_start s x : d_ins_h (set_d_block_start s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma fk_hash_size_block_start s x : d_hash_size (set_d_block_start s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma fk_hash_bits_block_start s x : d_hash_bits (set_d_block_start s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma fk_hash_mask_block_start s x : d_hash_mask (set_d_block_start s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma fk_hash_shift_block_start s x : d_hash_shift (set_d_block_start s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma fk_block_start_block_start s x : d_block_start (set_d_block_start s x) = x. Proof. reflexivity. Qed.
Lemma fk_match_length_block_start s x : d_match_length (set_d_block_start s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma fk_prev_match_block_start s x : d_prev_match (set_d_block_start s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma fk_match_available_block_start s x : d_match_available (set_d_block_start s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma fk_strstart_block_start s x : d_strstart (set_d_block_start s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma fk_match_start_block_start s x : d_match_start (set_d_block_start s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma fk_lookahead_block_start s x : d_lookahead (set_d_block_start s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma fk_prev_length_block_start s x : d_prev_length (set_d_block_start s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma fk_max_chain_length_block_start s x : d_max_chain_length (set_d_block_start s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma fk_max_lazy_match_block_start s x : d_max_lazy_match (set_d_block_start s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma fk_good_match_block_start s x : d_good_match (set_d_block_start s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma fk_nice_match_block_start s x : d_nice_match (set_d_block_start s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma fk_insert_block_start s x : d_insert (set_d_block_start s x) = d_insert s. Proof. reflexivity. Qed.
Lemma fk_high_water_block_start s x : d_high_water (set_d_block_start s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma fk_slid_block_start s x : d_slid (set_d_block_start s x) = d_slid s. Proof. reflexivity. Qed.
Lemma fk_pending_buf_size_block_start s x : d_pending_buf_size (set_d_block_start s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma fk_tr_block_start s x : d_tr (set_d_block_start s x) = d_tr s. Proof. reflexivity. Qed.
Lemma fk_pbm_block_start s x : d_pbm (set_d_block_start s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma fk_status_match_length s x : d_status (set_d_match_length s x) = d_status s. Proof. reflexivity. Qed.
Lemma fk_po_match_length s x : d_po (set_d_match_length s x) = d_po s. Proof. reflexivity. Qed.
Lemma fk_wrap_match_length s x : d_wrap (set_d_match_length s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma fk_gzhead_match_length s x : d_gzhead (set_d_match_length s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma fk_gzindex_match_length s x : d_gzindex (set_d_match_length s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma fk_method_match_length s x : d_method (set_d_match_length s x) = d_method s. Proof. reflexivity. Qed.
Lemma fk_last_flush_match_length s x : d_last_flush (set_d_match_length s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma fk_w_size_match_length s x : d_w_size (set_d_match_length s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma fk_w_bits_match_length s x : d_w_bits (set_d_match_length s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma fk_w_mask_match_length s x : d_w_mask (set_d_match_length s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma fk_window_match_length s x : d_window (set_d_match_length s x) = d_window s. Proof. reflexivity. Qed.
Lemma fk_window_size_match_length s x : d_window_size (set_d_match_length s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma fk_prev_match_length s x : d_prev (set_d_match_length s x) = d_prev s. Proof. reflexivity. Qed.
Lemma fk_head_match_length s x : d_head (set_d_match_length s x) = d_head s. Proof. reflexivity. Qed.
Lemma fk_ins_h_match_length s x : d_ins_h (set_d_match_length s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma fk_hash_size_match_length s x : d_hash_size (set_d_match_length s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma fk_hash_bits_match_length s x : d_hash_bits (set_d_match_length s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma fk_hash_mask_match_length s x : d_hash_mask (set_d_match_length s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma fk_hash_shift_match_length s x : d_hash_shift (set_d_match_length s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma fk_block_start_match_length s x : d_block_start (set_d_match_length s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma fk_match_length_match_length s x : d_match_length (set_d_match_length s x) = x. Proof. reflexivity. Qed.
Lemma fk_prev_match_match_length s x : d_prev_match (set_d_match_length s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma fk_match_available_match_length s x : d_match_available (set_d_match_length s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma fk_strstart_match_length s x : d_strstart (set_d_match_length s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma fk_match_start_match_length s x : d_match_start (set_d_match_length s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma fk_lookahead_match_length s x : d_lookahead (set_d_match_length s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma fk_prev_length_match_length s x : d_prev_length (set_d_match_length s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma fk_max_chain_length_match_length s x : d_max_chain_length (set_d_match_length s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma fk_max_lazy_match_match_length s x : d_max_lazy_match (set_d_match_length s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma fk_good_match_match_length s x : d_good_match (set_d_match_length s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma fk_nice_match_match_length s x : d_nice_match (set_d_match_length s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma fk_insert_match_length s x : d_insert (set_d_match_length s x) = d_insert s. Proof. reflexivity. Qed.
Lemma fk_high_water_match_length s x : d_high_water (set_d_match_length s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma fk_slid_match_length s x : d_slid (set_d_match_length s x) = d_slid s. Proof. reflexivity. Qed.
Lemma fk_pending_buf_size_match_length s x : d_pending_buf_size (set_d_match_length s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma fk_tr_match_length s x : d_tr (set_d_match_length s x) = d_tr s. Proof. reflexivity. Qed.
Lemma fk_pbm_match_length s x : d_pbm (set_d_match_length s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma fk_status_strstart s x : d_status (set_d_strstart s x) = d_status s. Proof. reflexivity. Qed.
Lemma fk_po_strstart s x : d_po (set_d_strstart s x) = d_po s. Proof. reflexivity. Qed.
Lemma fk_wrap_strstart s x : d_wrap (set_d_strstart s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma fk_gzhead_strstart s x : d_gzhead (set_d_strstart s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma fk_gzindex_strstart s x : d_gzindex (set_d_strstart s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma fk_method_strstart s x : d_method (set_d_strstart s x) = d_method s. Proof. reflexivity. Qed.
Lemma fk_last_flush_strstart s x : d_last_flush (set_d_strstart s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma fk_w_size_strstart s x : d_w_size (set_d_strstart s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma fk_w_bits_strstart s x : d_w_bits (set_d_strstart s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma fk_w_mask_strstart s x : d_w_mask (set_d_strstart s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma fk_window_strstart s x : d_window (set_d_strstart s x) = d_window s. Proof. reflexivity. Qed.
Lemma fk_window_size_strstart s x : d_window_size (set_d_strstart s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma fk_prev_strstart s x : d_prev (set_d_strstart s x) = d_prev s. Proof. reflexivity. Qed.
Lemma fk_head_strstart s x : d_head (set_d_strstart s x) = d_head s. Proof. reflexivity. Qed.
Lemma fk_ins_h_strstart s x : d_ins_h (set_d_strstart s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma fk_hash_size_strstart s x : d_hash_size (set_d_strstart s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma fk_hash_bits_strstart s x : d_hash_bits (set_d_strstart s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma fk_hash_mask_strstart s x : d_hash_mask (set_d_strstart s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma fk_hash_shift_strstart s x : d_hash_shift (set_d_strstart s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma fk_block_start_strstart s x : d_block_start (set_d_strstart s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma fk_match_length_strstart s x : d_match_length (set_d_strstart s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma fk_prev_match_strstart s x : d_prev_match (set_d_strstart s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma fk_match_available_strstart s x : d_match_available (set_d_strstart s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma fk_strstart_strstart s x : d_strstart (set_d_strstart s x) = x. Proof. reflexivity. Qed.
Lemma fk_match_start_strstart s x : d_match_start (set_d_strstart s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma fk_lookahead_strstart s x : d_lookahead (set_d_strstart s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma fk_prev_length_strstart s x : d_prev_length (set_d_strstart s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma fk_max_chain_length_strstart s x : d_max_chain_length (set_d_strstart s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma fk_max_lazy_match_strstart s x : d_max_lazy_match (set_d_strstart s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma fk_good_match_strstart s x : d_good_match (set_d_strstart s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma fk_nice_match_strstart s x : d_nice_match (set_d_strstart s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma fk_insert_strstart s x : d_insert (set_d_strstart s x) = d_insert s. Proof. reflexivity. Qed.
Lemma fk_high_water_strstart s x : d_high_water (set_d_strstart s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma fk_slid_strstart s x : d_slid (set_d_strstart s x) = d_slid s. Proof. reflexivity. Qed.
Lemma fk_pending_buf_size_strstart s x : d_pending_buf_size (set_d_strstart s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma fk_tr_strstart s x : d_tr (set_d_strstart s x) = d_tr s. Proof. reflexivity. Qed.
Lemma fk_pbm_strstart s x : d_pbm (set_d_strstart s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma fk_status_match_start s x : d_status (set_d_match_start s x) = d_status s. Proof. reflexivity. Qed.
Lemma fk_po_match_start s x : d_po (set_d_match_start s x) = d_po s. Proof. reflexivity. Qed.
Lemma fk_wrap_match_start s x : d_wrap (set_d_match_start s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma fk_gzhead_match_start s x : d_gzhead (set_d_match_start s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma fk_gzindex_match_start s x : d_gzindex (set_d_match_start s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma fk_method_match_start s x : d_method (set_d_match_start s x) = d_method s. Proof. reflexivity. Qed.
Lemma fk_last_flush_match_start s x : d_last_flush (set_d_match_start s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma fk_w_size_match_start s x : d_w_size (set_d_match_start s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma fk_w_bits_match_start s x : d_w_bits (set_d_match_start s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma fk_w_mask_match_start s x : d_w_mask (set_d_match_start s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma fk_window_match_start s x : d_window (set_d_match_start s x) = d_window s. Proof. reflexivity. Qed.
Lemma fk_window_size_match_start s x : d_window_size (set_d_match_start s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma fk_prev_match_start s x : d_prev (set_d_match_start s x) = d_prev s. Proof. reflexivity. Qed.
Lemma fk_head_match_start s x : d_head (set_d_match_start s x) = d_head s. Proof. reflexivity. Qed.
Lemma fk_ins_h_match_start s x : d_ins_h (set_d_match_start s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma fk_hash_size_match_start s x : d_hash_size (set_d_match_start s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma fk_hash_bits_match_start s x : d_hash_bits (set_d_match_start s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma fk_hash_mask_match_start s x : d_hash_mask (set_d_match_start s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma fk_hash_shift_match_start s x : d_hash_shift (set_d_match_start s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma fk_block_start_match_start s x : d_block_start (set_d_match_start s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma fk_match_length_match_start s x : d_match_length (set_d_match_start s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma fk_prev_match_match_start s x : d_prev_match (set_d_match_start s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma fk_match_available_match_start s x : d_match_available (set_d_match_start s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma fk_strstart_match_start s x : d_strstart (set_d_match_start s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma fk_match_start_match_start s x : d_match_start (set_d_match_start s x) = x. Proof. reflexivity. Qed.
Lemma fk_lookahead_match_start s x : d_lookahead (set_d_match_start s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma fk_prev_length_match_start s x : d_prev_length (set_d_match_start s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma fk_max_chain_length_match_start s x : d_max_chain_length (set_d_match_start s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma fk_max_lazy_match_match_start s x : d_max_lazy_match (set_d_match_start s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma fk_good_match_match_start s x : d_good_match (set_d_match_start s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma fk_nice_match_match_start s x : d_nice_match (set_d_match_start s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma fk_insert_match_start s x : d_insert (set_d_match_start s x) = d_insert s. Proof. reflexivity. Qed.
Lemma fk_high_water_match_start s x : d_high_water (set_d_match_start s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma fk_slid_match_start s x : d_slid (set_d_match_start s x) = d_slid s. Proof. reflexivity. Qed.
Lemma fk_pending_buf_size_match_start s x : d_pending_buf_size (set_d_match_start s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma fk_tr_match_start s x : d_tr (set_d_match_start s x) = d_tr s. Proof. reflexivity. Qed.
Lemma fk_pbm_match_start s x : d_pbm (set_d_match_start s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma fk_status_lookahead s x : d_status (set_d_lookahead s x) = d_status s. Proof. reflexivity. Qed.
Lemma fk_po_lookahead s x : d_po (set_d_lookahead s x) = d_po s. Proof. reflexivity. Qed.
Lemma fk_wrap_lookahead s x : d_wrap (set_d_lookahead s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma fk_gzhead_lookahead s x : d_gzhead (set_d_lookahead s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma fk_gzindex_lookahead s x : d_gzindex (set_d_lookahead s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma fk_method_lookahead s x : d_method (set_d_lookahead s x) = d_method s. Proof. reflexivity. Qed.
Lemma fk_last_flush_lookahead s x : d_last_flush (set_d_lookahead s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma fk_w_size_lookahead s x : d_w_size (set_d_lookahead s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma fk_w_bits_lookahead s x : d_w_bits (set_d_lookahead s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma fk_w_mask_lookahead s x : d_w_mask (set_d_lookahead s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma fk_window_lookahead s x : d_window (set_d_lookahead s x) = d_window s. Proof. reflexivity. Qed.
Lemma fk_window_size_lookahead s x : d_window_size (set_d_lookahead s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma fk_prev_lookahead s x : d_prev (set_d_lookahead s x) = d_prev s. Proof. reflexivity. Qed.
Lemma fk_head_lookahead s x : d_head (set_d_lookahead s x) = d_head s. Proof. reflexivity. Qed.
Lemma fk_ins_h_lookahead s x : d_ins_h (set_d_lookahead s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma fk_hash_size_lookahead s x : d_hash_size (set_d_lookahead s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma fk_hash_bits_lookahead s x : d_hash_bits (set_d_lookahead s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma fk_hash_mask_lookahead s x : d_hash_mask (set_d_lookahead s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma fk_hash_shift_lookahead s x : d_hash_shift (set_d_lookahead s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma fk_block_start_lookahead s x : d_block_start (set_d_lookahead s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma fk_match_length_lookahead s x : d_match_length (set_d_lookahead s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma fk_prev_match_lookahead s x : d_prev_match (set_d_lookahead s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma fk_match_available_lookahead s x : d_match_available (set_d_lookahead s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma fk_strstart_lookahead s x : d_strstart (set_d_lookahead s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma fk_match_start_lookahead s x : d_match_start (set_d_lookahead s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma fk_lookahead_lookahead s x : d_lookahead (set_d_lookahead s x) = x. Proof. reflexivity. Qed.
Lemma fk_prev_length_lookahead s x : d_prev_length (set_d_lookahead s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma fk_max_chain_length_lookahead s x : d_max_chain_length (set_d_lookahead s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma fk_max_lazy_match_lookahead s x : d_max_lazy_match (set_d_lookahead s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma fk_good_match_lookahead s x : d_good_match (set_d_lookahead s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma fk_nice_match_lookahead s x : d_nice_match (set_d_lookahead s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma fk_insert_lookahead s x : d_insert (set_d_lookahead s x) = d_insert s. Proof. reflexivity. Qed.
Lemma fk_high_water_lookahead s x : d_high_water (set_d_lookahead s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma fk_slid_lookahead s x : d_slid (set_d_lookahead s x) = d_slid s. Proof. reflexivity. Qed.
Lemma fk_pending_buf_size_lookahead s x : d_pending_buf_size (set_d_lookahead s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma fk_tr_lookahead s x : d_tr (set_d_lookahead s x) = d_tr s. Proof. reflexivity. Qed.
Lemma fk_pbm_lookahead s x : d_pbm (set_d_lookahead s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma fk_status_insert s x : d_status (set_d_insert s x) = d_status s. Proof. reflexivity. Qed.
Lemma fk_po_insert s x : d_po (set_d_insert s x) = d_po s. Proof. reflexivity. Qed.
Lemma fk_wrap_insert s x : d_wrap (set_d_insert s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma fk_gzhead_insert s x : d_gzhead (set_d_insert s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma fk_gzindex_insert s x : d_gzindex (set_d_insert s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma fk_method_insert s x : d_method (set_d_insert s x) = d_method s. Proof. reflexivity. Qed.
Lemma fk_last_flush_insert s x : d_last_flush (set_d_insert s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma fk_w_size_insert s x : d_w_size (set_d_insert s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma fk_w_bits_insert s x : d_w_bits (set_d_insert s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma fk_w_mask_insert s x : d_w_mask (set_d_insert s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma fk_window_insert s x : d_window (set_d_insert s x) = d_window s. Proof. reflexivity. Qed.
Lemma fk_window_size_insert s x : d_window_size (set_d_insert s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma fk_prev_insert s x : d_prev (set_d_insert s x) = d_prev s. Proof. reflexivity. Qed.
Lemma fk_head_insert s x : d_head (set_d_insert s x) = d_head s. Proof. reflexivity. Qed.
Lemma fk_ins_h_insert s x : d_ins_h (set_d_insert s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma fk_hash_size_insert s x : d_hash_size (set_d_insert s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma fk_hash_bits_insert s x : d_hash_bits (set_d_insert s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma fk_hash_mask_insert s x : d_hash_mask (set_d_insert s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma fk_hash_shift_insert s x : d_hash_shift (set_d_insert s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma fk_block_start_insert s x : d_block_start (set_d_insert s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma fk_match_length_insert s x : d_match_length (set_d_insert s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma fk_prev_match_insert s x : d_prev_match (set_d_insert s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma fk_match_available_insert s x : d_match_available (set_d_insert s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma fk_strstart_insert s x : d_strstart (set_d_insert s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma fk_match_start_insert s x : d_match_start (set_d_insert s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma fk_lookahead_insert s x : d_lookahead (set_d_insert s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma fk_prev_length_insert s x : d_prev_length (set_d_insert s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma fk_max_chain_length_insert s x : d_max_chain_length (set_d_insert s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma fk_max_lazy_match_insert s x : d_max_lazy_match (set_d_insert s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma fk_good_match_insert s x : d_good_match (set_d_insert s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma fk_nice_match_insert s x : d_nice_match (set_d_insert s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma fk_insert_insert s x : d_insert (set_d_insert s x) = x. Proof. reflexivity. Qed.
Lemma fk_high_water_insert s x : d_high_water (set_d_insert s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma fk_slid_insert s x : d_slid (set_d_insert s x) = d_slid s. Proof. reflexivity. Qed.
Lemma fk_pending_buf_size_insert s x : d_pending_buf_size (set_d_insert s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma fk_tr_insert s x : d_tr (set_d_insert s x) = d_tr s. Proof. reflexivity. Qed.
Lemma fk_pbm_insert s x : d_pbm (set_d_insert s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma fk_status_tr s x : d_status (set_d_tr s x) = d_status s. Proof. reflexivity. Qed.
Lemma fk_po_tr s x : d_po (set_d_tr s x) = d_po s. Proof. reflexivity. Qed.
Lemma fk_wrap_tr s x : d_wrap (set_d_tr s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma fk_gzhead_tr s x : d_gzhead (set_d_tr s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma fk_gzindex_tr s x : d_gzindex (set_d_tr s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma fk_method_tr s x : d_method (set_d_tr s x) = d_method s. Proof. reflexivity. Qed.
Lemma fk_last_flush_tr s x : d_last_flush (set_d_tr s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma fk_w_size_tr s x : d_w_size (set_d_tr s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma fk_w_bits_tr s x : d_w_bits (set_d_tr s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma fk_w_mask_tr s x : d_w_mask (set_d_tr s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma fk_window_tr s x : d_window (set_d_tr s x) = d_window s. Proof. reflexivity. Qed.
Lemma fk_window_size_tr s x : d_window_size (set_d_tr s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma fk_prev_tr s x : d_prev (set_d_tr s x) = d_prev s. Proof. reflexivity. Qed.
Lemma fk_head_tr s x : d_head (set_d_tr s x) = d_head s. Proof. reflexivity. Qed.
Lemma fk_ins_h_tr s x : d_ins_h (set_d_tr s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma fk_hash_size_tr s x : d_hash_size (set_d_tr s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma fk_hash_bits_tr s x : d_hash_bits (set_d_tr s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma fk_hash_mask_tr s x : d_hash_mask (set_d_tr s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma fk_hash_shift_tr s x : d_hash_shift (set_d_tr s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma fk_block_start_tr s x : d_block_start (set_d_tr s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma fk_match_length_tr s x : d_match_length (set_d_tr s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma fk_prev_match_tr s x : d_prev_match (set_d_tr s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma fk_match_available_tr s x : d_match_available (set_d_tr s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma fk_strstart_tr s x : d_strstart (set_d_tr s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma fk_match_start_tr s x : d_match_start (set_d_tr s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma fk_lookahead_tr s x : d_lookahead (set_d_tr s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma fk_prev_length_tr s x : d_prev_length (set_d_tr s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma fk_max_chain_length_tr s x : d_max_chain_length (set_d_tr s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma fk_max_lazy_match_tr s x : d_max_lazy_match (set_d_tr s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma fk_good_match_tr s x : d_good_match (set_d_tr s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma fk_nice_match_tr s x : d_nice_match (set_d_tr s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma fk_insert_tr s x : d_insert (set_d_tr s x) = d_insert s. Proof. reflexivity. Qed.
Lemma fk_high_water_tr s x : d_high_water (set_d_tr s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma fk_slid_tr s x : d_slid (set_d_tr s x) = d_slid s. Proof. reflexivity. Qed.
Lemma fk_pending_buf_size_tr s x : d_pending_buf_size (set_d_tr s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma fk_tr_tr s x : d_tr (set_d_tr s x) = x. Proof. reflexivity. Qed.
Lemma fk_pbm_tr s x : d_pbm (set_d_tr s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma fk_status_pbm s x : d_status (set_d_pbm s x) = d_status s. Proof. reflexivity. Qed.
Lemma fk_po_pbm s x : d_po (set_d_pbm s x) = d_po s. Proof. reflexivity. Qed.
Lemma fk_wrap_pbm s x : d_wrap (set_d_pbm s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma fk_gzhead_pbm s x : d_gzhead (set_d_pbm s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma fk_gzindex_pbm s x : d_gzindex (set_d_pbm s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma fk_method_pbm s x : d_method (set_d_pbm s x) = d_method s. Proof. reflexivity. Qed.
Lemma fk_last_flush_pbm s x : d_last_flush (set_d_pbm s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma fk_w_size_pbm s x : d_w_size (set_d_pbm s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma fk_w_bits_pbm s x : d_w_bits (set_d_pbm s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma fk_w_mask_pbm s x : d_w_mask (set_d_pbm s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma fk_window_pbm s x : d_window (set_d_pbm s x) = d_window s. Proof. reflexivity. Qed.
Lemma fk_window_size_pbm s x : d_window_size (set_d_pbm s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma fk_prev_pbm s x : d_prev (set_d_pbm s x) = d_prev s. Proof. reflexivity. Qed.
Lemma fk_head_pbm s x : d_head (set_d_pbm s x) = d_head s. Proof. reflexivity. Qed.
Lemma fk_ins_h_pbm s x : d_ins_h (set_d_pbm s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma fk_hash_size_pbm s x : d_hash_size (set_d_pbm s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma fk_hash_bits_pbm s x : d_hash_bits (set_d_pbm s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma fk_hash_mask_pbm s x : d_hash_mask (set_d_pbm s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma fk_hash_shift_pbm s x : d_hash_shift (set_d_pbm s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma fk_block_start_pbm s x : d_block_start (set_d_pbm s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma fk_match_length_pbm s x : d_match_length (set_d_pbm s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma fk_prev_match_pbm s x : d_prev_match (set_d_pbm s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma fk_match_available_pbm s x : d_match_available (set_d_pbm s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma fk_strstart_pbm s x : d_strstart (set_d_pbm s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma fk_match_start_pbm s x : d_match_start (set_d_pbm s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma fk_lookahead_pbm s x : d_lookahead (set_d_pbm s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma fk_prev_length_pbm s x : d_prev_length (set_d_pbm s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma fk_max_chain_length_pbm s x : d_max_chain_length (set_d_pbm s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma fk_max_lazy_match_pbm s x : d_max_lazy_match (set_d_pbm s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma fk_good_match_pbm s x : d_good_match (set_d_pbm s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma fk_nice_match_pbm s x : d_nice_match (set_d_pbm s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma fk_insert_pbm s x : d_insert (set_d_pbm s x) = d_insert s. Proof. reflexivity. Qed.
Lemma fk_high_water_pbm s x : d_high_water (set_d_pbm s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma fk_slid_pbm s x : d_slid (set_d_pbm s x) = d_slid s. Proof. reflexivity. Qed.
Lemma fk_pending_buf_size_pbm s x : d_pending_buf_size (set_d_pbm s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma fk_tr_pbm s x : d_tr (set_d_pbm s x) = d_tr s. Proof. reflexivity. Qed.
Lemma fk_pbm_pbm s x : d_pbm (set_d_pbm s x) = x. Proof. reflexivity. Qed.
#[export] Hint Rewrite fk_status_po fk_po_po fk_wrap_po fk_gzhead_po fk_gzindex_po fk_method_po fk_last_flush_po fk_w_size_po fk_w_bits_po fk_w_mask_po fk_window_po fk_window_size_po fk_prev_po fk_head_po fk_ins_h_po fk_hash_size_po fk_hash_bits_po fk_hash_mask_po fk_hash_shift_po fk_block_start_po fk_match_length_po fk_prev_match_po fk_match_available_po fk_strstart_po fk_match_start_po fk_lookahead_po fk_prev_length_po fk_max_chain_length_po fk_max_lazy_match_po fk_good_match_po fk_nice_match_po fk_insert_po fk_high_water_po fk_slid_po fk_pending_buf_size_po fk_tr_po fk_pbm_po fk_status_prev fk_po_prev fk_wrap_prev fk_gzhead_prev fk_gzindex_prev fk_method_prev fk_last_flush_prev fk_w_size_prev fk_w_bits_prev fk_w_mask_prev fk_window_prev fk_window_size_prev fk_prev_prev fk_head_prev fk_ins_h_prev fk_hash_size_prev fk_hash_bits_prev fk_hash_mask_prev fk_hash_shift_prev fk_block_start_prev fk_match_length_prev fk_prev_match_prev fk_match_available_prev fk_strstart_prev fk_match_start_prev fk_lookahead_prev fk_prev_length_prev fk_max_chain_length_prev fk_max_lazy_match_prev fk_good_match_prev fk_nice_match_prev fk_insert_prev fk_high_water_prev fk_slid_prev fk_pending_buf_size_prev fk_tr_prev fk_pbm_prev fk_status_head fk_po_head fk_wrap_head fk_gzhead_head fk_gzindex_head fk_method_head fk_last_flush_head fk_w_size_head fk_w_bits_head fk_w_mask_head fk_window_head fk_window_size_head fk_prev_head fk_head_head fk_ins_h_head fk_hash_size_head fk_hash_bits_head fk_hash_mask_head fk_hash_shift_head fk_block_start_head fk_match_length_head fk_prev_match_head fk_match_available_head fk_strstart_head fk_match_start_head fk_lookahead_head fk_prev_length_head fk_max_chain_length_head fk_max_lazy_match_head fk_good_match_head fk_nice_match_head fk_insert_head fk_high_water_head fk_slid_head fk_pending_buf_size_head fk_tr_head fk_pbm_head fk_status_ins_h fk_po_ins_h fk_wrap_ins_h fk_gzhead_ins_h fk_gzindex_ins_h fk_method_ins_h fk_last_flush_ins_h fk_w_size_ins_h fk_w_bits_ins_h fk_w_mask_ins_h fk_window_ins_h fk_window_size_ins_h fk_prev_ins_h fk_head_ins_h fk_ins_h_ins_h fk_hash_size_ins_h fk_hash_bits_ins_h fk_hash_mask_ins_h fk_hash_shift_ins_h fk_block_start_ins_h fk_match_length_ins_h fk_prev_match_ins_h fk_match_available_ins_h fk_strstart_ins_h fk_match_start_ins_h fk_lookahead_ins_h fk_prev_length_ins_h fk_max_chain_length_ins_h fk_max_lazy_match_ins_h fk_good_match_ins_h fk_nice_match_ins_h fk_insert_ins_h fk_high_water_ins_h fk_slid_ins_h fk_pending_buf_size_ins_h fk_tr_ins_h fk_pbm_ins_h fk_status_block_start fk_po_block_start fk_wrap_block_start fk_gzhead_block_start fk_gzindex_block_start fk_method_block_start fk_last_flush_block_start fk_w_size_block_start fk_w_bits_block_start fk_w_mask_block_start fk_window_block_start fk_window_size_block_start fk_prev_block_start fk_head_block_start fk_ins_h_block_start fk_hash_size_block_start fk_hash_bits_block_start fk_hash_mask_block_start fk_hash_shift_block_start fk_block_start_block_start fk_match_length_block_start fk_prev_match_block_start fk_match_available_block_start fk_strstart_block_start fk_match_start_block_start fk_lookahead_block_start fk_prev_length_block_start fk_max_chain_length_block_start fk_max_lazy_match_block_start fk_good_match_block_start fk_nice_match_block_start fk_insert_block_start fk_high_water_block_start fk_slid_block_start fk_pending_buf_size_block_start fk_tr_block_start fk_pbm_block_start fk_status_match_length fk_po_match_length fk_wrap_match_length fk_gzhead_match_length fk_gzindex_match_length fk_method_match_length fk_last_flush_match_length fk_w_size_match_length fk_w_bits_match_length fk_w_mask_match_length fk_window_match_length fk_window_size_match_length fk_prev_match_length fk_head_match_length fk_ins_h_match_length fk_hash_size_match_length fk_hash_bits_match_length fk_hash_mask_match_length fk_hash_shift_match_length fk_block_start_match_length fk_match_length_match_length fk_prev_match_match_length fk_match_available_match_length fk_strstart_match_length fk_match_start_match_length fk_lookahead_match_length fk_prev_length_match_length fk_max_chain_length_match_length fk_max_lazy_match_match_length fk_good_match_match_length fk_nice_match_match_length fk_insert_match_length fk_high_water_match_length fk_slid_match_length fk_pending_buf_size_match_length fk_tr_match_length fk_pbm_match_length fk_status_strstart fk_po_strstart fk_wrap_strstart fk_gzhead_strstart fk_gzindex_strstart fk_method_strstart fk_last_flush_strstart fk_w_size_strstart fk_w_bits_strstart fk_w_mask_strstart fk_window_strstart fk_window_size_strstart fk_prev_strstart fk_head_strstart fk_ins_h_strstart fk_hash_size_strstart fk_hash_bits_strstart fk_hash_mask_strstart fk_hash_shift_strstart fk_block_start_strstart fk_match_length_strstart fk_prev_match_strstart fk_match_available_strstart fk_strstart_strstart fk_match_start_strstart fk_lookahead_strstart fk_prev_length_strstart fk_max_chain_length_strstart fk_max_lazy_match_strstart fk_good_match_strstart fk_nice_match_strstart fk_insert_strstart fk_high_water_strstart fk_slid_strstart fk_pending_buf_size_strstart fk_tr_strstart fk_pbm_strstart fk_status_match_start fk_po_match_start fk_wrap_match_start fk_gzhead_match_start fk_gzindex_match_start fk_method_match_start fk_last_flush_match_start fk_w_size_match_start fk_w_bits_match_start fk_w_mask_match_start fk_window_match_start fk_window_size_match_start fk_prev_match_start fk_head_match_start fk_ins_h_match_start fk_hash_size_match_start fk_hash_bits_match_start fk_hash_mask_match_start fk_hash_shift_match_start fk_block_start_match_start fk_match_length_match_start fk_prev_match_match_start fk_match_available_match_start fk_strstart_match_start fk_match_start_match_start fk_lookahead_match_start fk_prev_length_match_start fk_max_chain_length_match_start fk_max_lazy_match_match_start fk_good_match_match_start fk_nice_match_match_start fk_insert_match_start fk_high_water_match_start fk_slid_match_start fk_pending_buf_size_match_start fk_tr_match_start fk_pbm_match_start fk_status_lookahead fk_po_lookahead fk_wrap_lookahead fk_gzhead_lookahead fk_gzindex_lookahead fk_method_lookahead fk_last_flush_lookahead fk_w_size_lookahead fk_w_bits_lookahead fk_w_mask_lookahead fk_window_lookahead fk_window_size_lookahead fk_prev_lookahead fk_head_lookahead fk_ins_h_lookahead fk_hash_size_lookahead fk_hash_bits_lookahead fk_hash_mask_lookahead fk_hash_shift_lookahead fk_block_start_lookahead fk_match_length_lookahead fk_prev_match_lookahead fk_match_available_lookahead fk_strstart_lookahead fk_match_start_lookahead fk_lookahead_lookahead fk_prev_length_lookahead fk_max_chain_length_lookahead fk_max_lazy_match_lookahead fk_good_match_lookahead fk_nice_match_lookahead fk_insert_lookahead fk_high_water_lookahead fk_slid_lookahead fk_pending_buf_size_lookahead fk_tr_lookahead fk_pbm_lookahead fk_status_insert fk_po_insert fk_wrap_insert fk_gzhead_insert fk_gzindex_insert fk_method_insert fk_last_flush_insert fk_w_size_insert fk_w_bits_insert fk_w_mask_insert fk_window_insert fk_window_size_insert fk_prev_insert fk_head_insert fk_ins_h_insert fk_hash_size_insert fk_hash_bits_insert fk_hash_mask_insert fk_hash_shift_insert fk_block_start_insert fk_match_length_insert fk_prev_match_insert fk_match_available_insert fk_strstart_insert fk_match_start_insert fk_lookahead_insert fk_prev_length_insert fk_max_chain_length_insert fk_max_lazy_match_insert fk_good_match_insert fk_nice_match_insert fk_insert_insert fk_high_water_insert fk_slid_insert fk_pending_buf_size_insert fk_tr_insert fk_pbm_insert fk_status_tr fk_po_tr fk_wrap_tr fk_gzhead_tr fk_gzindex_tr fk_method_tr fk_last_flush_tr fk_w_size_tr fk_w_bits_tr fk_w_mask_tr fk_window_tr fk_window_size_tr fk_prev_tr fk_head_tr fk_ins_h_tr fk_hash_size_tr fk_hash_bits_tr fk_hash_mask_tr fk_hash_shift_tr fk_block_start_tr fk_match_length_tr fk_prev_match_tr fk_match_available_tr fk_strstart_tr fk_match_start_tr fk_lookahead_tr fk_prev_length_tr fk_max_chain_length_tr fk_max_lazy_match_tr fk_good_match_tr fk_nice_match_tr fk_insert_tr fk_high_water_tr fk_slid_tr fk_pending_buf_size_tr fk_tr_tr fk_pbm_tr fk_status_pbm fk_po_pbm fk_wrap_pbm fk_gzhead_pbm fk_gzindex_pbm fk_method_pbm fk_last_flush_pbm fk_w_size_pbm fk_w_bits_pbm fk_w_mask_pbm fk_window_pbm fk_window_size_pbm fk_prev_pbm fk_head_pbm fk_ins_h_pbm fk_hash_size_pbm fk_hash_bits_pbm fk_hash_mask_pbm fk_hash_shift_pbm fk_block_start_pbm fk_match_length_pbm fk_prev_match_pbm fk_match_available_pbm fk_strstart_pbm fk_match_start_pbm fk_lookahead_pbm fk_prev_length_pbm fk_max_chain_length_pbm fk_max_lazy_match_pbm fk_good_match_pbm fk_nice_match_pbm fk_insert_pbm fk_high_water_pbm fk_slid_pbm fk_pending_buf_size_pbm fk_tr_pbm fk_pbm_pbm : fproj.

(** ** What a piece of a compression call guarantees (cpost without the block_state part) *)
Definition crel (s : dstate) (z : strm) (flush : Z) (s' : dstate) (z' : strm) (evs : list dev) : Prop :=
  W s' /\ outok s' /\ same_prm s s' /\ api_eq s s' /\
  (exists k x, zstep (d_wrap s) z z' k x /\ bytes x /\ k + ub s = sum_len evs + ub s') /\
  ev_chain (Gb s (z_total_out z)) evs (Gb s' (z_total_out z')) /\
  Forall (ev_ok s flush) evs.

(** The block_state part of cpost. *)
Definition bpost (s : dstate) (z : strm) (flush : Z) (s' : dstate) (z' : strm) (bs : bstate) (evs : list dev)
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
    nothing pending, the stream sane. *)
Definition FI (s : dstate) (z : strm) (flush : Z) (s' : dstate) (z' : strm) (evs : list dev) : Prop :=
  crel s z flush s' z' evs /\ quiet s' /\ zall z' /\ adler_ok (d_wrap s') (z_adler z') /\
  Forall (fun e => ev_last e = 0) evs.

(** A step inside one iteration that changes neither the stream nor the bit count nor ub. *)
Definition fr (s s' : dstate) : Prop :=
  same_prm s s' /\ api_eq s s' /\ ub s' = ub s /\ (forall tout, Gb s' tout = Gb s tout).

(** After the refill: enough lookahead, or a fill just happened (strstart low, high_water far enough). *)
Definition ready (s : dstate) : Prop :=
  MIN_LOOKAHEAD <= d_lookahead s \/
  (d_strstart s < d_w_size s + MAX_DIST s /\
   Z.min (d_window_size s) (d_strstart s + d_lookahead s + WIN_INIT) <= d_high_water s).

(** A state of deflate_fast with the symbols [syms] (at most L - 1 of them: a full sym_buf is allowed) and
    strstart inside the window: [W] minus the L - 2 bound, plus outok, quiet. *)
Definition TS0 (s : dstate) (syms : list (Z * Z)) : Prop :=
  prm s /\ wstruct s /\ wpos s /\ wwin s /\ whash s /\ wmatch s /\
  tree_ok (d_tr s) (d_pbm s) syms /\ Zlength syms <= d_L s - 1 /\ Forall (sym_ok s) syms /\
  blk_len syms = d_strstart s - d_block_start s /\
  outok s /\ quiet s /\ fn_of s = 1 /\ d_strstart s < d_window_size s.

(** ... after a tally that returned [bf]. *)
Definition TS (s : dstate) (syms : list (Z * Z)) (bf : bool) : Prop :=
  TS0 s syms /\ bf = (Zlength syms =? d_L s - 1).

(** ** The pieces of df_step *)

(** [hash_head = NIL; if (lookahead >= MIN_MATCH) INSERT_STRING; if (hash_head != NIL && ...) longest_match] *)
Definition fsearch (s : dstate) : option dstate :=
  let* (s, hash_head) := c_insert_head s in
  if negb (hash_head =? NIL) && (u32 (d_strstart s - hash_head) <=? max_dist s) then
    let* (s, ml) := c_longest_match s hash_head in Some (set_d_match_length s ml)
  else Some s.

(** The match branch *)
Definition fmatch (s : dstate) : option (dstate * bool) :=
  let* (s, bflush) := c_dtally_dist s (u32 (d_strstart s - d_match_start s))
                                      (u32 (d_match_length s - MIN_MATCH)) in
  let s := set_d_lookahead s (u32 (d_lookahead s - d_match_length s)) in
  if (d_match_length s <=? d_max_lazy_match s) && (d_lookahead s >=? MIN_MATCH) then
    let s := set_d_match_length s (u32 (d_match_length s - 1)) in
    let* s := loop FUEL df_insert_body s in
    Some (set_d_strstart s (u32 (d_strstart s + 1)), bflush)
  else
    let s := set_d_strstart s (u32 (d_strstart s + d_match_length s)) in
    let s := set_d_match_length s 0 in
    let* c0 := mb_rd (d_window s) (d_strstart s) in
    let s := set_d_ins_h s c0 in
    let* _ := guard (d_hash_shift s <? 32) in
    let* c1 := mb_rd (d_window s) (u32 (d_strstart s + 1)) in
    Some (set_d_ins_h s (update_hash s (d_ins_h s) c1), bflush).

(** The literal branch *)
Definition flit (s : dstate) : option (dstate * bool) :=
  let* c := mb_rd (d_window s) (d_strstart s) in
  let* (s, bflush) := c_dtally_lit s c in
  let s := set_d_lookahead s (u32 (d_lookahead s - 1)) in
  Some (set_d_strstart s (u32 (d_strstart s + 1)), bflush).

Definition fbranch (s : dstate) : option (dstate * bool) :=
  if d_match_length s >=? MIN_MATCH then fmatch s else flit s.

Lemma df_step_eq s z :
  df_step s z = let* s2 := fsearch s in let* (s3, bf) := fbranch s2 in c_bflush s3 z bf.
Proof.
  unfold df_step, fsearch, fbranch, fmatch, flit.
  destruct (c_insert_head s) as [[s1 h]|]; [|reflexivity]. cbn [bind].
  destruct (negb (h =? NIL) && (u32 (d_strstart s1 - h) <=? max_dist s1)).
  - destruct (c_longest_match s1 h) as [[s2 ml]|]; reflexivity.
  - reflexivity.
Qed.

(** The fields fsearch may change blanked (ins_h, prev, head, match_start, match_length). *)
Definition sr_keep (s : dstate) : dstate := hc_keep (set_d_match_start (set_d_match_length s 0) 0).

(** The result [s2] of fsearch on [s]: the chains with the new entry (strstart, when inserted), and the match
    found (match_length >= MIN_MATCH only for a real match within MAX_DIST). *)
Definition SR (s s2 : dstate) : Prop :=
  sr_keep s2 = sr_keep s /\ wstruct s2 /\
  (exists G, chain_with s2 (d_strstart s + 1) (lim s) G) /\
  0 <= d_match_length s2 <= MAX_MATCH /\
  (MIN_MATCH <= d_match_length s2 ->
     d_match_length s2 <= d_lookahead s /\ lim s <= d_match_start s2 /\ 0 < d_match_start s2 < d_strstart s).

(** The fields the insertion loop may change blanked (strstart, match_length, ins_h, prev, head). *)
Definition il_keep (s : dstate) : dstate := hc_keep (set_d_strstart (set_d_match_length s 0) 0).

(** ** The part statements *)

Definition refill_stmt : Prop :=
  forall s z flush,
    W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 1 -> 0 <= flush <= 5 ->
    exists r, c_refill need_min_lookahead flush s z = Some r /\
    match r with
    | inl (s', z') =>
        FI s z flush s' z' [] /\ ready s' /\ 1 <= d_lookahead s' /\
        z_avail_in z' + d_lookahead s' = z_avail_in z + d_lookahead s
    | inr (s', z', Some bs) => bs = need_more /\ crel s z flush s' z' [] /\ bpost s z flush s' z' need_more []
    | inr (s', z', None) =>
        FI s z flush s' z' [] /\ d_lookahead s' = 0 /\ z_avail_in z' = 0 /\ flush <> Z_NO_FLUSH /\
        d_strstart s' < d_w_size s' + MAX_DIST s'
    end.

Definition search_stmt : Prop :=
  forall s, W s -> fn_of s = 1 -> ready s -> 1 <= d_lookahead s ->
    exists s2, fsearch s = Some s2 /\ SR s s2.

Definition lit_stmt : Prop :=
  forall s s2,
    W s -> outok s -> quiet s -> fn_of s = 1 -> ready s -> 1 <= d_lookahead s ->
    SR s s2 -> d_match_length s2 < MIN_MATCH ->
    exists s3 bf syms3, flit s2 = Some (s3, bf) /\ TS s3 syms3 bf /\ fr s s3 /\ d_lookahead s3 < d_lookahead s.

Definition match_stmt : Prop :=
  forall s s2,
    W s -> outok s -> quiet s -> fn_of s = 1 -> ready s -> 1 <= d_lookahead s ->
    SR s s2 -> MIN_MATCH <= d_match_length s2 ->
    exists s3 bf syms3, fmatch s2 = Some (s3, bf) /\ TS s3 syms3 bf /\ fr s s3 /\ d_lookahead s3 < d_lookahead s.

(** The insertion loop from strstart = p0 with match_length = k: inserts p0 + 1 .. p0 + k, ends with
    strstart = p0 + k, match_length = 0. *)
Definition insloop_stmt : Prop :=
  forall s l G,
    prm s -> wstruct s -> chain_with s (d_strstart s + 1) l G ->
    1 <= d_match_length s -> 0 <= d_strstart s -> d_strstart s + d_match_length s < 65536 ->
    d_strstart s + d_match_length s + 2 < Zlength (mb_val (d_window s)) ->
    (forall i, 0 <= i <= d_strstart s + d_match_length s + 2 -> Znth i (mb_def (d_window s)) = true) ->
    d_strstart s + d_match_length s - d_w_size s < l ->
    exists s' G',
      loop FUEL df_insert_body s = Some s' /\
      il_keep s' = il_keep s /\ wstruct s' /\
      d_strstart s' = d_strstart s + d_match_length s /\ d_match_length s' = 0 /\
      chain_with s' (d_strstart s' + 1) l G'.

Definition fbw_stmt : Prop :=
  forall s z flush syms last,
    TS0 s syms -> zall z -> adler_ok (d_wrap s) (z_adler z) -> 0 <= flush <= 5 -> 0 <= last <= 1 ->
    (last = 1 -> flush = Z_FINISH) ->
    (last = 0 -> Zlength syms = d_L s - 1 \/ (flush <> Z_NO_FLUSH /\ flush <> Z_FINISH)) ->
    exists s' z' e,
      c_flush_block_only s z last = Some (s', z') /\ crel s z flush s' z' [e] /\ ev_last e = last /\
      zall z' /\ z_adler z' = z_adler z /\ z_avail_in z' = z_avail_in z /\
      d_lookahead s' = d_lookahead s /\ d_strstart s' = d_strstart s /\ d_block_start s' = d_strstart s /\
      d_sym_next s' = 0 /\ d_bi_valid s' <= 7 /\ (last = 1 -> d_bi_valid s' = 0) /\
      (d_pending s' = 0 \/ z_avail_out z' = 0).

Definition bflush_stmt : Prop :=
  forall s z flush syms bf,
    TS s syms bf -> zall z -> adler_ok (d_wrap s) (z_adler z) -> 0 <= flush <= 5 ->
    exists r, c_bflush s z bf = Some r /\
    match r with
    | inl (s', z') =>
        (exists evs, FI s z flush s' z' evs) /\ d_lookahead s' = d_lookahead s /\ z_avail_in z' = z_avail_in z
    | inr (s', z', o) =>
        o = Some need_more /\ exists evs, crel s z flush s' z' evs /\ bpost s z flush s' z' need_more evs
    end.

Definition tail_stmt : Prop :=
  forall s z flush,
    W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 1 ->
    0 <= flush <= 5 -> flush <> Z_NO_FLUSH ->
    d_lookahead s = 0 -> z_avail_in z = 0 -> d_strstart s < d_w_size s + MAX_DIST s ->
    exists s' z' bs evs,
      c_deflate_tail (set_insert_end s) z flush = Some (s', z', bs) /\
      crel s z flush s' z' evs /\ bpost s z flush s' z' bs evs.

(** ** Helper lemmas (Qed) *)

Lemma fn_of_fast s : prm s -> fn_of s = 1 ->
  1 <= d_level s <= 3 /\ d_strategy s <> Z_HUFFMAN_ONLY /\ d_strategy s <> Z_RLE.
Proof.
  intros Hp Hf. destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & Hs & _).
  unfold fn_of in Hf.
  destruct (Z.eqb_spec (d_level s) 0) as [E0|N0]; [discriminate|].
  destruct (Z.eqb_spec (d_strategy s) Z_HUFFMAN_ONLY) as [E1|N1]; [discriminate|].
  destruct (Z.eqb_spec (d_strategy s) Z_RLE) as [E2|N2]; [discriminate|].
  split; [|split; assumption].
  assert (Hc : forall l, 0 <= l <= 9 -> l <> 0 -> cfg_f l = 1 -> 1 <= l <= 3).
  { intros l Hl' Hn Hc.
    assert (l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7 \/ l = 8 \/ l = 9) by lia.
    destruct H as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; vm_compute in Hc; lia. }
  apply Hc; auto.
Qed.

Lemma fn_of_same_prm s s' : same_prm s s' -> fn_of s' = fn_of s.
Proof.
  intros (_ & _ & _ & _ & _ & El & Es). unfold fn_of. rewrite El, Es. reflexivity.
Qed.

Lemma sumZ_app' a b : HuffAbs.sumZ (a ++ b) = HuffAbs.sumZ a + HuffAbs.sumZ b.
Proof. induction a as [|x a IH]; cbn [app HuffAbs.sumZ]; [lia|]. rewrite IH. lia. Qed.

Lemma blk_len_app syms x : blk_len (syms ++ [x]) = blk_len syms + sym_len x.
Proof. unfold blk_len. rewrite map_app, sumZ_app'. cbn [map HuffAbs.sumZ]. lia. Qed.

Lemma blk_len_bound syms :
  (forall x, In x syms -> valid_sym (fst x) (snd x)) -> 0 <= blk_len syms <= 258 * Zlength syms.
Proof.
  induction syms as [|x syms IH]; intros Hv.
  - unfold blk_len. cbn. lia.
  - unfold blk_len in *. cbn [map HuffAbs.sumZ]. rewrite Zlength_cons.
    assert (Hx : valid_sym (fst x) (snd x)) by (apply Hv; left; reflexivity).
    assert (IH' : 0 <= HuffAbs.sumZ (map sym_len syms) <= 258 * Zlength syms) by (apply IH; intros; apply Hv; right; auto).
    unfold sym_len, valid_sym in *. destruct (fst x =? 0); lia.
Qed.

(** [W] from [TS0] when sym_buf is not full. *)
Lemma TS0_W s syms : TS0 s syms -> Zlength syms <= d_L s - 2 -> W s.
Proof.
  intros (Hp & Hs & Hpos & Hw & Hh & Hm & Ht & HL & Hf & Hb & Ho & Hq & Hfn & Hss) HL2.
  assert (Hlev := fn_of_fast s Hp Hfn).
  assert (Ha : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  unfold W. split; [exact Hp|]. split; [exact Hs|]. split; [exact Hpos|]. split; [exact Hw|].
  split; [exact Hh|]. split; [exact Hm|]. split; [intros; lia|].
  exists syms. unfold wtrees. split; [exact Ht|]. split; [exact HL2|]. split; [exact Hf|].
  split; [intros; lia|]. intros _. rewrite Ha. lia.
Qed.

(** [TS0] from [W]. *)
Lemma W_TS0 s : W s -> outok s -> quiet s -> fn_of s = 1 -> d_strstart s < d_window_size s ->
  exists syms, TS0 s syms /\ Zlength syms <= d_L s - 2.
Proof.
  intros (Hp & Hs & Hpos & Hw & Hh & Hm & H0 & syms & Ht & HL & Hf & Hz & Hb) Ho Hq Hfn Hss.
  assert (Hlev := fn_of_fast s Hp Hfn).
  assert (Ha : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  exists syms. split; [|exact HL].
  unfold TS0. split; [exact Hp|]. split; [exact Hs|]. split; [exact Hpos|]. split; [exact Hw|].
  split; [exact Hh|]. split; [exact Hm|]. split; [exact Ht|]. split; [lia|]. split; [exact Hf|].
  split; [rewrite Hb by lia; rewrite Ha; lia|]. split; [exact Ho|]. split; [exact Hq|]. split; [exact Hfn|].
  exact Hss.
Qed.

Lemma FI_refl s z flush :
  W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> FI s z flush s z [].
Proof.
  intros HW Ho Hq Hz Ha. unfold FI, crel.
  split; [|split; [exact Hq|split; [exact Hz|split; [exact Ha|constructor]]]].
  split; [exact HW|]. split; [exact Ho|].
  split; [unfold same_prm; repeat split; reflexivity|].
  split; [unfold api_eq; repeat split; reflexivity|].
  split; [exists 0, []; split; [apply zstep_refl; auto|split; [constructor|cbn; lia]]|].
  split; [cbn; reflexivity|constructor].
Qed.

Lemma cpost_of s z flush s' z' bs evs :
  crel s z flush s' z' evs -> bpost s z flush s' z' bs evs -> cpost W s z flush s' z' bs evs.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7) B. unfold cpost.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
  split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. exact B.
Qed.
