(** * The checked functional model of deflate.c: the state

    The model of deflate.c (DModel*.v) is a checked model in the sense of [Zlib.proof.trees.CBase]: every function
    returns [None] exactly when the C would access memory outside the objects it is given, read a byte never
    written, or run a loop past its fuel, and otherwise [Some] of what the C computes.  The VST specification of
    each function of deflate.c is "PRE: the representation of the arguments and [c_f args = Some r]; POST: the
    representation of [r]".  All reasoning about safety (that the runs succeed) and about what deflate produces
    is pure Coq over this model.

    The state of a deflate stream is two records:
    - [dstate]: the fields of deflate_state (struct internal_state) that are not trees.c's, plus the trees.c part
      [d_tr : Model.tstate] (the huffman model's state: the three trees, the work area, pending_buf contents with
      pending, bi_buf, bi_valid, bi_used, sym_next, sym_end, matches, lit_bufsize, level, strategy, and
      strm->data_type) and the definedness mask [d_pbm] of pending_buf (pending_buf comes from malloc
      uninitialised).  Pointers are not modelled: pending_out is the offset [d_po] into pending_buf, the window is
      the masked buffer [d_window] (2 * w_size bytes), prev and head are lists of numbers (all defined: deflateInit2_
      zeroes prev, CLEAR_HASH zeroes head), gzhead is [None] (Z_NULL) or the header's contents.
    - [strm]: the z_stream as deflate sees it during one call: the input object of the call [z_in] with next_in at
      offset [z_next_in] (deflate_stored also reads back consumed bytes of it); the bytes written to the output
      object since the start of the call [z_out] (next_out = the call's initial next_out + Zlength z_out: deflate
      writes its output object sequentially); avail_in, avail_out, total_in, total_out, adler; msg ([None] =
      Z_NULL, [Some e] = ERR_MSG(e)).  data_type lives in [d_tr] (trees.c writes it). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.trees.CBase.
Require Export Zlib.proof.huffman.Model.
Import ListNotations.
Local Open Scope Z_scope.

(** The user's gzip header (deflateSetHeader): only the fields deflate() reads.  [gz_extra], [gz_name],
    [gz_comment]: [None] for Z_NULL, else the whole contents of the object the pointer points to (deflate reads
    extra[0 .. extra_len & 0xffff), and name / comment up to and including their first zero byte). *)
Record gzh := mkGZ {
  gz_text : Z;          (* int *)
  gz_time : Z;          (* uLong *)
  gz_os : Z;            (* int *)
  gz_extra : option (list Z);
  gz_extra_len : Z;     (* uInt *)
  gz_name : option (list Z);
  gz_comment : option (list Z);
  gz_hcrc : Z           (* int *)
}.

Record dstate := mkDS {
  d_status : Z;           (* int *)
  d_po : Z;               (* pending_out - pending_buf *)
  d_wrap : Z;             (* int *)
  d_gzhead : option gzh;
  d_gzindex : Z;          (* ulg *)
  d_method : Z;           (* Byte *)
  d_last_flush : Z;       (* int *)
  d_w_size : Z;           (* uInt *)
  d_w_bits : Z;           (* uInt *)
  d_w_mask : Z;           (* uInt *)
  d_window : mbuf;        (* Bytef[2 * w_size] *)
  d_window_size : Z;      (* ulg *)
  d_prev : list Z;        (* Pos[w_size] *)
  d_head : list Z;        (* Pos[hash_size] *)
  d_ins_h : Z;            (* uInt *)
  d_hash_size : Z;        (* uInt *)
  d_hash_bits : Z;        (* uInt *)
  d_hash_mask : Z;        (* uInt *)
  d_hash_shift : Z;       (* uInt *)
  d_block_start : Z;      (* long *)
  d_match_length : Z;     (* uInt *)
  d_prev_match : Z;       (* IPos = unsigned *)
  d_match_available : Z;  (* int *)
  d_strstart : Z;         (* uInt *)
  d_match_start : Z;      (* uInt *)
  d_lookahead : Z;        (* uInt *)
  d_prev_length : Z;      (* uInt *)
  d_max_chain_length : Z; (* uInt *)
  d_max_lazy_match : Z;   (* uInt *)
  d_good_match : Z;       (* uInt *)
  d_nice_match : Z;       (* int *)
  d_insert : Z;           (* uInt *)
  d_high_water : Z;       (* ulg *)
  d_slid : Z;             (* int *)
  d_pending_buf_size : Z; (* ulg *)
  d_tr : tstate;          (* trees.c's part, see Model.v *)
  d_pbm : list bool       (* the definedness mask of o_buf (tr_out d_tr) = pending_buf *)
}.

Record strm := mkST {
  z_in : list Z;          (* the input object of this call *)
  z_next_in : Z;          (* next_in - (start of z_in) *)
  z_avail_in : Z;         (* uInt *)
  z_total_in : Z;         (* uLong *)
  z_out : list Z;         (* bytes written to next_out since the start of the call *)
  z_avail_out : Z;        (* uInt *)
  z_total_out : Z;        (* uLong *)
  z_adler : Z;            (* uLong *)
  z_msg : option Z        (* None: Z_NULL; Some e: ERR_MSG(e) *)
}.

Definition set_d_status (s : dstate) (x : Z) : dstate := mkDS x (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_po (s : dstate) (x : Z) : dstate := mkDS (d_status s) x (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_wrap (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) x (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_gzhead (s : dstate) (x : option gzh) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) x (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_gzindex (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) x (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_method (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) x (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_last_flush (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) x (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_w_size (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) x (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_w_bits (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) x (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_w_mask (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) x (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_window (s : dstate) (x : mbuf) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) x (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_window_size (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) x (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_prev (s : dstate) (x : list Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) x (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_head (s : dstate) (x : list Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) x (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_ins_h (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) x (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_hash_size (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) x (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_hash_bits (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) x (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_hash_mask (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) x (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_hash_shift (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) x (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_block_start (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) x (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_match_length (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) x (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_prev_match (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) x (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_match_available (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) x (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_strstart (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) x (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_match_start (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) x (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_lookahead (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) x (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_prev_length (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) x (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_max_chain_length (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) x (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_max_lazy_match (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) x (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_good_match (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) x (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_nice_match (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) x (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_insert (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) x (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_high_water (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) x (d_slid s) (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_slid (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) x (d_pending_buf_size s) (d_tr s) (d_pbm s).
Definition set_d_pending_buf_size (s : dstate) (x : Z) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) x (d_tr s) (d_pbm s).
Definition set_d_tr (s : dstate) (x : tstate) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) x (d_pbm s).
Definition set_d_pbm (s : dstate) (x : list bool) : dstate := mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s) (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s) (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s) (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s) (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s) (d_tr s) x.

Definition set_z_in (s : strm) (x : list Z) : strm := mkST x (z_next_in s) (z_avail_in s) (z_total_in s) (z_out s) (z_avail_out s) (z_total_out s) (z_adler s) (z_msg s).
Definition set_z_next_in (s : strm) (x : Z) : strm := mkST (z_in s) x (z_avail_in s) (z_total_in s) (z_out s) (z_avail_out s) (z_total_out s) (z_adler s) (z_msg s).
Definition set_z_avail_in (s : strm) (x : Z) : strm := mkST (z_in s) (z_next_in s) x (z_total_in s) (z_out s) (z_avail_out s) (z_total_out s) (z_adler s) (z_msg s).
Definition set_z_total_in (s : strm) (x : Z) : strm := mkST (z_in s) (z_next_in s) (z_avail_in s) x (z_out s) (z_avail_out s) (z_total_out s) (z_adler s) (z_msg s).
Definition set_z_out (s : strm) (x : list Z) : strm := mkST (z_in s) (z_next_in s) (z_avail_in s) (z_total_in s) x (z_avail_out s) (z_total_out s) (z_adler s) (z_msg s).
Definition set_z_avail_out (s : strm) (x : Z) : strm := mkST (z_in s) (z_next_in s) (z_avail_in s) (z_total_in s) (z_out s) x (z_total_out s) (z_adler s) (z_msg s).
Definition set_z_total_out (s : strm) (x : Z) : strm := mkST (z_in s) (z_next_in s) (z_avail_in s) (z_total_in s) (z_out s) (z_avail_out s) x (z_adler s) (z_msg s).
Definition set_z_adler (s : strm) (x : Z) : strm := mkST (z_in s) (z_next_in s) (z_avail_in s) (z_total_in s) (z_out s) (z_avail_out s) (z_total_out s) x (z_msg s).
Definition set_z_msg (s : strm) (x : option Z) : strm := mkST (z_in s) (z_next_in s) (z_avail_in s) (z_total_in s) (z_out s) (z_avail_out s) (z_total_out s) (z_adler s) x.

(** The trees.c part with its mask, as the checked trees model (trees/CModel.v) takes it. *)
Definition d_trm (s : dstate) : tstate * list bool := (d_tr s, d_pbm s).
Definition set_d_trm (s : dstate) (x : tstate * list bool) : dstate := set_d_pbm (set_d_tr s (fst x)) (snd x).
Definition d_level (s : dstate) : Z := tr_level (d_tr s).
Definition d_strategy (s : dstate) : Z := tr_strategy (d_tr s).
Definition d_pending (s : dstate) : Z := o_pending (tr_out (d_tr s)).

(** Constants of deflate.h / zlib.h used by the model. *)
Definition INIT_STATE := 42.
Definition GZIP_STATE := 57.
Definition EXTRA_STATE := 69.
Definition NAME_STATE := 73.
Definition COMMENT_STATE := 91.
Definition HCRC_STATE := 103.
Definition BUSY_STATE := 113.
Definition FINISH_STATE := 666.
Definition Z_NO_FLUSH := 0.
Definition Z_PARTIAL_FLUSH := 1.
Definition Z_SYNC_FLUSH := 2.
Definition Z_FULL_FLUSH := 3.
Definition Z_FINISH := 4.
Definition Z_BLOCK := 5.
Definition Z_OK := 0.
Definition Z_STREAM_END := 1.
Definition Z_STREAM_ERROR := -2.
Definition Z_DATA_ERROR := -3.
Definition Z_MEM_ERROR := -4.
Definition Z_BUF_ERROR := -5.
Definition Z_VERSION_ERROR := -6.
Definition Z_FILTERED := 1.
Definition Z_HUFFMAN_ONLY := 2.
Definition Z_RLE := 3.
Definition Z_DEFAULT_STRATEGY := 0.
Definition Z_DEFLATED := 8.
Definition MAX_MATCH := 258.
Definition MIN_LOOKAHEAD := MAX_MATCH + MIN_MATCH + 1.
Definition WIN_INIT := MAX_MATCH.
Definition MAX_STORED := 65535.
Definition TOO_FAR := 4096.
Definition NIL := 0.
Definition PRESET_DICT := 32.
Definition OS_CODE := 3.
Definition MAX_DIST (s : dstate) : Z := d_w_size s - MIN_LOOKAHEAD.

(** block_state *)
Inductive bstate := need_more | block_done | finish_started | finish_done.

(** configuration_table: (good_length, max_lazy, nice_length, max_chain, func) with func 0 = deflate_stored,
    1 = deflate_fast, 2 = deflate_slow. *)
Definition config_table : list (Z * Z * Z * Z * Z) :=
  [(0, 0, 0, 0, 0); (4, 4, 8, 4, 1); (4, 5, 16, 8, 1); (4, 6, 32, 32, 1);
   (4, 4, 16, 16, 2); (8, 16, 32, 32, 2); (8, 16, 128, 128, 2); (8, 32, 128, 256, 2);
   (32, 128, 258, 1024, 2); (32, 258, 258, 4096, 2)].
