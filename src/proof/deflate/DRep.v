(** * The representation of a deflate stream in memory (field-wise), at the joint compspecs DCS.CS

    The model (DState.v): [s : dstate] (deflate_state, with the trees.c part [d_tr s] and the mask [d_pbm s]) and
    [z : strm] (the z_stream during one call).  The pointers are not in the model; they are the record [dptrs].

    Groups of fields of deflate_state (each function's specification mentions the groups it touches):
    - trees.c's part: [trees_at (d_trm s)] (TRep.v), which includes pending, pending_buf and its contents;
    - [win_at]: window (pointer and contents, 2 * w_size bytes, [mb_vals] of the masked buffer), window_size,
      w_size, w_bits, w_mask, high_water;
    - [hash_at]: prev, head (pointers and contents: w_size and hash_size unsigned shorts), ins_h, hash_size,
      hash_bits, hash_mask, hash_shift;
    - [match_at]: block_start, match_length, prev_match, match_available, strstart, match_start, lookahead,
      prev_length, insert, slid;
    - [cfg_at]: max_chain_length, max_lazy_match, good_match, nice_match;
    - [stat_at]: status, pending_buf_size, pending_out (= pending_buf + d_po), wrap, gzhead (the pointer: NULL
      when [d_gzhead s = None]), gzindex, method, last_flush.
    The z_stream: [strm_at] (all its fields but data_type, which is in [trees_at]), with the input object
    ([z_in z] at [p_in]: next_in = p_in + z_next_in) and the output space (next_out at the start of the call
    is [p_out]; the bytes [z_out z] written since, then [z_avail_out z] bytes not yet written, whose contents
    [rest] the caller chooses).

    [dstream_at] is the whole stream (all groups, the stream, the malloc tokens of deflate's five allocations);
    the user's gzip header ([gzh_at]) is separate: it belongs to the caller. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Export Zlib.proof.trees.TRep.
Require Export Zlib.proof.deflate.DState.
Require Import Zlib.deflate.code.

#[export] Existing Instance DCS.CS.

Definition t_gzh := Tstruct _gz_header_s noattr.

(** The pointers of a stream. *)
Record dptrs := mkDP {
  p_strm : val;     (* the z_stream *)
  p_s : val;        (* the deflate_state *)
  p_window : val;
  p_prev : val;
  p_head : val;
  p_pbuf : val;     (* pending_buf *)
  p_gzhead : val    (* the user's gz_header, or nullval *)
}.

Definition mb_vals (b : mbuf) : list val := pb_vals (mb_val b) (mb_def b).

Definition win_at (s : dstate) (p : dptrs) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _window) (p_window p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _window_size) (vl (d_window_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_mask) (vi (d_w_mask s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _high_water) (vl (d_high_water s)) (p_s p) *
  @data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p))%logic.

Definition hash_at (s : dstate) (p : dptrs) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _ins_h) (vi (d_ins_h s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _hash_bits) (vi (d_hash_bits s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _hash_mask) (vi (d_hash_mask s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _hash_shift) (vi (d_hash_shift s)) (p_s p) *
  @data_at DCS.CS Ews (tarray tushort (Zlength (d_prev s))) (map vi (d_prev s)) (p_prev p) *
  @data_at DCS.CS Ews (tarray tushort (Zlength (d_head s))) (map vi (d_head s)) (p_head p))%logic.

Definition match_at (s : dstate) (p : dptrs) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p))%logic.

Definition cfg_at (s : dstate) (p : dptrs) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _max_chain_length) (vi (d_max_chain_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _max_lazy_match) (vi (d_max_lazy_match s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _good_match) (vi (d_good_match s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _nice_match) (vi (d_nice_match s)) (p_s p))%logic.

Definition stat_at (s : dstate) (p : dptrs) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s) (p_pbuf p)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p))%logic.

(** The ranges of the C types of the fields (and sizes of the arrays); see also TRep.tree_ranges. *)
Definition u32_ok (x : Z) : Prop := 0 <= x <= Int.max_unsigned.
Definition u64_ok (x : Z) : Prop := 0 <= x <= Int64.max_unsigned.
Definition s32_ok (x : Z) : Prop := Int.min_signed <= x <= Int.max_signed.
Definition s64_ok (x : Z) : Prop := Int64.min_signed <= x <= Int64.max_signed.

Definition dstate_ranges (s : dstate) : Prop :=
  s32_ok (d_status s) /\ u64_ok (d_pending_buf_size s) /\ 0 <= d_po s /\ s32_ok (d_wrap s) /\
  u64_ok (d_gzindex s) /\ 0 <= d_method s < 256 /\ s32_ok (d_last_flush s) /\
  u32_ok (d_w_size s) /\ u32_ok (d_w_bits s) /\ u32_ok (d_w_mask s) /\ mb_ok (d_window s) /\
  Zlength (mb_val (d_window s)) <= Int.max_unsigned /\ u64_ok (d_window_size s) /\
  Forall (fun x => 0 <= x < 65536) (d_prev s) /\ Forall (fun x => 0 <= x < 65536) (d_head s) /\
  Zlength (d_prev s) <= Int.max_unsigned /\ Zlength (d_head s) <= Int.max_unsigned /\
  u32_ok (d_ins_h s) /\ u32_ok (d_hash_size s) /\ u32_ok (d_hash_bits s) /\ u32_ok (d_hash_mask s) /\
  u32_ok (d_hash_shift s) /\ s64_ok (d_block_start s) /\ u32_ok (d_match_length s) /\
  u32_ok (d_prev_match s) /\ s32_ok (d_match_available s) /\ u32_ok (d_strstart s) /\
  u32_ok (d_match_start s) /\ u32_ok (d_lookahead s) /\ u32_ok (d_prev_length s) /\
  u32_ok (d_max_chain_length s) /\ u32_ok (d_max_lazy_match s) /\ u32_ok (d_good_match s) /\
  s32_ok (d_nice_match s) /\ u32_ok (d_insert s) /\ u64_ok (d_high_water s) /\ s32_ok (d_slid s).

(** ** The z_stream *)

(** The output space of a call: [p_out] (next_out at the start of the call), the bytes written [z_out z], then
    [z_avail_out z] bytes [rest] not written by the call. *)
Definition out_space (z : strm) (p_out : val) (rest : list val) : mpred :=
  (!! (Zlength rest = z_avail_out z) &&
  @data_at DCS.CS Ews (tarray tuchar (Zlength (z_out z) + z_avail_out z)) (map vi (z_out z) ++ rest) p_out)%logic.

(** The input object: read-only for deflate (any readable share [ish]). *)
Definition in_obj (ish : share) (z : strm) (p_in : val) : mpred :=
  (@data_at DCS.CS ish (tarray tuchar (Zlength (z_in z))) (map vi (z_in z)) p_in)%logic.

(** strm->msg: Z_NULL or one of the messages of zutil.c's z_errmsg. *)
Definition msg_ok (m : option Z) (v : val) : Prop :=
  match m with None => v = nullval | Some _ => is_pointer_or_null v end.

Definition strm_at (z : strm) (sp : val) (p_strm p_in p_out : val) (msgv : val) (gv : globals) : mpred :=
  (@field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) p_in) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) p_out) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _total_out) (vl (z_total_out z)) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _msg) msgv p_strm *
  @field_at DCS.CS Ews t_strm (DOT _state) sp p_strm *
  @field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _opaque) nullval p_strm *
  @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) p_strm *
  @field_at_ DCS.CS Ews t_strm (DOT _reserved) p_strm)%logic.

(** The input side of the z_stream (v2): every field but next_out, avail_out, total_out.  read_buf and
    fill_window never touch the output, and deflateSetDictionary calls fill_window with next_out any value
    (Z_NULL in the harnesses).  [strm_at_split]: strm_at = strm_in_at * the three output fields. *)
Definition strm_in_at (z : strm) (sp : val) (p_strm p_in : val) (msgv : val) (gv : globals) : mpred :=
  (@field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) p_in) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _msg) msgv p_strm *
  @field_at DCS.CS Ews t_strm (DOT _state) sp p_strm *
  @field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _opaque) nullval p_strm *
  @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) p_strm *
  @field_at_ DCS.CS Ews t_strm (DOT _reserved) p_strm)%logic.

Definition strm_out_fields (z : strm) (p_strm p_out : val) : mpred :=
  (@field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) p_out) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) p_strm *
  @field_at DCS.CS Ews t_strm (DOT _total_out) (vl (z_total_out z)) p_strm)%logic.

Lemma strm_at_split z sp p_strm p_in p_out msgv gv :
  strm_at z sp p_strm p_in p_out msgv gv = (strm_in_at z sp p_strm p_in msgv gv * strm_out_fields z p_strm p_out)%logic.
Proof. unfold strm_at, strm_in_at, strm_out_fields. apply pred_ext; cancel. Qed.

Definition strm_ranges (z : strm) : Prop :=
  0 <= z_next_in z /\ 0 <= z_avail_in z /\ z_next_in z + z_avail_in z <= Zlength (z_in z) /\
  Zlength (z_in z) <= Int.max_unsigned /\ u32_ok (z_avail_in z) /\ u64_ok (z_total_in z) /\
  u32_ok (z_avail_out z) /\ Zlength (z_out z) + z_avail_out z <= Int.max_unsigned /\
  u64_ok (z_total_out z) /\ u64_ok (z_adler z) /\ Forall (fun b => 0 <= b < 256) (z_in z) /\
  Forall (fun b => 0 <= b < 256) (z_out z).

(** ** The user's gzip header (deflateSetHeader): the struct and the objects of extra, name, comment.
    [gzh_at sh h hp xp np cp]: the gz_header at [hp] with the fields of [h] (extra / name / comment pointers
    [xp], [np], [cp], NULL exactly when the field is [None]); the other fields of the struct any value. *)
Definition opt_obj (sh : share) (o : option (list Z)) (p : val) : mpred :=
  (match o with
  | None => !! (p = nullval) && emp
  | Some b => (* the contents are bytes (v6) *)
              !! Forall (fun x => 0 <= x < 256) b &&
              (@data_at DCS.CS sh (tarray tuchar (Zlength b)) (map vi b) p *
              (* an empty object (malloc(0)): its token makes the pointer valid for `p == Z_NULL` (v2) *)
              (if Zlength b =? 0 then @malloc_token DCS.CS Ews (tarray tuchar 0) p else emp))
  end)%logic.

Definition gzh_ok (h : gzh) : Prop :=
  Int.min_signed <= gz_text h <= Int.max_signed /\ 0 <= gz_time h <= Int64.max_unsigned /\
  Int.min_signed <= gz_os h <= Int.max_signed /\ 0 <= gz_extra_len h <= Int.max_unsigned /\
  Int.min_signed <= gz_hcrc h <= Int.max_signed.

Definition gzh_at (sh : share) (h : gzh) (hp xp np cp : val) : mpred :=
  (!! (readable_share sh /\ gzh_ok h) &&
  (@field_at DCS.CS sh t_gzh (DOT _text) (vi (gz_text h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _time) (vl (gz_time h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _os) (vi (gz_os h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _extra) xp hp *
  @field_at DCS.CS sh t_gzh (DOT _extra_len) (vi (gz_extra_len h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _name) np hp *
  @field_at DCS.CS sh t_gzh (DOT _comment) cp hp *
  @field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _xflags) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _extra_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _name_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _comm_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _done) v hp) *
  opt_obj sh (gz_extra h) xp * opt_obj sh (gz_name h) np * opt_obj sh (gz_comment h) cp))%logic.

(** ** Globals deflate.c reads: configuration_table (with its function pointers), zutil.c's z_errmsg, and
    trees.c's tables (TRep.trees_globals). *)
Definition errmsg_at (gv : globals) : mpred :=
  (EX vs : list val, !! (Zlength vs = 10 /\ Forall is_pointer_or_null vs) &&
  @data_at DCS.CS Ers (tarray (tptr tschar) 10) vs (gv _z_errmsg))%logic.

(** The malloc tokens of the five allocations of deflateInit2_ (zcalloc: Zutil Spec.v). *)
(** The padding of deflate_state at DCS.CS (v7: no field_at holds it; deflateInit2_ gets it from
    zalloc, deflateEnd gives it back to zfree): the gaps between the fields, size 5968. *)
Definition ds_pad (sp : val) : mpred :=
  (spacer Ews 12 16 sp * spacer Ews 52 56 sp * spacer Ews 73 76 sp * spacer Ews 92 96 sp *
   spacer Ews 148 152 sp * spacer Ews 5881 5888 sp * spacer Ews 5908 5912 sp * spacer Ews 5938 5940 sp *
   spacer Ews 5948 5952 sp * spacer Ews 5964 5968 sp)%logic.

Definition dtokens (s : dstate) (p : dptrs) : mpred :=
  (malloc_token Ews t_ds (p_s p) *
  malloc_token Ews (tarray tuchar (2 * d_w_size s)) (p_window p) *
  malloc_token Ews (tarray tushort (d_w_size s)) (p_prev p) *
  malloc_token Ews (tarray tushort (d_hash_size s)) (p_head p) *
  malloc_token Ews (tarray tuchar (4 * tr_lit_bufsize (d_tr s))) (p_pbuf p) *
  ds_pad (p_s p))%logic.

(** The whole deflate_state (all groups). *)
Definition dstate_at (s : dstate) (p : dptrs) (gv : globals) : mpred :=
  (!! dstate_ranges s &&
  (trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * win_at s p * hash_at s p * match_at s p *
   cfg_at s p * stat_at s p))%logic.
