(** * The representation of trees.c's state in memory (field-wise), at the joint compspecs DCS.CS

    The trees.c part of deflate_state is the huffman model's [tstate] (Model.v) together with the definedness
    mask of pending_buf (CBase.v, CModel.v: [cstate = tstate * list bool]).  Its representation is a set of
    [field_at]s of deflate_state, one group per kind of field, so that each function's specification mentions
    only the groups it touches (whole-struct [data_at]s make VST's forward steps very slow):

    - [ltree_at], [dtree_at], [bltree_at]: dyn_ltree (573 entries), dyn_dtree (61), bl_tree (39), each in the
      canonical presentation [ct_canon] (both unions in their first member, Freq and Dad; Ct.v: data_at does not
      depend on the member, so proofs switch members freely);
    - [ldesc_at], [ddesc_at], [bldesc_at] (and [td_at] for a descriptor as a stand-alone struct): l_desc / d_desc / bl_desc (dyn_tree pointer, max_code, stat_desc pointer);
    - [work_at]: heap, heap_len, heap_max, depth, bl_count, opt_len, static_len;
    - [out_at]: pending, pending_buf (the pointer), bi_buf, bi_valid, bi_used, and the contents of pending_buf
      ([pb_vals]: the byte where the mask is true, Vundef elsewhere);
    - [sym_at]: sym_buf (= pending_buf + lit_bufsize), lit_bufsize, sym_next, sym_end, matches;
    - [lvl_at]: level, strategy; [dtype_at]: strm->data_type and the strm pointer field.

    [trees_at] is all of them for a [cstate].  [trees_globals] = [static_trees] * [trees_tables]: trees.c's
    read-only data. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Export Zlib.proof.deflate.Rep.
Require Export Zlib.proof.trees.Ct.
Require Export Zlib.proof.huffman.Model.
Require Export Zlib.proof.trees.CBase.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Definition t_sd := Tstruct _static_tree_desc_s noattr.

(** ** Trees.  Every predicate carries the ranges of its C types ([!! ...]), so that a postcondition that
    gives the predicate also gives the ranges. *)
Definition ct_canon (t : tree) : list (reptype t_ct) := ct_arr ffalse ffalse t.

Definition ltree_at (t : tree) (sp : val) : mpred :=
  (!! tree_ok t HEAP_SIZE && @field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon t) sp)%logic.
Definition dtree_at (t : tree) (sp : val) : mpred :=
  (!! tree_ok t (2 * D_CODES + 1) && @field_at DCS.CS Ews t_ds (DOT _dyn_dtree) (ct_canon t) sp)%logic.
Definition bltree_at (t : tree) (sp : val) : mpred :=
  (!! tree_ok t (2 * BL_CODES + 1) && @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_canon t) sp)%logic.

(** A tree as a stand-alone array of [n] entries (the tree argument of pqdownheap, gen_codes, scan_tree,
    send_tree, compress_block, gen_bitlen; a tree of the state is turned into one with field_at_data_at). *)
Definition tree_arr (sh : share) (n : Z) (t : tree) (p : val) : mpred :=
  (!! tree_ok t n && @data_at DCS.CS sh (tarray t_ct n) (ct_canon t) p)%logic.

(** ** Tree descriptors *)
Definition td_at (sh : share) (treep : val) (maxc : Z) (statp : val) (dp : val) : mpred :=
  (!! (Int.min_signed <= maxc <= Int.max_signed) &&
   @data_at DCS.CS sh t_td (td_val (mkTD treep maxc statp)) dp)%logic.
Definition ldesc_at (treep : val) (maxc : Z) (statp : val) (sp : val) : mpred :=
  (!! (Int.min_signed <= maxc <= Int.max_signed) &&
   @field_at DCS.CS Ews t_ds (DOT _l_desc) (td_val (mkTD treep maxc statp)) sp)%logic.
Definition ddesc_at (treep : val) (maxc : Z) (statp : val) (sp : val) : mpred :=
  (!! (Int.min_signed <= maxc <= Int.max_signed) &&
   @field_at DCS.CS Ews t_ds (DOT _d_desc) (td_val (mkTD treep maxc statp)) sp)%logic.
Definition bldesc_at (treep : val) (maxc : Z) (statp : val) (sp : val) : mpred :=
  (!! (Int.min_signed <= maxc <= Int.max_signed) &&
   @field_at DCS.CS Ews t_ds (DOT _bl_desc) (td_val (mkTD treep maxc statp)) sp)%logic.

(** ** The work area *)
Definition work_ok (w : work) : Prop :=
  Zlength (w_heap w) = 2 * L_CODES + 1 /\ Zlength (w_depth w) = 2 * L_CODES + 1 /\
  Zlength (w_bl_count w) = MAX_BITS + 1 /\
  Forall (fun x => Int.min_signed <= x <= Int.max_signed) (w_heap w) /\
  Int.min_signed <= w_heap_len w <= Int.max_signed /\ Int.min_signed <= w_heap_max w <= Int.max_signed /\
  Forall (fun x => 0 <= x < 256) (w_depth w) /\ Forall (fun x => 0 <= x < 65536) (w_bl_count w) /\
  0 <= w_opt_len w <= Int64.max_unsigned /\ 0 <= w_static_len w <= Int64.max_unsigned.

Definition work_at (w : work) (sp : val) : mpred :=
  (!! work_ok w &&
  (@field_at DCS.CS Ews t_ds (DOT _heap) (map vi (w_heap w)) sp *
   @field_at DCS.CS Ews t_ds (DOT _heap_len) (vi (w_heap_len w)) sp *
   @field_at DCS.CS Ews t_ds (DOT _heap_max) (vi (w_heap_max w)) sp *
   @field_at DCS.CS Ews t_ds (DOT _depth) (map vi (w_depth w)) sp *
   @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi (w_bl_count w)) sp *
   @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl (w_opt_len w)) sp *
   @field_at DCS.CS Ews t_ds (DOT _static_len) (vl (w_static_len w)) sp))%logic.

(** ** Bit output and pending_buf *)
Definition pb_vals (b : list Z) (m : list bool) : list val :=
  map (fun x : Z * bool => if snd x then vi (fst x) else Vundef) (combine b m).

(** The ranges of the C types (and the mask's length); bytes where the mask is true are bytes. *)
Definition out_ok (o : outbuf) (m : list bool) : Prop :=
  mb_ok (mkMB (o_buf o) m) /\ 0 <= Zlength (o_buf o) <= Int.max_unsigned /\
  0 <= o_pending o <= Int64.max_unsigned /\ 0 <= o_bi_buf o < 65536 /\
  Int.min_signed <= o_bi_valid o <= Int.max_signed /\ Int.min_signed <= o_bi_used o <= Int.max_signed.

Definition out_at (o : outbuf) (m : list bool) (sp pbp : val) : mpred :=
  (!! out_ok o m &&
  (@field_at DCS.CS Ews t_ds (DOT _pending) (vl (o_pending o)) sp *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf) pbp sp *
   @field_at DCS.CS Ews t_ds (DOT _bi_buf) (vi (o_bi_buf o)) sp *
   @field_at DCS.CS Ews t_ds (DOT _bi_valid) (vi (o_bi_valid o)) sp *
   @field_at DCS.CS Ews t_ds (DOT _bi_used) (vi (o_bi_used o)) sp *
   @data_at DCS.CS Ews (tarray tuchar (Zlength (o_buf o))) (pb_vals (o_buf o) m) pbp))%logic.

(** ** Symbols, level, data_type *)
Definition sym_at (s : tstate) (sp pbp : val) : mpred :=
  (!! (0 <= tr_sym_next s <= Int.max_unsigned /\ 0 <= tr_sym_end s <= Int.max_unsigned /\
       0 <= tr_matches s <= Int.max_unsigned /\ 0 <= tr_lit_bufsize s <= Int.max_unsigned) &&
  (@field_at DCS.CS Ews t_ds (DOT _sym_buf) (offset_val (tr_lit_bufsize s) pbp) sp *
   @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) (vi (tr_lit_bufsize s)) sp *
   @field_at DCS.CS Ews t_ds (DOT _sym_next) (vi (tr_sym_next s)) sp *
   @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi (tr_sym_end s)) sp *
   @field_at DCS.CS Ews t_ds (DOT _matches) (vi (tr_matches s)) sp))%logic.

Definition lvl_at (s : tstate) (sp : val) : mpred :=
  (!! (Int.min_signed <= tr_level s <= Int.max_signed /\ Int.min_signed <= tr_strategy s <= Int.max_signed) &&
  (@field_at DCS.CS Ews t_ds (DOT _level) (vi (tr_level s)) sp *
   @field_at DCS.CS Ews t_ds (DOT _strategy) (vi (tr_strategy s)) sp))%logic.

Definition dtype_at (s : tstate) (sp strmp : val) : mpred :=
  (!! (Int.min_signed <= tr_data_type s <= Int.max_signed) &&
  (@field_at DCS.CS Ews t_ds (DOT _strm) strmp sp *
   @field_at DCS.CS Ews t_strm (DOT _data_type) (vi (tr_data_type s)) strmp))%logic.

(** ** The whole trees.c part of deflate_state, for a [cstate] (the tstate and the pending_buf mask). *)
Definition trees_at (cs : tstate * list bool) (sp pbp strmp : val) (gv : globals) : mpred :=
  (ltree_at (tr_ltree (fst cs)) sp * dtree_at (tr_dtree (fst cs)) sp * bltree_at (tr_bltree (fst cs)) sp *
   ldesc_at (field_address t_ds (DOT _dyn_ltree) sp) (tr_lmax (fst cs)) (gv _static_l_desc) sp *
   ddesc_at (field_address t_ds (DOT _dyn_dtree) sp) (tr_dmax (fst cs)) (gv _static_d_desc) sp *
   bldesc_at (field_address t_ds (DOT _bl_tree) sp) (tr_blmax (fst cs)) (gv _static_bl_desc) sp *
   work_at (tr_wk (fst cs)) sp * out_at (tr_out (fst cs)) (snd cs) sp pbp * sym_at (fst cs) sp pbp *
   lvl_at (fst cs) sp * dtype_at (fst cs) sp strmp)%logic.

(** ** trees.c's read-only data: the static trees and the tables *)
Definition static_ltree_t : tree := mkTree static_ltree_code static_ltree_len.
Definition static_dtree_t : tree := mkTree static_dtree_code static_dtree_len.

Definition static_trees (gv : globals) : mpred :=
  (tree_arr Ers (L_CODES + 2) static_ltree_t (gv _static_ltree) *
   tree_arr Ers D_CODES static_dtree_t (gv _static_dtree))%logic.

Definition trees_tables (gv : globals) : mpred :=
  (@data_at DCS.CS Ers (tarray tuchar 512) (map vi dist_code_tab) (gv __dist_code) *
   @data_at DCS.CS Ers (tarray tuchar 256) (map vi length_code_tab) (gv __length_code) *
   @data_at DCS.CS Ers (tarray tint 29) (map vi base_length_tab) (gv _base_length) *
   @data_at DCS.CS Ers (tarray tint 30) (map vi base_dist_tab) (gv _base_dist) *
   @data_at DCS.CS Ers (tarray tint 29) (map vi extra_lbits) (gv _extra_lbits) *
   @data_at DCS.CS Ers (tarray tint 30) (map vi extra_dbits) (gv _extra_dbits) *
   @data_at DCS.CS Ers (tarray tint 19) (map vi extra_blbits) (gv _extra_blbits) *
   @data_at DCS.CS Ers (tarray tuchar 19) (map vi bl_order) (gv _bl_order) *
   @data_at DCS.CS Ers t_sd (gv _static_ltree, (gv _extra_lbits, (vi 257, (vi 286, vi 15)))) (gv _static_l_desc) *
   @data_at DCS.CS Ers t_sd (gv _static_dtree, (gv _extra_dbits, (vi 0, (vi 30, vi 15)))) (gv _static_d_desc) *
   @data_at DCS.CS Ers t_sd (nullval, (gv _extra_blbits, (vi 0, (vi 19, vi 7)))) (gv _static_bl_desc))%logic.

Definition trees_globals (gv : globals) : mpred := (static_trees gv * trees_tables gv)%logic.

(** The static descriptor of the model and its address. *)
Definition sdesc_ptr (gv : globals) (sd : stat_desc) (p : val) : Prop :=
  (sd = static_l_desc /\ p = gv _static_l_desc) \/ (sd = static_d_desc /\ p = gv _static_d_desc) \/
  (sd = static_bl_desc /\ p = gv _static_bl_desc).
