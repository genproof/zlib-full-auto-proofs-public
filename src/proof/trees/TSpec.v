(** * THE specifications of trees.c's functions (one per function, shared by every law)

    Uniform shape: the representation of what the function touches (TRep.v), and the checked model
    (CModel.v) run [c_f args = Some r]; the postcondition is the representation of [r].  So a caller proves
    that the checked run succeeds (pure Coq), and the body proof follows the model one access at a time.
    Trees given by pointer ([ct_data *tree] arguments) are stand-alone arrays [tree_arr sh n t p]; when they are
    fields of deflate_state, callers turn [ltree_at]/[dtree_at]/[bltree_at] into [tree_arr] at the field's
    address (field_at_data_at).  A tree descriptor argument ([tree_desc *desc]) is [td_at] at the field's
    address.  The compspecs is DCS.CS (deflate.c and trees.c linked).

    Not specified (never called): _tr_tally (deflate.c uses the _tr_tally_* macros). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Export Zlib.proof.trees.TRep.
Require Export Zlib.proof.trees.CModel.
Require Import Zlib.proof.zutil.Libc.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Definition Vprog : varspecs. mk_varspecs Zlib.trees.code.prog. Defined.

(** ** Leaves *)

Definition tr_static_init_spec :=
 DECLARE _tr_static_init
 WITH u : unit
 PRE [ ] PROP () PARAMS () SEP ()
 POST [ tvoid ] PROP () RETURN () SEP ().

Definition bi_reverse_spec :=
 DECLARE _bi_reverse
 WITH code : Z, len : Z, r : Z
 PRE [ tuint, tint ]
  PROP (0 <= code <= Int.max_unsigned; Int.min_signed <= len <= Int.max_signed; c_bi_reverse code len = Some r)
  PARAMS (vi code; vi len)
  SEP ()
 POST [ tuint ]
  PROP () RETURN (vi r) SEP ().

Definition bi_flush_spec :=
 DECLARE _bi_flush
 WITH sp : val, pbp : val, o : outbuf, m : list bool, r : cout
 PRE [ tptr t_ds ]
  PROP (c_bi_flush (o, m) = Some r)
  PARAMS (sp)
  SEP (out_at o m sp pbp)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (out_at (fst r) (snd r) sp pbp).

Definition bi_windup_spec :=
 DECLARE _bi_windup
 WITH sp : val, pbp : val, o : outbuf, m : list bool, r : cout
 PRE [ tptr t_ds ]
  PROP (c_bi_windup (o, m) = Some r)
  PARAMS (sp)
  SEP (out_at o m sp pbp)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (out_at (fst r) (snd r) sp pbp).

Definition tr_flush_bits_spec :=
 DECLARE __tr_flush_bits
 WITH sp : val, pbp : val, o : outbuf, m : list bool, r : cout
 PRE [ tptr t_ds ]
  PROP (c_tr_flush_bits (o, m) = Some r)
  PARAMS (sp)
  SEP (out_at o m sp pbp)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (out_at (fst r) (snd r) sp pbp).

Definition tr_align_spec :=
 DECLARE __tr_align
 WITH sp : val, pbp : val, o : outbuf, m : list bool, r : cout, gv : globals
 PRE [ tptr t_ds ]
  PROP (c_tr_align (o, m) = Some r)
  PARAMS (sp) GLOBALS (gv)
  SEP (out_at o m sp pbp; static_trees gv)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (out_at (fst r) (snd r) sp pbp; static_trees gv).

(** [_tr_stored_block(s, buf, stored_len, last)]: [buf] holds the bytes [b] (v5: bytes in [0, 256)) (only read when [stored_len > 0];
    then [buf] points at an object holding [b], e.g. a slice of the window). *)
Definition buf_at (sh : share) (stored_len : Z) (b : list Z) (bufp : val) : mpred :=
  if stored_len =? 0 then emp
  else (!! (readable_share sh /\ Forall (fun x => 0 <= x < 256) b) &&
        @data_at DCS.CS sh (tarray tuchar (Zlength b)) (map vi b) bufp)%logic.

Definition tr_stored_block_spec :=
 DECLARE __tr_stored_block
 WITH sp : val, pbp : val, o : outbuf, m : list bool, bufp : val, bsh : share, b : list Z,
      stored_len : Z, last : Z, r : cout
 PRE [ tptr t_ds, tptr tschar, tulong, tint ]
  PROP (0 <= stored_len <= Int64.max_unsigned; Int.min_signed <= last <= Int.max_signed;
        c_tr_stored_block (o, m) b stored_len last = Some r)
  PARAMS (sp; bufp; vl stored_len; vi last)
  SEP (out_at o m sp pbp; buf_at bsh stored_len b bufp)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (out_at (fst r) (snd r) sp pbp; buf_at bsh stored_len b bufp).

(** ** Tree building *)

Definition gen_codes_spec :=
 DECLARE _gen_codes
 WITH tp : val, n : Z, t : tree, max_code : Z, bcp : val, blc : list Z, r : tree
 PRE [ tptr t_ct, tint, tptr tushort ]
  PROP (Int.min_signed <= max_code <= Int.max_signed; Zlength blc = 16;
        Forall (fun x => 0 <= x < 65536) blc; c_gen_codes t max_code blc = Some r)
  PARAMS (tp; vi max_code; bcp)
  SEP (tree_arr Ews n t tp; @data_at DCS.CS Ews (tarray tushort (16)) (map vi blc) bcp)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (tree_arr Ews n r tp; @data_at DCS.CS Ews (tarray tushort (16)) (map vi blc) bcp).

Definition pqdownheap_spec :=
 DECLARE _pqdownheap
 WITH sp : val, tp : val, tsh : share, n : Z, t : tree, w : work, k : Z, r : work
 PRE [ tptr t_ds, tptr t_ct, tint ]
  PROP (readable_share tsh; Int.min_signed <= k <= Int.max_signed; c_pqdownheap t w k = Some r)
  PARAMS (sp; tp; vi k)
  SEP (tree_arr tsh n t tp; work_at w sp)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (tree_arr tsh n t tp; work_at r sp).

(** [gen_bitlen(s, desc)] and [build_tree(s, desc)]: [desc] is the descriptor (at [dp], a field of the state)
    of the tree at [tp] ([n] entries) with the static descriptor [sd] at [statp]. *)
Definition gen_bitlen_spec :=
 DECLARE _gen_bitlen
 WITH sp : val, dp : val, tp : val, n : Z, t : tree, max_code : Z, statp : val, sd : stat_desc, w : work,
      r : tree * work, gv : globals
 PRE [ tptr t_ds, tptr t_td ]
  PROP (sdesc_ptr gv sd statp; c_gen_bitlen sd max_code t w = Some r)
  PARAMS (sp; dp) GLOBALS (gv)
  SEP (td_at Ews tp max_code statp dp; tree_arr Ews n t tp; work_at w sp; trees_globals gv)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (td_at Ews tp max_code statp dp; tree_arr Ews n (fst r) tp; work_at (snd r) sp; trees_globals gv).

Definition build_tree_spec :=
 DECLARE _build_tree
 WITH sp : val, dp : val, tp : val, n : Z, t : tree, max_code : Z, statp : val, sd : stat_desc, w : work,
      r : tree * Z * work, gv : globals
 PRE [ tptr t_ds, tptr t_td ]
  PROP (sdesc_ptr gv sd statp; c_build_tree sd t w = Some r)
  PARAMS (sp; dp) GLOBALS (gv)
  SEP (td_at Ews tp max_code statp dp; tree_arr Ews n t tp; work_at w sp; trees_globals gv)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (td_at Ews tp (snd (fst r)) statp dp; tree_arr Ews n (fst (fst r)) tp; work_at (snd r) sp;
       trees_globals gv).

Definition scan_tree_spec :=
 DECLARE _scan_tree
 WITH sp : val, tp : val, n : Z, t : tree, max_code : Z, bl : tree, r : tree * tree
 PRE [ tptr t_ds, tptr t_ct, tint ]
  PROP (Int.min_signed <= max_code <= Int.max_signed; c_scan_tree t max_code bl = Some r)
  PARAMS (sp; tp; vi max_code)
  SEP (tree_arr Ews n t tp; bltree_at bl sp)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (tree_arr Ews n (fst r) tp; bltree_at (snd r) sp).

(** [build_bl_tree(s)]: on the trees, descriptors and work area of the state; returns max_blindex. *)
Definition build_bl_tree_spec :=
 DECLARE _build_bl_tree
 WITH sp : val, ts : tstate, r : tstate * Z, gv : globals
 PRE [ tptr t_ds ]
  PROP (c_build_bl_tree ts = Some r)
  PARAMS (sp) GLOBALS (gv)
  SEP (ltree_at (tr_ltree ts) sp; dtree_at (tr_dtree ts) sp; bltree_at (tr_bltree ts) sp;
       ldesc_at (field_address t_ds (DOT _dyn_ltree) sp) (tr_lmax ts) (gv _static_l_desc) sp;
       ddesc_at (field_address t_ds (DOT _dyn_dtree) sp) (tr_dmax ts) (gv _static_d_desc) sp;
       bldesc_at (field_address t_ds (DOT _bl_tree) sp) (tr_blmax ts) (gv _static_bl_desc) sp;
       work_at (tr_wk ts) sp; trees_globals gv)
 POST [ tint ]
  PROP () RETURN (vi (snd r))
  SEP (ltree_at (tr_ltree (fst r)) sp; dtree_at (tr_dtree (fst r)) sp; bltree_at (tr_bltree (fst r)) sp;
       ldesc_at (field_address t_ds (DOT _dyn_ltree) sp) (tr_lmax (fst r)) (gv _static_l_desc) sp;
       ddesc_at (field_address t_ds (DOT _dyn_dtree) sp) (tr_dmax (fst r)) (gv _static_d_desc) sp;
       bldesc_at (field_address t_ds (DOT _bl_tree) sp) (tr_blmax (fst r)) (gv _static_bl_desc) sp;
       work_at (tr_wk (fst r)) sp; trees_globals gv).

Definition detect_data_type_spec :=
 DECLARE _detect_data_type
 WITH sp : val, lt : tree, r : Z
 PRE [ tptr t_ds ]
  PROP (c_detect_data_type (fc lt) = Some r)
  PARAMS (sp)
  SEP (ltree_at lt sp)
 POST [ tint ]
  PROP () RETURN (vi r)
  SEP (ltree_at lt sp).

Definition init_block_spec :=
 DECLARE _init_block
 WITH sp : val, pbp : val, ts : tstate, r : tstate
 PRE [ tptr t_ds ]
  PROP (c_init_block ts = Some r)
  PARAMS (sp)
  SEP (ltree_at (tr_ltree ts) sp; dtree_at (tr_dtree ts) sp; bltree_at (tr_bltree ts) sp;
       work_at (tr_wk ts) sp; sym_at ts sp pbp)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (ltree_at (tr_ltree r) sp; dtree_at (tr_dtree r) sp; bltree_at (tr_bltree r) sp;
       work_at (tr_wk r) sp; sym_at r sp pbp).

(** ** Output of trees and blocks *)

Definition send_tree_spec :=
 DECLARE _send_tree
 WITH sp : val, pbp : val, o : outbuf, m : list bool, tp : val, tsh : share, n : Z, t : tree,
      max_code : Z, bl : tree, r : cout
 PRE [ tptr t_ds, tptr t_ct, tint ]
  PROP (readable_share tsh; Int.min_signed <= max_code <= Int.max_signed;
        c_send_tree (o, m) t max_code bl = Some r)
  PARAMS (sp; tp; vi max_code)
  SEP (out_at o m sp pbp; tree_arr tsh n t tp; bltree_at bl sp)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (out_at (fst r) (snd r) sp pbp; tree_arr tsh n t tp; bltree_at bl sp).

Definition send_all_trees_spec :=
 DECLARE _send_all_trees
 WITH sp : val, pbp : val, o : outbuf, m : list bool, lt : tree, dt : tree, bl : tree,
      lcodes : Z, dcodes : Z, blcodes : Z, r : cout, gv : globals
 PRE [ tptr t_ds, tint, tint, tint ]
  PROP (Int.min_signed <= lcodes <= Int.max_signed; Int.min_signed <= dcodes <= Int.max_signed;
        Int.min_signed <= blcodes <= Int.max_signed;
        c_send_all_trees (o, m) lt dt bl lcodes dcodes blcodes = Some r)
  PARAMS (sp; vi lcodes; vi dcodes; vi blcodes) GLOBALS (gv)
  SEP (out_at o m sp pbp; ltree_at lt sp; dtree_at dt sp; bltree_at bl sp; trees_tables gv)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (out_at (fst r) (snd r) sp pbp; ltree_at lt sp; dtree_at dt sp; bltree_at bl sp; trees_tables gv).

(** [compress_block(s, ltree, dtree)]: the symbols are read from sym_buf = pending_buf + lit_bufsize (the
    overlay), so [out_at] covers them; [ltree] / [dtree] are the static trees or the state's dynamic trees. *)
Definition compress_block_spec :=
 DECLARE _compress_block
 WITH sp : val, pbp : val, o : outbuf, m : list bool, ts : tstate,
      ltp : val, lsh : share, ln : Z, lt : tree, dtp : val, dsh : share, dn : Z, dt : tree,
      r : cout, gv : globals
 PRE [ tptr t_ds, tptr t_ct, tptr t_ct ]
  PROP (readable_share lsh; readable_share dsh;
        c_compress_block (o, m) (tr_lit_bufsize ts) (tr_sym_next ts) (fc lt) (dl lt) (fc dt) (dl dt) = Some r)
  PARAMS (sp; ltp; dtp) GLOBALS (gv)
  SEP (out_at o m sp pbp; sym_at ts sp pbp; tree_arr lsh ln lt ltp; tree_arr dsh dn dt dtp; trees_tables gv)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (out_at (fst r) (snd r) sp pbp; sym_at ts sp pbp; tree_arr lsh ln lt ltp; tree_arr dsh dn dt dtp;
       trees_tables gv).

(** ** The entry points of trees.c *)

(** [_tr_init(s)]: sets the descriptors' dyn_tree and stat_desc (whatever they were: after deflateInit2_'s
    zmemzero, NULL) and initializes the bit buffer and the first block. *)
Definition tr_init_spec :=
 DECLARE __tr_init
 WITH sp : val, pbp : val, strmp : val, cs : cstate, r : cstate, lp0 : val, ls0 : val, dp0 : val, ds0 : val,
      bp0 : val, bs0 : val, gv : globals
 PRE [ tptr t_ds ]
  PROP (c_tr_init cs = Some r)
  PARAMS (sp) GLOBALS (gv)
  SEP (ltree_at (tr_ltree (fst cs)) sp; dtree_at (tr_dtree (fst cs)) sp; bltree_at (tr_bltree (fst cs)) sp;
       ldesc_at lp0 (tr_lmax (fst cs)) ls0 sp; ddesc_at dp0 (tr_dmax (fst cs)) ds0 sp;
       bldesc_at bp0 (tr_blmax (fst cs)) bs0 sp;
       work_at (tr_wk (fst cs)) sp; out_at (tr_out (fst cs)) (snd cs) sp pbp; sym_at (fst cs) sp pbp)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (ltree_at (tr_ltree (fst r)) sp; dtree_at (tr_dtree (fst r)) sp; bltree_at (tr_bltree (fst r)) sp;
       ldesc_at (field_address t_ds (DOT _dyn_ltree) sp) (tr_lmax (fst r)) (gv _static_l_desc) sp;
       ddesc_at (field_address t_ds (DOT _dyn_dtree) sp) (tr_dmax (fst r)) (gv _static_d_desc) sp;
       bldesc_at (field_address t_ds (DOT _bl_tree) sp) (tr_blmax (fst r)) (gv _static_bl_desc) sp;
       work_at (tr_wk (fst r)) sp; out_at (tr_out (fst r)) (snd r) sp pbp; sym_at (fst r) sp pbp).

(** [_tr_flush_block(s, buf, stored_len, last)]: [buf] is NULL ([bo = None]) or points at the [stored_len]
    window bytes of the block ([bo = Some b]). *)
Definition opt_buf_at (sh : share) (bo : option (list Z)) (bufp : val) : mpred :=
  match bo with
  | None => !! (bufp = nullval) && emp
  | Some b => !! (readable_share sh /\ Forall (fun x => 0 <= x < 256) b) &&
              @data_at DCS.CS sh (tarray tuchar (Zlength b)) (map vi b) bufp
  end%logic.

Definition tr_flush_block_spec :=
 DECLARE __tr_flush_block
 WITH sp : val, pbp : val, strmp : val, cs : cstate, bufp : val, bsh : share, bo : option (list Z),
      stored_len : Z, last : Z, r : cstate * block_kind, gv : globals
 PRE [ tptr t_ds, tptr tschar, tulong, tint ]
  PROP (0 <= stored_len <= Int64.max_unsigned; Int.min_signed <= last <= Int.max_signed;
        c_tr_flush_block cs bo stored_len last = Some r)
  PARAMS (sp; bufp; vl stored_len; vi last) GLOBALS (gv)
  SEP (trees_at cs sp pbp strmp gv; trees_globals gv; opt_buf_at bsh bo bufp)
 POST [ tvoid ]
  PROP () RETURN ()
  SEP (trees_at (fst r) sp pbp strmp gv; trees_globals gv; opt_buf_at bsh bo bufp).

(** ** The contexts of the body proofs: each function's callees (QuickProof.Assembly, entry_shared). *)
Definition Gprog_bi_reverse : funspecs := [].
Definition Gprog_bi_flush : funspecs := [].
Definition Gprog_bi_windup : funspecs := [].
Definition Gprog_tr_flush_bits : funspecs := [bi_flush_spec].
Definition Gprog_tr_align : funspecs := [bi_flush_spec].
Definition Gprog_tr_stored_block : funspecs := [bi_windup_spec; memcpy_spec].
Definition Gprog_gen_codes : funspecs := [bi_reverse_spec].
Definition Gprog_pqdownheap : funspecs := [].
Definition Gprog_gen_bitlen : funspecs := [].
Definition Gprog_build_tree : funspecs := [pqdownheap_spec; gen_bitlen_spec; gen_codes_spec].
Definition Gprog_scan_tree : funspecs := [].
Definition Gprog_build_bl_tree : funspecs := [scan_tree_spec; build_tree_spec].
Definition Gprog_detect_data_type : funspecs := [].
Definition Gprog_init_block : funspecs := [].
Definition Gprog_send_tree : funspecs := [].
Definition Gprog_send_all_trees : funspecs := [send_tree_spec].
Definition Gprog_compress_block : funspecs := [].
Definition Gprog_tr_static_init : funspecs := [].
Definition Gprog_tr_init : funspecs := [tr_static_init_spec; init_block_spec].
Definition Gprog_tr_flush_block : funspecs :=
  [detect_data_type_spec; build_tree_spec; build_bl_tree_spec; tr_stored_block_spec; compress_block_spec;
   send_all_trees_spec; init_block_spec; bi_windup_spec].
