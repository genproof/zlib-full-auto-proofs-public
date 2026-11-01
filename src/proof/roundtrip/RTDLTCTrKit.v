(** * TREES part of the core theory: the statements of the sub-parts of [trees_ok]

    RTDLTCTrees.v proves [trees_ok] from the theorems below (one file each):
    - [bt_some_statement] (RTDLTCTrBuild.v): the checked build_tree runs (Some) under [BtSpec.bt_req];
    - [prep_statement] (RTDLTCTrPrep.v, from [bt_some_statement]): the first part of _tr_flush_block (detect_data_type,
      the two build_tree calls, build_bl_tree) runs and gives the model's [flush_prep], with the sizes / ranges of
      the trees afterwards;
    - [comp_statement] (RTDLTCTrComp.v): compress_block runs over the overlaid buffer under [overlay_ok];
    - [send_statement] (RTDLTCTrSend.v): send_all_trees runs when its writes stay inside pending_buf;
    - [stored_statement] (RTDLTCTrStored.v): _tr_stored_block runs when the block fits;
    - [bytes_statement] (RTDLTCTrBytes.v): _tr_flush_block writes only bytes, only in [pending, pending');
    - [tally_statement] (RTDLTCTrTally.v): the _tr_tally macros (RTDLTCSpecs.tally_spec with lit_bufsize <= 2^15).
    Each is a closed theorem; the model-level facts come from src/proof/huffman (dyn_prep, dyn_sum, overlay). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCLib.
Require Export Zlib.proof.trees.CEquiv.
Require Export Zlib.proof.huffman.BtSpec.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The first part of c_tr_flush_block (the trees, opt_lenb, static_lenb, max_blindex) *)
Definition c_flush_prep (s : tstate) (stored_len : Z) : option (tstate * Z * Z * Z) :=
  if tr_level s >? 0 then
    let* s := (if tr_data_type s =? Z_UNKNOWN then
                 let* dt := c_detect_data_type (fc (tr_ltree s)) in Some (set_data_type s dt)
               else Some s) in
    let* (lt, lmax, w) := c_build_tree static_l_desc (tr_ltree s) (tr_wk s) in
    let s := set_wk (set_lmax (set_ltree s lt) lmax) w in
    let* (dt, dmax, w) := c_build_tree static_d_desc (tr_dtree s) (tr_wk s) in
    let s := set_wk (set_dmax (set_dtree s dt) dmax) w in
    let* (s, max_blindex) := c_build_bl_tree s in
    let opt_lenb := Z.shiftr (u64 (w_opt_len (tr_wk s) + 3 + 7)) 3 in
    let static_lenb := Z.shiftr (u64 (w_static_len (tr_wk s) + 3 + 7)) 3 in
    let opt_lenb := if (static_lenb <=? opt_lenb) || (tr_strategy s =? Z_FIXED) then static_lenb else opt_lenb in
    Some (s, opt_lenb, static_lenb, max_blindex)
  else Some (s, u64 (stored_len + 5), u64 (stored_len + 5), 0).

(** ** build_tree (part BUILD) *)
Definition bt_some_statement : Prop :=
  forall sd t w,
    (sd = static_l_desc \/ sd = static_d_desc \/ sd = static_bl_desc) ->
    bt_req sd t w ->
    c_build_tree sd t w = Some (build_tree sd t w).

(** ** The trees part of _tr_flush_block (part PREP) *)
Definition prep_statement : Prop :=
  forall s syms stored_len,
    flush_pre s syms -> 0 < tr_level s ->
    c_flush_prep s stored_len = Some (flush_prep s stored_len) /\
    let s' := fst (fst (fst (flush_prep s stored_len))) in
    tr_cfg s' = tr_cfg s /\ tr_out s' = tr_out s /\ tr_sym_next s' = tr_sym_next s /\
    tr_matches s' = tr_matches s /\
    Zlength (fc (tr_ltree s')) = HEAP_SIZE /\ Zlength (dl (tr_ltree s')) = HEAP_SIZE /\
    (forall n, 0 <= n < HEAP_SIZE -> 0 <= Znth n (fc (tr_ltree s')) < 65536) /\
    Zlength (fc (tr_dtree s')) = 2 * D_CODES + 1 /\ Zlength (dl (tr_dtree s')) = 2 * D_CODES + 1 /\
    (forall n, 0 <= n < 2 * D_CODES + 1 -> 0 <= Znth n (fc (tr_dtree s')) < 65536) /\
    Zlength (fc (tr_bltree s')) = 2 * BL_CODES + 1 /\ Zlength (dl (tr_bltree s')) = 2 * BL_CODES + 1 /\
    (forall n, 0 <= n < 2 * BL_CODES + 1 -> 0 <= Znth n (fc (tr_bltree s')) < 65536) /\
    Zlength (w_heap (tr_wk s')) = HEAP_SIZE /\ Zlength (w_depth (tr_wk s')) = HEAP_SIZE /\
    Zlength (w_bl_count (tr_wk s')) = MAX_BITS + 1.

(** ** compress_block over the overlaid buffer (part COMP) *)
Definition comp_statement : Prop :=
  forall L syms o m lcodes llens dcodes dlens,
    (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
    overlay_ok L syms (o, lcodes, llens, dcodes, dlens) ->
    Zlength syms <= L - 1 -> Zlength m = 4 * L ->
    (forall i, 0 <= i < 3 * Zlength syms -> Znth (L + i) m = true) ->
    L_CODES <= Zlength lcodes -> L_CODES <= Zlength llens ->
    D_CODES <= Zlength dcodes -> D_CODES <= Zlength dlens ->
    exists m',
      c_compress_block (o, m) L (3 * Zlength syms) lcodes llens dcodes dlens =
        Some (compress_block o L (3 * Zlength syms) lcodes llens dcodes dlens, m').

(** ** send_all_trees (part SEND) *)
Definition send_statement : Prop :=
  forall o m lt dt bl lcodes dcodes blcodes,
    bits_ok o -> Zlength m = Zlength (o_buf o) ->
    1 <= lcodes <= L_CODES -> 1 <= dcodes <= D_CODES -> 0 <= blcodes <= BL_CODES ->
    lcodes < Zlength (dl lt) -> dcodes < Zlength (dl dt) ->
    (forall i, 0 <= i < lcodes -> 0 <= Znth i (dl lt) <= 15) ->
    (forall i, 0 <= i < dcodes -> 0 <= Znth i (dl dt) <= 15) ->
    Zlength (fc bl) = 2 * BL_CODES + 1 -> Zlength (dl bl) = 2 * BL_CODES + 1 ->
    (forall i, 0 <= i < BL_CODES -> 0 <= Znth i (dl bl) <= 7) ->
    o_pending (send_all_trees o lt dt bl lcodes dcodes blcodes) <= Zlength (o_buf o) ->
    exists m',
      c_send_all_trees (o, m) lt dt bl lcodes dcodes blcodes =
        Some (send_all_trees o lt dt bl lcodes dcodes blcodes, m').

(** ** _tr_stored_block (part STORED) *)
Definition stored_statement : Prop :=
  forall o m b sl last,
    bits_ok o -> Zlength m = Zlength (o_buf o) -> 0 <= last <= 1 ->
    0 <= sl <= Zlength b ->
    o_pending o + (o_bi_valid o + 3 + 7) / 8 + 4 + sl <= Zlength (o_buf o) ->
    exists m', c_tr_stored_block (o, m) b sl last = Some (tr_stored_block o b sl last, m').

(** ** What _tr_flush_block writes into pending_buf (part BYTES) *)
Definition bytes_statement : Prop :=
  forall s m buf sl last s' m' k,
    c_tr_flush_block (s, m) buf sl last = Some ((s', m'), k) ->
    (forall b, buf = Some b -> bytes b) ->
    Zlength (o_buf (tr_out s')) = Zlength (o_buf (tr_out s)) /\
    (forall i, i < o_pending (tr_out s) \/ o_pending (tr_out s') <= i ->
       Znth i (o_buf (tr_out s')) = Znth i (o_buf (tr_out s))) /\
    (forall i, o_pending (tr_out s) <= i < o_pending (tr_out s') ->
       0 <= Znth i (o_buf (tr_out s')) < 256).

(** ** The _tr_tally macros (part TALLY): RTDLTCSpecs.tally_spec with lit_bufsize <= 2^15 (the u16 counters) *)
Definition tally_statement : Prop :=
  (forall t m syms c,
     tree_ok t m syms -> Zlength syms <= tr_lit_bufsize t - 2 -> tr_lit_bufsize t <= 32768 -> 0 <= c < 256 ->
     exists t' m',
       c_tr_tally_lit (t, m) c = Some ((t', m'), 3 * Zlength syms + 3 =? tr_sym_end t) /\
       tree_ok t' m' (syms ++ [(0, c)]) /\ tally_frame t m t' m') /\
  (forall t m syms dist len,
     tree_ok t m syms -> Zlength syms <= tr_lit_bufsize t - 2 -> tr_lit_bufsize t <= 32768 ->
     1 <= dist <= 32768 -> 0 <= len <= 255 ->
     exists t' m',
       c_tr_tally_dist (t, m) dist len = Some ((t', m'), 3 * Zlength syms + 3 =? tr_sym_end t) /\
       tree_ok t' m' (syms ++ [(dist, len)]) /\ tally_frame t m t' m').

(** c_tr_flush_block through [c_flush_prep] (definitional). *)
Lemma c_tr_flush_block_prep : forall s m buf stored_len last,
  c_tr_flush_block (s, m) buf stored_len last =
  let* (s, opt_lenb, static_lenb, max_blindex) := c_flush_prep s stored_len in
  let* (om, kind) :=
    (match buf with
     | Some b =>
       if u64 (stored_len + 4) <=? opt_lenb then
         let* _ := guard (0 <? Zlength b) in
         let* om := c_tr_stored_block (tr_out s, m) b stored_len last in Some (om, BK_stored)
       else if static_lenb =? opt_lenb then
         let* _ := guard (last <=? 2147483645) in
         let* om := c_send_bits (tr_out s, m) (Z.shiftl STATIC_TREES 1 + last) 3 in
         let* om := c_compress_block om (tr_lit_bufsize s) (tr_sym_next s)
                      static_ltree_code static_ltree_len static_dtree_code static_dtree_len in
         Some (om, BK_static)
       else
         let* _ := guard (last <=? 2147483643) in
         let* om := c_send_bits (tr_out s, m) (Z.shiftl DYN_TREES 1 + last) 3 in
         let* om := c_send_all_trees om (tr_ltree s) (tr_dtree s) (tr_bltree s)
                      (tr_lmax s + 1) (tr_dmax s + 1) (max_blindex + 1) in
         let* om := c_compress_block om (tr_lit_bufsize s) (tr_sym_next s)
                      (fc (tr_ltree s)) (dl (tr_ltree s)) (fc (tr_dtree s)) (dl (tr_dtree s)) in
         Some (om, BK_dynamic)
     | None =>
       if static_lenb =? opt_lenb then
         let* _ := guard (last <=? 2147483645) in
         let* om := c_send_bits (tr_out s, m) (Z.shiftl STATIC_TREES 1 + last) 3 in
         let* om := c_compress_block om (tr_lit_bufsize s) (tr_sym_next s)
                      static_ltree_code static_ltree_len static_dtree_code static_dtree_len in
         Some (om, BK_static)
       else
         let* _ := guard (last <=? 2147483643) in
         let* om := c_send_bits (tr_out s, m) (Z.shiftl DYN_TREES 1 + last) 3 in
         let* om := c_send_all_trees om (tr_ltree s) (tr_dtree s) (tr_bltree s)
                      (tr_lmax s + 1) (tr_dmax s + 1) (max_blindex + 1) in
         let* om := c_compress_block om (tr_lit_bufsize s) (tr_sym_next s)
                      (fc (tr_ltree s)) (dl (tr_ltree s)) (fc (tr_dtree s)) (dl (tr_dtree s)) in
         Some (om, BK_dynamic)
     end) in
  let '(o, m) := om in
  let* s := c_init_block (set_out s o) in
  let* (s, m) := (if negb (last =? 0) then
                     let* (o, m) := c_bi_windup (tr_out s, m) in Some (set_out s o, m)
                   else Some (s, m)) in
  Some ((s, m), kind).
Proof. reflexivity. Qed.
