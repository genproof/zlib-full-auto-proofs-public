(** * A functional model of trees.c (block coding), faithful to the C

    Every function below transcribes one function (or macro) of trees.c, statement by statement, in the
    configuration of this project (no LIT_MEM, no ZLIB_DEBUG, static tables from trees.h).  Arrays are lists of
    [Z] accessed with VST's [Znth]/[upd_Znth] (from the pure list library [VST.zlist.sublist]; nothing here uses
    the program logic).  Every store into a narrow C object is truncated as the C store truncates it: [ush] fields
    modulo 2^16 ([u16]), [uch] modulo 2^8 ([u8]), [ulg] (64-bit unsigned long) modulo 2^64 ([u64]).
    The loops are fuel-indexed; each fuel constant is larger than the number of iterations the C loop can run on
    the states it is called on.

    The union members of [ct_data] are both kept in one field each: [fc] (Freq / Code) and [dl] (Dad / Len).

    Correspondence with deflate_state:
    - [tr_ltree]/[tr_dtree]/[tr_bltree]: dyn_ltree (HEAP_SIZE entries), dyn_dtree (2*D_CODES+1), bl_tree
      (2*BL_CODES+1);
    - [tr_lmax]/[tr_dmax]/[tr_blmax]: l_desc.max_code, d_desc.max_code, bl_desc.max_code;
    - [tr_wk]: heap, heap_len, heap_max, depth, bl_count, opt_len, static_len;
    - [tr_out]: pending_buf (its whole [pending_buf_size] = 4 * lit_bufsize bytes), pending, bi_buf, bi_valid,
      bi_used.  sym_buf is [pending_buf + lit_bufsize] (no LIT_MEM): the symbols are read from [tr_out]'s buffer
      at offset [tr_lit_bufsize], as compress_block reads them, so the overlay is part of the model;
    - [tr_sym_next], [tr_sym_end], [tr_matches], [tr_lit_bufsize], [tr_level], [tr_strategy], and [tr_data_type]
      (= strm->data_type). *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.huffman.Tables.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Constants (deflate.h, trees.c, zlib.h) *)

Definition LENGTH_CODES := 29.
Definition LITERALS := 256.
Definition L_CODES := 286.
Definition D_CODES := 30.
Definition BL_CODES := 19.
Definition HEAP_SIZE := 573.
Definition MAX_BITS := 15.
Definition MAX_BL_BITS := 7.
Definition END_BLOCK := 256.
Definition REP_3_6 := 16.
Definition REPZ_3_10 := 17.
Definition REPZ_11_138 := 18.
Definition Buf_size := 16.
Definition SMALLEST := 1.
Definition MIN_MATCH := 3.
Definition STORED_BLOCK := 0.
Definition STATIC_TREES := 1.
Definition DYN_TREES := 2.
Definition Z_FIXED := 4.
Definition Z_BINARY := 0.
Definition Z_TEXT := 1.
Definition Z_UNKNOWN := 2.

Definition extra_lbits : list Z :=
  [0;0;0;0;0;0;0;0;1;1;1;1;2;2;2;2;3;3;3;3;4;4;4;4;5;5;5;5;0].
Definition extra_dbits : list Z :=
  [0;0;0;0;1;1;2;2;3;3;4;4;5;5;6;6;7;7;8;8;9;9;10;10;11;11;12;12;13;13].
Definition extra_blbits : list Z :=
  [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;2;3;7].
Definition bl_order : list Z :=
  [16;17;18;0;8;7;9;6;10;5;11;4;12;3;13;2;14;1;15].

(** Truncations of the C stores. *)
Definition u8 (x : Z) : Z := x mod 256.
Definition u16 (x : Z) : Z := x mod 65536.
Definition u32 (x : Z) : Z := x mod 4294967296.
Definition u64 (x : Z) : Z := x mod 18446744073709551616.

(** [d_code] (deflate.h): [dist] is the match distance minus one. *)
Definition d_code (dist : Z) : Z :=
  if dist <? 256 then Znth dist dist_code_tab else Znth (256 + Z.shiftr dist 7) dist_code_tab.

(** ** Trees and the static tree descriptors *)

(** One [ct_data] array: [fc] holds the [fc] union (Freq or Code), [dl] the [dl] union (Dad or Len). *)
Record tree := mkTree { fc : list Z; dl : list Z }.

Definition set_fc (t : tree) (i v : Z) : tree := mkTree (upd_Znth i (fc t) v) (dl t).
Definition set_dl (t : tree) (i v : Z) : tree := mkTree (fc t) (upd_Znth i (dl t) v).

(** [static_tree_desc]: [sd_stree] is [None] for the bit length tree (static_tree == NULL), else the lengths of
    the static tree (only its [Len] fields are read by trees.c's tree building). *)
Record stat_desc := mkSD {
  sd_stree : option (list Z);
  sd_extra : list Z;
  sd_base : Z;
  sd_elems : Z;
  sd_maxlen : Z
}.

Definition static_l_desc := mkSD (Some static_ltree_len) extra_lbits (LITERALS + 1) L_CODES MAX_BITS.
Definition static_d_desc := mkSD (Some static_dtree_len) extra_dbits 0 D_CODES MAX_BITS.
Definition static_bl_desc := mkSD None extra_blbits 0 BL_CODES MAX_BL_BITS.

(** ** The tree-building work area of deflate_state *)

Record work := mkWork {
  w_heap : list Z;       (* int heap[2*L_CODES+1] *)
  w_heap_len : Z;
  w_heap_max : Z;
  w_depth : list Z;      (* uch depth[2*L_CODES+1] *)
  w_bl_count : list Z;   (* ush bl_count[MAX_BITS+1] *)
  w_opt_len : Z;         (* ulg *)
  w_static_len : Z       (* ulg *)
}.

Definition w_set_heap w h := mkWork h (w_heap_len w) (w_heap_max w) (w_depth w) (w_bl_count w) (w_opt_len w) (w_static_len w).
Definition w_set_heap_len w x := mkWork (w_heap w) x (w_heap_max w) (w_depth w) (w_bl_count w) (w_opt_len w) (w_static_len w).
Definition w_set_heap_max w x := mkWork (w_heap w) (w_heap_len w) x (w_depth w) (w_bl_count w) (w_opt_len w) (w_static_len w).
Definition w_set_depth w d := mkWork (w_heap w) (w_heap_len w) (w_heap_max w) d (w_bl_count w) (w_opt_len w) (w_static_len w).
Definition w_set_bl_count w b := mkWork (w_heap w) (w_heap_len w) (w_heap_max w) (w_depth w) b (w_opt_len w) (w_static_len w).
Definition w_set_opt_len w x := mkWork (w_heap w) (w_heap_len w) (w_heap_max w) (w_depth w) (w_bl_count w) x (w_static_len w).
Definition w_set_static_len w x := mkWork (w_heap w) (w_heap_len w) (w_heap_max w) (w_depth w) (w_bl_count w) (w_opt_len w) x.

(** ** pqdownheap, smaller (trees.c) *)

Definition smaller (t : tree) (depth : list Z) (n m : Z) : bool :=
  (Znth n (fc t) <? Znth m (fc t)) ||
  ((Znth n (fc t) =? Znth m (fc t)) && (Znth n depth <=? Znth m depth)).

(** The loop of pqdownheap, from the state (heap, k, j) at the loop test; returns (heap, k) after the loop. *)
Fixpoint pqdownheap_loop (fuel : nat) (t : tree) (depth : list Z) (heap_len v : Z)
    (heap : list Z) (k j : Z) : list Z * Z :=
  match fuel with
  | O => (heap, k)
  | S f =>
    if j <=? heap_len then
      let j := if (j <? heap_len) && smaller t depth (Znth (j + 1) heap) (Znth j heap) then j + 1 else j in
      if smaller t depth v (Znth j heap) then (heap, k)
      else pqdownheap_loop f t depth heap_len v (upd_Znth k heap (Znth j heap)) j (Z.shiftl j 1)
    else (heap, k)
  end.

(** j at least doubles each iteration and the heap has fewer than 2^10 elements. *)
Definition pq_fuel : nat := 12.

Definition pqdownheap (t : tree) (w : work) (k : Z) : work :=
  let v := Znth k (w_heap w) in
  let '(heap, k') := pqdownheap_loop pq_fuel t (w_depth w) (w_heap_len w) v (w_heap w) k (Z.shiftl k 1) in
  w_set_heap w (upd_Znth k' heap v).

(** ** gen_bitlen *)

(** First pass: [for (h = s->heap_max + 1; h < HEAP_SIZE; h++)]. *)
Fixpoint gen_bitlen_pass1 (fuel : nat) (sd : stat_desc) (max_code : Z)
    (t : tree) (w : work) (overflow h : Z) : tree * work * Z :=
  match fuel with
  | O => (t, w, overflow)
  | S f =>
    if h <? HEAP_SIZE then
      let n := Znth h (w_heap w) in
      let bits := Znth (Znth n (dl t)) (dl t) + 1 in
      let '(bits, overflow) :=
        if bits >? sd_maxlen sd then (sd_maxlen sd, overflow + 1) else (bits, overflow) in
      let t := set_dl t n (u16 bits) in
      if n >? max_code then gen_bitlen_pass1 f sd max_code t w overflow (h + 1)
      else
        let w := w_set_bl_count w (upd_Znth bits (w_bl_count w) (u16 (Znth bits (w_bl_count w) + 1))) in
        let xbits := if n >=? sd_base sd then Znth (n - sd_base sd) (sd_extra sd) else 0 in
        let fr := Znth n (fc t) in
        let w := w_set_opt_len w (u64 (w_opt_len w + fr * u32 (bits + xbits))) in
        let w := match sd_stree sd with
                 | Some stree => w_set_static_len w (u64 (w_static_len w + fr * u32 (Znth n stree + xbits)))
                 | None => w
                 end in
        gen_bitlen_pass1 f sd max_code t w overflow (h + 1)
    else (t, w, overflow)
  end.

(** [while (s->bl_count[bits] == 0) bits--;] *)
Fixpoint find_nonzero_down (fuel : nat) (bl_count : list Z) (bits : Z) : Z :=
  match fuel with
  | O => bits
  | S f => if Znth bits bl_count =? 0 then find_nonzero_down f bl_count (bits - 1) else bits
  end.

(** The overflow repair: [do { ... } while (overflow > 0);] *)
Fixpoint gen_bitlen_repair (fuel : nat) (max_length : Z) (bl_count : list Z) (overflow : Z) : list Z :=
  match fuel with
  | O => bl_count
  | S f =>
    let bits := find_nonzero_down 20 bl_count (max_length - 1) in
    let bl_count := upd_Znth bits bl_count (u16 (Znth bits bl_count - 1)) in
    let bl_count := upd_Znth (bits + 1) bl_count (u16 (Znth (bits + 1) bl_count + 2)) in
    let bl_count := upd_Znth max_length bl_count (u16 (Znth max_length bl_count - 1)) in
    let overflow := overflow - 2 in
    if overflow >? 0 then gen_bitlen_repair f max_length bl_count overflow else bl_count
  end.

(** The inner loop of the recomputation: [while (n != 0) { m = s->heap[--h]; ... }] *)
Fixpoint gen_bitlen_reassign_inner (fuel : nat) (max_code bits : Z) (heap : list Z)
    (t : tree) (opt_len : Z) (h n : Z) : tree * Z * Z :=
  match fuel with
  | O => (t, opt_len, h)
  | S f =>
    if n =? 0 then (t, opt_len, h)
    else
      let h := h - 1 in
      let m := Znth h heap in
      if m >? max_code then gen_bitlen_reassign_inner f max_code bits heap t opt_len h n
      else
        let '(t, opt_len) :=
          if negb (Znth m (dl t) =? bits) then
            (set_dl t m (u16 bits), u64 (opt_len + u64 (bits - Znth m (dl t)) * Znth m (fc t)))
          else (t, opt_len) in
        gen_bitlen_reassign_inner f max_code bits heap t opt_len h (n - 1)
  end.

(** [for (bits = max_length; bits != 0; bits--) { n = s->bl_count[bits]; while ... }] *)
Fixpoint gen_bitlen_reassign (fuel : nat) (max_code : Z) (heap bl_count : list Z)
    (t : tree) (opt_len : Z) (h bits : Z) : tree * Z :=
  match fuel with
  | O => (t, opt_len)
  | S f =>
    if bits =? 0 then (t, opt_len)
    else
      let '(t, opt_len, h) :=
        gen_bitlen_reassign_inner (Z.to_nat HEAP_SIZE) max_code bits heap t opt_len h (Znth bits bl_count) in
      gen_bitlen_reassign f max_code heap bl_count t opt_len h (bits - 1)
  end.

Definition gen_bitlen (sd : stat_desc) (max_code : Z) (t : tree) (w : work) : tree * work :=
  let w := w_set_bl_count w (repeat 0 (Z.to_nat (MAX_BITS + 1))) in
  let t := set_dl t (Znth (w_heap_max w) (w_heap w)) 0 in
  let '(t, w, overflow) := gen_bitlen_pass1 (Z.to_nat HEAP_SIZE) sd max_code t w 0 (w_heap_max w + 1) in
  if overflow =? 0 then (t, w)
  else
    let bl_count := gen_bitlen_repair (Z.to_nat HEAP_SIZE) (sd_maxlen sd) (w_bl_count w) overflow in
    let w := w_set_bl_count w bl_count in
    let '(t, opt_len) :=
      gen_bitlen_reassign 20 max_code (w_heap w) bl_count t (w_opt_len w) HEAP_SIZE (sd_maxlen sd) in
    (t, w_set_opt_len w opt_len).

(** ** gen_codes, bi_reverse *)

Fixpoint bi_reverse_loop (fuel : nat) (code res len : Z) : Z :=
  match fuel with
  | O => res
  | S f =>
    let res := Z.lor res (Z.land code 1) in
    let code := Z.shiftr code 1 in
    let res := Z.shiftl res 1 in
    let len := len - 1 in
    if len >? 0 then bi_reverse_loop f code res len else res
  end.

(** [bi_reverse(code, len)] for [1 <= len <= 15] ([unsigned] arithmetic: values stay below 2^16). *)
Definition bi_reverse (code len : Z) : Z := Z.shiftr (bi_reverse_loop 16 code 0 len) 1.

(** [for (bits = 1; bits <= MAX_BITS; bits++) { code = (code + bl_count[bits - 1]) << 1; next_code[bits] = code; }] *)
Fixpoint gen_next_code (fuel : nat) (bl_count next_code : list Z) (code bits : Z) : list Z :=
  match fuel with
  | O => next_code
  | S f =>
    if bits <=? MAX_BITS then
      let code := u32 (Z.shiftl (code + Znth (bits - 1) bl_count) 1) in
      gen_next_code f bl_count (upd_Znth bits next_code (u16 code)) code (bits + 1)
    else next_code
  end.

Fixpoint gen_codes_loop (fuel : nat) (max_code : Z) (t : tree) (next_code : list Z) (n : Z) : tree :=
  match fuel with
  | O => t
  | S f =>
    if n <=? max_code then
      let len := Znth n (dl t) in
      if len =? 0 then gen_codes_loop f max_code t next_code (n + 1)
      else
        let c := Znth len next_code in
        gen_codes_loop f max_code (set_fc t n (u16 (bi_reverse c len)))
                       (upd_Znth len next_code (u16 (c + 1))) (n + 1)
    else t
  end.

Definition gen_codes (t : tree) (max_code : Z) (bl_count : list Z) : tree :=
  let next_code := gen_next_code 16 bl_count (repeat 0 (Z.to_nat (MAX_BITS + 1))) 0 1 in
  gen_codes_loop (Z.to_nat HEAP_SIZE) max_code t next_code 0.

(** ** build_tree *)

(** [for (n = 0; n < elems; n++) { if (tree[n].Freq != 0) ... else tree[n].Len = 0; }] *)
Fixpoint bt_init (fuel : nat) (elems : Z) (t : tree) (w : work) (max_code n : Z) : tree * work * Z :=
  match fuel with
  | O => (t, w, max_code)
  | S f =>
    if n <? elems then
      if negb (Znth n (fc t) =? 0) then
        let hl := w_heap_len w + 1 in
        let w := w_set_heap_len w hl in
        let w := w_set_heap w (upd_Znth hl (w_heap w) n) in
        let w := w_set_depth w (upd_Znth n (w_depth w) 0) in
        bt_init f elems t w n (n + 1)
      else bt_init f elems (set_dl t n 0) w max_code (n + 1)
    else (t, w, max_code)
  end.

(** [while (s->heap_len < 2) { node = s->heap[++(s->heap_len)] = (max_code < 2 ? ++max_code : 0); ... }] *)
Fixpoint bt_force (fuel : nat) (sd : stat_desc) (t : tree) (w : work) (max_code : Z) : tree * work * Z :=
  match fuel with
  | O => (t, w, max_code)
  | S f =>
    if w_heap_len w <? 2 then
      let '(node, max_code) := if max_code <? 2 then (max_code + 1, max_code + 1) else (0, max_code) in
      let hl := w_heap_len w + 1 in
      let w := w_set_heap_len w hl in
      let w := w_set_heap w (upd_Znth hl (w_heap w) node) in
      let t := set_fc t node 1 in
      let w := w_set_depth w (upd_Znth node (w_depth w) 0) in
      let w := w_set_opt_len w (u64 (w_opt_len w - 1)) in
      let w := match sd_stree sd with
               | Some stree => w_set_static_len w (u64 (w_static_len w - Znth node stree))
               | None => w
               end in
      bt_force f sd t w max_code
    else (t, w, max_code)
  end.

(** [for (n = s->heap_len/2; n >= 1; n--) pqdownheap(s, tree, n);] *)
Fixpoint bt_heapify (fuel : nat) (t : tree) (w : work) (n : Z) : work :=
  match fuel with
  | O => w
  | S f => if n >=? 1 then bt_heapify f t (pqdownheap t w n) (n - 1) else w
  end.

(** pqremove(s, tree, n): returns n (the old top) and the work area. *)
Definition pqremove (t : tree) (w : work) : Z * work :=
  (Znth SMALLEST (w_heap w),
   pqdownheap t (w_set_heap_len (w_set_heap w (upd_Znth SMALLEST (w_heap w) (Znth (w_heap_len w) (w_heap w))))
                                (w_heap_len w - 1)) SMALLEST).

(** [s->heap[--(s->heap_max)] = x;] *)
Definition store_removed (w : work) (x : Z) : work :=
  w_set_heap (w_set_heap_max w (w_heap_max w - 1)) (upd_Znth (w_heap_max w - 1) (w_heap w) x).

(** The new node father of n and m: its Freq, its depth, the Dad fields of n and m (in this order). *)
Definition new_node (t : tree) (w : work) (n m node : Z) : tree * work :=
  let dn := Znth n (w_depth w) in
  let dm := Znth m (w_depth w) in
  (set_dl (set_dl (set_fc t node (u16 (Znth n (fc t) + Znth m (fc t)))) m (u16 node)) n (u16 node),
   w_set_depth w (upd_Znth node (w_depth w) (u8 ((if dn >=? dm then dn else dm) + 1)))).

(** One iteration of the [do { ... } while (s->heap_len >= 2);] loop of build_tree. *)
Definition merge_body (t : tree) (w : work) (node : Z) : tree * work :=
  let '(n, w1) := pqremove t w in
  let m := Znth SMALLEST (w_heap w1) in
  let w2 := store_removed (store_removed w1 n) m in
  let '(t3, w3) := new_node t w2 n m node in
  (t3, pqdownheap t3 (w_set_heap w3 (upd_Znth SMALLEST (w_heap w3) node)) SMALLEST).

Fixpoint bt_merge (fuel : nat) (t : tree) (w : work) (node : Z) : tree * work * Z :=
  match fuel with
  | O => (t, w, node)
  | S f =>
    let '(t, w) := merge_body t w node in
    if w_heap_len w >=? 2 then bt_merge f t w (node + 1) else (t, w, node + 1)
  end.

(** build_tree(s, desc): returns the tree, its new max_code and the work area. *)
Definition build_tree (sd : stat_desc) (t : tree) (w : work) : tree * Z * work :=
  let w := w_set_heap_len w 0 in
  let w := w_set_heap_max w HEAP_SIZE in
  let '(t, w, max_code) := bt_init (Z.to_nat (sd_elems sd)) (sd_elems sd) t w (-1) 0 in
  let '(t, w, max_code) := bt_force 2 sd t w max_code in
  let w := bt_heapify (Z.to_nat (w_heap_len w / 2)) t w (w_heap_len w / 2) in
  let '(t, w, _) := bt_merge (Z.to_nat (w_heap_len w)) t w (sd_elems sd) in
  let w := w_set_heap_max w (w_heap_max w - 1) in
  let w := w_set_heap w (upd_Znth (w_heap_max w) (w_heap w) (Znth SMALLEST (w_heap w))) in
  let '(t, w) := gen_bitlen sd max_code t w in
  let t := gen_codes t max_code (w_bl_count w) in
  (t, max_code, w).

(** ** scan_tree, build_bl_tree *)

(** The loop of scan_tree: state (n, prevlen, nextlen, count, max_count, min_count) and the bit length tree's
    frequencies [blf] (= the [fc] field of bl_tree). *)
Fixpoint scan_tree_loop (fuel : nat) (t : tree) (max_code : Z) (blf : list Z)
    (n prevlen nextlen count max_count min_count : Z) : list Z :=
  match fuel with
  | O => blf
  | S f =>
    if n <=? max_code then
      let curlen := nextlen in
      let nextlen := Znth (n + 1) (dl t) in
      let count := count + 1 in
      if (count <? max_count) && (curlen =? nextlen) then
        scan_tree_loop f t max_code blf (n + 1) prevlen nextlen count max_count min_count
      else
        let blf :=
          if count <? min_count then upd_Znth curlen blf (u16 (Znth curlen blf + u16 count))
          else if negb (curlen =? 0) then
            let blf := if negb (curlen =? prevlen) then upd_Znth curlen blf (u16 (Znth curlen blf + 1)) else blf in
            upd_Znth REP_3_6 blf (u16 (Znth REP_3_6 blf + 1))
          else if count <=? 10 then upd_Znth REPZ_3_10 blf (u16 (Znth REPZ_3_10 blf + 1))
          else upd_Znth REPZ_11_138 blf (u16 (Znth REPZ_11_138 blf + 1)) in
        let '(max_count, min_count) :=
          if nextlen =? 0 then (138, 3)
          else if curlen =? nextlen then (6, 3)
          else (7, 4) in
        scan_tree_loop f t max_code blf (n + 1) curlen nextlen 0 max_count min_count
    else blf
  end.

(** scan_tree(s, tree, max_code): returns the tree (with the guard [tree[max_code + 1].Len = 0xffff] stored) and
    the bit length tree. *)
Definition scan_tree (t : tree) (max_code : Z) (bl : tree) : tree * tree :=
  let nextlen := Znth 0 (dl t) in
  let '(max_count, min_count) := if nextlen =? 0 then (138, 3) else (7, 4) in
  let t := set_dl t (max_code + 1) 65535 in
  let blf := scan_tree_loop (Z.to_nat (max_code + 1)) t max_code (fc bl) 0 (-1) nextlen 0 max_count min_count in
  (t, mkTree blf (dl bl)).

(** [for (max_blindex = BL_CODES-1; max_blindex >= 3; max_blindex--) if (...Len != 0) break;] *)
Fixpoint find_max_blindex (fuel : nat) (bl : tree) (i : Z) : Z :=
  match fuel with
  | O => i
  | S f =>
    if i >=? 3 then
      if negb (Znth (Znth i bl_order) (dl bl) =? 0) then i else find_max_blindex f bl (i - 1)
    else i
  end.

(** ** The whole trees.c state *)

(** Bit output: pending_buf, pending, bi_buf, bi_valid, bi_used. *)
Record outbuf := mkOut {
  o_buf : list Z;
  o_pending : Z;
  o_bi_buf : Z;
  o_bi_valid : Z;
  o_bi_used : Z
}.

Record tstate := mkTS {
  tr_ltree : tree;
  tr_dtree : tree;
  tr_bltree : tree;
  tr_lmax : Z;
  tr_dmax : Z;
  tr_blmax : Z;
  tr_wk : work;
  tr_out : outbuf;
  tr_sym_next : Z;
  tr_sym_end : Z;
  tr_matches : Z;
  tr_lit_bufsize : Z;
  tr_level : Z;
  tr_strategy : Z;
  tr_data_type : Z
}.

Definition set_ltree s t := mkTS t (tr_dtree s) (tr_bltree s) (tr_lmax s) (tr_dmax s) (tr_blmax s) (tr_wk s) (tr_out s) (tr_sym_next s) (tr_sym_end s) (tr_matches s) (tr_lit_bufsize s) (tr_level s) (tr_strategy s) (tr_data_type s).
Definition set_dtree s t := mkTS (tr_ltree s) t (tr_bltree s) (tr_lmax s) (tr_dmax s) (tr_blmax s) (tr_wk s) (tr_out s) (tr_sym_next s) (tr_sym_end s) (tr_matches s) (tr_lit_bufsize s) (tr_level s) (tr_strategy s) (tr_data_type s).
Definition set_bltree s t := mkTS (tr_ltree s) (tr_dtree s) t (tr_lmax s) (tr_dmax s) (tr_blmax s) (tr_wk s) (tr_out s) (tr_sym_next s) (tr_sym_end s) (tr_matches s) (tr_lit_bufsize s) (tr_level s) (tr_strategy s) (tr_data_type s).
Definition set_lmax s x := mkTS (tr_ltree s) (tr_dtree s) (tr_bltree s) x (tr_dmax s) (tr_blmax s) (tr_wk s) (tr_out s) (tr_sym_next s) (tr_sym_end s) (tr_matches s) (tr_lit_bufsize s) (tr_level s) (tr_strategy s) (tr_data_type s).
Definition set_dmax s x := mkTS (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s) x (tr_blmax s) (tr_wk s) (tr_out s) (tr_sym_next s) (tr_sym_end s) (tr_matches s) (tr_lit_bufsize s) (tr_level s) (tr_strategy s) (tr_data_type s).
Definition set_blmax s x := mkTS (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s) (tr_dmax s) x (tr_wk s) (tr_out s) (tr_sym_next s) (tr_sym_end s) (tr_matches s) (tr_lit_bufsize s) (tr_level s) (tr_strategy s) (tr_data_type s).
Definition set_wk s w := mkTS (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s) (tr_dmax s) (tr_blmax s) w (tr_out s) (tr_sym_next s) (tr_sym_end s) (tr_matches s) (tr_lit_bufsize s) (tr_level s) (tr_strategy s) (tr_data_type s).
Definition set_out s o := mkTS (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s) (tr_dmax s) (tr_blmax s) (tr_wk s) o (tr_sym_next s) (tr_sym_end s) (tr_matches s) (tr_lit_bufsize s) (tr_level s) (tr_strategy s) (tr_data_type s).
Definition set_sym_next s x := mkTS (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s) (tr_dmax s) (tr_blmax s) (tr_wk s) (tr_out s) x (tr_sym_end s) (tr_matches s) (tr_lit_bufsize s) (tr_level s) (tr_strategy s) (tr_data_type s).
Definition set_matches s x := mkTS (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s) (tr_dmax s) (tr_blmax s) (tr_wk s) (tr_out s) (tr_sym_next s) (tr_sym_end s) x (tr_lit_bufsize s) (tr_level s) (tr_strategy s) (tr_data_type s).
Definition set_data_type s x := mkTS (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s) (tr_dmax s) (tr_blmax s) (tr_wk s) (tr_out s) (tr_sym_next s) (tr_sym_end s) (tr_matches s) (tr_lit_bufsize s) (tr_level s) (tr_strategy s) x.

(** build_bl_tree(s): returns the state and max_blindex. *)
Definition build_bl_tree (s : tstate) : tstate * Z :=
  let '(lt, bl) := scan_tree (tr_ltree s) (tr_lmax s) (tr_bltree s) in
  let '(dt, bl) := scan_tree (tr_dtree s) (tr_dmax s) bl in
  let '(bl, blmax, w) := build_tree static_bl_desc bl (tr_wk s) in
  let max_blindex := find_max_blindex 20 bl (BL_CODES - 1) in
  let w := w_set_opt_len w (u64 (w_opt_len w + (3 * (max_blindex + 1) + 5 + 5 + 4))) in
  let s := set_ltree s lt in
  let s := set_dtree s dt in
  let s := set_bltree s bl in
  let s := set_blmax s blmax in
  (set_wk s w, max_blindex).

(** ** Bit output: put_byte, put_short, send_bits, bi_flush, bi_windup *)

Definition put_byte (o : outbuf) (c : Z) : outbuf :=
  mkOut (upd_Znth (o_pending o) (o_buf o) (u8 c)) (o_pending o + 1) (o_bi_buf o) (o_bi_valid o) (o_bi_used o).

Definition put_short (o : outbuf) (w : Z) : outbuf :=
  put_byte (put_byte o (Z.land w 255)) (Z.shiftr (u16 w) 8).

Definition set_bits (o : outbuf) (bb bv : Z) : outbuf :=
  mkOut (o_buf o) (o_pending o) bb bv (o_bi_used o).

(** The send_bits macro (non-debug build).  [value] fits in [length] bits, [1 <= length <= 16]. *)
Definition send_bits (o : outbuf) (value length : Z) : outbuf :=
  if o_bi_valid o >? Buf_size - length then
    let bb := u16 (Z.lor (o_bi_buf o) (Z.shiftl (u16 value) (o_bi_valid o))) in
    let o' := put_short (set_bits o bb (o_bi_valid o)) bb in
    set_bits o' (Z.shiftr (u16 value) (Buf_size - o_bi_valid o)) (o_bi_valid o + length - Buf_size)
  else
    set_bits o (u16 (Z.lor (o_bi_buf o) (Z.shiftl (u16 value) (o_bi_valid o)))) (o_bi_valid o + length).

(** send_code(s, c, tree): the tree is given by its [Code] and [Len] arrays. *)
Definition send_code (o : outbuf) (c : Z) (codes lens : list Z) : outbuf :=
  send_bits o (Znth c codes) (Znth c lens).

Definition bi_flush (o : outbuf) : outbuf :=
  if o_bi_valid o =? 16 then
    set_bits (put_short o (o_bi_buf o)) 0 0
  else if o_bi_valid o >=? 8 then
    let o := put_byte o (o_bi_buf o) in
    set_bits o (Z.shiftr (o_bi_buf o) 8) (o_bi_valid o - 8)
  else o.

Definition bi_windup (o : outbuf) : outbuf :=
  let o := if o_bi_valid o >? 8 then put_short o (o_bi_buf o)
           else if o_bi_valid o >? 0 then put_byte o (o_bi_buf o)
           else o in
  mkOut (o_buf o) (o_pending o) 0 0 (Z.land (o_bi_valid o - 1) 7 + 1).

(** ** send_tree, send_all_trees *)

Fixpoint send_tree_loop (fuel : nat) (t : tree) (max_code : Z) (blc bll : list Z) (o : outbuf)
    (n prevlen nextlen count max_count min_count : Z) : outbuf :=
  match fuel with
  | O => o
  | S f =>
    if n <=? max_code then
      let curlen := nextlen in
      let nextlen := Znth (n + 1) (dl t) in
      let count := count + 1 in
      if (count <? max_count) && (curlen =? nextlen) then
        send_tree_loop f t max_code blc bll o (n + 1) prevlen nextlen count max_count min_count
      else
        let o :=
          if count <? min_count then
            (* do { send_code(s, curlen, s->bl_tree); } while (--count != 0); *)
            Nat.iter (Z.to_nat count) (fun o => send_code o curlen blc bll) o
          else if negb (curlen =? 0) then
            let '(o, count) :=
              if negb (curlen =? prevlen) then (send_code o curlen blc bll, count - 1) else (o, count) in
            send_bits (send_code o REP_3_6 blc bll) (count - 3) 2
          else if count <=? 10 then send_bits (send_code o REPZ_3_10 blc bll) (count - 3) 3
          else send_bits (send_code o REPZ_11_138 blc bll) (count - 11) 7 in
        let '(max_count, min_count) :=
          if nextlen =? 0 then (138, 3)
          else if curlen =? nextlen then (6, 3)
          else (7, 4) in
        send_tree_loop f t max_code blc bll o (n + 1) curlen nextlen 0 max_count min_count
    else o
  end.

(** send_tree(s, tree, max_code); the guard [tree[max_code + 1].Len] was stored by scan_tree. *)
Definition send_tree (o : outbuf) (t : tree) (max_code : Z) (bl : tree) : outbuf :=
  let nextlen := Znth 0 (dl t) in
  let '(max_count, min_count) := if nextlen =? 0 then (138, 3) else (7, 4) in
  send_tree_loop (Z.to_nat (max_code + 1)) t max_code (fc bl) (dl bl) o 0 (-1) nextlen 0 max_count min_count.

Fixpoint send_bl_lens (fuel : nat) (bl : tree) (o : outbuf) (rank blcodes : Z) : outbuf :=
  match fuel with
  | O => o
  | S f =>
    if rank <? blcodes then
      send_bl_lens f bl (send_bits o (Znth (Znth rank bl_order) (dl bl)) 3) (rank + 1) blcodes
    else o
  end.

Definition send_all_trees (o : outbuf) (lt dt bl : tree) (lcodes dcodes blcodes : Z) : outbuf :=
  let o := send_bits o (lcodes - 257) 5 in
  let o := send_bits o (dcodes - 1) 5 in
  let o := send_bits o (blcodes - 4) 4 in
  let o := send_bl_lens 19 bl o 0 blcodes in
  let o := send_tree o lt (lcodes - 1) bl in
  send_tree o dt (dcodes - 1) bl.

(** ** compress_block *)

(** One symbol: [dist] as read from sym_buf (0 for a literal, else the distance), [lc] the literal or the length
    minus MIN_MATCH. *)
Definition send_symbol (o : outbuf) (lcodes llens dcodes dlens : list Z) (dist lc : Z) : outbuf :=
  if dist =? 0 then send_code o lc lcodes llens
  else
    let code := Znth lc length_code_tab in
    let o := send_code o (code + LITERALS + 1) lcodes llens in
    let extra := Znth code extra_lbits in
    let o := if negb (extra =? 0) then send_bits o (lc - Znth code base_length_tab) extra else o in
    let dist := dist - 1 in
    let code := d_code dist in
    let o := send_code o code dcodes dlens in
    let extra := Znth code extra_dbits in
    if negb (extra =? 0) then send_bits o (dist - Znth code base_dist_tab) extra else o.

(** The loop of compress_block, reading the symbols from the overlaid buffer [sym_buf = pending_buf + lit_bufsize]
    (the output is written into the same buffer, at [pending]). *)
Fixpoint compress_loop (fuel : nat) (lit_bufsize sym_next : Z) (lcodes llens dcodes dlens : list Z)
    (o : outbuf) (sx : Z) : outbuf :=
  match fuel with
  | O => o
  | S f =>
    let dist := Z.land (Znth (lit_bufsize + sx) (o_buf o)) 255 in
    let dist := dist + Z.shiftl (Z.land (Znth (lit_bufsize + sx + 1) (o_buf o)) 255) 8 in
    let lc := Znth (lit_bufsize + sx + 2) (o_buf o) in
    let sx := sx + 3 in
    let o := send_symbol o lcodes llens dcodes dlens dist lc in
    if sx <? sym_next then compress_loop f lit_bufsize sym_next lcodes llens dcodes dlens o sx else o
  end.

Definition compress_block (o : outbuf) (lit_bufsize sym_next : Z) (lcodes llens dcodes dlens : list Z) : outbuf :=
  let o := if negb (sym_next =? 0)
           then compress_loop (Z.to_nat sym_next) lit_bufsize sym_next lcodes llens dcodes dlens o 0
           else o in
  send_code o END_BLOCK lcodes llens.

(** ** init_block, _tr_init, _tr_tally, detect_data_type *)

Fixpoint zero_fc (fuel : nat) (t : tree) (n hi : Z) : tree :=
  match fuel with
  | O => t
  | S f => if n <? hi then zero_fc f (set_fc t n 0) (n + 1) hi else t
  end.

Definition init_block (s : tstate) : tstate :=
  let s := set_ltree s (zero_fc (Z.to_nat L_CODES) (tr_ltree s) 0 L_CODES) in
  let s := set_dtree s (zero_fc (Z.to_nat D_CODES) (tr_dtree s) 0 D_CODES) in
  let s := set_bltree s (zero_fc (Z.to_nat BL_CODES) (tr_bltree s) 0 BL_CODES) in
  let s := set_ltree s (set_fc (tr_ltree s) END_BLOCK 1) in
  let s := set_wk s (w_set_static_len (w_set_opt_len (tr_wk s) 0) 0) in
  set_matches (set_sym_next s 0) 0.

(** _tr_init(s) (tr_static_init is empty with the static tables of trees.h). *)
Definition tr_init (s : tstate) : tstate :=
  let o := tr_out s in
  init_block (set_out s (mkOut (o_buf o) (o_pending o) 0 0 0)).

Definition put_sym (s : tstate) (b : Z) : tstate :=
  let o := tr_out s in
  set_sym_next
    (set_out s (mkOut (upd_Znth (tr_lit_bufsize s + tr_sym_next s) (o_buf o) (u8 b))
                      (o_pending o) (o_bi_buf o) (o_bi_valid o) (o_bi_used o)))
    (tr_sym_next s + 1).

Definition incr_lfreq (s : tstate) (i : Z) : tstate :=
  set_ltree s (set_fc (tr_ltree s) i (u16 (Znth i (fc (tr_ltree s)) + 1))).
Definition incr_dfreq (s : tstate) (i : Z) : tstate :=
  set_dtree s (set_fc (tr_dtree s) i (u16 (Znth i (fc (tr_dtree s)) + 1))).

(** _tr_tally(s, dist, lc): returns the state and the flush flag. *)
Definition tr_tally (s : tstate) (dist lc : Z) : tstate * bool :=
  let s := put_sym s dist in
  let s := put_sym s (Z.shiftr dist 8) in
  let s := put_sym s lc in
  let s :=
    if dist =? 0 then incr_lfreq s lc
    else
      let s := set_matches s (u32 (tr_matches s + 1)) in
      let dist := dist - 1 in
      incr_dfreq (incr_lfreq s (Znth lc length_code_tab + LITERALS + 1)) (d_code dist) in
  (s, tr_sym_next s =? tr_sym_end s).

(** The _tr_tally_lit / _tr_tally_dist macros of deflate.h (non-debug build; they do not count matches). *)
Definition tr_tally_lit (s : tstate) (c : Z) : tstate * bool :=
  let cc := u8 c in
  let s := put_sym (put_sym (put_sym s 0) 0) cc in
  let s := incr_lfreq s cc in
  (s, tr_sym_next s =? tr_sym_end s).

Definition tr_tally_dist (s : tstate) (distance length : Z) : tstate * bool :=
  let len := u8 length in
  let dist := u16 distance in
  let s := put_sym (put_sym (put_sym s dist) (Z.shiftr dist 8)) len in
  let dist := u16 (dist - 1) in
  let s := incr_dfreq (incr_lfreq s (Znth len length_code_tab + LITERALS + 1)) (d_code dist) in
  (s, tr_sym_next s =? tr_sym_end s).

(** detect_data_type(s): block_mask 0xf3ffc07f. *)
Definition block_listed (n : Z) : bool := Z.testbit 4093624447 n.

Fixpoint dd_block (fuel : nat) (lf : list Z) (n : Z) : bool :=
  match fuel with
  | O => false
  | S f => if n <=? 31 then (block_listed n && negb (Znth n lf =? 0)) || dd_block f lf (n + 1) else false
  end.

Fixpoint dd_allow (fuel : nat) (lf : list Z) (n : Z) : bool :=
  match fuel with
  | O => false
  | S f => if n <? LITERALS then negb (Znth n lf =? 0) || dd_allow f lf (n + 1) else false
  end.

Definition detect_data_type (lf : list Z) : Z :=
  if dd_block 32 lf 0 then Z_BINARY
  else if negb (Znth 9 lf =? 0) || negb (Znth 10 lf =? 0) || negb (Znth 13 lf =? 0) then Z_TEXT
  else if dd_allow 224 lf 32 then Z_TEXT
  else Z_BINARY.

(** ** _tr_stored_block, _tr_flush_bits, _tr_align, _tr_flush_block *)

(** [buf] is the bytes [buf[0 .. stored_len)] when [stored_len > 0]. *)
Definition copy_bytes (dst : list Z) (pos : Z) (src : list Z) : list Z :=
  sublist 0 pos dst ++ src ++ sublist (pos + Zlength src) (Zlength dst) dst.

Definition tr_stored_block (o : outbuf) (buf : list Z) (stored_len last : Z) : outbuf :=
  let o := send_bits o (Z.shiftl STORED_BLOCK 1 + last) 3 in
  let o := bi_windup o in
  let o := put_short o (u16 stored_len) in
  let o := put_short o (u16 (Z.lnot stored_len)) in
  let b := if negb (stored_len =? 0) then copy_bytes (o_buf o) (o_pending o) (sublist 0 stored_len buf)
           else o_buf o in
  mkOut b (o_pending o + stored_len) (o_bi_buf o) (o_bi_valid o) (o_bi_used o).

Definition tr_flush_bits (o : outbuf) : outbuf := bi_flush o.

Definition tr_align (o : outbuf) : outbuf :=
  let o := send_bits o (Z.shiftl STATIC_TREES 1) 3 in
  let o := send_code o END_BLOCK static_ltree_code static_ltree_len in
  bi_flush o.

(** The block type _tr_flush_block chooses. *)
Inductive block_kind := BK_stored | BK_static | BK_dynamic.

(** _tr_flush_block(s, buf, stored_len, last); [buf = None] is [buf == NULL]. *)
Definition tr_flush_block (s : tstate) (buf : option (list Z)) (stored_len last : Z) : tstate * block_kind :=
  let '(s, opt_lenb, static_lenb, max_blindex) :=
    if tr_level s >? 0 then
      let s := if tr_data_type s =? Z_UNKNOWN then set_data_type s (detect_data_type (fc (tr_ltree s))) else s in
      let '(lt, lmax, w) := build_tree static_l_desc (tr_ltree s) (tr_wk s) in
      let s := set_wk (set_lmax (set_ltree s lt) lmax) w in
      let '(dt, dmax, w) := build_tree static_d_desc (tr_dtree s) (tr_wk s) in
      let s := set_wk (set_dmax (set_dtree s dt) dmax) w in
      let '(s, max_blindex) := build_bl_tree s in
      let opt_lenb := Z.shiftr (u64 (w_opt_len (tr_wk s) + 3 + 7)) 3 in
      let static_lenb := Z.shiftr (u64 (w_static_len (tr_wk s) + 3 + 7)) 3 in
      let opt_lenb := if (static_lenb <=? opt_lenb) || (tr_strategy s =? Z_FIXED) then static_lenb else opt_lenb in
      (s, opt_lenb, static_lenb, max_blindex)
    else (s, u64 (stored_len + 5), u64 (stored_len + 5), 0) in
  let '(o, kind) :=
    match buf with
    | Some b =>
      if u64 (stored_len + 4) <=? opt_lenb then (tr_stored_block (tr_out s) b stored_len last, BK_stored)
      else if static_lenb =? opt_lenb then
        (compress_block (send_bits (tr_out s) (Z.shiftl STATIC_TREES 1 + last) 3) (tr_lit_bufsize s)
           (tr_sym_next s) static_ltree_code static_ltree_len static_dtree_code static_dtree_len, BK_static)
      else
        (compress_block
           (send_all_trees (send_bits (tr_out s) (Z.shiftl DYN_TREES 1 + last) 3)
              (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s + 1) (tr_dmax s + 1) (max_blindex + 1))
           (tr_lit_bufsize s) (tr_sym_next s)
           (fc (tr_ltree s)) (dl (tr_ltree s)) (fc (tr_dtree s)) (dl (tr_dtree s)), BK_dynamic)
    | None =>
      if static_lenb =? opt_lenb then
        (compress_block (send_bits (tr_out s) (Z.shiftl STATIC_TREES 1 + last) 3) (tr_lit_bufsize s)
           (tr_sym_next s) static_ltree_code static_ltree_len static_dtree_code static_dtree_len, BK_static)
      else
        (compress_block
           (send_all_trees (send_bits (tr_out s) (Z.shiftl DYN_TREES 1 + last) 3)
              (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s + 1) (tr_dmax s + 1) (max_blindex + 1))
           (tr_lit_bufsize s) (tr_sym_next s)
           (fc (tr_ltree s)) (dl (tr_ltree s)) (fc (tr_dtree s)) (dl (tr_dtree s)), BK_dynamic)
    end in
  let s := init_block (set_out s o) in
  let s := if negb (last =? 0) then set_out s (bi_windup (tr_out s)) else s in
  (s, kind).
