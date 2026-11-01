(** * The checked model of trees.c

    One function [c_X] per function [X] of the unchecked model [Zlib.proof.huffman.Model] that transcribes a
    function or macro of trees.c (and the _tr_tally_* macros of deflate.h), in the sense of [CBase]: [c_X args]
    is [None] exactly when the C code would access an array out of its bounds, read a byte of pending_buf that
    was never written, do something undefined that is not excluded by the C types of its operands (see the
    guards below), or run a loop past its fuel; otherwise it is [Some] of what the C computes, which is what
    [Model.X] computes (CEquiv.v).

    Conventions.
    - Same arguments and argument order as [Model.X]; same fuel.  Each [let*] is one memory access of the C,
      in C statement order (a C expression that reads the same element twice, as [smaller] does, is read once).
    - Arrays of numbers are read with [rd] and written with [wr] on the model's list, whose length is the C
      array's when the state is well formed (heap/depth 573, bl_count 16, dyn_ltree 573, dyn_dtree 61,
      bl_tree 39, the static tables, next_code 16, ...); so an index out of the C array gives [None].
    - pending_buf carries its definedness mask: [cout] is an [outbuf] with the mask of its [o_buf] (same
      length), [cstate] a [tstate] with the mask of [o_buf (tr_out s)].  Writes into pending_buf ([c_put_byte],
      [c_put_sym], the stored-block copy) check the index against [Zlength (o_buf o)] and set the mask; reads
      ([c_rd_pb], the sym_buf reads of compress_block) need the index in range and the mask set.  Functions
      that never touch pending_buf take and return a plain [tstate] ([c_init_block], [c_build_bl_tree],
      [c_incr_lfreq], ...); the entry points of trees.c take a [cout] or [cstate].
    - Loops: same fuel as the model.  Running out of fuel gives [None], except that a loop whose test is pure
      (reads no memory) evaluates its test once more when the fuel is exhausted and returns [Some] of the
      current state when the loop exits there.  (The model returns the current state on exhausted fuel; for
      loops whose fuel is exactly the iteration count -- bt_init, bt_force with fuel 2 on an empty tree,
      bt_heapify, scan_tree, send_tree, send_bl_lens with 19 codes, zero_fc, dd_block, dd_allow -- this keeps
      [Some] reachable.)  Fuel notes: [c_gen_bitlen_reassign_inner] (fuel 573) and [c_gen_codes_loop] (fuel
      573) could only run out on states where the heap below heap_max or max_code = 572 are involved, which
      build_tree never produces.
    - Guards (C undefined behaviour other than memory, not excluded by the C types of the operands or by the
      checks already made):
      * [c_send_bits]: [0 <= bi_valid <= 16] (the shift amounts [bi_valid] and [16 - bi_valid] must be in
        [0, 32); the representation invariant of the bit writer, Bits.v [bw_ok], has it);
      * [c_bi_windup]: [0 <= bi_valid <= 16] ([bi_valid - 1] must not overflow);
      * [c_bi_reverse]: [1 <= len] ([--len] must not overflow at INT_MIN);
      * [c_send_all_trees]: [lcodes - 257], [lcodes - 1], [dcodes - 1], [blcodes - 4] do not overflow (int
        parameters);
      * [c_tr_flush_block]: [(STATIC_TREES<<1) + last] and [(DYN_TREES<<1) + last] do not overflow ([last] is an
        int parameter);
      * [c_tr_stored_block]: the zmemcpy: [0 < stored_len <= Zlength buf] and the destination
        [pending .. pending + stored_len) inside pending_buf.
      Additions such as [s->heap[++(s->heap_len)]] or [tree[max_code + 1]] need no guard: the checked access
      that follows bounds the sum by the array size.  The int fields bi_valid (outside send_bits), heap_len,
      heap_max are bounded by the accesses they index or by the representation invariants.
    - Each loop body calls the loop once where possible (see [c_dd_block]).
    - Truncations of stores (u8, u16, u32, u64) are as in the model. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.huffman.Model.
Require Export Zlib.proof.trees.CBase.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The state with masks *)

Definition cout := (outbuf * list bool)%type.
Definition cstate := (tstate * list bool)%type.

(** Checked updates of one entry of a tree. *)
Definition c_set_fc (t : tree) (i v : Z) : option tree :=
  let* l := wr (fc t) i v in Some (mkTree l (dl t)).
Definition c_set_dl (t : tree) (i v : Z) : option tree :=
  let* l := wr (dl t) i v in Some (mkTree (fc t) l).

(** A read of pending_buf: in range and written. *)
Definition c_rd_pb (om : cout) (i : Z) : option Z :=
  let '(o, m) := om in
  if in_range i (Zlength (o_buf o)) && Znth i m then Some (Znth i (o_buf o)) else None.

(** The mask after [n] bytes written from [lo] on (the stored block's zmemcpy). *)
Fixpoint mask_set_n (n : nat) (m : list bool) (lo : Z) : list bool :=
  match n with
  | O => m
  | S n' => mask_set_n n' (upd_Znth lo m true) (lo + 1)
  end.

(** ** pqdownheap, smaller *)

(** [smaller(tree, n, m, depth)]: the second disjunct re-reads [tree[n].Freq] and [tree[m].Freq] (same values). *)
Definition c_smaller (t : tree) (depth : list Z) (n m : Z) : option bool :=
  let* fn := rd (fc t) n in
  let* fm := rd (fc t) m in
  if fn <? fm then Some true
  else if fn =? fm then
    let* dn := rd depth n in
    let* dm := rd depth m in
    Some (dn <=? dm)
  else Some false.

Fixpoint c_pqdownheap_loop (fuel : nat) (t : tree) (depth : list Z) (heap_len v : Z)
    (heap : list Z) (k j : Z) : option (list Z * Z) :=
  match fuel with
  | O => if j <=? heap_len then None else Some (heap, k)
  | S f =>
    if j <=? heap_len then
      let* j := (if j <? heap_len then
                   let* a := rd heap (j + 1) in
                   let* b := rd heap j in
                   let* sm := c_smaller t depth a b in
                   Some (if sm then j + 1 else j)
                 else Some j) in
      let* hj := rd heap j in
      let* sm := c_smaller t depth v hj in
      if sm then Some (heap, k)
      else
        let* heap := wr heap k hj in
        c_pqdownheap_loop f t depth heap_len v heap j (Z.shiftl j 1)
    else Some (heap, k)
  end.

Definition c_pqdownheap (t : tree) (w : work) (k : Z) : option work :=
  let* v := rd (w_heap w) k in
  let* (heap, k') := c_pqdownheap_loop pq_fuel t (w_depth w) (w_heap_len w) v (w_heap w) k (Z.shiftl k 1) in
  let* heap := wr heap k' v in
  Some (w_set_heap w heap).

(** ** gen_bitlen *)

Fixpoint c_gen_bitlen_pass1 (fuel : nat) (sd : stat_desc) (max_code : Z)
    (t : tree) (w : work) (overflow h : Z) : option (tree * work * Z) :=
  match fuel with
  | O => if h <? HEAP_SIZE then None else Some (t, w, overflow)
  | S f =>
    if h <? HEAP_SIZE then
      let* n := rd (w_heap w) h in
      let* d := rd (dl t) n in
      let* ld := rd (dl t) d in
      let bits := ld + 1 in
      let '(bits, overflow) :=
        if bits >? sd_maxlen sd then (sd_maxlen sd, overflow + 1) else (bits, overflow) in
      let* t := c_set_dl t n (u16 bits) in
      if n >? max_code then c_gen_bitlen_pass1 f sd max_code t w overflow (h + 1)
      else
        let* bc := rd (w_bl_count w) bits in
        let* bcl := wr (w_bl_count w) bits (u16 (bc + 1)) in
        let w := w_set_bl_count w bcl in
        let* xbits := (if n >=? sd_base sd then rd (sd_extra sd) (n - sd_base sd) else Some 0) in
        let* fr := rd (fc t) n in
        let w := w_set_opt_len w (u64 (w_opt_len w + fr * u32 (bits + xbits))) in
        let* w := match sd_stree sd with
                  | Some stree =>
                    let* sl := rd stree n in
                    Some (w_set_static_len w (u64 (w_static_len w + fr * u32 (sl + xbits))))
                  | None => Some w
                  end in
        c_gen_bitlen_pass1 f sd max_code t w overflow (h + 1)
    else Some (t, w, overflow)
  end.

Fixpoint c_find_nonzero_down (fuel : nat) (bl_count : list Z) (bits : Z) : option Z :=
  match fuel with
  | O => None
  | S f =>
    let* b := rd bl_count bits in
    if b =? 0 then c_find_nonzero_down f bl_count (bits - 1) else Some bits
  end.

Fixpoint c_gen_bitlen_repair (fuel : nat) (max_length : Z) (bl_count : list Z) (overflow : Z)
    : option (list Z) :=
  match fuel with
  | O => None
  | S f =>
    let* bits := c_find_nonzero_down 20 bl_count (max_length - 1) in
    let* b := rd bl_count bits in
    let* bl_count := wr bl_count bits (u16 (b - 1)) in
    let* b1 := rd bl_count (bits + 1) in
    let* bl_count := wr bl_count (bits + 1) (u16 (b1 + 2)) in
    let* bm := rd bl_count max_length in
    let* bl_count := wr bl_count max_length (u16 (bm - 1)) in
    let overflow := overflow - 2 in
    if overflow >? 0 then c_gen_bitlen_repair f max_length bl_count overflow else Some bl_count
  end.

Fixpoint c_gen_bitlen_reassign_inner (fuel : nat) (max_code bits : Z) (heap : list Z)
    (t : tree) (opt_len : Z) (h n : Z) : option (tree * Z * Z) :=
  match fuel with
  | O => if n =? 0 then Some (t, opt_len, h) else None
  | S f =>
    if n =? 0 then Some (t, opt_len, h)
    else
      let h := h - 1 in
      let* m := rd heap h in
      if m >? max_code then c_gen_bitlen_reassign_inner f max_code bits heap t opt_len h n
      else
        let* lm := rd (dl t) m in
        let* (t, opt_len) :=
          (if negb (lm =? bits) then
             let* fm := rd (fc t) m in
             let* t' := c_set_dl t m (u16 bits) in
             Some (t', u64 (opt_len + u64 (bits - lm) * fm))
           else Some (t, opt_len)) in
        c_gen_bitlen_reassign_inner f max_code bits heap t opt_len h (n - 1)
  end.

Fixpoint c_gen_bitlen_reassign (fuel : nat) (max_code : Z) (heap bl_count : list Z)
    (t : tree) (opt_len : Z) (h bits : Z) : option (tree * Z) :=
  match fuel with
  | O => if bits =? 0 then Some (t, opt_len) else None
  | S f =>
    if bits =? 0 then Some (t, opt_len)
    else
      let* n := rd bl_count bits in
      let* (t, opt_len, h) :=
        c_gen_bitlen_reassign_inner (Z.to_nat HEAP_SIZE) max_code bits heap t opt_len h n in
      c_gen_bitlen_reassign f max_code heap bl_count t opt_len h (bits - 1)
  end.

(** [for (bits = 0; bits <= MAX_BITS; bits++) s->bl_count[bits] = 0;] writes constant indices of the 16-entry
    array bl_count: it cannot fail, and is kept as in the model. *)
Definition c_gen_bitlen (sd : stat_desc) (max_code : Z) (t : tree) (w : work) : option (tree * work) :=
  let w := w_set_bl_count w (repeat 0 (Z.to_nat (MAX_BITS + 1))) in
  let* r := rd (w_heap w) (w_heap_max w) in
  let* t := c_set_dl t r 0 in
  let* (t, w, overflow) := c_gen_bitlen_pass1 (Z.to_nat HEAP_SIZE) sd max_code t w 0 (w_heap_max w + 1) in
  if overflow =? 0 then Some (t, w)
  else
    let* bl_count := c_gen_bitlen_repair (Z.to_nat HEAP_SIZE) (sd_maxlen sd) (w_bl_count w) overflow in
    let w := w_set_bl_count w bl_count in
    let* (t, opt_len) :=
      c_gen_bitlen_reassign 20 max_code (w_heap w) bl_count t (w_opt_len w) HEAP_SIZE (sd_maxlen sd) in
    Some (t, w_set_opt_len w opt_len).

(** ** gen_codes, bi_reverse *)

Fixpoint c_bi_reverse_loop (fuel : nat) (code res len : Z) : option Z :=
  match fuel with
  | O => None
  | S f =>
    let res := Z.lor res (Z.land code 1) in
    let code := Z.shiftr code 1 in
    let res := Z.shiftl res 1 in
    let len := len - 1 in
    if len >? 0 then c_bi_reverse_loop f code res len else Some res
  end.

(** [code] is an [unsigned] below 2^16 (next_code is [ush]); within the fuel, [res] stays below 2^17.
    Guard: [1 <= len] ([--len] must not overflow; the callers pass 1..15). *)
Definition c_bi_reverse (code len : Z) : option Z :=
  let* _ := guard (1 <=? len) in
  let* r := c_bi_reverse_loop 16 code 0 len in Some (Z.shiftr r 1).

Fixpoint c_gen_next_code (fuel : nat) (bl_count next_code : list Z) (code bits : Z) : option (list Z) :=
  match fuel with
  | O => if bits <=? MAX_BITS then None else Some next_code
  | S f =>
    if bits <=? MAX_BITS then
      let* b := rd bl_count (bits - 1) in
      let code := u32 (Z.shiftl (code + b) 1) in
      let* next_code := wr next_code bits (u16 code) in
      c_gen_next_code f bl_count next_code code (bits + 1)
    else Some next_code
  end.

Fixpoint c_gen_codes_loop (fuel : nat) (max_code : Z) (t : tree) (next_code : list Z) (n : Z) : option tree :=
  match fuel with
  | O => if n <=? max_code then None else Some t
  | S f =>
    if n <=? max_code then
      let* len := rd (dl t) n in
      if len =? 0 then c_gen_codes_loop f max_code t next_code (n + 1)
      else
        let* c := rd next_code len in
        let* next_code := wr next_code len (u16 (c + 1)) in
        let* r := c_bi_reverse c len in
        let* t := c_set_fc t n (u16 r) in
        c_gen_codes_loop f max_code t next_code (n + 1)
    else Some t
  end.

(** The local [ush next_code[MAX_BITS+1]] is uninitialised; entries 1..15 are written by the first loop, and
    the second reads only [next_code[len]] with [len >= 1] (a [len > 15] is out of range: [None]).  The model's
    initial zeros are never read. *)
Definition c_gen_codes (t : tree) (max_code : Z) (bl_count : list Z) : option tree :=
  let* next_code := c_gen_next_code 16 bl_count (repeat 0 (Z.to_nat (MAX_BITS + 1))) 0 1 in
  c_gen_codes_loop (Z.to_nat HEAP_SIZE) max_code t next_code 0.

(** ** build_tree *)

Fixpoint c_bt_init (fuel : nat) (elems : Z) (t : tree) (w : work) (max_code n : Z) : option (tree * work * Z) :=
  match fuel with
  | O => if n <? elems then None else Some (t, w, max_code)
  | S f =>
    if n <? elems then
      let* fr := rd (fc t) n in
      if negb (fr =? 0) then
        let hl := w_heap_len w + 1 in
        let w := w_set_heap_len w hl in
        let* heap := wr (w_heap w) hl n in
        let w := w_set_heap w heap in
        let* depth := wr (w_depth w) n 0 in
        let w := w_set_depth w depth in
        c_bt_init f elems t w n (n + 1)
      else
        let* t := c_set_dl t n 0 in
        c_bt_init f elems t w max_code (n + 1)
    else Some (t, w, max_code)
  end.

Fixpoint c_bt_force (fuel : nat) (sd : stat_desc) (t : tree) (w : work) (max_code : Z) : option (tree * work * Z) :=
  match fuel with
  | O => if w_heap_len w <? 2 then None else Some (t, w, max_code)
  | S f =>
    if w_heap_len w <? 2 then
      let '(node, max_code) := if max_code <? 2 then (max_code + 1, max_code + 1) else (0, max_code) in
      let hl := w_heap_len w + 1 in
      let w := w_set_heap_len w hl in
      let* heap := wr (w_heap w) hl node in
      let w := w_set_heap w heap in
      let* t := c_set_fc t node 1 in
      let* depth := wr (w_depth w) node 0 in
      let w := w_set_depth w depth in
      let w := w_set_opt_len w (u64 (w_opt_len w - 1)) in
      let* w := match sd_stree sd with
                | Some stree =>
                  let* sl := rd stree node in Some (w_set_static_len w (u64 (w_static_len w - sl)))
                | None => Some w
                end in
      c_bt_force f sd t w max_code
    else Some (t, w, max_code)
  end.

Fixpoint c_bt_heapify (fuel : nat) (t : tree) (w : work) (n : Z) : option work :=
  match fuel with
  | O => if n >=? 1 then None else Some w
  | S f =>
    if n >=? 1 then
      let* w := c_pqdownheap t w n in c_bt_heapify f t w (n - 1)
    else Some w
  end.

(** [pqremove]: [top = s->heap[SMALLEST]; s->heap[SMALLEST] = s->heap[s->heap_len--]; pqdownheap(s, tree, SMALLEST);] *)
Definition c_pqremove (t : tree) (w : work) : option (Z * work) :=
  let* top := rd (w_heap w) SMALLEST in
  let* last := rd (w_heap w) (w_heap_len w) in
  let* heap := wr (w_heap w) SMALLEST last in
  let* w' := c_pqdownheap t (w_set_heap_len (w_set_heap w heap) (w_heap_len w - 1)) SMALLEST in
  Some (top, w').

Definition c_store_removed (w : work) (x : Z) : option work :=
  let* heap := wr (w_heap w) (w_heap_max w - 1) x in
  Some (w_set_heap (w_set_heap_max w (w_heap_max w - 1)) heap).

(** [tree[node].Freq = tree[n].Freq + tree[m].Freq; s->depth[node] = ...; tree[n].Dad = tree[m].Dad = node;]
    (the conditional re-reads one of [depth[n]], [depth[m]]: same value). *)
Definition c_new_node (t : tree) (w : work) (n m node : Z) : option (tree * work) :=
  let* fn := rd (fc t) n in
  let* fm := rd (fc t) m in
  let* t := c_set_fc t node (u16 (fn + fm)) in
  let* dn := rd (w_depth w) n in
  let* dm := rd (w_depth w) m in
  let* depth := wr (w_depth w) node (u8 ((if dn >=? dm then dn else dm) + 1)) in
  let* t := c_set_dl t m (u16 node) in
  let* t := c_set_dl t n (u16 node) in
  Some (t, w_set_depth w depth).

Definition c_merge_body (t : tree) (w : work) (node : Z) : option (tree * work) :=
  let* (n, w1) := c_pqremove t w in
  let* m := rd (w_heap w1) SMALLEST in
  let* w2 := c_store_removed w1 n in
  let* w2 := c_store_removed w2 m in
  let* (t3, w3) := c_new_node t w2 n m node in
  let* heap := wr (w_heap w3) SMALLEST node in
  let* w4 := c_pqdownheap t3 (w_set_heap w3 heap) SMALLEST in
  Some (t3, w4).

Fixpoint c_bt_merge (fuel : nat) (t : tree) (w : work) (node : Z) : option (tree * work * Z) :=
  match fuel with
  | O => None
  | S f =>
    let* (t, w) := c_merge_body t w node in
    if w_heap_len w >=? 2 then c_bt_merge f t w (node + 1) else Some (t, w, node + 1)
  end.

Definition c_build_tree (sd : stat_desc) (t : tree) (w : work) : option (tree * Z * work) :=
  let w := w_set_heap_len w 0 in
  let w := w_set_heap_max w HEAP_SIZE in
  let* (t, w, max_code) := c_bt_init (Z.to_nat (sd_elems sd)) (sd_elems sd) t w (-1) 0 in
  let* (t, w, max_code) := c_bt_force 2 sd t w max_code in
  let* w := c_bt_heapify (Z.to_nat (w_heap_len w / 2)) t w (w_heap_len w / 2) in
  let* (t, w, _) := c_bt_merge (Z.to_nat (w_heap_len w)) t w (sd_elems sd) in
  let w := w_set_heap_max w (w_heap_max w - 1) in
  let* top := rd (w_heap w) SMALLEST in
  let* heap := wr (w_heap w) (w_heap_max w) top in
  let w := w_set_heap w heap in
  let* (t, w) := c_gen_bitlen sd max_code t w in
  let* t := c_gen_codes t max_code (w_bl_count w) in
  Some (t, max_code, w).

(** ** scan_tree, build_bl_tree *)

Fixpoint c_scan_tree_loop (fuel : nat) (t : tree) (max_code : Z) (blf : list Z)
    (n prevlen nextlen count max_count min_count : Z) : option (list Z) :=
  match fuel with
  | O => if n <=? max_code then None else Some blf
  | S f =>
    if n <=? max_code then
      let curlen := nextlen in
      let* nextlen := rd (dl t) (n + 1) in
      let count := count + 1 in
      if (count <? max_count) && (curlen =? nextlen) then
        c_scan_tree_loop f t max_code blf (n + 1) prevlen nextlen count max_count min_count
      else
        let* blf :=
          (if count <? min_count then
             let* x := rd blf curlen in wr blf curlen (u16 (x + u16 count))
           else if negb (curlen =? 0) then
             let* blf := (if negb (curlen =? prevlen) then
                            let* x := rd blf curlen in wr blf curlen (u16 (x + 1))
                          else Some blf) in
             let* x := rd blf REP_3_6 in wr blf REP_3_6 (u16 (x + 1))
           else if count <=? 10 then
             let* x := rd blf REPZ_3_10 in wr blf REPZ_3_10 (u16 (x + 1))
           else
             let* x := rd blf REPZ_11_138 in wr blf REPZ_11_138 (u16 (x + 1))) in
        let '(max_count, min_count) :=
          if nextlen =? 0 then (138, 3)
          else if curlen =? nextlen then (6, 3)
          else (7, 4) in
        c_scan_tree_loop f t max_code blf (n + 1) curlen nextlen 0 max_count min_count
    else Some blf
  end.

Definition c_scan_tree (t : tree) (max_code : Z) (bl : tree) : option (tree * tree) :=
  (* v3: max_code + 1 (the guard store, the loop's n + 1) must not overflow *)
  let* _ := guard (max_code <? 2147483647) in
  let* nextlen := rd (dl t) 0 in
  let '(max_count, min_count) := if nextlen =? 0 then (138, 3) else (7, 4) in
  let* t := c_set_dl t (max_code + 1) 65535 in
  let* blf := c_scan_tree_loop (Z.to_nat (max_code + 1)) t max_code (fc bl) 0 (-1) nextlen 0 max_count min_count in
  Some (t, mkTree blf (dl bl)).

Fixpoint c_find_max_blindex (fuel : nat) (bl : tree) (i : Z) : option Z :=
  match fuel with
  | O => if i >=? 3 then None else Some i
  | S f =>
    if i >=? 3 then
      let* r := rd bl_order i in
      let* len := rd (dl bl) r in
      if negb (len =? 0) then Some i else c_find_max_blindex f bl (i - 1)
    else Some i
  end.

Definition c_build_bl_tree (s : tstate) : option (tstate * Z) :=
  let* (lt, bl) := c_scan_tree (tr_ltree s) (tr_lmax s) (tr_bltree s) in
  let* (dt, bl) := c_scan_tree (tr_dtree s) (tr_dmax s) bl in
  let* (bl, blmax, w) := c_build_tree static_bl_desc bl (tr_wk s) in
  let* max_blindex := c_find_max_blindex 20 bl (BL_CODES - 1) in
  let w := w_set_opt_len w (u64 (w_opt_len w + (3 * (max_blindex + 1) + 5 + 5 + 4))) in
  let s := set_ltree s lt in
  let s := set_dtree s dt in
  let s := set_bltree s bl in
  let s := set_blmax s blmax in
  Some (set_wk s w, max_blindex).

(** ** Bit output *)

(** [put_byte(s, c)]: [s->pending_buf[s->pending++] = (Bytef)(c);] *)
Definition c_put_byte (om : cout) (c : Z) : option cout :=
  let '(o, m) := om in
  let* b := wr (o_buf o) (o_pending o) (u8 c) in
  Some (mkOut b (o_pending o + 1) (o_bi_buf o) (o_bi_valid o) (o_bi_used o), upd_Znth (o_pending o) m true).

Definition c_put_short (om : cout) (w : Z) : option cout :=
  let* om := c_put_byte om (Z.land w 255) in
  c_put_byte om (Z.shiftr (u16 w) 8).

(** Guard: [0 <= bi_valid <= 16] (the shift amounts [bi_valid] and [Buf_size - bi_valid]). *)
Definition c_send_bits (om : cout) (value length : Z) : option cout :=
  let '(o, m) := om in
  let* _ := guard ((0 <=? o_bi_valid o) && (o_bi_valid o <=? Buf_size)) in
  if o_bi_valid o >? Buf_size - length then
    let bb := u16 (Z.lor (o_bi_buf o) (Z.shiftl (u16 value) (o_bi_valid o))) in
    let* (o', m') := c_put_short (set_bits o bb (o_bi_valid o), m) bb in
    Some (set_bits o' (Z.shiftr (u16 value) (Buf_size - o_bi_valid o)) (o_bi_valid o + length - Buf_size), m')
  else
    Some (set_bits o (u16 (Z.lor (o_bi_buf o) (Z.shiftl (u16 value) (o_bi_valid o)))) (o_bi_valid o + length), m).

(** [send_code(s, c, tree)] = [send_bits(s, tree[c].Code, tree[c].Len)]: the macro reads [Len] first. *)
Definition c_send_code (om : cout) (c : Z) (codes lens : list Z) : option cout :=
  let* len := rd lens c in
  let* code := rd codes c in
  c_send_bits om code len.

Definition c_bi_flush (om : cout) : option cout :=
  let '(o, m) := om in
  if o_bi_valid o =? 16 then
    let* (o, m) := c_put_short (o, m) (o_bi_buf o) in
    Some (set_bits o 0 0, m)
  else if o_bi_valid o >=? 8 then
    let* (o, m) := c_put_byte (o, m) (o_bi_buf o) in
    Some (set_bits o (Z.shiftr (o_bi_buf o) 8) (o_bi_valid o - 8), m)
  else Some (o, m).

Definition c_bi_windup (om : cout) : option cout :=
  let '(o, m) := om in
  let* _ := guard ((0 <=? o_bi_valid o) && (o_bi_valid o <=? 16)) in
  let* (o, m) := (if o_bi_valid o >? 8 then c_put_short (o, m) (o_bi_buf o)
                   else if o_bi_valid o >? 0 then c_put_byte (o, m) (o_bi_buf o)
                   else Some (o, m)) in
  Some (mkOut (o_buf o) (o_pending o) 0 0 (Z.land (o_bi_valid o - 1) 7 + 1), m).

(** ** send_tree, send_all_trees *)

(** [do { send_code(s, c, s->bl_tree); } while (--count != 0);] with fuel [Z.to_nat count]. *)
Fixpoint c_send_codes (fuel : nat) (om : cout) (c : Z) (codes lens : list Z) (count : Z) : option cout :=
  match fuel with
  | O => None
  | S f =>
    let* om := c_send_code om c codes lens in
    let count := count - 1 in
    if negb (count =? 0) then c_send_codes f om c codes lens count else Some om
  end.

Fixpoint c_send_tree_loop (fuel : nat) (t : tree) (max_code : Z) (blc bll : list Z) (om : cout)
    (n prevlen nextlen count max_count min_count : Z) : option cout :=
  match fuel with
  | O => if n <=? max_code then None else Some om
  | S f =>
    if n <=? max_code then
      let curlen := nextlen in
      let* nextlen := rd (dl t) (n + 1) in
      let count := count + 1 in
      if (count <? max_count) && (curlen =? nextlen) then
        c_send_tree_loop f t max_code blc bll om (n + 1) prevlen nextlen count max_count min_count
      else
        let* om :=
          (if count <? min_count then
             c_send_codes (Z.to_nat count) om curlen blc bll count
           else if negb (curlen =? 0) then
             let* (om, count) :=
               (if negb (curlen =? prevlen) then
                  let* om := c_send_code om curlen blc bll in Some (om, count - 1)
                else Some (om, count)) in
             let* om := c_send_code om REP_3_6 blc bll in
             c_send_bits om (count - 3) 2
           else if count <=? 10 then
             let* om := c_send_code om REPZ_3_10 blc bll in c_send_bits om (count - 3) 3
           else
             let* om := c_send_code om REPZ_11_138 blc bll in c_send_bits om (count - 11) 7) in
        let '(max_count, min_count) :=
          if nextlen =? 0 then (138, 3)
          else if curlen =? nextlen then (6, 3)
          else (7, 4) in
        c_send_tree_loop f t max_code blc bll om (n + 1) curlen nextlen 0 max_count min_count
    else Some om
  end.

Definition c_send_tree (om : cout) (t : tree) (max_code : Z) (bl : tree) : option cout :=
  (* v3: the loop's n + 1 must not overflow *)
  let* _ := guard (max_code <? 2147483647) in
  let* nextlen := rd (dl t) 0 in
  let '(max_count, min_count) := if nextlen =? 0 then (138, 3) else (7, 4) in
  c_send_tree_loop (Z.to_nat (max_code + 1)) t max_code (fc bl) (dl bl) om 0 (-1) nextlen 0 max_count min_count.

Fixpoint c_send_bl_lens (fuel : nat) (bl : tree) (om : cout) (rank blcodes : Z) : option cout :=
  match fuel with
  | O => if rank <? blcodes then None else Some om
  | S f =>
    if rank <? blcodes then
      let* r := rd bl_order rank in
      let* len := rd (dl bl) r in
      let* om := c_send_bits om len 3 in
      c_send_bl_lens f bl om (rank + 1) blcodes
    else Some om
  end.

(** Guard: the int parameters do not overflow in [lcodes - 257], [lcodes - 1], [dcodes - 1], [blcodes - 4]. *)
Definition c_send_all_trees (om : cout) (lt dt bl : tree) (lcodes dcodes blcodes : Z) : option cout :=
  let* _ := guard ((-2147483648 + 257 <=? lcodes) && (-2147483648 + 1 <=? dcodes) &&
                   (-2147483648 + 4 <=? blcodes)) in
  let* om := c_send_bits om (lcodes - 257) 5 in
  let* om := c_send_bits om (dcodes - 1) 5 in
  let* om := c_send_bits om (blcodes - 4) 4 in
  let* om := c_send_bl_lens 19 bl om 0 blcodes in
  let* om := c_send_tree om lt (lcodes - 1) bl in
  c_send_tree om dt (dcodes - 1) bl.

(** ** compress_block *)

(** [d_code(dist)] (deflate.h). *)
Definition c_d_code (dist : Z) : option Z :=
  if dist <? 256 then rd dist_code_tab dist else rd dist_code_tab (256 + Z.shiftr dist 7).

Definition c_send_symbol (om : cout) (lcodes llens dcodes dlens : list Z) (dist lc : Z) : option cout :=
  if dist =? 0 then c_send_code om lc lcodes llens
  else
    let* code := rd length_code_tab lc in
    let* om := c_send_code om (code + LITERALS + 1) lcodes llens in
    let* extra := rd extra_lbits code in
    let* om := (if negb (extra =? 0) then
                  let* bl := rd base_length_tab code in c_send_bits om (lc - bl) extra
                else Some om) in
    let dist := dist - 1 in
    let* code := c_d_code dist in
    let* om := c_send_code om code dcodes dlens in
    let* extra := rd extra_dbits code in
    if negb (extra =? 0) then
      let* bd := rd base_dist_tab code in c_send_bits om (dist - bd) extra
    else Some om.

(** The do-while loop of compress_block: the symbols are read from pending_buf at [lit_bufsize + sx] (sym_buf),
    checked for range and definedness. *)
Fixpoint c_compress_loop (fuel : nat) (lit_bufsize sym_next : Z) (lcodes llens dcodes dlens : list Z)
    (om : cout) (sx : Z) : option cout :=
  match fuel with
  | O => None
  | S f =>
    let* d0 := c_rd_pb om (lit_bufsize + sx) in
    let dist := Z.land d0 255 in
    let* d1 := c_rd_pb om (lit_bufsize + sx + 1) in
    let dist := dist + Z.shiftl (Z.land d1 255) 8 in
    let* lc := c_rd_pb om (lit_bufsize + sx + 2) in
    let sx := sx + 3 in
    let* om := c_send_symbol om lcodes llens dcodes dlens dist lc in
    if sx <? sym_next then c_compress_loop f lit_bufsize sym_next lcodes llens dcodes dlens om sx else Some om
  end.

Definition c_compress_block (om : cout) (lit_bufsize sym_next : Z) (lcodes llens dcodes dlens : list Z)
    : option cout :=
  let* om := (if negb (sym_next =? 0)
              then c_compress_loop (Z.to_nat sym_next) lit_bufsize sym_next lcodes llens dcodes dlens om 0
              else Some om) in
  c_send_code om END_BLOCK lcodes llens.

(** ** init_block, _tr_init, _tr_tally, detect_data_type *)

Fixpoint c_zero_fc (fuel : nat) (t : tree) (n hi : Z) : option tree :=
  match fuel with
  | O => if n <? hi then None else Some t
  | S f => if n <? hi then let* t := c_set_fc t n 0 in c_zero_fc f t (n + 1) hi else Some t
  end.

Definition c_init_block (s : tstate) : option tstate :=
  let* lt := c_zero_fc (Z.to_nat L_CODES) (tr_ltree s) 0 L_CODES in
  let s := set_ltree s lt in
  let* dt := c_zero_fc (Z.to_nat D_CODES) (tr_dtree s) 0 D_CODES in
  let s := set_dtree s dt in
  let* bt := c_zero_fc (Z.to_nat BL_CODES) (tr_bltree s) 0 BL_CODES in
  let s := set_bltree s bt in
  let* lt := c_set_fc (tr_ltree s) END_BLOCK 1 in
  let s := set_ltree s lt in
  let s := set_wk s (w_set_static_len (w_set_opt_len (tr_wk s) 0) 0) in
  Some (set_matches (set_sym_next s 0) 0).

(** _tr_init: the mask is unchanged. *)
Definition c_tr_init (cs : cstate) : option cstate :=
  let '(s, m) := cs in
  let o := tr_out s in
  let* s := c_init_block (set_out s (mkOut (o_buf o) (o_pending o) 0 0 0)) in
  Some (s, m).

(** [s->sym_buf[s->sym_next++] = (uch)b;] with sym_buf = pending_buf + lit_bufsize. *)
Definition c_put_sym (cs : cstate) (b : Z) : option cstate :=
  let '(s, m) := cs in
  let o := tr_out s in
  let i := tr_lit_bufsize s + tr_sym_next s in
  let* buf := wr (o_buf o) i (u8 b) in
  Some (set_sym_next (set_out s (mkOut buf (o_pending o) (o_bi_buf o) (o_bi_valid o) (o_bi_used o)))
                     (tr_sym_next s + 1),
        upd_Znth i m true).

Definition c_incr_lfreq (s : tstate) (i : Z) : option tstate :=
  let* x := rd (fc (tr_ltree s)) i in
  let* t := c_set_fc (tr_ltree s) i (u16 (x + 1)) in
  Some (set_ltree s t).
Definition c_incr_dfreq (s : tstate) (i : Z) : option tstate :=
  let* x := rd (fc (tr_dtree s)) i in
  let* t := c_set_fc (tr_dtree s) i (u16 (x + 1)) in
  Some (set_dtree s t).

Definition c_tr_tally (cs : cstate) (dist lc : Z) : option (cstate * bool) :=
  let* cs := c_put_sym cs dist in
  let* cs := c_put_sym cs (Z.shiftr dist 8) in
  let* (s, m) := c_put_sym cs lc in
  let* s :=
    (if dist =? 0 then c_incr_lfreq s lc
     else
       let s := set_matches s (u32 (tr_matches s + 1)) in
       let dist := dist - 1 in
       let* code := rd length_code_tab lc in
       let* s := c_incr_lfreq s (code + LITERALS + 1) in
       let* dc := c_d_code dist in
       c_incr_dfreq s dc) in
  Some ((s, m), tr_sym_next s =? tr_sym_end s).

Definition c_tr_tally_lit (cs : cstate) (c : Z) : option (cstate * bool) :=
  let cc := u8 c in
  let* cs := c_put_sym cs 0 in
  let* cs := c_put_sym cs 0 in
  let* (s, m) := c_put_sym cs cc in
  let* s := c_incr_lfreq s cc in
  Some ((s, m), tr_sym_next s =? tr_sym_end s).

Definition c_tr_tally_dist (cs : cstate) (distance length : Z) : option (cstate * bool) :=
  let len := u8 length in
  let dist := u16 distance in
  let* cs := c_put_sym cs dist in
  let* cs := c_put_sym cs (Z.shiftr dist 8) in
  let* (s, m) := c_put_sym cs len in
  let dist := u16 (dist - 1) in
  let* code := rd length_code_tab len in
  let* s := c_incr_lfreq s (code + LITERALS + 1) in
  let* dc := c_d_code dist in
  let* s := c_incr_dfreq s dc in
  Some ((s, m), tr_sym_next s =? tr_sym_end s).

(** The recursive call is written once (not in both branches of [block_listed n]): with concrete arguments,
    a duplicated call makes conversion checks exponential in the fuel. *)
Fixpoint c_dd_block (fuel : nat) (lf : list Z) (n : Z) : option bool :=
  match fuel with
  | O => if n <=? 31 then None else Some false
  | S f =>
    if n <=? 31 then
      let* hit := (if block_listed n then let* x := rd lf n in Some (negb (x =? 0)) else Some false) in
      if hit then Some true else c_dd_block f lf (n + 1)
    else Some false
  end.

Fixpoint c_dd_allow (fuel : nat) (lf : list Z) (n : Z) : option bool :=
  match fuel with
  | O => if n <? LITERALS then None else Some false
  | S f =>
    if n <? LITERALS then
      let* x := rd lf n in
      if negb (x =? 0) then Some true else c_dd_allow f lf (n + 1)
    else Some false
  end.

Definition c_detect_data_type (lf : list Z) : option Z :=
  let* b := c_dd_block 32 lf 0 in
  if b then Some Z_BINARY
  else
    let* x9 := rd lf 9 in
    if negb (x9 =? 0) then Some Z_TEXT
    else
      let* x10 := rd lf 10 in
      if negb (x10 =? 0) then Some Z_TEXT
      else
        let* x13 := rd lf 13 in
        if negb (x13 =? 0) then Some Z_TEXT
        else
          let* a := c_dd_allow 224 lf 32 in
          Some (if a then Z_TEXT else Z_BINARY).

(** ** _tr_stored_block, _tr_flush_bits, _tr_align, _tr_flush_block *)

(** The zmemcpy reads [buf[0 .. stored_len)] (the window bytes, given as a list) and writes
    [pending_buf[pending .. pending + stored_len)]. *)
Definition c_tr_stored_block (om : cout) (buf : list Z) (stored_len last : Z) : option cout :=
  let* om := c_send_bits om (Z.shiftl STORED_BLOCK 1 + last) 3 in
  let* om := c_bi_windup om in
  let* om := c_put_short om (u16 stored_len) in
  let* (o, m) := c_put_short om (u16 (Z.lnot stored_len)) in
  let* (b, m) :=
    (if negb (stored_len =? 0) then
       let* _ := guard ((0 <? stored_len) && (stored_len <=? Zlength buf)) in
       let* _ := guard (o_pending o + stored_len <=? Zlength (o_buf o)) in
       Some (copy_bytes (o_buf o) (o_pending o) (sublist 0 stored_len buf),
             mask_set_n (Z.to_nat stored_len) m (o_pending o))
     else Some (o_buf o, m)) in
  Some (mkOut b (o_pending o + stored_len) (o_bi_buf o) (o_bi_valid o) (o_bi_used o), m).

Definition c_tr_flush_bits (om : cout) : option cout := c_bi_flush om.

Definition c_tr_align (om : cout) : option cout :=
  let* om := c_send_bits om (Z.shiftl STATIC_TREES 1) 3 in
  let* om := c_send_code om END_BLOCK static_ltree_code static_ltree_len in
  c_bi_flush om.

(** Guards: [last <= 2^31 - 3] (static) and [last <= 2^31 - 5] (dynamic), so that [(STATIC_TREES<<1) + last] and
    [(DYN_TREES<<1) + last] do not overflow; a non-empty [buf] when the stored-block test is reached (v2). *)
Definition c_tr_flush_block (cs : cstate) (buf : option (list Z)) (stored_len last : Z)
    : option (cstate * block_kind) :=
  let '(s, m) := cs in
  let* (s, opt_lenb, static_lenb, max_blindex) :=
    (if tr_level s >? 0 then
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
     else Some (s, u64 (stored_len + 5), u64 (stored_len + 5), 0)) in
  let* (om, kind) :=
    (match buf with
     | Some b =>
       if u64 (stored_len + 4) <=? opt_lenb then
         (* `buf != NULL` is then evaluated: VST needs buf weakly valid, which a 0-byte buf does not give *)
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
