(** * The checked model of deflate.c, part 2: the compression functions

    deflate_stored, deflate_fast, deflate_slow (not FASTEST: max_insert_length = max_lazy_match, TOO_FAR = 4096),
    deflate_rle, deflate_huff.  Each [c_deflate_X s z flush] is [None] exactly when the C would be unsafe, else
    [Some (s', z', r)] with the state, the stream and the block_state the C returns.  Conventions: DModel1.v,
    DModel1b.v, CBase.v (one [let*] per memory access, in the C's order; unsigned arithmetic truncated with
    [u32] / [u64], signed [long] arithmetic of block_start guarded with [in_long]).

    The main [for (;;)] loops are [loop FUEL] over [(dstate * strm)]; their exit value is
    [(dstate * strm * option bstate)]: [Some r] when the function returns [r] from inside the loop (FLUSH_BLOCK,
    need_more), [None] at the [break]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DModel1b.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Helpers *)

(** pending_buf as a masked buffer, and a checked byte store into it ([s->pending_buf[i] = v]). *)
Definition d_pb (s : dstate) : mbuf := mkMB (o_buf (tr_out (d_tr s))) (d_pbm s).
Definition set_d_pb (s : dstate) (b : mbuf) : dstate :=
  let o := tr_out (d_tr s) in
  set_d_out s (mkOut (mb_val b) (o_pending o) (o_bi_buf o) (o_bi_valid o) (o_bi_used o), mb_def b).
Definition c_pb_wr (s : dstate) (i v : Z) : option dstate :=
  let* b := mb_wr (d_pb s) i v in Some (set_d_pb s b).

(** [s->bi_used = x] *)
Definition set_d_bi_used (s : dstate) (x : Z) : dstate :=
  let o := tr_out (d_tr s) in
  set_d_tr s (set_out (d_tr s) (mkOut (o_buf o) (o_pending o) (o_bi_buf o) (o_bi_valid o) x)).

(** [s->matches] (uInt, trees.c's part of the state) *)
Definition d_matches (s : dstate) : Z := tr_matches (d_tr s).
Definition set_d_matches (s : dstate) (x : Z) : dstate := set_d_tr s (set_matches (d_tr s) x).

(** [s->sym_next] *)
Definition d_sym_next (s : dstate) : Z := tr_sym_next (d_tr s).

(** [zmemcpy(b + dst, b + src, len)] within one buffer: memcpy's specification takes two separate slices, so the
    ranges must not overlap; then a checked read of the source and a checked write of the destination. *)
Definition mb_move (b : mbuf) (dst src len : Z) : option mbuf :=
  let* _ := guard ((dst + len <=? src) || (src + len <=? dst)) in
  let* bytes := mb_read b src len in
  mb_write b dst bytes.

(** The _tr_tally_lit / _tr_tally_dist macros on the state: returns the state and bflush. *)
Definition c_dtally_lit (s : dstate) (c : Z) : option (dstate * bool) :=
  let* (t, bf) := c_tr_tally_lit (d_trm s) c in Some (set_d_trm s t, bf).
Definition c_dtally_dist (s : dstate) (dist len : Z) : option (dstate * bool) :=
  let* (t, bf) := c_tr_tally_dist (d_trm s) dist len in Some (set_d_trm s t, bf).

(** [MAX_DIST(s)] as the C computes it: [s->w_size - MIN_LOOKAHEAD] in unsigned. *)
Definition max_dist (s : dstate) : Z := u32 (MAX_DIST s).

(** The exit value of the main loops: [Some r] = [return r], [None] = [break]. *)
Definition dexit := (dstate * strm * option bstate)%type.

(** [if (bflush) FLUSH_BLOCK(s, 0);] at the end of an iteration of a main loop. *)
Definition c_bflush (s : dstate) (z : strm) (bflush : bool) : option ((dstate * strm) + dexit) :=
  if bflush then
    let* (s, z, r) := c_flush_block s z 0 in
    match r with Some r => Some (inr (s, z, Some r)) | None => Some (inl (s, z)) end
  else Some (inl (s, z)).

(** The top of the main loops of deflate_fast / deflate_slow / deflate_rle:
    [if (need) { fill_window(s); if (need && flush == Z_NO_FLUSH) return need_more;
                 if (s->lookahead == 0) break; }]
    with [need s] = [s->lookahead < MIN_LOOKAHEAD] (fast, slow) or [s->lookahead <= MAX_MATCH] (rle). *)
Definition c_refill (need : dstate -> bool) (flush : Z) (s : dstate) (z : strm)
    : option ((dstate * strm) + dexit) :=
  if need s then
    let* (s, z) := c_fill_window s z in
    if need s && (flush =? Z_NO_FLUSH) then Some (inr (s, z, Some need_more))
    else if d_lookahead s =? 0 then Some (inr (s, z, None))
    else Some (inl (s, z))
  else Some (inl (s, z)).

(** The end of deflate_fast / slow / rle / huff after the loop (s->insert already set):
    [if (flush == Z_FINISH) { FLUSH_BLOCK(s, 1); return finish_done; }
     if (s->sym_next) FLUSH_BLOCK(s, 0); return block_done;] *)
Definition c_deflate_tail (s : dstate) (z : strm) (flush : Z) : option (dstate * strm * bstate) :=
  if flush =? Z_FINISH then
    let* (s, z, r) := c_flush_block s z 1 in
    match r with Some r => Some (s, z, r) | None => Some (s, z, finish_done) end
  else if negb (d_sym_next s =? 0) then
    let* (s, z, r) := c_flush_block s z 0 in
    match r with Some r => Some (s, z, r) | None => Some (s, z, block_done) end
  else Some (s, z, block_done).

(** ** deflate_stored(s, flush) *)

(** [((unsigned)s->bi_valid + 42) >> 3]: the bytes of a stored block header. *)
Definition stored_hdr (s : dstate) : Z := Z.shiftr (u32 (u32 (o_bi_valid (tr_out (d_tr s))) + 42)) 3.

(** One iteration of the do-while loop of the first phase (direct copy to next_out); [last] is 0 on entry.
    Exit: (s, z, last) ([break] leaves with last = 0).  The three comparisons of [len] with
    [left + strm->avail_in] add in 64 bits (patch F9: [(z_size_t)left + avail_in]). *)
Definition ds_body (flush min_block : Z) (a : dstate * strm) : option ((dstate * strm) + (dstate * strm * Z)) :=
  let '(s, z) := a in
  let len := MAX_STORED in
  let have := stored_hdr s in
  if z_avail_out z <? have then Some (inr (s, z, 0)) else
  let have := u32 (z_avail_out z - have) in
  let* _ := guard (in_long (d_strstart s - d_block_start s)) in
  let left := u32 (d_strstart s - d_block_start s) in
  let len := if len >? u64 (left + z_avail_in z) then u32 (left + z_avail_in z) else len in
  let len := if len >? have then have else len in
  if (len <? min_block) &&
     (((len =? 0) && negb (flush =? Z_FINISH)) || (flush =? Z_NO_FLUSH) ||
      negb (len =? u64 (left + z_avail_in z)))
  then Some (inr (s, z, 0)) else
  let last := if (flush =? Z_FINISH) && (len =? u64 (left + z_avail_in z)) then 1 else 0 in
  (* _tr_stored_block(s, (char * )0, 0L, last) *)
  let* o := c_tr_stored_block (d_out s) [] 0 last in
  let s := set_d_out s o in
  (* the length bytes of the dummy block *)
  let* s := c_pb_wr s (u64 (d_pending s - 4)) (u8 len) in
  let* s := c_pb_wr s (u64 (d_pending s - 3)) (u8 (Z.shiftr len 8)) in
  let* s := c_pb_wr s (u64 (d_pending s - 2)) (u8 (u32 (Z.lnot len))) in
  let* s := c_pb_wr s (u64 (d_pending s - 1)) (u8 (Z.shiftr (u32 (Z.lnot len)) 8)) in
  let* (s, z) := c_flush_pending s z in
  (* copy from the window *)
  let* (s, z, len) :=
    (if left =? 0 then Some (s, z, len) else
     let left := if left >? len then len else left in
     let* bytes := mb_read (d_window s) (d_block_start s) left in
     let* z := out_put z bytes in
     let z := set_z_avail_out z (u32 (z_avail_out z - left)) in
     let z := set_z_total_out z (u64 (z_total_out z + left)) in
     let* _ := guard (in_long (d_block_start s + left)) in
     let s := set_d_block_start s (d_block_start s + left) in
     Some (s, z, u32 (len - left))) in
  (* copy from next_in *)
  let* z :=
    (if len =? 0 then Some z else
     let* (z, data) := c_read_buf s z len in
     let* _ := guard (Zlength data =? len) in
     let* z := out_put z data in
     let z := set_z_avail_out z (u32 (z_avail_out z - len)) in
     Some (set_z_total_out z (u64 (z_total_out z + len)))) in
  if last =? 0 then Some (inl (s, z)) else Some (inr (s, z, last)).

(** [s->insert += MIN(n, s->w_size - s->insert)] *)
Definition add_insert (s : dstate) (n : Z) : dstate :=
  let m := u32 (d_w_size s - d_insert s) in
  set_d_insert s (u32 (d_insert s + (if n >? m then m else n))).

(** [if (s->matches < 2) s->matches++;] and [if (s->insert > s->strstart) s->insert = s->strstart;] *)
Definition incr_matches (s : dstate) : dstate :=
  if d_matches s <? 2 then set_d_matches s (u32 (d_matches s + 1)) else s.
Definition clamp_insert (s : dstate) : dstate :=
  if d_insert s >? d_strstart s then set_d_insert s (d_strstart s) else s.

(** [if (s->high_water < s->strstart) s->high_water = s->strstart;] *)
Definition upd_high_water (s : dstate) : dstate :=
  if d_high_water s <? d_strstart s then set_d_high_water s (d_strstart s) else s.

(** The window update after the first phase ([used] input bytes copied directly). *)
Definition c_ds_window (s : dstate) (z : strm) (used : Z) : option dstate :=
  if used =? 0 then Some s else
  let* s :=
    (if used >=? d_w_size s then
       let s := set_d_matches s 2 in
       let* bytes := rds (z_in z) (z_next_in z - d_w_size s) (d_w_size s) in
       let* win := mb_write (d_window s) 0 bytes in
       let s := set_d_window s win in
       let s := set_d_strstart s (d_w_size s) in
       Some (set_d_insert s (d_strstart s))
     else
       let* s :=
         (if u64 (d_window_size s - d_strstart s) <=? used then
            let s := set_d_strstart s (u32 (d_strstart s - d_w_size s)) in
            let* win := mb_move (d_window s) 0 (d_w_size s) (d_strstart s) in
            let s := set_d_window s win in
            let s := incr_matches s in
            Some (clamp_insert s)
          else Some s) in
       let* bytes := rds (z_in z) (z_next_in z - used) used in
       let* win := mb_write (d_window s) (d_strstart s) bytes in
       let s := set_d_window s win in
       let s := set_d_strstart s (u32 (d_strstart s + used)) in
       Some (add_insert s used)) in
  Some (set_d_block_start s (d_strstart s)).

Definition c_deflate_stored (s : dstate) (z : strm) (flush : Z) : option (dstate * strm * bstate) :=
  let min_block := u32 (let a := u64 (d_pending_buf_size s - 5) in if a >? d_w_size s then d_w_size s else a) in
  let used := z_avail_in z in
  let* (s, z, last) := loop FUEL (ds_body flush min_block) (s, z) in
  let used := u32 (used - z_avail_in z) in
  let* s := c_ds_window s z used in
  let s := upd_high_water s in
  if negb (last =? 0) then Some (set_d_bi_used s 8, z, finish_done) else
  if negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH) && (z_avail_in z =? 0) &&
     (d_strstart s =? d_block_start s)
  then Some (s, z, block_done) else
  (* fill the window with any remaining input *)
  let have := u32 (u64 (d_window_size s - d_strstart s)) in
  let* (s, have) :=
    (if (z_avail_in z >? have) && (d_block_start s >=? d_w_size s) then
       let s := set_d_block_start s (d_block_start s - d_w_size s) in
       let s := set_d_strstart s (u32 (d_strstart s - d_w_size s)) in
       let* win := mb_move (d_window s) 0 (d_w_size s) (d_strstart s) in
       let s := set_d_window s win in
       let s := incr_matches s in
       let have := u32 (have + d_w_size s) in
       Some (clamp_insert s, have)
     else Some (s, have)) in
  let have := if have >? z_avail_in z then z_avail_in z else have in
  let* (s, z) :=
    (if have =? 0 then Some (s, z) else
     let* (z, data) := c_read_buf s z have in
     let* win := mb_write (d_window s) (d_strstart s) data in
     let s := set_d_window s win in
     let s := set_d_strstart s (u32 (d_strstart s + have)) in
     Some (add_insert s have, z)) in
  let s := upd_high_water s in
  (* a stored block from the window into pending *)
  let have := stored_hdr s in
  let have := u32 (let a := u64 (d_pending_buf_size s - have) in if a >? MAX_STORED then MAX_STORED else a) in
  let min_block := if have >? d_w_size s then d_w_size s else have in
  let* _ := guard (in_long (d_strstart s - d_block_start s)) in
  let left := u32 (d_strstart s - d_block_start s) in
  let* (s, z, last) :=
    (if (left >=? min_block) ||
        ((negb (left =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH) &&
         (z_avail_in z =? 0) && (left <=? have)) then
       let len := if left >? have then have else left in
       let last := if (flush =? Z_FINISH) && (z_avail_in z =? 0) && (len =? left) then 1 else 0 in
       let* buf := (if len =? 0 then Some [] else mb_read (d_window s) (d_block_start s) len) in
       let* o := c_tr_stored_block (d_out s) buf len last in
       let s := set_d_out s o in
       let* _ := guard (in_long (d_block_start s + len)) in
       let s := set_d_block_start s (d_block_start s + len) in
       let* (s, z) := c_flush_pending s z in
       Some (s, z, last)
     else Some (s, z, 0)) in
  if last =? 0 then Some (s, z, need_more) else Some (set_d_bi_used s 8, z, finish_started).

(** ** deflate_fast(s, flush) *)

(** [do { s->strstart++; INSERT_STRING(s, s->strstart, hash_head); } while (--s->match_length != 0);] *)
Definition df_insert_body (s : dstate) : option (dstate + dstate) :=
  let s := set_d_strstart s (u32 (d_strstart s + 1)) in
  let* (s, _) := c_insert_string s (d_strstart s) in
  let s := set_d_match_length s (u32 (d_match_length s - 1)) in
  if d_match_length s =? 0 then Some (inr s) else Some (inl s).

(** [hash_head = NIL; if (s->lookahead >= MIN_MATCH) INSERT_STRING(s, s->strstart, hash_head);] *)
Definition c_insert_head (s : dstate) : option (dstate * Z) :=
  if d_lookahead s >=? MIN_MATCH then c_insert_string s (d_strstart s) else Some (s, NIL).

(** One iteration after the refill. *)
Definition df_step (s : dstate) (z : strm) : option ((dstate * strm) + dexit) :=
  let* (s, hash_head) := c_insert_head s in
  let* s :=
    (if negb (hash_head =? NIL) && (u32 (d_strstart s - hash_head) <=? max_dist s) then
       let* (s, ml) := c_longest_match s hash_head in Some (set_d_match_length s ml)
     else Some s) in
  let* (s, bflush) :=
    (if d_match_length s >=? MIN_MATCH then
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
         let* _ := guard (d_hash_shift s <? 32) in   (* the shift of UPDATE_HASH (v2) *)
         let* c1 := mb_rd (d_window s) (u32 (d_strstart s + 1)) in
         Some (set_d_ins_h s (update_hash s (d_ins_h s) c1), bflush)
     else
       let* c := mb_rd (d_window s) (d_strstart s) in
       let* (s, bflush) := c_dtally_lit s c in
       let s := set_d_lookahead s (u32 (d_lookahead s - 1)) in
       Some (set_d_strstart s (u32 (d_strstart s + 1)), bflush)) in
  c_bflush s z bflush.

Definition need_min_lookahead (s : dstate) : bool := d_lookahead s <? MIN_LOOKAHEAD.

Definition df_body (flush : Z) (a : dstate * strm) : option ((dstate * strm) + dexit) :=
  let '(s, z) := a in
  let* r := c_refill need_min_lookahead flush s z in
  match r with
  | inr e => Some (inr e)
  | inl (s, z) => df_step s z
  end.

(** [s->insert = s->strstart < MIN_MATCH-1 ? s->strstart : MIN_MATCH-1;] *)
Definition set_insert_end (s : dstate) : dstate :=
  set_d_insert s (if d_strstart s <? MIN_MATCH - 1 then d_strstart s else MIN_MATCH - 1).

Definition c_deflate_fast (s : dstate) (z : strm) (flush : Z) : option (dstate * strm * bstate) :=
  let* (s, z, r) := loop FUEL (df_body flush) (s, z) in
  match r with
  | Some r => Some (s, z, r)
  | None => c_deflate_tail (set_insert_end s) z flush
  end.

(** ** deflate_slow(s, flush) *)

(** [do { if (++s->strstart <= max_insert) INSERT_STRING(s, s->strstart, hash_head); }
     while (--s->prev_length != 0);] *)
Definition dsl_insert_body (max_insert : Z) (s : dstate) : option (dstate + dstate) :=
  let s := set_d_strstart s (u32 (d_strstart s + 1)) in
  let* s :=
    (if d_strstart s <=? max_insert then let* (s, _) := c_insert_string s (d_strstart s) in Some s
     else Some s) in
  let s := set_d_prev_length s (u32 (d_prev_length s - 1)) in
  if d_prev_length s =? 0 then Some (inr s) else Some (inl s).

Definition dsl_step (s : dstate) (z : strm) : option ((dstate * strm) + dexit) :=
  let* (s, hash_head) := c_insert_head s in
  let s := set_d_prev_length s (d_match_length s) in
  let s := set_d_prev_match s (d_match_start s) in
  let s := set_d_match_length s (MIN_MATCH - 1) in
  let* s :=
    (if negb (hash_head =? NIL) && (d_prev_length s <? d_max_lazy_match s) &&
        (u32 (d_strstart s - hash_head) <=? max_dist s) then
       let* (s, ml) := c_longest_match s hash_head in
       let s := set_d_match_length s ml in
       if (d_match_length s <=? 5) &&
          ((d_strategy s =? Z_FILTERED) ||
           ((d_match_length s =? MIN_MATCH) && (u32 (d_strstart s - d_match_start s) >? TOO_FAR)))
       then Some (set_d_match_length s (MIN_MATCH - 1))
       else Some s
     else Some s) in
  if (d_prev_length s >=? MIN_MATCH) && (d_match_length s <=? d_prev_length s) then
    let max_insert := u32 (d_strstart s + d_lookahead s - MIN_MATCH) in
    let* (s, bflush) := c_dtally_dist s (u32 (d_strstart s - 1 - d_prev_match s))
                                        (u32 (d_prev_length s - MIN_MATCH)) in
    let s := set_d_lookahead s (u32 (d_lookahead s - u32 (d_prev_length s - 1))) in
    let s := set_d_prev_length s (u32 (d_prev_length s - 2)) in
    let* s := loop FUEL (dsl_insert_body max_insert) s in
    let s := set_d_match_available s 0 in
    let s := set_d_match_length s (MIN_MATCH - 1) in
    let s := set_d_strstart s (u32 (d_strstart s + 1)) in
    c_bflush s z bflush
  else if negb (d_match_available s =? 0) then
    let* c := mb_rd (d_window s) (u32 (d_strstart s - 1)) in
    let* (s, bflush) := c_dtally_lit s c in
    let* (s, z) := (if bflush then c_flush_block_only s z 0 else Some (s, z)) in
    let s := set_d_strstart s (u32 (d_strstart s + 1)) in
    let s := set_d_lookahead s (u32 (d_lookahead s - 1)) in
    if z_avail_out z =? 0 then Some (inr (s, z, Some need_more)) else Some (inl (s, z))
  else
    let s := set_d_match_available s 1 in
    let s := set_d_strstart s (u32 (d_strstart s + 1)) in
    Some (inl (set_d_lookahead s (u32 (d_lookahead s - 1)), z)).

Definition dsl_body (flush : Z) (a : dstate * strm) : option ((dstate * strm) + dexit) :=
  let '(s, z) := a in
  let* r := c_refill need_min_lookahead flush s z in
  match r with
  | inr e => Some (inr e)
  | inl (s, z) => dsl_step s z
  end.

Definition c_deflate_slow (s : dstate) (z : strm) (flush : Z) : option (dstate * strm * bstate) :=
  let* (s, z, r) := loop FUEL (dsl_body flush) (s, z) in
  match r with
  | Some r => Some (s, z, r)
  | None =>
    let* s :=
      (if negb (d_match_available s =? 0) then
         let* c := mb_rd (d_window s) (u32 (d_strstart s - 1)) in
         let* (s, _) := c_dtally_lit s c in
         Some (set_d_match_available s 0)
       else Some s) in
    c_deflate_tail (set_insert_end s) z flush
  end.

(** ** deflate_rle(s, flush) *)

(** The run scan [do {} while (prev == *++scan && ... (8 times) && scan < strend);], state (scan, k) with k the
    comparisons made in the current group of 8 (scan, strend: offsets in the window); returns scan.  The pointer
    comparison [scan < strend] needs both pointers within the window or one past it (VST's test_order_ptrs:
    weak_valid_pointer); scan was just read, so the guard is on strend. *)
Definition rle_cmp_body (s : dstate) (prev strend : Z) (a : Z * Z) : option ((Z * Z) + Z) :=
  let '(scan, k) := a in
  let scan := scan + 1 in
  let* c := mb_rd (d_window s) scan in
  if negb (prev =? c) then Some (inr scan)
  else if k =? 7 then
    let* _ := guard (strend <=? Zlength (mb_val (d_window s))) in
    if scan <? strend then Some (inl (scan, 0)) else Some (inr scan)
  else Some (inl (scan, k + 1)).

Definition rle_step (s : dstate) (z : strm) : option ((dstate * strm) + dexit) :=
  let s := set_d_match_length s 0 in
  let* s :=
    (if (d_lookahead s >=? MIN_MATCH) && (d_strstart s >? 0) then
       let scan := d_strstart s - 1 in
       let* prev := mb_rd (d_window s) scan in
       let* c1 := mb_rd (d_window s) (scan + 1) in
       if negb (prev =? c1) then Some s else
       let* c2 := mb_rd (d_window s) (scan + 2) in
       if negb (prev =? c2) then Some s else
       let* c3 := mb_rd (d_window s) (scan + 3) in
       if negb (prev =? c3) then Some s else
       let strend := d_strstart s + MAX_MATCH in
       let* scan := loop FUEL (rle_cmp_body s prev strend) (scan + 3, 0) in
       let s := set_d_match_length s (u32 (MAX_MATCH - u32 (strend - scan))) in
       Some (if d_match_length s >? d_lookahead s then set_d_match_length s (d_lookahead s) else s)
     else Some s) in
  let* (s, bflush) :=
    (if d_match_length s >=? MIN_MATCH then
       let* (s, bflush) := c_dtally_dist s 1 (u32 (d_match_length s - MIN_MATCH)) in
       let s := set_d_lookahead s (u32 (d_lookahead s - d_match_length s)) in
       let s := set_d_strstart s (u32 (d_strstart s + d_match_length s)) in
       Some (set_d_match_length s 0, bflush)
     else
       let* c := mb_rd (d_window s) (d_strstart s) in
       let* (s, bflush) := c_dtally_lit s c in
       let s := set_d_lookahead s (u32 (d_lookahead s - 1)) in
       Some (set_d_strstart s (u32 (d_strstart s + 1)), bflush)) in
  c_bflush s z bflush.

Definition need_rle (s : dstate) : bool := d_lookahead s <=? MAX_MATCH.

Definition rle_body (flush : Z) (a : dstate * strm) : option ((dstate * strm) + dexit) :=
  let '(s, z) := a in
  let* r := c_refill need_rle flush s z in
  match r with
  | inr e => Some (inr e)
  | inl (s, z) => rle_step s z
  end.

Definition c_deflate_rle (s : dstate) (z : strm) (flush : Z) : option (dstate * strm * bstate) :=
  let* (s, z, r) := loop FUEL (rle_body flush) (s, z) in
  match r with
  | Some r => Some (s, z, r)
  | None => c_deflate_tail (set_d_insert s 0) z flush
  end.

(** ** deflate_huff(s, flush) *)

Definition huff_body (flush : Z) (a : dstate * strm) : option ((dstate * strm) + dexit) :=
  let '(s, z) := a in
  let* r :=
    (if d_lookahead s =? 0 then
       let* (s, z) := c_fill_window s z in
       if d_lookahead s =? 0 then
         (if flush =? Z_NO_FLUSH then Some (inr (s, z, Some need_more)) else Some (inr (s, z, None)))
       else Some (inl (s, z))
     else Some (inl (s, z))) in
  match r with
  | inr e => Some (inr e)
  | inl (s, z) =>
    let s := set_d_match_length s 0 in
    let* c := mb_rd (d_window s) (d_strstart s) in
    let* (s, bflush) := c_dtally_lit s c in
    let s := set_d_lookahead s (u32 (d_lookahead s - 1)) in
    let s := set_d_strstart s (u32 (d_strstart s + 1)) in
    c_bflush s z bflush
  end.

Definition c_deflate_huff (s : dstate) (z : strm) (flush : Z) : option (dstate * strm * bstate) :=
  let* (s, z, r) := loop FUEL (huff_body flush) (s, z) in
  match r with
  | Some r => Some (s, z, r)
  | None => c_deflate_tail (set_d_insert s 0) z flush
  end.

(** ** Guards that are not memory-access checks

    - [in_long (strstart - block_start)] (deflate_stored, both computations of [left]): the C subtraction is in
      [long] (uInt converted to long), so it must not overflow; block_start is otherwise unconstrained here.
    - [in_long (block_start + left)] and [in_long (block_start + len)] (deflate_stored): [s->block_start += ...]
      is long arithmetic.  ([s->block_start -= s->w_size] in the second phase needs none: it runs only when
      block_start >= w_size >= 0.)
    - [Zlength data = len] after [read_buf(s->strm, s->strm->next_out, len)] (deflate_stored, first phase): the C
      advances next_out by len, while the model's next_out is the start plus [Zlength z_out]; the two agree
      only when read_buf copies all len bytes, which holds since len <= avail_in there (len <= left + avail_in
      before [len -= left]).  Never fails on a run of the C; it keeps [z_out] an exact image of next_out.
    - [mb_move]: the two ranges of [zmemcpy(s->window, s->window + s->w_size, s->strstart)] are disjoint
      (memcpy's specification, zutil/Libc.v, takes two separate slices).  Implied by the source check when the
      window has 2 * w_size bytes; stated so the model does not depend on that invariant.
    - [strend <= Zlength window] at [scan < strend] (deflate_rle): a pointer order comparison in VST requires
      both pointers weakly valid (within the object or one past it).

    Everything else is either a checked access ([mb_rd], [mb_read], [mb_write], [mb_wr], [rds], [out_put]) or
    inside the callees' checked models. *)
