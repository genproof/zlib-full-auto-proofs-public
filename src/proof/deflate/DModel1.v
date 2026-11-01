(** * The checked model of deflate.c, part 1: input, window, hash chains, matching

    read_buf, slide_hash, fill_window, longest_match (not FASTEST), the macros UPDATE_HASH, INSERT_STRING,
    CLEAR_HASH, and lm_init.  Conventions: DState.v (the state), DLoop.v (loops, [rds], [in_long]), CBase.v (the
    monad, masked buffers).  Each [let*] is one memory access of the C code, in the C's order.  Unsigned C
    arithmetic is truncated ([u32] for unsigned/uInt, [u64] for ulg/uLong/size_t); signed arithmetic that the C
    types do not bound is guarded ([in_int], [in_long]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DState Zlib.proof.deflate.DLoop.
Require Zlib.proof.adler32.Model Zlib.proof.crc32.Model.
Import ListNotations.
Local Open Scope Z_scope.

(** ** read_buf(strm, buf, size): returns the stream and the bytes copied to buf (the caller puts them where buf
    points: the window or next_out).  [adler32] and [crc32] by their shared specifications. *)
Definition c_read_buf (s : dstate) (z : strm) (size : Z) : option (strm * list Z) :=
  let len := if z_avail_in z >? size then size else z_avail_in z in
  if len =? 0 then Some (z, []) else
  let z := set_z_avail_in z (z_avail_in z - len) in
  let* data := rds (z_in z) (z_next_in z) len in
  let z := if d_wrap s =? 1 then set_z_adler z (Zlib.proof.adler32.Model.adler32_z_val (z_adler z) data)
           else if d_wrap s =? 2 then set_z_adler z (Zlib.proof.crc32.Model.ref_crc32 (z_adler z) data)
           else z in
  let z := set_z_next_in z (z_next_in z + len) in
  let z := set_z_total_in z (u64 (z_total_in z + len)) in
  Some (z, data).

(** ** UPDATE_HASH, INSERT_STRING, CLEAR_HASH *)
Definition update_hash (s : dstate) (h c : Z) : Z :=
  u32 (Z.land (Z.lxor (u32 (Z.shiftl h (d_hash_shift s))) c) (d_hash_mask s)).

(** [INSERT_STRING(s, str, match_head)]: returns the state and match_head. *)
Definition c_insert_string (s : dstate) (str : Z) : option (dstate * Z) :=
  let* _ := guard (d_hash_shift s <? 32) in   (* the shift of UPDATE_HASH (v2) *)
  let* c := mb_rd (d_window s) (u32 (str + (MIN_MATCH - 1))) in
  let s := set_d_ins_h s (update_hash s (d_ins_h s) c) in
  let* h := rd (d_head s) (d_ins_h s) in
  let* prev := wr (d_prev s) (Z.land str (d_w_mask s)) h in
  let s := set_d_prev s prev in
  let* head := wr (d_head s) (d_ins_h s) (u16 str) in
  Some (set_d_head s head, h).

(** [CLEAR_HASH(s)]: head[hash_size - 1] = NIL; zmemzero(head, (hash_size - 1) * 2); slid = 0. *)
Definition c_clear_hash (s : dstate) : option dstate :=
  let* head := wr (d_head s) (u32 (d_hash_size s - 1)) NIL in
  let* _ := guard ((1 <=? d_hash_size s) && (Zlength head =? d_hash_size s)) in
  Some (set_d_slid (set_d_head s (repeat 0 (Z.to_nat (d_hash_size s)))) 0).

(** ** slide_hash(s) *)
Definition slide_entry (wsize m : Z) : Z := if m >=? wsize then m - wsize else NIL.

Definition c_slide_hash (s : dstate) : option dstate :=
  let wsize := d_w_size s in
  let* _ := guard ((1 <=? d_hash_size s) && (Zlength (d_head s) =? d_hash_size s) &&
                   (1 <=? wsize) && (Zlength (d_prev s) =? wsize)) in
  let s := set_d_head s (map (slide_entry wsize) (d_head s)) in
  let s := set_d_prev s (map (slide_entry wsize) (d_prev s)) in
  Some (set_d_slid s 1).

(** ** fill_window(s) *)

(** The hash insertion of fill_window: [while (s->insert) { ... }], state (s, str). *)
Definition fw_insert_body (a : dstate * Z) : option ((dstate * Z) + dstate) :=
  let '(s, str) := a in
  if d_insert s =? 0 then Some (inr s) else
  let* _ := guard (d_hash_shift s <? 32) in   (* the shift of UPDATE_HASH (v2) *)
  let* c := mb_rd (d_window s) (u32 (str + MIN_MATCH - 1)) in
  let s := set_d_ins_h s (update_hash s (d_ins_h s) c) in
  let* h := rd (d_head s) (d_ins_h s) in
  let* prev := wr (d_prev s) (Z.land str (d_w_mask s)) h in
  let s := set_d_prev s prev in
  let* head := wr (d_head s) (d_ins_h s) (u16 str) in
  let s := set_d_head s head in
  let str := u32 (str + 1) in
  let s := set_d_insert s (u32 (d_insert s - 1)) in
  if u32 (d_lookahead s + d_insert s) <? MIN_MATCH then Some (inr s) else Some (inl (s, str)).

(** [if (s->lookahead + s->insert >= MIN_MATCH) { ... }] *)
Definition c_fw_insert (s : dstate) : option dstate :=
  if u32 (d_lookahead s + d_insert s) >=? MIN_MATCH then
    let str := u32 (d_strstart s - d_insert s) in
    let* c0 := mb_rd (d_window s) str in
    let s := set_d_ins_h s c0 in
    let* _ := guard (d_hash_shift s <? 32) in   (* the shift of UPDATE_HASH (v2) *)
    let* c1 := mb_rd (d_window s) (u32 (str + 1)) in
    let s := set_d_ins_h s (update_hash s (d_ins_h s) c1) in
    loop FUEL fw_insert_body (s, str)
  else Some s.

(** The slide of fill_window: [if (s->strstart >= wsize + MAX_DIST(s)) { ... }]; returns the state and [more]. *)
Definition c_fw_slide (s : dstate) (more : Z) : option (dstate * Z) :=
  let wsize := d_w_size s in
  if d_strstart s >=? u32 (wsize + u32 (d_w_size s - MIN_LOOKAHEAD)) then
    (* the zmemcpy's source and destination must not overlap (v2) *)
    let* _ := guard (u32 (wsize - more) <=? wsize) in
    let* src := mb_read (d_window s) wsize (u32 (wsize - more)) in
    let* win := mb_write (d_window s) 0 src in
    let s := set_d_window s win in
    let s := set_d_match_start s (u32 (d_match_start s - wsize)) in
    let s := set_d_strstart s (u32 (d_strstart s - wsize)) in
    let* _ := guard (in_long (d_block_start s - wsize)) in
    let s := set_d_block_start s (d_block_start s - wsize) in
    let s := if d_insert s >? d_strstart s then set_d_insert s (d_strstart s) else s in
    let* s := c_slide_hash s in
    Some (s, u32 (more + wsize))
  else Some (s, more).

(** One iteration of the do-while loop of fill_window. *)
Definition fw_body (a : dstate * strm) : option ((dstate * strm) + (dstate * strm)) :=
  let '(s, z) := a in
  let more := u32 (d_window_size s - d_lookahead s - d_strstart s) in
  let* (s, more) := c_fw_slide s more in
  if z_avail_in z =? 0 then Some (inr (s, z)) else
  let* (z, data) := c_read_buf s z more in
  let* win := mb_write (d_window s) (d_strstart s + d_lookahead s) data in
  let s := set_d_window s win in
  let s := set_d_lookahead s (u32 (d_lookahead s + Zlength data)) in
  let* s := c_fw_insert s in
  if (d_lookahead s <? MIN_LOOKAHEAD) && negb (z_avail_in z =? 0) then Some (inl (s, z)) else Some (inr (s, z)).

(** The WIN_INIT zeroing after the loop. *)
Definition c_fw_high_water (s : dstate) : option dstate :=
  if d_high_water s <? d_window_size s then
    let curr := d_strstart s + d_lookahead s in
    if d_high_water s <? curr then
      let init := u64 (d_window_size s - curr) in
      let init := if init >? WIN_INIT then WIN_INIT else init in
      let* win := mb_write (d_window s) curr (repeat 0 (Z.to_nat init)) in
      Some (set_d_high_water (set_d_window s win) (curr + init))
    else if d_high_water s <? curr + WIN_INIT then
      let init := u64 (curr + WIN_INIT - d_high_water s) in
      let init := if init >? u64 (d_window_size s - d_high_water s)
                  then u64 (d_window_size s - d_high_water s) else init in
      let* win := mb_write (d_window s) (d_high_water s) (repeat 0 (Z.to_nat (u32 init))) in
      Some (set_d_high_water (set_d_window s win) (u64 (d_high_water s + init)))
    else Some s
  else Some s.

Definition c_fill_window (s : dstate) (z : strm) : option (dstate * strm) :=
  let* (s, z) := loop FUEL fw_body (s, z) in
  let* s := c_fw_high_water s in
  Some (s, z).

(** ** longest_match(s, cur_match) (not FASTEST, not UNALIGNED_OK) *)

(** The inner comparison loop [do {} while ( *++scan == *++match && ... (8 times) && scan < strend);]:
    state (scan, match, k) with k the number of comparisons made in the current group of 8; returns scan. *)
Definition lm_cmp_body (s : dstate) (strend : Z) (a : Z * Z * Z) : option ((Z * Z * Z) + Z) :=
  let '(scan, mt, k) := a in
  let scan := scan + 1 in
  let mt := mt + 1 in
  let* c1 := mb_rd (d_window s) scan in
  let* c2 := mb_rd (d_window s) mt in
  if negb (c1 =? c2) then Some (inr scan)
  else if k =? 7 then (if scan <? strend then Some (inl (scan, mt, 0)) else Some (inr scan))
  else Some (inl (scan, mt, k + 1)).

(** The state of the chain loop: cur_match, chain_length, best_len, scan_end1, scan_end, and the state (for
    match_start). *)
Record lm_st := mkLM { lm_cur : Z; lm_chain : Z; lm_best : Z; lm_end1 : Z; lm_end : Z; lm_s : dstate }.

(** One iteration of [do { ... } while ((cur_match = prev[cur_match & wmask]) > limit && --chain_length != 0);]
    with [nice_match] and [limit] fixed; the exit value is (best_len, state). *)
Definition lm_body (nice limit : Z) (a : lm_st) : option (lm_st + (Z * dstate)) :=
  let s := lm_s a in
  let scan := d_strstart s in
  let strend := d_strstart s + MAX_MATCH in
  let cur := lm_cur a in
  let best := lm_best a in
  (* the loop test, after the body or after a continue *)
  let next (a : lm_st) : option (lm_st + (Z * dstate)) :=
    let s := lm_s a in
    let* cur' := rd (d_prev s) (Z.land (lm_cur a) (d_w_mask s)) in
    if cur' >? limit then
      let chain := u32 (lm_chain a - 1) in
      if chain =? 0 then Some (inr (lm_best a, s))
      else Some (inl (mkLM cur' chain (lm_best a) (lm_end1 a) (lm_end a) s))
    else Some (inr (lm_best a, s)) in
  (* if (match[best_len] != scan_end || match[best_len - 1] != scan_end1 || *match != *scan
         || *++match != scan[1]) continue; *)
  let* m0 := mb_rd (d_window s) (cur + best) in
  if negb (m0 =? lm_end a) then next a else
  let* m1 := mb_rd (d_window s) (cur + best - 1) in
  if negb (m1 =? lm_end1 a) then next a else
  let* m2 := mb_rd (d_window s) cur in
  let* sc0 := mb_rd (d_window s) scan in
  if negb (m2 =? sc0) then next a else
  let* m3 := mb_rd (d_window s) (cur + 1) in
  let* sc1 := mb_rd (d_window s) (scan + 1) in
  if negb (m3 =? sc1) then next a else
  (* scan += 2, match++ *)
  let* scan' := loop FUEL (lm_cmp_body s strend) (scan + 2, cur + 2, 0) in
  let len := MAX_MATCH - (strend - scan') in
  if len >? best then
    let s := set_d_match_start s cur in
    if len >=? nice then Some (inr (len, s)) else
    let* e1 := mb_rd (d_window s) (scan + len - 1) in
    let* e := mb_rd (d_window s) (scan + len) in
    next (mkLM cur (lm_chain a) len e1 e s)
  else next a.

(** longest_match: returns the state (match_start) and the result. *)
Definition c_longest_match (s : dstate) (cur_match : Z) : option (dstate * Z) :=
  let chain := d_max_chain_length s in
  let best := d_prev_length s in
  let nice := d_nice_match s in
  let maxd := u32 (d_w_size s - MIN_LOOKAHEAD) in
  let limit := if d_strstart s >? maxd then u32 (d_strstart s - maxd) else NIL in
  let* _ := guard (in_int best) in
  (* nice_match = (int)s->lookahead must not change sign (v2) *)
  let* _ := guard (in_int (d_lookahead s)) in
  (* strend = window + strstart + MAX_MATCH is compared with scan: VST needs it within the window (or one past) *)
  let* _ := guard (d_strstart s + MAX_MATCH <=? Zlength (mb_val (d_window s))) in
  let* e1 := mb_rd (d_window s) (d_strstart s + best - 1) in
  let* e := mb_rd (d_window s) (d_strstart s + best) in
  let chain := if d_prev_length s >=? d_good_match s then Z.shiftr chain 2 else chain in
  let nice := if u32 nice >? d_lookahead s then d_lookahead s else nice in
  let* (best, s) := loop FUEL (lm_body nice limit) (mkLM cur_match chain best e1 e s) in
  Some (s, if best <=? d_lookahead s then best else d_lookahead s).

(** ** lm_init(s) *)
Definition c_lm_init (s : dstate) : option dstate :=
  let s := set_d_window_size s (u64 (2 * d_w_size s)) in
  let* s := c_clear_hash s in
  let* _ := guard ((0 <=? d_level s) && (d_level s <? 10)) in
  let '(good, lazy, nice, chain, _) := Znth (d_level s) config_table in
  let s := set_d_max_lazy_match s lazy in
  let s := set_d_good_match s good in
  let s := set_d_nice_match s nice in
  let s := set_d_max_chain_length s chain in
  let s := set_d_strstart s 0 in
  let s := set_d_block_start s 0 in
  let s := set_d_lookahead s 0 in
  let s := set_d_insert s 0 in
  let s := set_d_match_length s (MIN_MATCH - 1) in
  let s := set_d_prev_length s (MIN_MATCH - 1) in
  let s := set_d_match_available s 0 in
  Some (set_d_ins_h s 0).
