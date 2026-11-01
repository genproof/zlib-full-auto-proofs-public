(** * The checked model of deflate.c, part 3: the API functions that do not call the compressors

    deflateStateCheck, deflateResetKeep, deflateReset, deflateInit2_, deflateInit_, deflateSetDictionary,
    deflateGetDictionary, deflateSetHeader, deflateTune, deflateBound_z, deflateBound, deflatePrime,
    deflateEnd, and compress.c's compressBound_z / compressBound.  Conventions: DState.v, DLoop.v, CBase.v,
    DModel1.v (one [let*] per memory access that can fail, in C order; unsigned arithmetic truncated like the
    C; signed arithmetic not bounded by the C types guarded).

    The stream: a stream without state ([strm->state == Z_NULL], e.g. after deflateEnd) is [None : option
    dstate]; [c_deflateStateCheck] is on [option dstate].  The functions on a live stream take [(s : dstate) (z :
    strm)] and return [option (dstate * strm * Z)] (the new state, the new stream, the return code); their
    first step is deflateStateCheck, so on a state whose status is invalid they return [Z_STREAM_ERROR] and
    change nothing.  On [None] every one of them returns [Z_STREAM_ERROR] and changes nothing
    ([c_on_state] lifts them to [option dstate]).  The facts deflateStateCheck tests besides the state pointer
    and the status ([strm != Z_NULL], [strm->zalloc], [strm->zfree] non-zero, [s->strm == strm]) are facts of
    the representation (DRep.v), not of the model.

    Pointers are not modelled: ERR_RETURN / [strm->msg = ERR_MSG(e)] is [z_msg = Some e]; the user's gz_header
    is [d_gzhead s : option gzh]; the dictionary of deflateSetDictionary is [None] (Z_NULL) or [Some d] with [d]
    exactly the [dictLength] bytes the caller passes (so dictLength = [Zlength d]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DModel1b.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Setters of the trees part used by the API *)
Definition api_set_level (t : tstate) (x : Z) : tstate :=
  mkTS (tr_ltree t) (tr_dtree t) (tr_bltree t) (tr_lmax t) (tr_dmax t) (tr_blmax t) (tr_wk t) (tr_out t)
       (tr_sym_next t) (tr_sym_end t) (tr_matches t) (tr_lit_bufsize t) x (tr_strategy t) (tr_data_type t).
Definition api_set_strategy (t : tstate) (x : Z) : tstate :=
  mkTS (tr_ltree t) (tr_dtree t) (tr_bltree t) (tr_lmax t) (tr_dmax t) (tr_blmax t) (tr_wk t) (tr_out t)
       (tr_sym_next t) (tr_sym_end t) (tr_matches t) (tr_lit_bufsize t) (tr_level t) x (tr_data_type t).

Definition set_d_level (s : dstate) (x : Z) : dstate := set_d_tr s (api_set_level (d_tr s) x).
Definition set_d_strategy (s : dstate) (x : Z) : dstate := set_d_tr s (api_set_strategy (d_tr s) x).

(** The constants of zlib.h / zutil.h / zconf.h used here. *)
Definition Z_DEFAULT_COMPRESSION := -1.
Definition MAX_MEM_LEVEL := 9.
Definition DEF_MEM_LEVEL := 8.
Definition MAX_WBITS := 15.
Definition LIT_BUFS := 4.
Definition UMAX64 := 18446744073709551615.  (* (z_size_t)-1 *)

(** ** deflateStateCheck(strm): 1 = not ok, 0 = ok. *)
Definition status_ok (st : Z) : bool :=
  (st =? INIT_STATE) || (st =? GZIP_STATE) || (st =? EXTRA_STATE) || (st =? NAME_STATE) ||
  (st =? COMMENT_STATE) || (st =? HCRC_STATE) || (st =? BUSY_STATE) || (st =? FINISH_STATE).

Definition c_deflateStateCheck (os : option dstate) : Z :=
  match os with
  | None => 1
  | Some s => if status_ok (d_status s) then 0 else 1
  end.

(** [deflateStateCheck(strm)] on a live state, as a boolean (true = not ok). *)
Definition bad_state (s : dstate) : bool := c_deflateStateCheck (Some s) =? 1.

(** A function on a live stream, lifted to [option dstate]: with no state, [Z_STREAM_ERROR] and no change. *)
Definition c_on_state (f : dstate -> strm -> option (dstate * strm * Z)) (os : option dstate) (z : strm)
    : option (option dstate * strm * Z) :=
  match os with
  | None => Some (None, z, Z_STREAM_ERROR)
  | Some s => let* (s', z', r) := f s z in Some (Some s', z', r)
  end.

(** ** deflateResetKeep(strm) *)
Definition c_deflateResetKeep (s : dstate) (z : strm) : option (dstate * strm * Z) :=
  if bad_state s then Some (s, z, Z_STREAM_ERROR) else
  let z := set_z_total_out (set_z_total_in z 0) 0 in
  let z := set_z_msg z None in
  let s := set_d_tr s (set_data_type (d_tr s) Z_UNKNOWN) in
  let o := tr_out (d_tr s) in
  let s := set_d_tr s (set_out (d_tr s) (mkOut (o_buf o) 0 (o_bi_buf o) (o_bi_valid o) (o_bi_used o))) in
  let s := set_d_po s 0 in
  let* s := (if d_wrap s <? 0 then
               let* _ := guard (in_int (- d_wrap s)) in
               Some (set_d_wrap s (- d_wrap s))
             else Some s) in
  let s := set_d_status s (if d_wrap s =? 2 then GZIP_STATE else INIT_STATE) in
  (* crc32(0L, Z_NULL, 0) = 0, adler32(0L, Z_NULL, 0) = 1 *)
  let z := set_z_adler z (if d_wrap s =? 2 then 0 else 1) in
  let s := set_d_last_flush s (-2) in
  let* t := c_tr_init (d_trm s) in
  Some (set_d_trm s t, z, Z_OK).

(** ** deflateReset(strm) *)
Definition c_deflateReset (s : dstate) (z : strm) : option (dstate * strm * Z) :=
  let* (s, z, ret) := c_deflateResetKeep s z in
  if ret =? Z_OK then let* s := c_lm_init s in Some (s, z, ret) else Some (s, z, ret).

(** ** deflateEnd(strm): the state is freed ([None]) unless deflateStateCheck fails. *)
Definition c_deflateEnd (s : dstate) (z : strm) : option (option dstate * strm * Z) :=
  if bad_state s then Some (Some s, z, Z_STREAM_ERROR) else
  let status := d_status s in
  Some (None, z, if status =? BUSY_STATE then Z_DATA_ERROR else Z_OK).

(** ** deflateInit2_ *)

(** The deflate_state after [zmemzero(s, sizeof(deflate_state))] and the assignments of deflateInit2_ up to
    the allocation check: every field zero except those set; the window and pending_buf as malloc gives them
    (no byte written: masks all false); prev all zero (the zmemzero after the check; before it its contents
    do not matter: only deflateEnd sees them); head all zero (its contents do not matter: lm_init's CLEAR_HASH
    overwrites all of it).  pending_out is NULL after the zmemzero; [d_po = 0] (deflateResetKeep sets
    pending_out = pending_buf before anything reads it).  The trees part: all trees, the work area and the
    counters zero; [tr_data_type] 0 (strm->data_type is not touched before deflateResetKeep sets it). *)
Definition zero_tree (n : Z) : tree := mkTree (repeat 0 (Z.to_nat n)) (repeat 0 (Z.to_nat n)).
Definition zero_work : work :=
  mkWork (repeat 0 (Z.to_nat (2 * L_CODES + 1))) 0 0 (repeat 0 (Z.to_nat (2 * L_CODES + 1)))
         (repeat 0 (Z.to_nat (MAX_BITS + 1))) 0 0.

Definition init_tstate (lit_bufsize : Z) : tstate :=
  mkTS (zero_tree HEAP_SIZE) (zero_tree (2 * D_CODES + 1)) (zero_tree (2 * BL_CODES + 1)) 0 0 0 zero_work
       (mkOut (repeat 0 (Z.to_nat (lit_bufsize * LIT_BUFS))) 0 0 0 0) 0 0 0 lit_bufsize 0 0 0.

Definition init_dstate (wrap w_bits hash_bits lit_bufsize : Z) : dstate :=
  let w_size := Z.shiftl 1 w_bits in
  let hash_size := Z.shiftl 1 hash_bits in
  mkDS INIT_STATE 0 wrap None 0 0 0
       w_size w_bits (u32 (w_size - 1))
       (mkMB (repeat 0 (Z.to_nat (2 * w_size))) (repeat false (Z.to_nat (2 * w_size)))) 0
       (repeat 0 (Z.to_nat w_size)) (repeat 0 (Z.to_nat hash_size))
       0 hash_size hash_bits (u32 (hash_size - 1)) ((hash_bits + MIN_MATCH - 1) / MIN_MATCH)
       (* block_start .. slid: 15 fields *)
       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
       (u64 (lit_bufsize * 4))
       (init_tstate lit_bufsize)
       (repeat false (Z.to_nat (lit_bufsize * LIT_BUFS))).

(** [deflateInit2_(strm, level, method, windowBits, memLevel, strategy, version, stream_size)].
    [version_ok]: version != Z_NULL and version[0] == ZLIB_VERSION[0]; [size_ok]: stream_size ==
    sizeof(z_stream); [strm_null]: strm == Z_NULL; [al_s], [al_win], [al_prev], [al_head], [al_pbuf]: whether
    the five ZALLOC calls (the deflate_state, window, prev, head, pending_buf) succeed.  Result: the new state
    ([None]: none was made -- on Z_VERSION_ERROR, Z_STREAM_ERROR and the first Z_MEM_ERROR strm->state is not
    written; on the second Z_MEM_ERROR deflateEnd has set it to Z_NULL), the stream, the code. *)
Definition c_deflateInit2_ (version_ok size_ok strm_null : bool)
    (level method windowBits memLevel strategy : Z) (al_s al_win al_prev al_head al_pbuf : bool) (z : strm)
    : option (option dstate * strm * Z) :=
  if negb version_ok || negb size_ok then Some (None, z, Z_VERSION_ERROR) else
  if strm_null then Some (None, z, Z_STREAM_ERROR) else
  let z := set_z_msg z None in
  let level := if level =? Z_DEFAULT_COMPRESSION then 6 else level in
  let wb_wrap :=
    if windowBits <? 0 then
      if windowBits <? -15 then None else Some (- windowBits, 0)
    else if windowBits >? 15 then Some (windowBits - 16, 2)
    else Some (windowBits, 1) in
  match wb_wrap with
  | None => Some (None, z, Z_STREAM_ERROR)
  | Some (windowBits, wrap) =>
  if (memLevel <? 1) || (memLevel >? MAX_MEM_LEVEL) || negb (method =? Z_DEFLATED) ||
     (windowBits <? 8) || (windowBits >? 15) || (level <? 0) || (level >? 9) ||
     (strategy <? 0) || (strategy >? Z_FIXED) || ((windowBits =? 8) && negb (wrap =? 1))
  then Some (None, z, Z_STREAM_ERROR) else
  let windowBits := if windowBits =? 8 then 9 else windowBits in
  if negb al_s then Some (None, z, Z_MEM_ERROR) else
  let lit_bufsize := Z.shiftl 1 (memLevel + 6) in
  let s := init_dstate wrap windowBits (memLevel + 7) lit_bufsize in
  if negb (al_win && al_prev && al_head && al_pbuf) then
    let s := set_d_status s FINISH_STATE in
    let z := set_z_msg z (Some Z_MEM_ERROR) in
    let* (os, z, _) := c_deflateEnd s z in
    Some (os, z, Z_MEM_ERROR)
  else
  let s := set_d_tr s (mkTS (tr_ltree (d_tr s)) (tr_dtree (d_tr s)) (tr_bltree (d_tr s)) 0 0 0 (tr_wk (d_tr s))
                            (tr_out (d_tr s)) 0 (u32 ((lit_bufsize - 1) * 3)) 0 lit_bufsize level strategy 0) in
  let s := set_d_method s (u8 method) in
  let* (s, z, r) := c_deflateReset s z in
  Some (Some s, z, r)
  end.

(** deflateInit_(strm, level, version, stream_size) = deflateInit2_ with Z_DEFLATED, MAX_WBITS, DEF_MEM_LEVEL,
    Z_DEFAULT_STRATEGY. *)
Definition c_deflateInit_ (version_ok size_ok strm_null : bool) (level : Z)
    (al_s al_win al_prev al_head al_pbuf : bool) (z : strm) : option (option dstate * strm * Z) :=
  c_deflateInit2_ version_ok size_ok strm_null level Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY
    al_s al_win al_prev al_head al_pbuf z.

(** ** deflateSetDictionary(strm, dictionary, dictLength) *)

(** The inner [do { UPDATE_HASH; prev[str & w_mask] = head[ins_h]; head[ins_h] = (Pos)str; str++; } while
    (--n);], state (s, str, n); exit (s, str). *)
Definition sd_insert_body (a : dstate * Z * Z) : option ((dstate * Z * Z) + (dstate * Z)) :=
  let '(s, str, n) := a in
  let* _ := guard (d_hash_shift s <? 32) in   (* the shift of UPDATE_HASH (v2) *)
  let* c := mb_rd (d_window s) (u32 (str + (MIN_MATCH - 1))) in
  let s := set_d_ins_h s (update_hash s (d_ins_h s) c) in
  let* h := rd (d_head s) (d_ins_h s) in
  let* prev := wr (d_prev s) (Z.land str (d_w_mask s)) h in
  let s := set_d_prev s prev in
  let* head := wr (d_head s) (d_ins_h s) (u16 str) in
  let s := set_d_head s head in
  let str := u32 (str + 1) in
  let n := u32 (n - 1) in
  if n =? 0 then Some (inr (s, str)) else Some (inl (s, str, n)).

(** One iteration of [while (s->lookahead >= MIN_MATCH) { ...; fill_window(s); }] (the stream is the one
    whose input is the dictionary). *)
Definition sd_body (a : dstate * strm) : option ((dstate * strm) + (dstate * strm)) :=
  let '(s, z) := a in
  if d_lookahead s >=? MIN_MATCH then
    let str := d_strstart s in
    let n := u32 (d_lookahead s - (MIN_MATCH - 1)) in
    let* (s, str) := loop FUEL sd_insert_body (s, str, n) in
    let s := set_d_strstart s str in
    let s := set_d_lookahead s (MIN_MATCH - 1) in
    let* (s, z) := c_fill_window s z in
    Some (inl (s, z))
  else Some (inr (s, z)).

(** The dictionary becomes the stream's input for fill_window ([strm->next_in = dictionary (+ the offset of
    the tail)], [strm->avail_in = dictLength]); next_in and avail_in are restored at the end; total_in keeps
    what read_buf added (adler: read_buf does not change it, wrap is 0 meanwhile). *)
Definition c_deflateSetDictionary (s : dstate) (z : strm) (dict : option (list Z)) : option (dstate * strm * Z) :=
  if bad_state s then Some (s, z, Z_STREAM_ERROR) else
  match dict with
  | None => Some (s, z, Z_STREAM_ERROR)
  | Some d =>
  let wrap := d_wrap s in
  if (wrap =? 2) || ((wrap =? 1) && negb (d_status s =? INIT_STATE)) || negb (d_lookahead s =? 0)
  then Some (s, z, Z_STREAM_ERROR) else
  let dictLength := Zlength d in
  let z := if wrap =? 1 then set_z_adler z (Zlib.proof.adler32.Model.adler32_z_val (z_adler z) d) else z in
  let s := set_d_wrap s 0 in
  let* (s, off, len) :=
    (if dictLength >=? d_w_size s then
       let* s := (if wrap =? 0 then
                    let* s := c_clear_hash s in
                    let s := set_d_strstart s 0 in
                    let s := set_d_block_start s 0 in
                    Some (set_d_insert s 0)
                  else Some s) in
       Some (s, dictLength - d_w_size s, d_w_size s)
     else Some (s, 0, dictLength)) in
  let zd := mkST d off len (z_total_in z) (z_out z) (z_avail_out z) (z_total_out z) (z_adler z) (z_msg z) in
  let* (s, zd) := c_fill_window s zd in
  let* (s, zd) := loop FUEL sd_body (s, zd) in
  let s := set_d_strstart s (u32 (d_strstart s + d_lookahead s)) in
  let s := set_d_block_start s (d_strstart s) in
  let s := set_d_insert s (d_lookahead s) in
  let s := set_d_lookahead s 0 in
  let s := set_d_prev_length (set_d_match_length s (MIN_MATCH - 1)) (MIN_MATCH - 1) in
  let s := set_d_match_available s 0 in
  let z := mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in zd) (z_out zd) (z_avail_out zd)
                (z_total_out zd) (z_adler zd) (z_msg zd) in
  let s := set_d_wrap s wrap in
  Some (s, z, Z_OK)
  end.

(** ** deflateGetDictionary(strm, dictionary, dictLength)
    [dict_nonnull]: dictionary != Z_NULL.  Result: the bytes written to dictionary ([] when it is Z_NULL or
    len = 0), len (written to *dictLength when dictLength != Z_NULL; 0 with Z_STREAM_ERROR), the code. *)
Definition c_deflateGetDictionary (s : dstate) (dict_nonnull : bool) : option (list Z * Z * Z) :=
  if bad_state s then Some ([], 0, Z_STREAM_ERROR) else
  let len := u32 (d_strstart s + d_lookahead s) in
  let len := if len >? d_w_size s then d_w_size s else len in
  if dict_nonnull && negb (len =? 0) then
    let* bytes := mb_read (d_window s) (d_strstart s + d_lookahead s - len) len in
    Some (bytes, len, Z_OK)
  else Some ([], len, Z_OK).

(** ** deflateSetHeader(strm, head) *)
Definition c_deflateSetHeader (s : dstate) (z : strm) (head : option gzh) : option (dstate * strm * Z) :=
  if bad_state s || negb (d_wrap s =? 2) then Some (s, z, Z_STREAM_ERROR) else
  Some (set_d_gzhead s head, z, Z_OK).

(** ** deflateTune(strm, good_length, max_lazy, nice_length, max_chain) (int arguments) *)
Definition c_deflateTune (s : dstate) (z : strm) (good_length max_lazy nice_length max_chain : Z)
    : option (dstate * strm * Z) :=
  if bad_state s then Some (s, z, Z_STREAM_ERROR) else
  let s := set_d_good_match s (u32 good_length) in
  let s := set_d_max_lazy_match s (u32 max_lazy) in
  let s := set_d_nice_match s nice_length in
  let s := set_d_max_chain_length s (u32 max_chain) in
  Some (s, z, Z_OK).

(** ** deflatePrime(strm, bits, value) *)

(** One iteration of the do-while loop, state (s, bits, value). *)
Definition prime_body (a : dstate * Z * Z) : option ((dstate * Z * Z) + dstate) :=
  let '(s, bits, value) := a in
  let o := tr_out (d_tr s) in
  let* _ := guard ((0 <=? o_bi_valid o) && (o_bi_valid o <=? Buf_size)) in
  let put := Buf_size - o_bi_valid o in
  let put := if put >? bits then bits else put in
  let* _ := guard ((0 <=? put) && (put <=? 16)) in
  let bb := u16 (Z.lor (o_bi_buf o) (u16 (Z.shiftl (Z.land value (Z.shiftl 1 put - 1)) (o_bi_valid o)))) in
  let s := set_d_out s (mkOut (o_buf o) (o_pending o) bb (o_bi_valid o + put) (o_bi_used o), d_pbm s) in
  let* om := c_tr_flush_bits (d_out s) in
  let s := set_d_out s om in
  let value := Z.shiftr value put in
  let bits := bits - put in
  if bits =? 0 then Some (inr s) else Some (inl (s, bits, value)).

(** sym_buf = pending_buf + lit_bufsize, pending_out = pending_buf + d_po: the comparison
    [s->sym_buf < s->pending_out + 2] compares two pointers into pending_buf, which must both be (weakly)
    valid: guarded. *)
Definition c_deflatePrime (s : dstate) (z : strm) (bits value : Z) : option (dstate * strm * Z) :=
  if bad_state s then Some (s, z, Z_STREAM_ERROR) else
  if (bits <? 0) || (bits >? 16) then Some (s, z, Z_BUF_ERROR) else
  let n := Zlength (o_buf (tr_out (d_tr s))) in
  let* _ := guard ((0 <=? tr_lit_bufsize (d_tr s)) && (tr_lit_bufsize (d_tr s) <=? n) &&
                   (0 <=? d_po s + 2) && (d_po s + 2 <=? n)) in
  if tr_lit_bufsize (d_tr s) <? d_po s + (Z.shiftr (Buf_size + 7) 3) then Some (s, z, Z_BUF_ERROR) else
  let* s := loop FUEL prime_body (s, bits, value) in
  Some (s, z, Z_OK).

(** ** deflateBound_z(strm, sourceLen) and deflateBound(strm, sourceLen) (z_size_t and uLong: 64 bits) *)

(** [do { wraplen++; } while ( *str++);] over the name or comment: state (index, wraplen). *)
Definition strlen_body (str : list Z) (a : Z * Z) : option ((Z * Z) + Z) :=
  let '(i, wl) := a in
  let wl := u64 (wl + 1) in
  let* c := rd str i in
  if c =? 0 then Some (inr wl) else Some (inl (i + 1, wl)).

Definition c_count_str (o : option (list Z)) (wl : Z) : option Z :=
  match o with
  | None => Some wl
  | Some str => loop FUEL (strlen_body str) (0, wl)
  end.

Definition c_deflateBound_z (os : option dstate) (sourceLen : Z) : option Z :=
  let fixedlen := u64 (sourceLen + Z.shiftr sourceLen 3 + Z.shiftr sourceLen 8 + Z.shiftr sourceLen 9 + 4) in
  let fixedlen := if fixedlen <? sourceLen then UMAX64 else fixedlen in
  let storelen := u64 (sourceLen + Z.shiftr sourceLen 5 + Z.shiftr sourceLen 7 + Z.shiftr sourceLen 11 + 7) in
  let storelen := if storelen <? sourceLen then UMAX64 else storelen in
  match os with
  | Some s => if bad_state s then
               let bound := if fixedlen >? storelen then fixedlen else storelen in
               Some (if u64 (bound + 18) <? bound then UMAX64 else u64 (bound + 18))
             else
    let* w := (if d_wrap s <? 0 then let* _ := guard (in_int (- d_wrap s)) in Some (- d_wrap s)
               else Some (d_wrap s)) in
    let* wraplen :=
      (if w =? 0 then Some 0
       else if w =? 1 then Some (6 + (if d_strstart s =? 0 then 0 else 4))
       else if w =? 2 then
         match d_gzhead s with
         | None => Some 18
         | Some h =>
           let wl := 18 in
           let wl := match gz_extra h with
                     | Some _ => u64 (wl + u32 (2 + gz_extra_len h))
                     | None => wl end in
           let* wl := c_count_str (gz_name h) wl in
           let* wl := c_count_str (gz_comment h) wl in
           Some (if gz_hcrc h =? 0 then wl else u64 (wl + 2))
         end
       else Some 18) in
    if negb (d_w_bits s =? 15) || negb (d_hash_bits s =? 8 + 7) ||
       ((d_strategy s =? Z_FIXED) && (d_level s >=? 1) && (d_level s <=? 3)) then
      let bound := if (d_w_bits s <=? d_hash_bits s) && negb (d_level s =? 0) then fixedlen else storelen in
      Some (if u64 (bound + wraplen) <? bound then UMAX64 else u64 (bound + wraplen))
    else
      let bound := u64 (sourceLen + Z.shiftr sourceLen 12 + Z.shiftr sourceLen 14 + Z.shiftr sourceLen 25
                        + 13 - 6 + wraplen) in
      Some (if bound <? sourceLen then UMAX64 else bound)
  | None =>
    let bound := if fixedlen >? storelen then fixedlen else storelen in
    Some (if u64 (bound + 18) <? bound then UMAX64 else u64 (bound + 18))
  end.

(** uLong and z_size_t are both 64 bits: [(uLong)bound != bound] is false. *)
Definition c_deflateBound (os : option dstate) (sourceLen : Z) : option Z := c_deflateBound_z os sourceLen.

(** ** compress.c: compressBound_z(sourceLen), compressBound(sourceLen) *)
Definition compressBound_z (sourceLen : Z) : Z :=
  let bound := u64 (sourceLen + Z.shiftr sourceLen 12 + Z.shiftr sourceLen 14 + Z.shiftr sourceLen 25 + 13) in
  if bound <? sourceLen then UMAX64 else bound.
Definition c_compressBound (sourceLen : Z) : Z := compressBound_z sourceLen.

(** ** Tests on small cases *)
Example test_compressBound : c_compressBound 100000 = 100000 + 24 + 6 + 0 + 13.
Proof. reflexivity. Qed.

Example test_bound_none : c_deflateBound None 0 = Some 25.
Proof. reflexivity. Qed.

Example test_init_bad_level :
  forall z, c_deflateInit2_ true true false 10 8 15 8 0 true true true true true z = Some (None, set_z_msg z None, Z_STREAM_ERROR).
Proof. reflexivity. Qed.

Example test_init_version :
  forall z, c_deflateInit2_ false true false 6 8 15 8 0 true true true true true z = Some (None, z, Z_VERSION_ERROR).
Proof. reflexivity. Qed.

Example test_init_mem :
  forall z, c_deflateInit2_ true true false 6 8 15 8 0 true true false true true z =
            Some (None, set_z_msg (set_z_msg z None) (Some Z_MEM_ERROR), Z_MEM_ERROR).
Proof. reflexivity. Qed.

(** A successful deflateInit2_ (raw, windowBits -9, memLevel 1), a dictionary, deflateBound, deflatePrime. *)
Definition test_z : strm := mkST [] 0 0 0 [] 0 0 0 None.
Definition test_init (wb ml : Z) : option dstate :=
  match c_deflateInit2_ true true false 6 8 wb ml 0 true true true true true test_z with
  | Some (os, _, r) => if r =? Z_OK then os else None
  | None => None
  end.

Example test_init_ok : match test_init (-9) 1 with Some s => (d_status s, d_wrap s, d_w_size s, d_hash_size s,
    tr_lit_bufsize (d_tr s), tr_sym_end (d_tr s), d_last_flush s, d_max_chain_length s) | None => (0,0,0,0,0,0,0,0) end
  = (INIT_STATE, 0, 512, 256, 128, 381, -2, 128).
Proof. vm_compute. reflexivity. Qed.

Definition test_dict : list Z := map (fun i => Z.of_nat i mod 7) (seq 0 20).

Example test_setdict :
  match test_init (-9) 1 with
  | Some s => match c_deflateSetDictionary s test_z (Some test_dict) with
              | Some (s', z', r) => (r, d_strstart s', d_block_start s', d_insert s', d_lookahead s', z_total_in z',
                                     d_wrap s', mb_read (d_window s') 0 20)
              | None => (99, 0, 0, 0, 0, 0, 0, None) end
  | None => (98, 0, 0, 0, 0, 0, 0, None) end
  = (Z_OK, 20, 20, 2, 0, 20, 0, Some test_dict).
Proof. vm_compute. reflexivity. Qed.

Example test_bound_raw :
  match test_init (-9) 1 with Some s => c_deflateBound (Some s) 1000 | None => None end
  = Some (1000 + 31 + 7 + 0 + 7). (* storelen: w_bits 9 > hash_bits 8 *)
Proof. vm_compute. reflexivity. Qed.

Example test_prime :
  match test_init (-9) 1 with
  | Some s => match c_deflatePrime s test_z 13 5000 with
              | Some (s', _, r) => (r, o_bi_valid (tr_out (d_tr s')), o_bi_buf (tr_out (d_tr s')), d_pending s',
                                    c_rd_pb (d_out s') 0)
              | None => (99, 0, 0, 0, None) end
  | None => (98, 0, 0, 0, None) end
  = (Z_OK, 5, Z.shiftr 5000 8 mod 32, 1, Some (5000 mod 256)).
Proof. vm_compute. reflexivity. Qed.

(** Guards of this file that are not memory-access checks, and why:
    - [c_deflateResetKeep]: [in_int (- d_wrap s)] when wrap < 0: [s->wrap = -s->wrap] is a signed negation,
      undefined for INT_MIN (wrap is in -2..2 on every reachable state).
    - [c_deflateBound_z]: [in_int (- d_wrap s)] when wrap < 0: the switch computes [s->wrap < 0 ? -s->wrap :
      s->wrap], undefined for INT_MIN.
    - [prime_body] (deflatePrime): [0 <= bi_valid <= 16]: [(...) << s->bi_valid] needs the shift amount in
      [0, 32) and [1 << put] with [put = 16 - bi_valid] (or bits) needs [put >= 0]; the second guard [0 <= put
      <= 16] then always holds (bits is in 0..16) and is kept for the VST proof ([(1 << put) - 1] does not
      overflow).  bi_valid in 0..16 is the bit writer's invariant (Bits.v [bw_ok]), as in CModel.c_send_bits.
    - [c_deflatePrime]: the pointer comparison [s->sym_buf < s->pending_out + 2] needs both pointers weakly
      valid in pending_buf ([0 <= lit_bufsize <= size], [0 <= d_po + 2 <= size]); a pointer check, not an
      array access.
    - Loops ([sd_insert_body], [sd_body], [prime_body], [strlen_body]): run with [loop FUEL] (2^40
      iterations); [None] if the fuel runs out.
    Not guards, no failure: deflateInit2_'s [1 << w_bits], [1 << (memLevel + 6)], [1 << hash_bits] and
    [-windowBits] are evaluated only on validated parameters (w_bits 9..15, memLevel 1..9, windowBits >= -15);
    [windowBits - 16] only for windowBits > 15; deflateParams' and deflate's int arithmetic is in DModel4. *)
