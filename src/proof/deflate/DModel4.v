(** * The checked model of deflate.c, part 4: deflate() and deflateParams()

    [c_deflate s z flush] is deflate(strm, flush) on a live stream (the whole state machine): the checks and
    ERR_RETURNs, the flush_pending at entry, the zlib header, the gzip header states GZIP / EXTRA / NAME /
    COMMENT / HCRC (HCRC_UPDATE: crc32_z over pending_buf[beg, pending), a checked read), the dispatch to the
    compression function (DModel2), the block_done handling (_tr_align, the empty stored block, CLEAR_HASH for
    Z_FULL_FLUSH), the trailer and the negation of wrap.  [c_deflateParams] may call it with Z_BLOCK.
    On a stream without state use [c_on_state] (DModel3): Z_STREAM_ERROR, no change.

    Structure: deflate() is a sequence of stages; each stage is a model function returning
    [option (dstate * strm * option Z)]: [Some (s, z, Some r)] when the C returns [r] in that stage,
    [Some (s, z, None)] when it falls through to the next one.  [then_stage] chains them.

    Pointers: [strm->next_out == Z_NULL] and [strm->next_in == Z_NULL] with avail_in != 0 are excluded by the
    representation (the output space and the input are objects, DRep.out_space / in_obj), so those two tests
    of the first ERR_RETURN are false in the model.  A Z_NULL gzhead in the states EXTRA .. HCRC (possible if
    the caller calls deflateSetHeader(strm, Z_NULL) in the middle of a gzip header) is a NULL dereference:
    the model is [None]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DModel2 Zlib.proof.deflate.DModel3.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Helpers *)

(** [s->pending = x] *)
Definition set_d_pending (s : dstate) (x : Z) : dstate :=
  let o := tr_out (d_tr s) in
  set_d_tr s (set_out (d_tr s) (mkOut (o_buf o) x (o_bi_buf o) (o_bi_valid o) (o_bi_used o))).

(** put_byte of each byte of a list, in order. *)
Fixpoint c_dput_bytes (s : dstate) (l : list Z) : option dstate :=
  match l with
  | [] => Some s
  | c :: l => let* s := c_dput_byte s c in c_dput_bytes s l
  end.

(** The stages of deflate(). *)
Definition dres := (dstate * strm * option Z)%type.

Definition then_stage (r : option dres) (k : dstate -> strm -> option dres) : option dres :=
  let* (s, z, o) := r in
  match o with Some c => Some (s, z, Some c) | None => k s z end.

(** [flush_pending(strm); if (s->pending != 0) { s->last_flush = -1; return Z_OK; }] *)
Definition c_flush_or_return (s : dstate) (z : strm) : option dres :=
  let* (s, z) := c_flush_pending s z in
  if negb (d_pending s =? 0) then Some (set_d_last_flush s (-1), z, Some Z_OK) else Some (s, z, None).

(** RANK(f) *)
Definition rank (f : Z) : Z := f * 2 - (if f >? 4 then 9 else 0).

(** [configuration_table[l].func]: 0 = deflate_stored, 1 = deflate_fast, 2 = deflate_slow (checked index). *)
Definition cfg_func (l : Z) : option Z :=
  if (0 <=? l) && (l <=? 9) then let '(_, _, _, _, f) := Znth l config_table in Some f else None.

(** [configuration_table[level].func] for a level already checked to be in 0..9 (deflateParams). *)
Definition cfg_f (l : Z) : Z := let '(_, _, _, _, f) := Znth l config_table in f.

(** HCRC_UPDATE(beg) *)
Definition c_hcrc_update (h : gzh) (s : dstate) (z : strm) (beg : Z) : option strm :=
  if negb (gz_hcrc h =? 0) && (d_pending s >? beg) then
    let* bytes := mb_read (d_pb s) beg (d_pending s - beg) in
    Some (set_z_adler z (Zlib.proof.crc32.Model.ref_crc32 (z_adler z) bytes))
  else Some z.

(** The XFL byte: [s->level == 9 ? 2 : (s->strategy >= Z_HUFFMAN_ONLY || s->level < 2 ? 4 : 0)] *)
Definition xfl_byte (s : dstate) : Z :=
  if d_level s =? 9 then 2 else if (d_strategy s >=? Z_HUFFMAN_ONLY) || (d_level s <? 2) then 4 else 0.

(** The gzhead pointer dereferenced: Z_NULL is undefined. *)
Definition c_gzhead (s : dstate) : option gzh := d_gzhead s.

(** ** Stage 1: the checks at entry (after deflateStateCheck and the flush range), last_flush, the flush of
    pending output, the duplicate-flush and input-after-finish errors. *)
Definition c_deflate_entry (s : dstate) (z : strm) (flush : Z) : option dres :=
  if (d_status s =? FINISH_STATE) && negb (flush =? Z_FINISH) then
    Some (s, set_z_msg z (Some Z_STREAM_ERROR), Some Z_STREAM_ERROR) else
  if z_avail_out z =? 0 then Some (s, set_z_msg z (Some Z_BUF_ERROR), Some Z_BUF_ERROR) else
  let old_flush := d_last_flush s in
  let s := set_d_last_flush s flush in
  let* r :=
    (if negb (d_pending s =? 0) then
       let* (s, z) := c_flush_pending s z in
       if z_avail_out z =? 0 then Some (set_d_last_flush s (-1), z, Some Z_OK) else Some (s, z, None)
     else if z_avail_in z =? 0 then
       let* _ := guard (in_int (old_flush * 2)) in
       if (rank flush <=? rank old_flush) && negb (flush =? Z_FINISH) then
         Some (s, set_z_msg z (Some Z_BUF_ERROR), Some Z_BUF_ERROR)
       else Some (s, z, None)
     else Some (s, z, None)) in
  then_stage (Some r) (fun s z =>
    if (d_status s =? FINISH_STATE) && negb (z_avail_in z =? 0) then
      Some (s, set_z_msg z (Some Z_BUF_ERROR), Some Z_BUF_ERROR)
    else Some (s, z, None)).

(** ** Stage 2: the zlib header (INIT_STATE). *)
Definition zlib_header (s : dstate) : Z :=
  let header := u32 (Z.shiftl (u32 (Z_DEFLATED + u32 (Z.shiftl (u32 (d_w_bits s - 8)) 4))) 8) in
  let level_flags :=
    if (d_strategy s >=? Z_HUFFMAN_ONLY) || (d_level s <? 2) then 0
    else if d_level s <? 6 then 1
    else if d_level s =? 6 then 2
    else 3 in
  let header := Z.lor header (Z.shiftl level_flags 6) in
  let header := if d_strstart s =? 0 then header else Z.lor header PRESET_DICT in
  u32 (header + u32 (31 - header mod 31)).

Definition c_deflate_zlib_header (s : dstate) (z : strm) : option dres :=
  let s := if (d_status s =? INIT_STATE) && (d_wrap s =? 0) then set_d_status s BUSY_STATE else s in
  if d_status s =? INIT_STATE then
    let* s := c_putShortMSB s (zlib_header s) in
    let* s := (if d_strstart s =? 0 then Some s else
                 let* s := c_putShortMSB s (u32 (Z.shiftr (z_adler z) 16)) in
                 c_putShortMSB s (u32 (Z.land (z_adler z) 65535))) in
    let z := set_z_adler z 1 in
    let s := set_d_status s BUSY_STATE in
    c_flush_or_return s z
  else Some (s, z, None).

(** ** Stage 3: GZIP_STATE *)
Definition gz_flags (h : gzh) : Z :=
  (if gz_text h =? 0 then 0 else 1) + (if gz_hcrc h =? 0 then 0 else 2) +
  (match gz_extra h with None => 0 | Some _ => 4 end) +
  (match gz_name h with None => 0 | Some _ => 8 end) +
  (match gz_comment h with None => 0 | Some _ => 16 end).

Definition c_deflate_gzip_header (s : dstate) (z : strm) : option dres :=
  if d_status s =? GZIP_STATE then
    let z := set_z_adler z 0 in
    let* s := c_dput_bytes s [31; 139; 8] in
    match d_gzhead s with
    | None =>
      let* s := c_dput_bytes s [0; 0; 0; 0; 0; xfl_byte s; OS_CODE] in
      let s := set_d_status s BUSY_STATE in
      c_flush_or_return s z
    | Some h =>
      let t := gz_time h in
      let* s := c_dput_bytes s [gz_flags h; Z.land t 255; Z.land (Z.shiftr t 8) 255; Z.land (Z.shiftr t 16) 255;
                                Z.land (Z.shiftr t 24) 255; xfl_byte s; Z.land (gz_os h) 255] in
      let* s := (match gz_extra h with
                 | Some _ => c_dput_bytes s [Z.land (gz_extra_len h) 255; Z.land (Z.shiftr (gz_extra_len h) 8) 255]
                 | None => Some s
                 end) in
      let* z := (if gz_hcrc h =? 0 then Some z else
                   let* bytes := mb_read (d_pb s) 0 (d_pending s) in
                   Some (set_z_adler z (Zlib.proof.crc32.Model.ref_crc32 (z_adler z) bytes))) in
      let s := set_d_gzindex s 0 in
      Some (set_d_status s EXTRA_STATE, z, None)
    end
  else Some (s, z, None).

(** ** Stage 4: EXTRA_STATE *)

(** One iteration of [while (s->pending + lft > s->pending_buf_size) { ... }], state (s, z, beg, lft); exit
    [inl (s, z, beg, lft)] at the loop test, [inr (s, z)] at the [return Z_OK] (last_flush already -1). *)
Definition extra_body (h : gzh) (x : list Z) (a : dstate * strm * Z * Z)
    : option ((dstate * strm * Z * Z) + ((dstate * strm * Z * Z) + (dstate * strm))) :=
  let '(s, z, beg, lft) := a in
  if u64 (d_pending s + lft) >? d_pending_buf_size s then
    let copy := u64 (d_pending_buf_size s - d_pending s) in
    let* bytes := rds x (d_gzindex s) copy in
    let* pb := mb_write (d_pb s) (d_pending s) bytes in
    let s := set_d_pb s pb in
    let s := set_d_pending s (d_pending_buf_size s) in
    let* z := c_hcrc_update h s z beg in
    let s := set_d_gzindex s (u64 (d_gzindex s + copy)) in
    let* (s, z) := c_flush_pending s z in
    if negb (d_pending s =? 0) then Some (inr (inr (set_d_last_flush s (-1), z)))
    else Some (inl (s, z, 0, u64 (lft - copy)))
  else Some (inr (inl (s, z, beg, lft))).

Definition c_deflate_extra (s : dstate) (z : strm) : option dres :=
  if d_status s =? EXTRA_STATE then
    let* h := c_gzhead s in
    let* r :=
      (match gz_extra h with
       | Some x =>
         let beg := d_pending s in
         let lft := u64 (Z.land (gz_extra_len h) 65535 - d_gzindex s) in
         let* e := loop FUEL (extra_body h x) (s, z, beg, lft) in
         match e with
         | inr (s, z) => Some (s, z, Some Z_OK)
         | inl (s, z, beg, lft) =>
           let* bytes := rds x (d_gzindex s) lft in
           let* pb := mb_write (d_pb s) (d_pending s) bytes in
           let s := set_d_pb s pb in
           let s := set_d_pending s (u64 (d_pending s + lft)) in
           let* z := c_hcrc_update h s z beg in
           Some (set_d_gzindex s 0, z, None)
         end
       | None => Some (s, z, None)
       end) in
    then_stage (Some r) (fun s z => Some (set_d_status s NAME_STATE, z, None))
  else Some (s, z, None).

(** ** Stages 5 and 6: NAME_STATE and COMMENT_STATE *)

(** One iteration of [do { if (s->pending == s->pending_buf_size) { HCRC_UPDATE(beg); flush_pending(strm);
    if (s->pending != 0) { s->last_flush = -1; return Z_OK; } beg = 0; } val = str[s->gzindex++];
    put_byte(s, val); } while (val != 0);], state (s, z, beg); exit [inl (s, z, beg)] at [val == 0],
    [inr (s, z)] at the [return Z_OK]. *)
Definition str_body (h : gzh) (str : list Z) (a : dstate * strm * Z)
    : option ((dstate * strm * Z) + ((dstate * strm * Z) + (dstate * strm))) :=
  let '(s, z, beg) := a in
  let* r :=
    (if d_pending s =? d_pending_buf_size s then
       let* z := c_hcrc_update h s z beg in
       let* (s, z) := c_flush_pending s z in
       if negb (d_pending s =? 0) then Some (inr (set_d_last_flush s (-1), z))
       else Some (inl (s, z, 0))
     else Some (inl (s, z, beg))) in
  match r with
  | inr e => Some (inr (inr e))
  | inl (s, z, beg) =>
    let* v := rd str (d_gzindex s) in
    let s := set_d_gzindex s (u64 (d_gzindex s + 1)) in
    let* s := c_dput_byte s v in
    if v =? 0 then Some (inr (inl (s, z, beg))) else Some (inl (s, z, beg))
  end.

(** The string loop and the HCRC_UPDATE after it; [reset]: [s->gzindex = 0] afterwards (the name; not the
    comment). *)
Definition c_deflate_str (h : gzh) (o : option (list Z)) (reset : bool) (s : dstate) (z : strm) : option dres :=
  match o with
  | Some str =>
    let beg := d_pending s in
    let* e := loop FUEL (str_body h str) (s, z, beg) in
    match e with
    | inr (s, z) => Some (s, z, Some Z_OK)
    | inl (s, z, beg) =>
      let* z := c_hcrc_update h s z beg in
      Some (if reset then set_d_gzindex s 0 else s, z, None)
    end
  | None => Some (s, z, None)
  end.

Definition c_deflate_name (s : dstate) (z : strm) : option dres :=
  if d_status s =? NAME_STATE then
    let* h := c_gzhead s in
    then_stage (c_deflate_str h (gz_name h) true s z) (fun s z => Some (set_d_status s COMMENT_STATE, z, None))
  else Some (s, z, None).

Definition c_deflate_comment (s : dstate) (z : strm) : option dres :=
  if d_status s =? COMMENT_STATE then
    let* h := c_gzhead s in
    then_stage (c_deflate_str h (gz_comment h) false s z) (fun s z => Some (set_d_status s HCRC_STATE, z, None))
  else Some (s, z, None).

(** ** Stage 7: HCRC_STATE *)
Definition c_deflate_hcrc (s : dstate) (z : strm) : option dres :=
  if d_status s =? HCRC_STATE then
    let* h := c_gzhead s in
    let* r :=
      (if gz_hcrc h =? 0 then Some (s, z, None) else
       then_stage
         (if u64 (d_pending s + 2) >? d_pending_buf_size s then c_flush_or_return s z else Some (s, z, None))
         (fun s z =>
            let* s := c_dput_bytes s [Z.land (z_adler z) 255; Z.land (Z.shiftr (z_adler z) 8) 255] in
            Some (s, set_z_adler z 0, None))) in
    then_stage (Some r) (fun s z => c_flush_or_return (set_d_status s BUSY_STATE) z)
  else Some (s, z, None).

(** ** Stage 8: compression *)

(** The dispatch: [s->level == 0 ? deflate_stored : s->strategy == Z_HUFFMAN_ONLY ? deflate_huff :
    s->strategy == Z_RLE ? deflate_rle : ( *(configuration_table[s->level].func))]. *)
Definition c_compress_func (s : dstate) (z : strm) (flush : Z) : option (dstate * strm * bstate) :=
  if d_level s =? 0 then c_deflate_stored s z flush
  else if d_strategy s =? Z_HUFFMAN_ONLY then c_deflate_huff s z flush
  else if d_strategy s =? Z_RLE then c_deflate_rle s z flush
  else
    let* f := cfg_func (d_level s) in
    if f =? 0 then c_deflate_stored s z flush
    else if f =? 1 then c_deflate_fast s z flush
    else c_deflate_slow s z flush.

Definition c_deflate_compress (s : dstate) (z : strm) (flush : Z) : option dres :=
  if negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
     (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE)) then
    let* (s, z, bs) := c_compress_func s z flush in
    let s := match bs with finish_started | finish_done => set_d_status s FINISH_STATE | _ => s end in
    match bs with
    | need_more | finish_started =>
      Some (if z_avail_out z =? 0 then set_d_last_flush s (-1) else s, z, Some Z_OK)
    | block_done =>
      let* s :=
        (if flush =? Z_PARTIAL_FLUSH then
           let* om := c_tr_align (d_out s) in Some (set_d_out s om)
         else if negb (flush =? Z_BLOCK) then
           let* om := c_tr_stored_block (d_out s) [] 0 0 in
           let s := set_d_out s om in
           if flush =? Z_FULL_FLUSH then
             let* s := c_clear_hash s in
             if d_lookahead s =? 0 then
               Some (set_d_insert (set_d_block_start (set_d_strstart s 0) 0) 0)
             else Some s
           else Some s
         else Some s) in
      let* (s, z) := c_flush_pending s z in
      if z_avail_out z =? 0 then Some (set_d_last_flush s (-1), z, Some Z_OK) else Some (s, z, None)
    | finish_done => Some (s, z, None)
    end
  else Some (s, z, None).

(** ** Stage 9: the trailer *)
Definition c_deflate_trailer (s : dstate) (z : strm) (flush : Z) : option (dstate * strm * Z) :=
  if negb (flush =? Z_FINISH) then Some (s, z, Z_OK) else
  if d_wrap s <=? 0 then Some (s, z, Z_STREAM_END) else
  let a := z_adler z in
  let t := z_total_in z in
  let* s :=
    (if d_wrap s =? 2 then
       c_dput_bytes s [Z.land a 255; Z.land (Z.shiftr a 8) 255; Z.land (Z.shiftr a 16) 255;
                       Z.land (Z.shiftr a 24) 255; Z.land t 255; Z.land (Z.shiftr t 8) 255;
                       Z.land (Z.shiftr t 16) 255; Z.land (Z.shiftr t 24) 255]
     else
       let* s := c_putShortMSB s (u32 (Z.shiftr a 16)) in
       c_putShortMSB s (u32 (Z.land a 65535))) in
  let* (s, z) := c_flush_pending s z in
  let s := if d_wrap s >? 0 then set_d_wrap s (- d_wrap s) else s in
  Some (s, z, if negb (d_pending s =? 0) then Z_OK else Z_STREAM_END).

(** ** deflate(strm, flush) *)
Definition c_deflate (s : dstate) (z : strm) (flush : Z) : option (dstate * strm * Z) :=
  if bad_state s || (flush >? Z_BLOCK) || (flush <? 0) then Some (s, z, Z_STREAM_ERROR) else
  let* (s, z, o) :=
    then_stage (c_deflate_entry s z flush) (fun s z =>
    then_stage (c_deflate_zlib_header s z) (fun s z =>
    then_stage (c_deflate_gzip_header s z) (fun s z =>
    then_stage (c_deflate_extra s z) (fun s z =>
    then_stage (c_deflate_name s z) (fun s z =>
    then_stage (c_deflate_comment s z) (fun s z =>
    then_stage (c_deflate_hcrc s z) (fun s z =>
    c_deflate_compress s z flush))))))) in
  match o with
  | Some r => Some (s, z, r)
  | None => c_deflate_trailer s z flush
  end.

(** ** deflateParams(strm, level, strategy) *)
Definition c_deflateParams (s : dstate) (z : strm) (level strategy : Z) : option (dstate * strm * Z) :=
  if bad_state s then Some (s, z, Z_STREAM_ERROR) else
  let level := if level =? Z_DEFAULT_COMPRESSION then 6 else level in
  if (level <? 0) || (level >? 9) || (strategy <? 0) || (strategy >? Z_FIXED) then Some (s, z, Z_STREAM_ERROR) else
  let* func := cfg_func (d_level s) in
  let* (s, z, o) :=
    (if (negb (strategy =? d_strategy s) || negb (func =? cfg_f level)) && negb (d_last_flush s =? -2) then
       let* (s, z, err) := c_deflate s z Z_BLOCK in
       if err =? Z_STREAM_ERROR then Some (s, z, Some err) else
       if negb (z_avail_in z =? 0) then Some (s, z, Some Z_BUF_ERROR) else
       let* _ := guard (in_long (d_strstart s - d_block_start s)) in
       let* _ := guard (in_long (d_strstart s - d_block_start s + d_lookahead s)) in
       if negb (d_strstart s - d_block_start s + d_lookahead s =? 0) then Some (s, z, Some Z_BUF_ERROR)
       else Some (s, z, None)
     else Some (s, z, None)) in
  match o with
  | Some r => Some (s, z, r)
  | None =>
    let* s :=
      (if negb (d_level s =? level) then
         let* s := (if (d_level s =? 0) && negb (d_matches s =? 0) then
                      let* s := (if d_matches s =? 1 then c_slide_hash s else c_clear_hash s) in
                      Some (set_d_matches s 0)
                    else Some s) in
         let s := set_d_level s level in
         let '(good, lazy, nice, chain, _) := Znth level config_table in
         let s := set_d_max_lazy_match s lazy in
         let s := set_d_good_match s good in
         let s := set_d_nice_match s nice in
         Some (set_d_max_chain_length s chain)
       else Some s) in
    Some (set_d_strategy s strategy, z, Z_OK)
  end.

(** ** Tests on small cases *)
Definition t_out (n : Z) (data : list Z) : strm := mkST data 0 (Zlength data) 0 [] n 0 0 None.

Definition t_init (wb : Z) : option dstate :=
  match c_deflateInit2_ true true false 6 8 wb 1 0 true true true true true test_z with
  | Some (Some s, _, r) => if r =? Z_OK then Some s else None
  | _ => None
  end.

(** zlib, empty input, Z_FINISH with ample output: header 78 xx, an empty final block, Adler-32 of nothing. *)
Example test_deflate_zlib_empty :
  match t_init 9 with
  | Some s => match c_deflate s (t_out 100 []) Z_FINISH with
              | Some (s', z', r) => (r, z_out z', d_wrap s', d_status s')
              | None => (99, [], 0, 0) end
  | None => (98, [], 0, 0) end
  = (Z_STREAM_END, [24; 149; 3; 0; 0; 0; 0; 1], -1, FINISH_STATE).
Proof. vm_compute. reflexivity. Qed.

(** gzip without header, input "a", Z_FINISH. *)
Example test_deflate_gzip :
  match t_init 25 with
  | Some s => match c_deflate s (t_out 100 [97]) Z_FINISH with
              | Some (s', z', r) => (r, sublist 0 10 (z_out z'), Zlength (z_out z'), z_total_in z')
              | None => (99, [], 0, 0) end
  | None => (98, [], 0, 0) end
  = (Z_STREAM_END, [31; 139; 8; 0; 0; 0; 0; 0; 0; 3], 21, 1).
Proof. vm_compute. reflexivity. Qed.

(** A second Z_FINISH after the end: Z_STREAM_END without progress; another flush: Z_STREAM_ERROR. *)
Example test_deflate_after_end :
  match t_init 9 with
  | Some s => match c_deflate s (t_out 100 []) Z_FINISH with
              | Some (s', _, _) =>
                (match c_deflate s' (t_out 10 []) Z_FINISH with Some (_, z, r) => (r, z_out z) | None => (99, []) end,
                 match c_deflate s' (t_out 10 []) Z_NO_FLUSH with Some (_, _, r) => r | None => 99 end)
              | None => ((97, []), 97) end
  | None => ((98, []), 98) end
  = ((Z_STREAM_END, []), Z_STREAM_ERROR).
Proof. vm_compute. reflexivity. Qed.

(** gzip with a user header (name "ab", hcrc), output 1 byte per call is not tested here; one call. *)
Definition test_gzh : gzh := mkGZ 1 0 3 (Some [7; 8; 9]) 3 (Some [97; 98; 0]) None 1.
Example test_deflate_gzip_header :
  match t_init 25 with
  | Some s => match c_deflateSetHeader s test_z (Some test_gzh) with
              | Some (s, _, 0) => match c_deflate s (t_out 100 []) Z_FINISH with
                                   | Some (s', z', r) => (r, sublist 0 20 (z_out z'))
                                   | None => (99, []) end
              | _ => (97, []) end
  | None => (98, []) end
  = (Z_STREAM_END, [31; 139; 8; 1 + 2 + 4 + 8; 0; 0; 0; 0; 0; 3; 3; 0; 7; 8; 9; 97; 98; 0;
                    Z.land (Zlib.proof.crc32.Model.ref_crc32 0 [31; 139; 8; 15; 0; 0; 0; 0; 0; 3; 3; 0; 7; 8; 9; 97; 98; 0]) 255;
                    Z.shiftr (Z.land (Zlib.proof.crc32.Model.ref_crc32 0 [31; 139; 8; 15; 0; 0; 0; 0; 0; 3; 3; 0; 7; 8; 9; 97; 98; 0]) 65535) 8]).
Proof. vm_compute. reflexivity. Qed.

(** deflateParams before any deflate call (last_flush = -2): no flush, level and strategy set. *)
Example test_params :
  match t_init 9 with
  | Some s => match c_deflateParams s test_z 1 Z_FILTERED with
              | Some (s', _, r) => (r, d_level s', d_strategy s', d_max_chain_length s')
              | None => (99, 0, 0, 0) end
  | None => (98, 0, 0, 0) end
  = (Z_OK, 1, Z_FILTERED, 4).
Proof. vm_compute. reflexivity. Qed.

(** Resumption: a gzip header larger than pending_buf (512 bytes with memLevel 1: the EXTRA copy loop and the
    NAME loop flush in the middle), written 7 bytes per call, gives the same bytes as one call. *)
Fixpoint t_run (fuel : nat) (s : dstate) (z : strm) (n : Z) (acc : list Z) : option (list Z * Z) :=
  match fuel with
  | O => None
  | S f =>
    let* (s', z', r) := c_deflate s (set_z_out (set_z_avail_out z n) []) Z_FINISH in
    let acc := acc ++ z_out z' in
    if r =? Z_STREAM_END then Some (acc, z_total_out z')
    else if r =? Z_OK then t_run f s' z' n acc
    else Some (acc, r)
  end.

Definition t_big : gzh :=
  mkGZ 0 305419896 255 (Some (map (fun i => Z.of_nat i mod 256) (seq 0 600))) 600
       (Some (map (fun i => 1 + Z.of_nat i mod 200) (seq 0 300) ++ [0])) (Some [99; 0]) 1.

Definition t_big_run (n : Z) : option (list Z * Z) :=
  let* s := t_init 25 in
  let* (s, _, _) := c_deflateSetHeader s test_z (Some t_big) in
  t_run 1000 s (t_out n [1; 2; 3]) n [].

Definition t_resume : option (Z * bool) :=
  let* (a, _) := t_big_run 7 in
  let* (b, _) := t_big_run 4000 in
  Some (Zlength a, if list_eq_dec Z.eq_dec a b then true else false).

(** ... and the header CRC (bytes 915, 916) is the low 16 bits of the CRC-32 of the 915 header bytes before it;
    the trailer is the CRC-32 of the data [1; 2; 3] and its length. *)
Example test_resume : t_resume = Some (930, true).
Proof. vm_compute. reflexivity. Qed.

Example test_hcrc :
  (let* (a, _) := t_big_run 7 in
   Some (Z.land (Zlib.proof.crc32.Model.ref_crc32 0 (sublist 0 915 a)) 65535 =? Znth 915 a + 256 * Znth 916 a,
         sublist 922 930 a))
  = Some (true, let c := Zlib.proof.crc32.Model.ref_crc32 0 [1; 2; 3] in
                [Z.land c 255; Z.land (Z.shiftr c 8) 255; Z.land (Z.shiftr c 16) 255; Z.shiftr c 24; 3; 0; 0; 0]).
Proof. vm_compute. reflexivity. Qed.

(** Guards of this file that are not memory-access checks, and why:
    - [c_deflate_entry]: [in_int (old_flush * 2)] when avail_in == 0 and nothing is pending: RANK(old_flush)
      multiplies the int last_flush by 2 (last_flush is in -2..5 on every reachable state; the field is an int
      the model does not otherwise bound).  RANK(flush) needs none (flush is 0..5 there).
    - [c_deflateParams]: [in_long (strstart - block_start)] and [in_long (strstart - block_start + lookahead)]
      when avail_in == 0 after the deflate(strm, Z_BLOCK): the C computes them in long (block_start is a long;
      the uInt operands are converted to long).
    - [cfg_func] (deflate's dispatch, deflateParams' read of configuration_table[s->level]): [0 <= level <= 9]
      -- this is the bounds check of the read of configuration_table[s->level] (an array access), listed here
      because it is a check on a number of the state (s->level is in 0..9 on every reachable state).
      deflateParams' second read, configuration_table[level], is on the validated argument ([cfg_f], unchecked).
    - Loops ([extra_body], [str_body]): [loop FUEL]; [None] if the fuel runs out.
    - [c_gzhead]: a NULL gzhead in the states EXTRA .. HCRC is a NULL dereference (memory), not a guard.
    No other int arithmetic can overflow: the gzip flag sum is at most 31, [- s->wrap] in the trailer is
    evaluated only for wrap > 0, the zlib header is uInt arithmetic (truncated with u32). *)
