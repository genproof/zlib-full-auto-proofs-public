(* A functional model of zlib 1.3.2's inflate() (inflate.c, with the quickproof patch: I3 gotos as
   `leave = 1; break;`, D1 field copies, F1, F4) and of inflate_fast() (inffast.c, I4).

   It follows the C code statement by statement over the values of the variables (all numbers are Z),
   so that the VST proof of each case of the switch is a simulation:
   - istate: the fields of struct inflate_state (Records.v);  i_wdata = window[0 .. whave) (the window's
     valid bytes: wnext = whave while whave < wsize);  i_codes = state->codes[];  i_lens = state->lens[];
     state->work is scratch (not modelled);  the pointers lencode / distcode / next as tref / offsets;
   - hstate: the gz_header the application gave to inflateGetHeader (only read/written when i_head);
   - mst: the machine during one inflate() call: the struct, the header, the input bytes offered
     (m_inp, at next_in on entry), avail_out on entry (m_aout), and the locals: m_nx (bytes of m_inp
     consumed: next = next_in + m_nx, have = |m_inp| - m_nx), m_ow (bytes written: put = next_out + |m_ow|,
     left = m_aout - |m_ow|), hold, bits, in, out, ret, leave; the stream fields the loop writes (adler,
     msg, total_in, total_out) and the stream's next_in/next_out as last stored by RESTORE (m_snx, m_sow).
   One pass of the switch is `step`; the loop is the relation `loop`; the call is `inflate_call`. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import compcert.common.AST.
Require Export Zlib.proof.inflate.Records.
Require Export Zlib.proof.crc32.Model.
Require Export Zlib.proof.adler32.Model.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Constants                                                                                      *)

Definition HEAD := 16180.   Definition FLAGS := 16181.  Definition TIME := 16182.
Definition OS := 16183.     Definition EXLEN := 16184.  Definition EXTRA := 16185.
Definition NAME := 16186.   Definition COMMENT := 16187. Definition HCRC := 16188.
Definition DICTID := 16189. Definition DICT := 16190.   Definition TYPE := 16191.
Definition TYPEDO := 16192. Definition STORED := 16193. Definition COPY_ := 16194.
Definition COPY := 16195.   Definition TABLE := 16196.  Definition LENLENS := 16197.
Definition CODELENS := 16198. Definition LEN_ := 16199. Definition LEN := 16200.
Definition LENEXT := 16201. Definition DIST := 16202.   Definition DISTEXT := 16203.
Definition MATCH := 16204.  Definition LIT := 16205.    Definition CHECK := 16206.
Definition LENGTH := 16207. Definition DONE := 16208.   Definition BAD := 16209.
Definition MEM := 16210.    Definition SYNC := 16211.

Definition Z_OK := 0.  Definition Z_STREAM_END := 1.  Definition Z_NEED_DICT := 2.
Definition Z_STREAM_ERROR := -2.  Definition Z_DATA_ERROR := -3.  Definition Z_MEM_ERROR := -4.
Definition Z_BUF_ERROR := -5.
Definition Z_FINISH := 4.  Definition Z_BLOCK := 5.  Definition Z_TREES := 6.

Definition ENOUGH_CODES : Z := 1444.

(* the permutation of the code length code lengths (inflate.c `order`) *)
Definition order : list Z := [16; 17; 18; 0; 8; 7; 9; 6; 10; 5; 11; 4; 12; 3; 13; 2; 14; 1; 15].

(* ---------------------------------------------------------------------------------------------- *)
(* Machine arithmetic                                                                             *)

Definition u32 (x: Z) : Z := x mod 2 ^ 32.
Definition u64 (x: Z) : Z := x mod 2 ^ 64.
(* (int) of an unsigned value: the low 32 bits, two's complement *)
Definition s32 (x: Z) : Z := let y := x mod 2 ^ 32 in if y <? 2 ^ 31 then y else y - 2 ^ 32.

(* ZSWAP32 of an unsigned long (only its low 32 bits) *)
Definition swap32 (q: Z) : Z :=
  (Z.shiftr q 24) mod 256 + Z.land (Z.shiftr q 8) 65280 + Z.shiftl (Z.land q 65280) 8
  + Z.shiftl (q mod 256) 24.

(* ---------------------------------------------------------------------------------------------- *)
(* Table entries                                                                                  *)

Definition is_null_tab (t: tref) : bool := match t with TCodes _ => false | _ => true end.

(* ---------------------------------------------------------------------------------------------- *)
(* Accessors and small state updates of the machine                                              *)

Definition m_mode (m: mst) : Z := i_mode (m_s m).
Definition m_have (m: mst) : Z := Zlength (m_inp m) - m_nx m.
Definition m_left (m: mst) : Z := m_aout m - Zlength (m_ow m).

Definition upd_s (m: mst) (f: istate -> istate) : mst := set_m_s m (f (m_s m)).
Definition upd_h (m: mst) (f: hstate -> hstate) : mst := set_m_h m (f (m_h m)).

Definition set_mode (m: mst) (v: Z) : mst := upd_s m (fun s => set_i_mode s v).
Definition set_leave (m: mst) : mst := set_m_leave m 1.

(* BITS(n), n <= 32 *)
Definition bitsn (m: mst) (n: Z) : Z := m_hold m mod 2 ^ n.

(* PULLBYTE() (the byte is there) *)
Definition pull (m: mst) : mst :=
  let b := Znth (m_nx m) (m_inp m) in
  set_m_bits (set_m_hold (set_m_nx m (m_nx m + 1)) (u64 (m_hold m + b * 2 ^ m_bits m))) (u32 (m_bits m + 8)).

(* NEEDBITS(n): pull while bits < n; leave = 1 when the input runs out.  Four pulls suffice (n <= 32). *)
Fixpoint needbits_f (k: nat) (n: Z) (m: mst) : mst :=
  match k with
  | O => m
  | S k' => if m_bits m <? n then
              if m_have m =? 0 then set_leave m else needbits_f k' n (pull m)
            else m
  end.
Definition needbits (n: Z) (m: mst) : mst := needbits_f 4 n m.

Definition dropbits (n: Z) (m: mst) : mst :=
  set_m_bits (set_m_hold m (Z.shiftr (m_hold m) n)) (u32 (m_bits m - n)).
Definition initbits (m: mst) : mst := set_m_bits (set_m_hold m 0) 0.
Definition bytebits (m: mst) : mst :=
  set_m_bits (set_m_hold m (Z.shiftr (m_hold m) (m_bits m mod 8))) (m_bits m - m_bits m mod 8).

Definition set_bad (m: mst) (e: msgid) : mst := set_mode (set_m_msg m (Some e)) BAD.

(* RESTORE(): strm->next_in/next_out (as positions), state->hold, state->bits := the locals *)
Definition restore (m: mst) : mst :=
  upd_s (set_m_sow (set_m_snx m (m_nx m)) (Zlength (m_ow m)))
        (fun s => set_i_bits (set_i_hold s (m_hold m)) (m_bits m)).

(* input bytes [nx, nx + n) *)
Definition inbytes (m: mst) (n: Z) : list Z := sublist (m_nx m) (m_nx m + n) (m_inp m).

(* UPDATE_CHECK(check, buf, len): crc32 for gzip (flags != 0), adler32 for zlib *)
Definition update_check (flags check: Z) (data: list Z) : Z :=
  if flags =? 0 then adler32_z_val check data else ref_crc32 check data.

(* CRC2 / CRC4 of hold (hbuf[]) *)
Definition hbytes2 (h: Z) : list Z := [h mod 256; Z.shiftr h 8 mod 256].
Definition hbytes4 (h: Z) : list Z :=
  [h mod 256; Z.shiftr h 8 mod 256; Z.shiftr h 16 mod 256; Z.shiftr h 24 mod 256].
Definition crc_if (m: mst) (data: list Z) : mst :=
  let s := m_s m in
  if negb (Z.land (i_flags s) 512 =? 0) && negb (Z.land (i_wrap s) 4 =? 0)
  then upd_s m (fun s => set_i_check s (ref_crc32 (i_check s) data)) else m.

(* ---------------------------------------------------------------------------------------------- *)
(* Table lookups                                                                                  *)

(* the entry at index i of the table t (fixed tables are given as parameters) *)
Definition tab_entry (lenfix distfix: list entry) (s: istate) (t: tref) (i: Z) : entry :=
  match t with
  | TLenfix => Znth i lenfix
  | TDistfix => Znth i distfix
  | TCodes k => Znth (k + i) (i_codes s)
  end.

(* for (;;) { here = tab[BITS(nb)]; if (here.bits <= bits) break; PULLBYTE(); }
   Result: (here, m', ok): ok = false when the input ran out (leave). *)
Fixpoint lookup1_f (k: nat) (fx dx: list entry) (t: tref) (nb: Z) (m: mst) : entry * mst * bool :=
  let here := tab_entry fx dx (m_s m) t (bitsn m nb) in
  match k with
  | O => (here, m, true)
  | S k' => if e_bits here <=? m_bits m then (here, m, true)
            else if m_have m =? 0 then (here, set_leave m, false)
            else lookup1_f k' fx dx t nb (pull m)
  end.
(* at most 2 pulls for a valid table (bits <= 15); the fuel is never the limit (Inv) *)
Definition lookup1 := lookup1_f 3.

(* for (;;) { here = tab[last.val + (BITS(last.bits + last.op) >> last.bits)];
             if (last.bits + here.bits <= bits) break; PULLBYTE(); } *)
Fixpoint lookup2_f (k: nat) (fx dx: list entry) (t: tref) (last: entry) (m: mst) : entry * mst * bool :=
  let here := tab_entry fx dx (m_s m) t
                (e_val last + Z.shiftr (bitsn m (e_bits last + e_op last)) (e_bits last)) in
  match k with
  | O => (here, m, true)
  | S k' => if e_bits last + e_bits here <=? m_bits m then (here, m, true)
            else if m_have m =? 0 then (here, set_leave m, false)
            else lookup2_f k' fx dx t last (pull m)
  end.
Definition lookup2 := lookup2_f 3.

(* ---------------------------------------------------------------------------------------------- *)
(* inflate_table (its model, model.v), as inflate calls it                                       *)

(* inflate_table(type, lens + lo, n, &state->next, &bits, work) with *bits = req:
   table region codes[next .. ENOUGH); returns (ret, codes', next', bits'). *)
Definition call_table (type lo n req: Z) (s: istate) : Z * list entry * Z * Z :=
  let old := sublist (i_next s) ENOUGH_CODES (i_codes s) in
  let r := inflate_table_model type (sublist lo (lo + n) (i_lens s)) req old in
  (it_ret r, sublist 0 (i_next s) (i_codes s) ++ it_tab old r, i_next s + it_adv r, it_bits req r).

(* ---------------------------------------------------------------------------------------------- *)
(* The output copy of MATCH and inflate_fast                                                      *)

(* where the bytes of a copy come from: the window (index), or the output (index into m_ow) *)
Inductive src := SWin (i: Z) | SOut (i: Z).

(* copy n bytes, one at a time; an output source sees the bytes appended by the copy itself *)
Fixpoint copy_f (n: nat) (w: list Z) (sr: src) (ow: list Z) : list Z * src :=
  match n with
  | O => (ow, sr)
  | S n' =>
      match sr with
      | SWin i => copy_f n' w (SWin (i + 1)) (ow ++ [Znth i w])
      | SOut i => copy_f n' w (SOut (i + 1)) (ow ++ [Znth i ow])
      end
  end.
Definition copy_bytes (w: list Z) (sr: src) (n: Z) (ow: list Z) : list Z * src :=
  copy_f (Z.to_nat n) w sr ow.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases of the switch.  Each returns IBrk m (break out of the switch, leave = 1 to exit the    *)
(* loop) or IRet r m (return r from inflate).  Fallthroughs call the next case.                   *)

Inductive iout := IBrk (m: mst) | IRet (r: Z) (m: mst).

Section Cases.
Variables (flush: Z) (lenfix distfix: list entry).
(* inflate_fast, a parameter of the cases (defined below) *)
Variable fast : mst -> mst.

Definition c_DONE (m: mst) : iout := IBrk (set_leave (set_m_ret m Z_STREAM_END)).
Definition c_BAD (m: mst) : iout := IBrk (set_leave (set_m_ret m Z_DATA_ERROR)).

Definition c_LENGTH (m: mst) : iout :=
  let s := m_s m in
  let go m := c_DONE (set_mode m DONE) in
  if negb (i_wrap s =? 0) && negb (i_flags s =? 0) then
    let m := needbits 32 m in
    if m_leave m =? 1 then IBrk m else
    if negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (m_hold m =? i_total (m_s m) mod 2 ^ 32)
    then IBrk (set_bad m M_lcheck)
    else go (initbits m)
  else go m.

Definition c_CHECK (m: mst) : iout :=
  if negb (i_wrap (m_s m) =? 0) then
    let m := needbits 32 m in
    if m_leave m =? 1 then IBrk m else
    let out := u32 (m_out m - m_left m) in
    let m := set_m_tout m (u64 (m_tout m + out)) in
    let m := upd_s m (fun s => set_i_total s (u64 (i_total s + out))) in
    let m := if negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (out =? 0) then
               let c := update_check (i_flags (m_s m)) (i_check (m_s m))
                          (sublist (Zlength (m_ow m) - out) (Zlength (m_ow m)) (m_ow m)) in
               set_m_adler (upd_s m (fun s => set_i_check s c)) c
             else m in
    let m := set_m_out m (m_left m) in
    let s := m_s m in
    if negb (Z.land (i_wrap s) 4 =? 0) &&
       negb ((if i_flags s =? 0 then swap32 (m_hold m) else m_hold m) =? i_check s)
    then IBrk (set_bad m M_dcheck)
    else c_LENGTH (set_mode (initbits m) LENGTH)
  else c_LENGTH (set_mode m LENGTH).

Definition c_LIT (m: mst) : iout :=
  if m_left m =? 0 then IBrk (set_leave m) else
  IBrk (set_mode (set_m_ow m (m_ow m ++ [i_length (m_s m) mod 256])) LEN).

Definition c_MATCH (m: mst) : iout :=
  if m_left m =? 0 then IBrk (set_leave m) else
  let s := m_s m in
  let copy0 := u32 (m_out m - m_left m) in
  let fin (sr: src) (copy: Z) :=
    let copy := Z.min copy (m_left m) in
    let '(ow', _) := copy_bytes (i_wdata s) sr copy (m_ow m) in
    let len' := i_length s - copy in
    let m := upd_s (set_m_ow m ow') (fun s => set_i_length s len') in
    IBrk (if len' =? 0 then set_mode m LEN else m) in
  if copy0 <? i_offset s then
    let copy := i_offset s - copy0 in
    if (i_whave s <? copy) && negb (i_sane s =? 0) then IBrk (set_bad m M_far) else
    let '(sr, copy) := if i_wnext s <? copy then (SWin (i_wsize s - (copy - i_wnext s)), copy - i_wnext s)
                       else (SWin (i_wnext s - copy), copy) in
    fin sr (Z.min copy (i_length s))
  else fin (SOut (Zlength (m_ow m) - i_offset s)) (i_length s).

Definition c_DISTEXT (m: mst) : iout :=
  let k m := c_MATCH (set_mode m MATCH) in
  let ex := i_extra (m_s m) in
  if negb (ex =? 0) then
    let m := needbits ex m in
    if m_leave m =? 1 then IBrk m else
    let off := u32 (i_offset (m_s m) + bitsn m ex) in
    let m := dropbits ex (upd_s m (fun s => set_i_offset (set_i_back s (i_back s + ex)) off)) in
    k m
  else k m.

Definition c_DIST (m: mst) : iout :=
  let s := m_s m in
  let '(here, m, ok) := lookup1 lenfix distfix (i_distcode s) (i_distbits s) m in
  if negb ok then IBrk m else
  let '(here, m, ok) :=
    if Z.land (e_op here) 240 =? 0 then
      let '(h2, m, ok) := lookup2 lenfix distfix (i_distcode s) here m in
      if negb ok then (h2, m, false) else
      (h2, dropbits (e_bits here) (upd_s m (fun s => set_i_back s (i_back s + e_bits here))), true)
    else (here, m, true) in
  if negb ok then IBrk m else
  let m := dropbits (e_bits here) (upd_s m (fun s => set_i_back s (i_back s + e_bits here))) in
  if negb (Z.land (e_op here) 64 =? 0) then IBrk (set_bad m M_d_code) else
  let m := upd_s m (fun s => set_i_extra (set_i_offset s (e_val here)) (Z.land (e_op here) 15)) in
  c_DISTEXT (set_mode m DISTEXT).

Definition c_LENEXT (m: mst) : iout :=
  let k m := c_DIST (set_mode (upd_s m (fun s => set_i_was s (i_length s))) DIST) in
  let ex := i_extra (m_s m) in
  if negb (ex =? 0) then
    let m := needbits ex m in
    if m_leave m =? 1 then IBrk m else
    let ln := u32 (i_length (m_s m) + bitsn m ex) in
    let m := dropbits ex (upd_s m (fun s => set_i_length (set_i_back s (i_back s + ex)) ln)) in
    k m
  else k m.

Definition c_LEN (m: mst) : iout :=
  if (6 <=? m_have m) && (258 <=? m_left m) && (m_bits m <? 8) then
    let m := fast (restore m) in
    IBrk (if m_mode m =? TYPE then upd_s m (fun s => set_i_back s (-1)) else m)
  else
  let m := upd_s m (fun s => set_i_back s 0) in
  let s := m_s m in
  let '(here, m, ok) := lookup1 lenfix distfix (i_lencode s) (i_lenbits s) m in
  if negb ok then IBrk m else
  let '(here, m, ok) :=
    if negb (e_op here =? 0) && (Z.land (e_op here) 240 =? 0) then
      let '(h2, m, ok) := lookup2 lenfix distfix (i_lencode s) here m in
      if negb ok then (h2, m, false) else
      (h2, dropbits (e_bits here) (upd_s m (fun s => set_i_back s (i_back s + e_bits here))), true)
    else (here, m, true) in
  if negb ok then IBrk m else
  let m := dropbits (e_bits here) (upd_s m (fun s => set_i_back s (i_back s + e_bits here))) in
  let m := upd_s m (fun s => set_i_length s (e_val here)) in
  if e_op here =? 0 then IBrk (set_mode m LIT) else
  if negb (Z.land (e_op here) 32 =? 0) then
    IBrk (set_mode (upd_s m (fun s => set_i_back s (-1))) TYPE) else
  if negb (Z.land (e_op here) 64 =? 0) then IBrk (set_bad m M_ll_code) else
  c_LENEXT (set_mode (upd_s m (fun s => set_i_extra s (Z.land (e_op here) 15))) LENEXT).

Definition c_LEN_ (m: mst) : iout := c_LEN (set_mode m LEN).

(* CODELENS: one pass of `while (state->have < state->nlen + state->ndist)`.
   CLnext m: continue the while; CLleave m: leave = 1 (out of input); CLbad m: mode = BAD. *)
Inductive clout := CLnext (m: mst) | CLleave (m: mst) | CLbad (m: mst).

Fixpoint lens_fill (k: nat) (len: Z) (s: istate) : istate :=
  match k with
  | O => s
  | S k' => lens_fill k' len (set_i_have (set_i_lens s (upd_Znth (i_have s) (i_lens s) len)) (i_have s + 1))
  end.

Definition codelens_iter (m: mst) : clout :=
  let s := m_s m in
  let '(here, m, ok) := lookup1 lenfix distfix (i_lencode s) (i_lenbits s) m in
  if negb ok then CLleave m else
  if e_val here <? 16 then
    let m := dropbits (e_bits here) m in
    CLnext (upd_s m (fun s => set_i_have (set_i_lens s (upd_Znth (i_have s) (i_lens s) (e_val here)))
                                         (i_have s + 1)))
  else
    let '(m, len, copy, ok) :=
      if e_val here =? 16 then
        let m := needbits (e_bits here + 2) m in
        if m_leave m =? 1 then (m, 0, 0, false) else
        let m := dropbits (e_bits here) m in
        if i_have (m_s m) =? 0 then (set_bad m M_repeat, 0, 0, true) else
        let len := Znth (i_have (m_s m) - 1) (i_lens (m_s m)) in
        let copy := 3 + bitsn m 2 in
        (dropbits 2 m, len, copy, true)
      else if e_val here =? 17 then
        let m := needbits (e_bits here + 3) m in
        if m_leave m =? 1 then (m, 0, 0, false) else
        let m := dropbits (e_bits here) m in
        let copy := 3 + bitsn m 3 in
        (dropbits 3 m, 0, copy, true)
      else
        let m := needbits (e_bits here + 7) m in
        if m_leave m =? 1 then (m, 0, 0, false) else
        let m := dropbits (e_bits here) m in
        let copy := 11 + bitsn m 7 in
        (dropbits 7 m, 0, copy, true) in
    if negb ok then CLleave m else
    if m_mode m =? BAD then CLbad m else
    let s := m_s m in
    if i_nlen s + i_ndist s <? i_have s + copy then CLbad (set_bad m M_repeat) else
    CLnext (upd_s m (lens_fill (Z.to_nat copy) len)).

(* the while loop; fuel: each pass adds to have (at most nlen + ndist <= 316 passes) *)
Fixpoint codelens_loop (k: nat) (m: mst) : clout :=
  match k with
  | O => CLnext m
  | S k' =>
      let s := m_s m in
      if i_have s <? i_nlen s + i_ndist s then
        match codelens_iter m with
        | CLnext m' => codelens_loop k' m'
        | o => o
        end
      else CLnext m
  end.

Definition c_CODELENS (m: mst) : iout :=
  match codelens_loop 320 m with
  | CLleave m => IBrk m
  | CLbad m => IBrk m
  | CLnext m =>
      let s := m_s m in
      if Znth 256 (i_lens s) =? 0 then IBrk (set_bad m M_eob) else
      let s := set_i_lenbits (set_i_lencode (set_i_next s 0) (TCodes 0)) 9 in
      let '(r, codes, nxt, lb) := call_table LENS 0 (i_nlen s) 9 s in
      let s := set_i_lenbits (set_i_next (set_i_codes s codes) nxt) lb in
      let m := set_m_ret (set_m_s m s) r in
      if negb (r =? 0) then IBrk (set_bad m M_ll_set) else
      let s := set_i_distbits (set_i_distcode s (TCodes (i_next s))) 6 in
      let '(r, codes, nxt, db) := call_table DISTS (i_nlen s) (i_ndist s) 6 s in
      let s := set_i_distbits (set_i_next (set_i_codes s codes) nxt) db in
      let m := set_m_ret (set_m_s m s) r in
      if negb (r =? 0) then IBrk (set_bad m M_d_set) else
      let m := set_mode m LEN_ in
      if flush =? Z_TREES then IBrk (set_leave m) else c_LEN_ m
  end.

(* while (state->have < state->ncode) { NEEDBITS(3); lens[order[have++]] = BITS(3); DROPBITS(3); } *)
Fixpoint lenlens_loop (k: nat) (m: mst) : mst :=
  match k with
  | O => m
  | S k' =>
      let s := m_s m in
      if i_have s <? i_ncode s then
        let m := needbits 3 m in
        if m_leave m =? 1 then m else
        let s := m_s m in
        let m := upd_s m (fun _ => set_i_have (set_i_lens s (upd_Znth (Znth (i_have s) order) (i_lens s) (bitsn m 3)))
                                               (i_have s + 1)) in
        lenlens_loop k' (dropbits 3 m)
      else m
  end.

(* while (state->have < 19) lens[order[have++]] = 0; *)
Fixpoint lenlens_zero (k: nat) (s: istate) : istate :=
  match k with
  | O => s
  | S k' => if i_have s <? 19 then
              lenlens_zero k' (set_i_have (set_i_lens s (upd_Znth (Znth (i_have s) order) (i_lens s) 0)) (i_have s + 1))
            else s
  end.

Definition c_LENLENS (m: mst) : iout :=
  let m := lenlens_loop 19 m in
  if m_leave m =? 1 then IBrk m else
  let s := lenlens_zero 19 (m_s m) in
  let s := set_i_lenbits (set_i_distcode (set_i_lencode (set_i_next s 0) (TCodes 0)) (TCodes 0)) 7 in
  let '(r, codes, nxt, lb) := call_table CODES 0 19 7 s in
  let s := set_i_lenbits (set_i_next (set_i_codes s codes) nxt) lb in
  let m := set_m_ret (set_m_s m s) r in
  if negb (r =? 0) then IBrk (set_bad m M_cl_set) else
  c_CODELENS (set_mode (upd_s m (fun s => set_i_have s 0)) CODELENS).

Definition c_TABLE (m: mst) : iout :=
  let m := needbits 14 m in
  if m_leave m =? 1 then IBrk m else
  let nlen := bitsn m 5 + 257 in let m := dropbits 5 m in
  let ndist := bitsn m 5 + 1 in let m := dropbits 5 m in
  let ncode := bitsn m 4 + 4 in let m := dropbits 4 m in
  let m := upd_s m (fun s => set_i_ncode (set_i_ndist (set_i_nlen s nlen) ndist) ncode) in
  if (286 <? nlen) || (30 <? ndist) then IBrk (set_bad m M_toomany) else
  c_LENLENS (set_mode (upd_s m (fun s => set_i_have s 0)) LENLENS).

Definition c_COPY (m: mst) : iout :=
  let s := m_s m in
  if negb (i_length s =? 0) then
    let copy := Z.min (Z.min (i_length s) (m_have m)) (m_left m) in
    if copy =? 0 then IBrk (set_leave m) else
    IBrk (upd_s (set_m_nx (set_m_ow m (m_ow m ++ inbytes m copy)) (m_nx m + copy))
                (fun s => set_i_length s (i_length s - copy)))
  else IBrk (set_mode m TYPE).

Definition c_COPY_ (m: mst) : iout := c_COPY (set_mode m COPY).

Definition c_STORED (m: mst) : iout :=
  let m := needbits 32 (bytebits m) in
  if m_leave m =? 1 then IBrk m else
  if negb (Z.land (m_hold m) 65535 =? Z.lxor (Z.shiftr (m_hold m) 16) 65535)
  then IBrk (set_bad m M_stored) else
  let m := set_mode (initbits (upd_s m (fun s => set_i_length s (m_hold m mod 65536)))) COPY_ in
  if flush =? Z_TREES then IBrk (set_leave m) else c_COPY_ m.

Definition c_TYPEDO (m: mst) : iout :=
  if negb (i_last (m_s m) =? 0) then IBrk (set_mode (bytebits m) CHECK) else
  let m := needbits 3 m in
  if m_leave m =? 1 then IBrk m else
  let m := dropbits 1 (upd_s m (fun s => set_i_last s (bitsn m 1))) in
  let bt := bitsn m 2 in
  if bt =? 0 then IBrk (dropbits 2 (set_mode m STORED))
  else if bt =? 1 then
    let m := set_mode (upd_s m (fun s =>
               set_i_distbits (set_i_distcode (set_i_lenbits (set_i_lencode s TLenfix) 9) TDistfix) 5)) LEN_ in
    if flush =? Z_TREES then IBrk (set_leave (dropbits 2 m)) else IBrk (dropbits 2 m)
  else if bt =? 2 then IBrk (dropbits 2 (set_mode m TABLE))
  else IBrk (dropbits 2 (set_bad m M_btype)).

Definition c_TYPE (m: mst) : iout :=
  if (flush =? Z_BLOCK) || (flush =? Z_TREES) then IBrk (set_leave m) else c_TYPEDO m.

Definition c_DICT (m: mst) : iout :=
  if i_havedict (m_s m) =? 0 then
    let m := restore m in
    IRet Z_NEED_DICT (set_m_tin m (u64 (m_tin m + u32 (m_in m - m_have m))))
  else c_TYPE (set_mode (set_m_adler (upd_s m (fun s => set_i_check s 1)) 1) TYPE).

Definition c_DICTID (m: mst) : iout :=
  let m := needbits 32 m in
  if m_leave m =? 1 then IBrk m else
  let c := swap32 (m_hold m) in
  c_DICT (set_mode (initbits (set_m_adler (upd_s m (fun s => set_i_check s c)) c)) DICT).

Definition c_HCRC (m: mst) : iout :=
  let fin m :=
    let m := if i_head (m_s m) then
               upd_h m (fun h => set_h_done (set_h_hcrc h (Z.land (Z.shiftr (i_flags (m_s m)) 9) 1)) 1)
             else m in
    IBrk (set_mode (set_m_adler (upd_s m (fun s => set_i_check s 0)) 0) TYPE) in
  if negb (Z.land (i_flags (m_s m)) 512 =? 0) then
    let m := needbits 16 m in
    if m_leave m =? 1 then IBrk m else
    if negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (m_hold m =? Z.land (i_check (m_s m)) 65535)
    then IBrk (set_bad m M_hcrc)
    else fin (initbits m)
  else fin m.

(* the do-while of NAME / COMMENT: read bytes from next until a zero byte (included) or `have` bytes;
   copy them into buf at [length, ...) while length < max.  Returns (copy, last byte, length', buf'). *)
Fixpoint zstr_f (k: nat) (bytes: list Z) (have length max: Z) (wr: bool) (buf: list Z) (copy: Z)
  : Z * Z * Z * list Z :=
  match k with
  | O => (copy, 0, length, buf)
  | S k' =>
      let b := Znth copy bytes in
      let '(length, buf) := if wr && (length <? max) then (length + 1, upd_Znth length buf b) else (length, buf) in
      if negb (b =? 0) && (copy + 1 <? have) then zstr_f k' bytes have length max wr buf (copy + 1)
      else (copy + 1, b, length, buf)
  end.

Definition c_COMMENT (m: mst) : iout :=
  let fin m := c_HCRC (set_mode (upd_s m (fun s => set_i_length s 0)) HCRC) in
  if negb (Z.land (i_flags (m_s m)) 4096 =? 0) then
    if m_have m =? 0 then IBrk (set_leave m) else
    let h := m_h m in
    let wr := i_head (m_s m) && h_cp h in
    let '(copy, b, ln, buf) := zstr_f (Z.to_nat (m_have m)) (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m))
                                 (m_have m) (i_length (m_s m)) (h_comm_max h) wr (h_cbuf h) 0 in
    let m := crc_if m (inbytes m copy) in
    let m := upd_h (upd_s m (fun s => set_i_length s ln)) (fun h => set_h_cbuf h buf) in
    let m := set_m_nx m (m_nx m + copy) in
    if negb (b =? 0) then IBrk (set_leave m) else fin m
  else fin (if i_head (m_s m) then upd_h m (fun h => set_h_cp h false) else m).

Definition c_NAME (m: mst) : iout :=
  let fin m := c_COMMENT (set_mode (upd_s m (fun s => set_i_length s 0)) COMMENT) in
  if negb (Z.land (i_flags (m_s m)) 2048 =? 0) then
    if m_have m =? 0 then IBrk (set_leave m) else
    let h := m_h m in
    let wr := i_head (m_s m) && h_np h in
    let '(copy, b, ln, buf) := zstr_f (Z.to_nat (m_have m)) (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m))
                                 (m_have m) (i_length (m_s m)) (h_name_max h) wr (h_nbuf h) 0 in
    let m := crc_if m (inbytes m copy) in
    let m := upd_h (upd_s m (fun s => set_i_length s ln)) (fun h => set_h_nbuf h buf) in
    let m := set_m_nx m (m_nx m + copy) in
    if negb (b =? 0) then IBrk (set_leave m) else fin m
  else fin (if i_head (m_s m) then upd_h m (fun h => set_h_np h false) else m).

(* zmemcpy(head->extra + len, next, n): bytes [nx, nx + n) into xbuf at [len, len + n) *)
Definition put_bytes (buf: list Z) (pos: Z) (bytes: list Z) : list Z :=
  sublist 0 pos buf ++ bytes ++ sublist (pos + Zlength bytes) (Zlength buf) buf.

Definition c_EXTRA (m: mst) : iout :=
  let fin m := c_NAME (set_mode (upd_s m (fun s => set_i_length s 0)) NAME) in
  let s := m_s m in
  if negb (Z.land (i_flags s) 1024 =? 0) then
    let copy := Z.min (i_length s) (m_have m) in
    let m := if negb (copy =? 0) then
        let h := m_h m in
        let len := u32 (h_extra_len h - i_length s) in
        let m := if i_head s && h_xp h && (len <? h_extra_max h) then
                   let n := if h_extra_max h <? u32 (len + copy) then h_extra_max h - len else copy in
                   upd_h m (fun h => set_h_xbuf h (put_bytes (h_xbuf h) len (inbytes m n)))
                 else m in
        let m := crc_if m (inbytes m copy) in
        set_m_nx (upd_s m (fun s => set_i_length s (i_length s - copy))) (m_nx m + copy)
      else m in
    if negb (i_length (m_s m) =? 0) then IBrk (set_leave m) else fin m
  else fin m.

Definition c_EXLEN (m: mst) : iout :=
  let fin m := c_EXTRA (set_mode m EXTRA) in
  if negb (Z.land (i_flags (m_s m)) 1024 =? 0) then
    let m := needbits 16 m in
    if m_leave m =? 1 then IBrk m else
    let v := u32 (m_hold m) in
    let m := upd_s m (fun s => set_i_length s v) in
    let m := if i_head (m_s m) then upd_h m (fun h => set_h_extra_len h v) else m in
    fin (initbits (crc_if m (hbytes2 (m_hold m))))
  else fin (if i_head (m_s m) then upd_h m (fun h => set_h_xp h false) else m).

Definition c_OS (m: mst) : iout :=
  let m := needbits 16 m in
  if m_leave m =? 1 then IBrk m else
  let m := if i_head (m_s m) then
             upd_h m (fun h => set_h_os (set_h_xflags h (Z.land (m_hold m) 255)) (s32 (Z.shiftr (m_hold m) 8)))
           else m in
  c_EXLEN (set_mode (initbits (crc_if m (hbytes2 (m_hold m)))) EXLEN).

Definition c_TIME (m: mst) : iout :=
  let m := needbits 32 m in
  if m_leave m =? 1 then IBrk m else
  let m := if i_head (m_s m) then upd_h m (fun h => set_h_time h (m_hold m)) else m in
  c_OS (set_mode (initbits (crc_if m (hbytes4 (m_hold m)))) OS).

Definition c_FLAGS (m: mst) : iout :=
  let m := needbits 16 m in
  if m_leave m =? 1 then IBrk m else
  let fl := s32 (m_hold m) in
  let m := upd_s m (fun s => set_i_flags s fl) in
  if negb (Z.land fl 255 =? 8) then IBrk (set_bad m M_method) else
  if negb (Z.land fl 57344 =? 0) then IBrk (set_bad m M_hflags) else
  let m := if i_head (m_s m) then upd_h m (fun h => set_h_text h (Z.land (Z.shiftr (m_hold m) 8) 1)) else m in
  c_TIME (set_mode (initbits (crc_if m (hbytes2 (m_hold m)))) TIME).

Definition c_HEAD (m: mst) : iout :=
  if i_wrap (m_s m) =? 0 then IBrk (set_mode m TYPEDO) else
  let m := needbits 16 m in
  if m_leave m =? 1 then IBrk m else
  let s := m_s m in
  if negb (Z.land (i_wrap s) 2 =? 0) && (m_hold m =? 35615) then
    let m := upd_s m (fun s => set_i_check (set_i_wbits s (if i_wbits s =? 0 then 15 else i_wbits s))
                                           (ref_crc32 0 (hbytes2 (m_hold m)))) in
    IBrk (set_mode (initbits m) FLAGS)
  else
  let m := if i_head s then upd_h m (fun h => set_h_done h (-1)) else m in
  if (Z.land (i_wrap s) 1 =? 0) ||
     negb (((m_hold m mod 256) * 256 + Z.shiftr (m_hold m) 8) mod 31 =? 0)
  then IBrk (set_bad m M_hdr_check) else
  if negb (m_hold m mod 16 =? 8) then IBrk (set_bad m M_method) else
  let m := dropbits 4 m in
  let len := m_hold m mod 16 + 8 in
  let m := upd_s m (fun s => set_i_wbits s (if i_wbits s =? 0 then len else i_wbits s)) in
  if (15 <? len) || (i_wbits (m_s m) <? len) then IBrk (set_bad m M_wsize) else
  let mode := if Z.land (m_hold m) 512 =? 0 then TYPE else DICTID in
  let m := upd_s m (fun s => set_i_check (set_i_flags (set_i_dmax s (2 ^ len)) 0) 1) in
  IBrk (set_mode (initbits (set_m_adler m 1)) mode).

(* one pass of the switch *)
Definition step (m: mst) : iout :=
  let md := m_mode m in
  if md =? HEAD then c_HEAD m
  else if md =? FLAGS then c_FLAGS m
  else if md =? TIME then c_TIME m
  else if md =? OS then c_OS m
  else if md =? EXLEN then c_EXLEN m
  else if md =? EXTRA then c_EXTRA m
  else if md =? NAME then c_NAME m
  else if md =? COMMENT then c_COMMENT m
  else if md =? HCRC then c_HCRC m
  else if md =? DICTID then c_DICTID m
  else if md =? DICT then c_DICT m
  else if md =? TYPE then c_TYPE m
  else if md =? TYPEDO then c_TYPEDO m
  else if md =? STORED then c_STORED m
  else if md =? COPY_ then c_COPY_ m
  else if md =? COPY then c_COPY m
  else if md =? TABLE then c_TABLE m
  else if md =? LENLENS then c_LENLENS m
  else if md =? CODELENS then c_CODELENS m
  else if md =? LEN_ then c_LEN_ m
  else if md =? LEN then c_LEN m
  else if md =? LENEXT then c_LENEXT m
  else if md =? DIST then c_DIST m
  else if md =? DISTEXT then c_DISTEXT m
  else if md =? MATCH then c_MATCH m
  else if md =? LIT then c_LIT m
  else if md =? CHECK then c_CHECK m
  else if md =? LENGTH then c_LENGTH m
  else if md =? DONE then c_DONE m
  else if md =? BAD then c_BAD m
  else if md =? MEM then IRet Z_MEM_ERROR m
  else IRet Z_STREAM_ERROR m.

End Cases.

(* ---------------------------------------------------------------------------------------------- *)
(* inflate_fast (inffast.c)                                                                       *)

Section Fast.
Variables (lenfix distfix: list entry).

(* in the fast loop the input is read without a test: *in++ *)
Definition fpull (m: mst) : mst := pull m.

(* the table walk of inflate_fast: here = tab + (hold & mask); then while the entry is a link:
   hold >>= here->bits; bits -= here->bits; here = tab + here->val + (hold & ((1 << op) - 1)).
   `islink op` is the negation of the loop's exit test (length table: op == 0 || op & 16 || op & 64;
   distance table: op & 16 || op & 64).  Fuel 2: a valid table has at most one link. *)
Fixpoint fwalk_f (k: nat) (islink: Z -> bool) (t: tref) (here: entry) (m: mst) : entry * mst :=
  let m := set_m_bits (set_m_hold m (Z.shiftr (m_hold m) (e_bits here))) (u32 (m_bits m - e_bits here)) in
  match k with
  | O => (here, m)
  | S k' => if islink (e_op here)
            then fwalk_f k' islink t (tab_entry lenfix distfix (m_s m) t (e_val here + m_hold m mod 2 ^ e_op here)) m
            else (here, m)
  end.
Definition len_link (op: Z) : bool := negb ((op =? 0) || negb (Z.land op 16 =? 0) || negb (Z.land op 64 =? 0)).
Definition dist_link (op: Z) : bool := negb (negb (Z.land op 16 =? 0) || negb (Z.land op 64 =? 0)).

(* the loop body; true = go on (the do-while test decides), false = break *)
Definition fast_iter (m: mst) : bool * mst :=
  let s := m_s m in
  let m := if m_bits m <? 15 then fpull (fpull m) else m in
  let '(here, m) := fwalk_f 2 len_link (i_lencode s) (tab_entry lenfix distfix s (i_lencode s) (m_hold m mod 2 ^ i_lenbits s)) m in
  let op := e_op here in
  if op =? 0 then (true, set_m_ow m (m_ow m ++ [e_val here mod 256]))
  else if negb (Z.land op 16 =? 0) then
    let len := e_val here in
    let opx := Z.land op 15 in
    let '(len, m) :=
      if negb (opx =? 0) then
        let m := if m_bits m <? opx then fpull m else m in
        (u32 (len + m_hold m mod 2 ^ opx), set_m_bits (set_m_hold m (Z.shiftr (m_hold m) opx)) (u32 (m_bits m - opx)))
      else (len, m) in
    let m := if m_bits m <? 15 then fpull (fpull m) else m in
    let '(here, m) := fwalk_f 2 dist_link (i_distcode s) (tab_entry lenfix distfix s (i_distcode s) (m_hold m mod 2 ^ i_distbits s)) m in
    let op := e_op here in
    if negb (Z.land op 16 =? 0) then
      let dist := e_val here in
      let opx := Z.land op 15 in
      let m := if m_bits m <? opx then (let m := fpull m in if m_bits m <? opx then fpull m else m) else m in
      let dist := u32 (dist + m_hold m mod 2 ^ opx) in
      let m := set_m_bits (set_m_hold m (Z.shiftr (m_hold m) opx)) (u32 (m_bits m - opx)) in
      let op := Zlength (m_ow m) in        (* out - beg *)
      if op <? dist then
        let op := dist - op in
        if (i_whave s <? op) && negb (i_sane s =? 0) then (false, set_bad m F_far) else
        let w := i_wdata s in
        let wsz := i_wsize s in let wnx := i_wnext s in
        (* the window part, then the rest (copy of `len` bytes from `sr`) *)
        let '(ow, sr, len) :=
          if wnx =? 0 then
            if op <? len then
              let '(ow, _) := copy_bytes w (SWin (wsz - op)) op (m_ow m) in
              (ow, SOut (Zlength ow - dist), len - op)
            else (m_ow m, SWin (wsz - op), len)
          else if wnx <? op then
            let op2 := op - wnx in
            if op2 <? len then
              let '(ow, _) := copy_bytes w (SWin (wsz + wnx - op)) op2 (m_ow m) in
              let len := len - op2 in
              if wnx <? len then
                let '(ow, _) := copy_bytes w (SWin 0) wnx ow in
                (ow, SOut (Zlength ow - dist), len - wnx)
              else (ow, SWin 0, len)
            else (m_ow m, SWin (wsz + wnx - op), len)
          else
            if op <? len then
              let '(ow, _) := copy_bytes w (SWin (wnx - op)) op (m_ow m) in
              (ow, SOut (Zlength ow - dist), len - op)
            else (m_ow m, SWin (wnx - op), len) in
        let '(ow, _) := copy_bytes w sr len ow in
        (true, set_m_ow m ow)
      else
        let '(ow, _) := copy_bytes (i_wdata s) (SOut (Zlength (m_ow m) - dist)) len (m_ow m) in
        (true, set_m_ow m ow)
    else (false, set_bad m F_d_code)
  else if negb (Z.land op 32 =? 0) then (false, set_mode m TYPE)
  else (false, set_bad m F_ll_code).

(* do { ... } while (in < last && out < end);  fuel: each pass that goes on writes a byte *)
Fixpoint fast_loop (k: nat) (m: mst) : mst :=
  match k with
  | O => m
  | S k' =>
      let '(go, m) := fast_iter m in
      if go && (m_nx m <? Zlength (m_inp m) - 5) && (Zlength (m_ow m) <? m_aout m - 257)
      then fast_loop k' m else m
  end.

(* inflate_fast(strm, start): the loop, then the unused bytes back, and the stores to strm/state *)
Definition fast (m: mst) : mst :=
  let m := fast_loop (Z.to_nat (m_aout m) + 1) m in
  let len := Z.shiftr (m_bits m) 3 in
  let m := set_m_nx m (m_nx m - len) in
  let bits := m_bits m - len * 8 in
  let m := set_m_bits (set_m_hold m (m_hold m mod 2 ^ bits)) bits in
  restore m.

End Fast.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop and the call                                                                         *)

Section Call.
Variables (flush: Z) (lenfix distfix: list entry).

Definition stepf (m: mst) : iout := step flush lenfix distfix (fast lenfix distfix) m.

(* for (;;) { switch ...; if (leave) break; } *)
Inductive loop : mst -> iout -> Prop :=
| loop_ret: forall m r m', stepf m = IRet r m' -> loop m (IRet r m')
| loop_leave: forall m m', stepf m = IBrk m' -> m_leave m' = 1 -> loop m (IBrk m')
| loop_next: forall m m' o, stepf m = IBrk m' -> m_leave m' <> 1 -> loop m' o -> loop m o.

End Call.

(* updatewindow(strm, end, copy) when the window exists (or was just allocated): data = the copy bytes
   before end *)
Definition updatewindow (s: istate) (data: list Z) : istate :=
  let copy := Zlength data in
  let s := if i_wsize s =? 0 then set_i_whave (set_i_wnext (set_i_wsize s (2 ^ i_wbits s)) 0) 0 else s in
  let ws := i_wsize s in
  let w := i_wdata s in
  if ws <=? copy then
    set_i_wdata (set_i_whave (set_i_wnext s 0) ws) (sublist (copy - ws) copy data)
  else
    let dist := Z.min (ws - i_wnext s) copy in
    let src1 := sublist 0 dist data in
    let full := sublist 0 (i_wnext s) w ++ src1 ++ sublist (i_wnext s + dist) (Zlength w) w in
    let copy' := copy - dist in
    if negb (copy' =? 0) then
      let src2 := sublist dist copy data in
      set_i_wdata (set_i_whave (set_i_wnext s copy') ws) (src2 ++ sublist copy' (Zlength full) full)
    else
      let wn := i_wnext s + dist in
      let wh := if i_whave s <? ws then i_whave s + dist else i_whave s in
      set_i_wdata (set_i_whave (set_i_wnext s (if wn =? ws then 0 else wn)) wh) full.

(* the outcome of an inflate() call on a valid stream *)
Record result := Res {
  r_ret : Z;              (* return value *)
  r_m : mst;              (* the final machine: struct, header, output, counters, stream fields *)
  r_dtype : option Z      (* strm->data_type (None: not written) *)
}.

(* the window update at inf_leave is attempted *)
Definition leave_ok (flush: Z) (m: mst) : bool :=
  let s := m_s m in
  negb (i_wsize s =? 0) ||
  (negb (m_out m =? m_left m) && (m_mode m <? BAD) && ((m_mode m <? CHECK) || negb (flush =? Z_FINISH))).

(* inf_leave when the window update (if any) succeeds *)
Definition leave_fin (flush: Z) (m: mst) : result :=
  let upd := leave_ok flush m in
  let m := restore m in
  let m := if upd then
             let copy := u32 (m_out m - m_left m) in
             upd_s m (fun s => set_i_win (updatewindow s (sublist (Zlength (m_ow m) - copy) (Zlength (m_ow m)) (m_ow m))) true)
           else m in
  let inn := u32 (m_in m - m_have m) in
  let out := u32 (m_out m - m_left m) in
  let m := set_m_tout (set_m_tin m (u64 (m_tin m + inn))) (u64 (m_tout m + out)) in
  let m := upd_s m (fun s => set_i_total s (u64 (i_total s + out))) in
  let m := if negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (out =? 0) then
             let c := update_check (i_flags (m_s m)) (i_check (m_s m))
                        (sublist (Zlength (m_ow m) - out) (Zlength (m_ow m)) (m_ow m)) in
             set_m_adler (upd_s m (fun s => set_i_check s c)) c
           else m in
  let s := m_s m in
  let dt := m_bits m + (if i_last s =? 0 then 0 else 64) + (if i_mode s =? TYPE then 128 else 0)
            + (if (i_mode s =? LEN_) || (i_mode s =? COPY_) then 256 else 0) in
  let r := if (((inn =? 0) && (out =? 0)) || (flush =? Z_FINISH)) && (m_ret m =? Z_OK)
           then Z_BUF_ERROR else m_ret m in
  Res r m (Some dt).

(* inf_leave: RESTORE, the window (allocated when needed: the allocation may fail), the counters,
   the check value, data_type, the return code *)
Inductive inf_leave (flush: Z) (m: mst) : result -> Prop :=
| il_mem: leave_ok flush m = true -> i_win (m_s m) = false ->
    inf_leave flush m (Res Z_MEM_ERROR (set_mode (restore m) MEM) None)
| il_ok: inf_leave flush m (leave_fin flush m).

(* the loop from the machine at its head, then the return *)
Definition run (flush: Z) (fx dx: list entry) (m0: mst) (res: result) : Prop :=
  exists o, loop flush fx dx m0 o /\
  match o with
  | IRet r m => res = Res r m None
  | IBrk m => inf_leave flush m res
  end.
