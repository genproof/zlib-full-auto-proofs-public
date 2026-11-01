(* The abstract decoder of the law api_split_invariant: inflate() as a deterministic machine that reads the
   input as one bit stream and writes the output one byte at a time.

   An inflate() call is limited by the input it is offered and by its output space; it stops in the middle
   of whatever it was doing (a NEEDBITS, a table lookup, a stored copy, a match, a header string) and the
   next call goes on from there.  The law says that where the calls stop does not matter.  The proof goes
   through this machine: every call of the concrete model (Model2.run2, with inflate_fast or not) moves
   the abstract state along the trace of `astep` (SIDefs.v: the relation between the two, the call
   lemma), so the one call and the split calls end at the same point of the same trace.

   The abstract state `ast` is the struct inflate_state (istate) with the bit position `a_q` in the
   whole input (the bits before it are consumed) and the whole output `a_O`.  The fields that only
   serve the C code's representation are not used here: hold and bits (the bits are read from the
   input at a_q), the window (the output is all there), total (it is |a_O|), back and was (inflateMark).
   The check value of the data phase is the value set by the header (1 for zlib, 0 for gzip): CHECK
   compares the trailer with the check of the whole output.

   One `astep` is one item of the input or the output: a header field or string byte, a block header,
   one code length, one literal/length or distance code with its extra bits, one byte of a stored block
   or of a match.  It says which bits it reads, [a_q, n) (`AGo n`), whether it writes a byte (`w`),
   and the next state; or it ends the stream with inflate()'s return value (`AEnd`).  The cases follow
   Model.v / Model2.v statement by statement (same tests, same field updates, same table lookups and
   table builds), with the bits taken from the input. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.inflate.Model2.
Require Export Zlib.proof.inflate.Fixed.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The input as a bit stream                                                                      *)

(* the bytes src[k .. k + n) as a little-endian number (bytes past the end read as 0) *)
Fixpoint le_val (src: list Z) (k: Z) (n: nat) : Z :=
  match n with
  | O => 0
  | S n' => Znth k src + 256 * le_val src (k + 1) n'
  end.

(* the n bits of the input from bit position q on (LSB first, as inflate's bit buffer holds them) *)
Definition sbits (src: list Z) (q n: Z) : Z :=
  Z.shiftr (le_val src (q / 8) (Z.to_nat ((q mod 8 + n + 7) / 8))) (q mod 8) mod 2 ^ n.

(* the byte at a byte-aligned bit position *)
Definition sbyte (src: list Z) (q: Z) : Z := Znth (q / 8) src.

(* q rounded up to a byte boundary (BYTEBITS) *)
Definition align8 (q: Z) : Z := (q + 7) / 8 * 8.

(* ---------------------------------------------------------------------------------------------- *)
(* The state                                                                                      *)

Record ast := AS { a_s : istate; a_q : Z; a_O : list Z }.

Definition a_mode (a: ast) : Z := i_mode (a_s a).

(* one step: reads the bits [a_q a, n) of the input, writes one byte when w, and goes on with a';
   or the stream ends with inflate()'s return value r *)
Inductive aout := AGo (n: Z) (w: bool) (a': ast) | AEnd (r: Z).

(* the istate update s := f s at bit position q (the output unchanged) *)
Definition ago (a: ast) (n: Z) (s: istate) : aout := AGo n false (AS s n (a_O a)).

(* a step to BAD after reading [a_q a, n) *)
Definition abad (a: ast) (n: Z) : aout := AGo n false (AS (set_i_mode (a_s a) BAD) n (a_O a)).

(* the header CRC (crc_if of Model.v on the istate) *)
Definition acrc (s: istate) (data: list Z) : istate :=
  if negb (Z.land (i_flags s) 512 =? 0) && negb (Z.land (i_wrap s) 4 =? 0)
  then set_i_check s (ref_crc32 (i_check s) data) else s.

(* a table walk at bit position q: the root entry of the nb bits at q; a link (islink of its op) leads
   to the sub-table entry of the next op bits.  Returns the final entry and the code's length in bits. *)
Definition adecode (fx dx: list entry) (src: list Z) (s: istate) (t: tref) (nb: Z) (islink: Z -> bool)
    (q: Z) : entry * Z :=
  let here := tab_entry fx dx s t (sbits src q nb) in
  if islink (e_op here) then
    let h2 := tab_entry fx dx s t (e_val here + sbits src (q + e_bits here) (e_op here)) in
    (h2, e_bits here + e_bits h2)
  else (here, e_bits here).

(* the link tests of inflate's slow path: LEN `here.op && (here.op & 0xf0) == 0`, DIST
   `(here.op & 0xf0) == 0`; the code length table has no links *)
Definition len_islink (op: Z) : bool := negb (op =? 0) && (Z.land op 240 =? 0).
Definition dist_islink (op: Z) : bool := Z.land op 240 =? 0.
Definition no_link (op: Z) : bool := false.

(* ---------------------------------------------------------------------------------------------- *)
(* The steps, one per mode                                                                        *)

Section Steps.
Variables (fx dx: list entry) (src: list Z).

Definition a_HEAD (a: ast) : aout :=
  let s := a_s a in let q := a_q a in
  if i_wrap s =? 0 then ago a q (set_i_mode s TYPEDO) else
  let h := sbits src q 16 in
  if negb (Z.land (i_wrap s) 2 =? 0) && (h =? 35615) then
    ago a (q + 16) (set_i_mode (set_i_check (set_i_wbits s (if i_wbits s =? 0 then 15 else i_wbits s))
                                            (ref_crc32 0 (hbytes2 h))) FLAGS)
  else
  if (Z.land (i_wrap s) 1 =? 0) || negb (((h mod 256) * 256 + Z.shiftr h 8) mod 31 =? 0) then abad a (q + 16) else
  if negb (h mod 16 =? 8) then abad a (q + 16) else
  let h4 := Z.shiftr h 4 in
  let len := h4 mod 16 + 8 in
  if (15 <? len) || (negb (i_wbits s =? 0) && (i_wbits s <? len)) then abad a (q + 16) else
  let s := set_i_wbits s (if i_wbits s =? 0 then len else i_wbits s) in
  let mode := if Z.land h4 512 =? 0 then TYPE else DICTID in
  ago a (q + 16) (set_i_mode (set_i_check (set_i_flags (set_i_dmax s (2 ^ len)) 0) 1) mode).

Definition a_FLAGS (a: ast) : aout :=
  let s := a_s a in let q := a_q a in
  let h := sbits src q 16 in
  let fl := s32 h in
  let s := set_i_flags s fl in
  if negb (Z.land fl 255 =? 8) then abad a (q + 16) else
  if negb (Z.land fl 57344 =? 0) then abad a (q + 16) else
  ago a (q + 16) (set_i_mode (acrc s (hbytes2 h)) TIME).

Definition a_TIME (a: ast) : aout :=
  let h := sbits src (a_q a) 32 in
  ago a (a_q a + 32) (set_i_mode (acrc (a_s a) (hbytes4 h)) OS).

Definition a_OS (a: ast) : aout :=
  let h := sbits src (a_q a) 16 in
  ago a (a_q a + 16) (set_i_mode (acrc (a_s a) (hbytes2 h)) EXLEN).

Definition a_EXLEN (a: ast) : aout :=
  let s := a_s a in
  if negb (Z.land (i_flags s) 1024 =? 0) then
    let h := sbits src (a_q a) 16 in
    ago a (a_q a + 16) (set_i_mode (acrc (set_i_length s (u32 h)) (hbytes2 h)) EXTRA)
  else ago a (a_q a) (set_i_mode s EXTRA).

(* one byte of the extra field *)
Definition a_EXTRA (a: ast) : aout :=
  let s := a_s a in
  if negb (Z.land (i_flags s) 1024 =? 0) && negb (i_length s =? 0) then
    let b := sbyte src (a_q a) in
    ago a (a_q a + 8) (set_i_length (acrc s [b]) (i_length s - 1))
  else ago a (a_q a) (set_i_mode (set_i_length s 0) NAME).

(* one byte of the file name (up to its zero byte) *)
Definition a_NAME (a: ast) : aout :=
  let s := a_s a in
  if negb (Z.land (i_flags s) 2048 =? 0) then
    let b := sbyte src (a_q a) in
    let s := acrc s [b] in
    ago a (a_q a + 8) (if b =? 0 then set_i_mode (set_i_length s 0) COMMENT else s)
  else ago a (a_q a) (set_i_mode (set_i_length s 0) COMMENT).

(* one byte of the comment (up to its zero byte); Model2: the length is not reset *)
Definition a_COMMENT (a: ast) : aout :=
  let s := a_s a in
  if negb (Z.land (i_flags s) 4096 =? 0) then
    let b := sbyte src (a_q a) in
    let s := acrc s [b] in
    ago a (a_q a + 8) (if b =? 0 then set_i_mode s HCRC else s)
  else ago a (a_q a) (set_i_mode s HCRC).

Definition a_HCRC (a: ast) : aout :=
  let s := a_s a in
  let fin q := ago a q (set_i_mode (set_i_check s 0) TYPE) in
  if negb (Z.land (i_flags s) 512 =? 0) then
    let h := sbits src (a_q a) 16 in
    if negb (Z.land (i_wrap s) 4 =? 0) && negb (h =? Z.land (i_check s) 65535) then abad a (a_q a + 16)
    else fin (a_q a + 16)
  else fin (a_q a).

Definition a_DICTID (a: ast) : aout :=
  let h := sbits src (a_q a) 32 in
  ago a (a_q a + 32) (set_i_mode (set_i_check (a_s a) (swap32 h)) DICT).

Definition a_DICT (a: ast) : aout :=
  if i_havedict (a_s a) =? 0 then AEnd Z_NEED_DICT
  else ago a (a_q a) (set_i_mode (set_i_check (a_s a) 1) TYPE).

Definition a_TYPE (a: ast) : aout := ago a (a_q a) (set_i_mode (a_s a) TYPEDO).

Definition a_TYPEDO (a: ast) : aout :=
  let s := a_s a in let q := a_q a in
  if negb (i_last s =? 0) then ago a (align8 q) (set_i_mode s CHECK) else
  let s := set_i_last s (sbits src q 1) in
  let bt := sbits src (q + 1) 2 in
  if bt =? 0 then ago a (q + 3) (set_i_mode s STORED)
  else if bt =? 1 then
    ago a (q + 3) (set_i_mode (set_i_distbits (set_i_distcode (set_i_lenbits (set_i_lencode s TLenfix) 9)
                                                TDistfix) 5) LEN_)
  else if bt =? 2 then ago a (q + 3) (set_i_mode s TABLE)
  else abad (AS s q (a_O a)) (q + 3).

(* the padding to the byte boundary, then LEN and NLEN *)
Definition a_STORED (a: ast) : aout :=
  let s := a_s a in let q := a_q a in
  if negb (q mod 8 =? 0) then ago a (align8 q) s else
  let h := sbits src q 32 in
  if negb (Z.land h 65535 =? Z.lxor (Z.shiftr h 16) 65535) then abad a (q + 32)
  else ago a (q + 32) (set_i_mode (set_i_length s (h mod 65536)) COPY_).

Definition a_COPY_ (a: ast) : aout := ago a (a_q a) (set_i_mode (a_s a) COPY).

(* one byte of a stored block *)
Definition a_COPY (a: ast) : aout :=
  let s := a_s a in
  if negb (i_length s =? 0) then
    AGo (a_q a + 8) true (AS (set_i_length s (i_length s - 1)) (a_q a + 8) (a_O a ++ [sbyte src (a_q a)]))
  else ago a (a_q a) (set_i_mode s TYPE).

Definition a_TABLE (a: ast) : aout :=
  let q := a_q a in
  let nlen := sbits src q 5 + 257 in
  let ndist := sbits src (q + 5) 5 + 1 in
  let ncode := sbits src (q + 10) 4 + 4 in
  let s := set_i_ncode (set_i_ndist (set_i_nlen (a_s a) nlen) ndist) ncode in
  if (286 <? nlen) || (30 <? ndist) then abad (AS s q (a_O a)) (q + 14)
  else ago a (q + 14) (set_i_mode (set_i_have s 0) LENLENS).

(* one code length code length; when all are read, the code length code's table *)
Definition a_LENLENS (a: ast) : aout :=
  let s := a_s a in
  if i_have s <? i_ncode s then
    ago a (a_q a + 3)
      (set_i_have (set_i_lens s (upd_Znth (Znth (i_have s) order) (i_lens s) (sbits src (a_q a) 3))) (i_have s + 1))
  else
  let s := lenlens_zero 19 s in
  let s := set_i_lenbits (set_i_distcode (set_i_lencode (set_i_next s 0) (TCodes 0)) (TCodes 0)) 7 in
  let '(r, codes, nxt, lb) := call_table CODES 0 19 7 s in
  let s := set_i_lenbits (set_i_next (set_i_codes s codes) nxt) lb in
  if negb (r =? 0) then abad (AS s (a_q a) (a_O a)) (a_q a)
  else ago a (a_q a) (set_i_mode (set_i_have s 0) CODELENS).

(* one code length symbol (with its repeat count); when all are read, the two tables *)
Definition a_CODELENS (a: ast) : aout :=
  let s := a_s a in let q := a_q a in
  if i_have s <? i_nlen s + i_ndist s then
    let '(here, l) := adecode fx dx src s (i_lencode s) (i_lenbits s) no_link q in
    if e_val here <? 16 then
      ago a (q + l) (set_i_have (set_i_lens s (upd_Znth (i_have s) (i_lens s) (e_val here))) (i_have s + 1))
    else
      let '(nx, len, copy, bad) :=
        if e_val here =? 16 then
          (q + l + 2, Znth (i_have s - 1) (i_lens s), 3 + sbits src (q + l) 2, i_have s =? 0)
        else if e_val here =? 17 then (q + l + 3, 0, 3 + sbits src (q + l) 3, false)
        else (q + l + 7, 0, 11 + sbits src (q + l) 7, false) in
      if bad then abad a nx else
      if i_nlen s + i_ndist s <? i_have s + copy then abad a nx else
      ago a nx (lens_fill (Z.to_nat copy) len s)
  else
  if Znth 256 (i_lens s) =? 0 then abad a q else
  let s := set_i_lenbits (set_i_lencode (set_i_next s 0) (TCodes 0)) 9 in
  let '(r, codes, nxt, lb) := call_table LENS 0 (i_nlen s) 9 s in
  let s := set_i_lenbits (set_i_next (set_i_codes s codes) nxt) lb in
  if negb (r =? 0) then abad (AS s q (a_O a)) q else
  let s := set_i_distbits (set_i_distcode s (TCodes (i_next s))) 6 in
  let '(r, codes, nxt, db) := call_table DISTS (i_nlen s) (i_ndist s) 6 s in
  let s := set_i_distbits (set_i_next (set_i_codes s codes) nxt) db in
  if negb (r =? 0) then abad (AS s q (a_O a)) q
  else ago a q (set_i_mode s LEN_).

Definition a_LEN_ (a: ast) : aout := ago a (a_q a) (set_i_mode (a_s a) LEN).

(* one literal/length code (inflate's slow path) *)
Definition a_LEN (a: ast) : aout :=
  let s := a_s a in let q := a_q a in
  let '(here, l) := adecode fx dx src s (i_lencode s) (i_lenbits s) len_islink q in
  let s := set_i_length s (e_val here) in
  if e_op here =? 0 then ago a (q + l) (set_i_mode s LIT)
  else if negb (Z.land (e_op here) 32 =? 0) then ago a (q + l) (set_i_mode s TYPE)
  else if negb (Z.land (e_op here) 64 =? 0) then abad a (q + l)
  else ago a (q + l) (set_i_mode (set_i_extra s (Z.land (e_op here) 15)) LENEXT).

(* the extra bits of a length *)
Definition a_LENEXT (a: ast) : aout :=
  let s := a_s a in let ex := i_extra s in
  if negb (ex =? 0) then
    ago a (a_q a + ex) (set_i_mode (set_i_length s (u32 (i_length s + sbits src (a_q a) ex))) DIST)
  else ago a (a_q a) (set_i_mode s DIST).

(* one distance code *)
Definition a_DIST (a: ast) : aout :=
  let s := a_s a in let q := a_q a in
  let '(here, l) := adecode fx dx src s (i_distcode s) (i_distbits s) dist_islink q in
  if negb (Z.land (e_op here) 64 =? 0) then abad a (q + l)
  else ago a (q + l) (set_i_mode (set_i_extra (set_i_offset s (e_val here)) (Z.land (e_op here) 15)) DISTEXT).

(* the extra bits of a distance *)
Definition a_DISTEXT (a: ast) : aout :=
  let s := a_s a in let ex := i_extra s in
  if negb (ex =? 0) then
    ago a (a_q a + ex) (set_i_mode (set_i_offset s (u32 (i_offset s + sbits src (a_q a) ex))) MATCH)
  else ago a (a_q a) (set_i_mode s MATCH).

(* one byte of a match; a distance past the start of the output is refused (it needs output space, as
   inflate tests the space first) *)
Definition a_MATCH (a: ast) : aout :=
  let s := a_s a in let O := a_O a in
  if Zlength O <? i_offset s then AGo (a_q a) true (AS (set_i_mode s BAD) (a_q a) O) else
  let s' := set_i_length s (i_length s - 1) in
  AGo (a_q a) true (AS (if i_length s - 1 =? 0 then set_i_mode s' LEN else s') (a_q a)
                       (O ++ [Znth (Zlength O - i_offset s) O])).

Definition a_LIT (a: ast) : aout :=
  AGo (a_q a) true (AS (set_i_mode (a_s a) LEN) (a_q a) (a_O a ++ [i_length (a_s a) mod 256])).

(* the trailer's check value: the check of the whole output *)
Definition a_CHECK (a: ast) : aout :=
  let s := a_s a in let q := a_q a in
  if negb (i_wrap s =? 0) then
    let h := sbits src q 32 in
    let c := update_check (i_flags s) (i_check s) (a_O a) in
    if negb (Z.land (i_wrap s) 4 =? 0) && negb ((if i_flags s =? 0 then swap32 h else h) =? c)
    then abad a (q + 32)
    else ago a (q + 32) (set_i_mode (set_i_check s c) LENGTH)
  else ago a q (set_i_mode s LENGTH).

(* the gzip trailer's length: the length of the whole output *)
Definition a_LENGTH (a: ast) : aout :=
  let s := a_s a in let q := a_q a in
  if negb (i_wrap s =? 0) && negb (i_flags s =? 0) then
    let h := sbits src q 32 in
    if negb (Z.land (i_wrap s) 4 =? 0) && negb (h =? Zlength (a_O a) mod 2 ^ 32) then abad a (q + 32)
    else ago a (q + 32) (set_i_mode s DONE)
  else ago a q (set_i_mode s DONE).

Definition astep (a: ast) : aout :=
  let md := a_mode a in
  if md =? HEAD then a_HEAD a
  else if md =? FLAGS then a_FLAGS a
  else if md =? TIME then a_TIME a
  else if md =? OS then a_OS a
  else if md =? EXLEN then a_EXLEN a
  else if md =? EXTRA then a_EXTRA a
  else if md =? NAME then a_NAME a
  else if md =? COMMENT then a_COMMENT a
  else if md =? HCRC then a_HCRC a
  else if md =? DICTID then a_DICTID a
  else if md =? DICT then a_DICT a
  else if md =? TYPE then a_TYPE a
  else if md =? TYPEDO then a_TYPEDO a
  else if md =? STORED then a_STORED a
  else if md =? COPY_ then a_COPY_ a
  else if md =? COPY then a_COPY a
  else if md =? TABLE then a_TABLE a
  else if md =? LENLENS then a_LENLENS a
  else if md =? CODELENS then a_CODELENS a
  else if md =? LEN_ then a_LEN_ a
  else if md =? LEN then a_LEN a
  else if md =? LENEXT then a_LENEXT a
  else if md =? DIST then a_DIST a
  else if md =? DISTEXT then a_DISTEXT a
  else if md =? MATCH then a_MATCH a
  else if md =? LIT then a_LIT a
  else if md =? CHECK then a_CHECK a
  else if md =? LENGTH then a_LENGTH a
  else if md =? DONE then AEnd Z_STREAM_END
  else if md =? BAD then AEnd Z_DATA_ERROR
  else if md =? MEM then AEnd Z_MEM_ERROR
  else AEnd Z_STREAM_ERROR.

End Steps.

(* ---------------------------------------------------------------------------------------------- *)
(* Traces under limits                                                                            *)

(* a step that needs more than I bytes of input, or writes when R bytes are written *)
Definition blocked (I R: Z) (a: ast) (o: aout) : Prop :=
  match o with
  | AGo n w _ => 8 * I < n \/ (w = true /\ R <= Zlength (a_O a))
  | AEnd _ => False
  end.

(* the steps from a to a', each within the limits I, R *)
Inductive areach (src: list Z) (I R: Z) : ast -> ast -> Prop :=
| ar_refl: forall a, areach src I R a a
| ar_step: forall a n w a1 a', astep lenfix_list distfix_list src a = AGo n w a1 ->
    ~ blocked I R a (AGo n w a1) -> areach src I R a1 a' -> areach src I R a a'.

(* the next step needs more than the call has, possibly after the free step TYPE -> TYPEDO (c_TYPE goes on
   into TYPEDO's NEEDBITS(3) without setting the mode, so a call that runs out of input there stops in TYPE) *)
Definition ablocked (src: list Z) (I R: Z) (a: ast) (o: aout) : Prop :=
  blocked I R a o \/
  (a_mode a = Zlib.proof.inflate.Model.TYPE /\
   match o with AGo _ _ a1 => blocked I R a1 (astep lenfix_list distfix_list src a1) | AEnd _ => False end).

(* where the trace stops under the limits: the stream ends with r (Some r), or the next step is
   blocked (None) *)
Definition astop (src: list Z) (I R: Z) (a: ast) (t: option Z) : Prop :=
  match astep lenfix_list distfix_list src a with
  | AEnd r => t = Some r
  | o => ablocked src I R a o /\ t = None
  end.
