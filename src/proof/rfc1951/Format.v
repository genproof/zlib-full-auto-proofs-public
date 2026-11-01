(* The DEFLATE stream format (RFC 1951) and its wrappers (RFC 1950 zlib, RFC 1952 gzip), abstract and standalone:
   no dependency on harness/deflate_ref.h, on a harness or on the model of inflate.  Shared by every law that
   relates compressed bytes to their data (inflate_decode, inflate_dict, the round-trip laws).

   - a stream is a non-empty list of blocks, the last one final: stored (3.2.4), fixed-Huffman (3.2.6),
     dynamic-Huffman (3.2.7: nlen, ndist, the code length code lengths as sent (HCLEN + 4 of them, in the
     order 16 17 18 0 8 ...), the code length tokens (a length 0..15, a repeat 16 of the previous length 3..6
     times, a zero run 17 / 18 of 3..10 / 11..138); symbols: literals and back-references (3.2.5);
   - `enc_blocks` / `deflate_bits` / `deflate_bytes`: the bit encoding (3.1.1: packed from the least
     significant bit of each byte; data elements least significant bit first, Huffman codes most significant
     bit first; canonical codes 3.2.2; a stored block's header padded with zero bits to the byte boundary;
     the stream padded with zero bits to a whole byte);
   - `expand` / `data`: the LZ77 expansion, from a history `hist` (a preset dictionary, or nothing);
   - `wf wmax hist bs`: well-formedness, i.e. what inflate accepts (deflate_ref.h code_ok): complete codes,
     the single-code (one code of length 1) and empty distance code exceptions, a code for 256, every sent
     symbol with a code, references within the history and the window wmax (2^wb);
   - `stream_bytes`: the raw / zlib / gzip wrapper around the deflate bytes with its trailer. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Zlib.proof.adler32.Model Zlib.proof.crc32.Model.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Bits (RFC 1951 3.1.1)                                                                          *)

(* the n low bits of v, the least significant first (a data element: lengths, extra bits) *)
Definition bits_le (v n: Z) : list bool := map (fun i => Z.testbit v (Z.of_nat i)) (seq 0 (Z.to_nat n)).
(* the n low bits of c, the most significant first (a Huffman code) *)
Definition bits_msb (c n: Z) : list bool := rev (bits_le c n).
Definition zeros (n: Z) : list bool := repeat false (Z.to_nat n).
(* the number of zero bits from bit position p to the next byte boundary *)
Definition pad8 (p: Z) : Z := (8 - p mod 8) mod 8.

(* the value of bits, the first one least significant *)
Fixpoint bval (bs: list bool) : Z := match bs with [] => 0 | b :: r => Z.b2z b + 2 * bval r end.
(* bytes from bits: byte k holds bits 8k .. 8k + 7 (the last byte padded with zeros) *)
Definition pack (bs: list bool) : list Z :=
  map (fun k => bval (sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs)) (seq 0 (Z.to_nat ((Zlength bs + 7) / 8))).
(* bits from bytes *)
Definition bytes_bits (l: list Z) : list bool := flat_map (fun b => bits_le b 8) l.

(* ---------------------------------------------------------------------------------------------- *)
(* Canonical Huffman codes (RFC 1951 3.2.2)                                                       *)

Definition MAXLEN : Z := 15.

(* count_of[l]: the number of codes of length l (none of length 0) *)
Definition count_of (lens: list Z) (l: Z) : Z := if l =? 0 then 0 else Zlength (filter (fun x => x =? l) lens).
(* next_code[l]: code = 0; for bits = 1..l: code = (code + count_of[bits - 1]) << 1 *)
Fixpoint next_code_n (lens: list Z) (l: nat) : Z :=
  match l with O => 0 | S l' => (next_code_n lens l' + count_of lens (Z.of_nat l')) * 2 end.
(* the code of symbol s: next_code[len] plus the number of earlier symbols of the same length *)
Definition code (lens: list Z) (s: Z) : Z :=
  let l := Znth s lens in next_code_n lens (Z.to_nat l) + Zlength (filter (fun x => x =? l) (sublist 0 s lens)).
(* the bits sent for symbol s *)
Definition send_sym (lens: list Z) (s: Z) : list bool := bits_msb (code lens s) (Znth s lens).

(* the Kraft sum in units of 2^-15 and the number of codes *)
Definition kraft_sum (lens: list Z) : Z := fold_right (fun l k => if l =? 0 then k else k + 2 ^ (MAXLEN - l)) 0 lens.
Definition nused (lens: list Z) : Z := Zlength (filter (fun l => negb (l =? 0)) lens).

Definition lens_ok (lens: list Z) : Prop := Forall (fun l => 0 <= l <= MAXLEN) lens.
Definition complete (lens: list Z) : Prop := kraft_sum lens = 2 ^ MAXLEN.
(* a single code of length 1 *)
Definition single (lens: list Z) : Prop := nused lens = 1 /\ kraft_sum lens = 2 ^ (MAXLEN - 1).
Definition empty_code (lens: list Z) : Prop := nused lens = 0.

(* ---------------------------------------------------------------------------------------------- *)
(* Lengths and distances (RFC 1951 3.2.5)                                                         *)

Definition len_base : list Z := [3; 4; 5; 6; 7; 8; 9; 10; 11; 13; 15; 17; 19; 23; 27; 31; 35; 43; 51; 59;
                              67; 83; 99; 115; 131; 163; 195; 227; 258].
Definition len_extra : list Z := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 2; 2; 2; 2; 3; 3; 3; 3; 4; 4; 4; 4; 5;
                             5; 5; 5; 0].
Definition dist_base : list Z := [1; 2; 3; 4; 5; 7; 9; 13; 17; 25; 33; 49; 65; 97; 129; 193; 257; 385; 513;
                              769; 1025; 1537; 2049; 3073; 4097; 6145; 8193; 12289; 16385; 24577].
Definition dist_extra : list Z := [0; 0; 0; 0; 1; 1; 2; 2; 3; 3; 4; 4; 5; 5; 6; 6; 7; 7; 8; 8; 9; 9; 10; 10;
                             11; 11; 12; 12; 13; 13].

(* the length code (0..28, symbol 257 + it) of a length 3..258: 258 is code 28 (symbol 285) *)
Definition len_code (len: Z) : Z :=
  if len =? 258 then 28 else Zlength (filter (fun b => b <=? len) (sublist 1 28 len_base)).
(* the distance code (0..29) of a distance 1..32768 *)
Definition dist_code (dist: Z) : Z := Zlength (filter (fun b => b <=? dist) (sublist 1 30 dist_base)).

(* ---------------------------------------------------------------------------------------------- *)
(* Streams                                                                                        *)

Inductive sym := Lit (b: Z) | Ref (len dist: Z).

(* a code length token: CLen l (symbol l, 0..15), CRep r (16: the previous length r = 3..6 times),
   CZeros r (17: r = 3..10 zeros; 18: r = 11..138 zeros) *)
Inductive cltok := CLen (l: Z) | CRep (r: Z) | CZeros (r: Z).

Inductive block :=
| Stored (bytes: list Z)
| Fixed (syms: list sym)
(* nlen, ndist; the code length code lengths as sent (HCLEN + 4 values, in the order clorder); the tokens of
   the nlen + ndist code lengths (one sequence: runs may cross from the literal/length to the distance
   lengths); the symbols *)
| Dynamic (nlen ndist: Z) (clsent: list Z) (toks: list cltok) (syms: list sym).

(* the fixed codes (3.2.6): literal/length 0..287, distance 0..31 (30 and 31 never occur) *)
Definition fixed_ll : list Z :=
  repeat 8 144 ++ repeat 9 112 ++ repeat 7 24 ++ repeat 8 8.
Definition fixed_dl : list Z := repeat 5 32.

(* the order of the code length code lengths, and the position of each symbol in it *)
Definition clorder : list Z := [16; 17; 18; 0; 8; 7; 9; 6; 10; 5; 11; 4; 12; 3; 13; 2; 14; 1; 15].
Definition clpos : list Z := [3; 17; 15; 13; 11; 9; 7; 5; 4; 6; 8; 10; 12; 14; 16; 18; 0; 1; 2].
(* the code length code lengths by symbol 0..18 (the ones not sent are 0) *)
Definition cl_lens (clsent: list Z) : list Z :=
  map (fun s => let i := Znth (Z.of_nat s) clpos in if i <? Zlength clsent then Znth i clsent else 0) (seq 0 19).

(* the code lengths a token adds after the lengths prev *)
Definition tok_vals (prev: list Z) (t: cltok) : list Z :=
  match t with
  | CLen l => [l]
  | CRep r => repeat (last prev 0) (Z.to_nat r)
  | CZeros r => repeat 0 (Z.to_nat r)
  end.
Fixpoint tok_expand (prev: list Z) (toks: list cltok) : list Z :=
  match toks with [] => prev | t :: r => tok_expand (prev ++ tok_vals prev t) r end.
(* the nlen + ndist code lengths of a dynamic block, the literal/length and the distance ones *)
Definition dyn_lens (toks: list cltok) : list Z := tok_expand [] toks.
Definition dyn_ll (nlen: Z) (toks: list cltok) : list Z := sublist 0 nlen (dyn_lens toks).
Definition dyn_dl (nlen ndist: Z) (toks: list cltok) : list Z := sublist nlen (nlen + ndist) (dyn_lens toks).

Definition send_tok (cl: list Z) (t: cltok) : list bool :=
  match t with
  | CLen l => send_sym cl l
  | CRep r => send_sym cl 16 ++ bits_le (r - 3) 2
  | CZeros r => if r <=? 10 then send_sym cl 17 ++ bits_le (r - 3) 3 else send_sym cl 18 ++ bits_le (r - 11) 7
  end.

Definition send_one (ll dl: list Z) (s: sym) : list bool :=
  match s with
  | Lit b => send_sym ll b
  | Ref len dist =>
      let i := len_code len in let j := dist_code dist in
      send_sym ll (257 + i) ++ bits_le (len - Znth i len_base) (Znth i len_extra) ++
      send_sym dl j ++ bits_le (dist - Znth j dist_base) (Znth j dist_extra)
  end.
(* the symbols, then the end-of-block code *)
Definition send_syms (ll dl: list Z) (syms: list sym) : list bool := flat_map (send_one ll dl) syms ++ send_sym ll 256.

(* a block starting at bit position p (from the start of the deflate stream) *)
Definition enc_block (p: Z) (final: bool) (b: block) : list bool :=
  final :: match b with
  | Stored bytes =>
      let n := Zlength bytes in
      [false; false] ++ zeros (pad8 (p + 3)) ++ bits_le n 16 ++ bits_le (65535 - n) 16 ++ bytes_bits bytes
  | Fixed syms => [true; false] ++ send_syms fixed_ll fixed_dl syms
  | Dynamic nlen ndist clsent toks syms =>
      [false; true] ++ bits_le (nlen - 257) 5 ++ bits_le (ndist - 1) 5 ++ bits_le (Zlength clsent - 4) 4 ++
      flat_map (fun c => bits_le c 3) clsent ++ flat_map (send_tok (cl_lens clsent)) toks ++
      send_syms (dyn_ll nlen toks) (dyn_dl nlen ndist toks) syms
  end.

(* the blocks from bit position p, the last one final *)
Fixpoint enc_blocks (p: Z) (bs: list block) : list bool :=
  match bs with
  | [] => []
  | b :: r =>
      let e := enc_block p (match r with [] => true | _ => false end) b in
      e ++ enc_blocks (p + Zlength e) r
  end.

(* the deflate stream: the blocks, padded to a whole byte *)
Definition deflate_bits (bs: list block) : list bool :=
  let e := enc_blocks 0 bs in e ++ zeros (pad8 (Zlength e)).
Definition deflate_bytes (bs: list block) : list Z := pack (deflate_bits bs).

(* ---------------------------------------------------------------------------------------------- *)
(* The data (LZ77 expansion)                                                                      *)

(* copy n bytes from distance dist back, one at a time (a copy may overlap the bytes it appends) *)
Fixpoint lz_copy (n: nat) (dist: Z) (out: list Z) : list Z :=
  match n with O => out | S n' => lz_copy n' dist (out ++ [Znth (Zlength out - dist) out]) end.

Definition sym_data (out: list Z) (s: sym) : list Z :=
  match s with Lit b => out ++ [b] | Ref len dist => lz_copy (Z.to_nat len) dist out end.
Definition syms_data (out: list Z) (syms: list sym) : list Z := fold_left sym_data syms out.

Definition block_data (out: list Z) (b: block) : list Z :=
  match b with
  | Stored bytes => out ++ bytes
  | Fixed syms => syms_data out syms
  | Dynamic _ _ _ _ syms => syms_data out syms
  end.

(* the history followed by the data of the blocks *)
Definition expand (hist: list Z) (bs: list block) : list Z := fold_left block_data bs hist.
(* the data of the blocks *)
Definition data (hist: list Z) (bs: list block) : list Z :=
  let e := expand hist bs in sublist (Zlength hist) (Zlength e) e.

(* ---------------------------------------------------------------------------------------------- *)
(* Well-formedness: what inflate accepts (wmax: the window size 2^wb)                             *)

Definition byte_ok (b: Z) : Prop := 0 <= b < 256.

(* a symbol after the output `out` (history included), with the codes ll / dl *)
Definition sym_ok (wmax: Z) (ll dl: list Z) (out: list Z) (s: sym) : Prop :=
  match s with
  | Lit b => byte_ok b /\ Znth b ll <> 0
  | Ref len dist =>
      3 <= len <= 258 /\ 1 <= dist <= Zlength out /\ dist <= wmax /\
      257 + len_code len < Zlength ll /\ Znth (257 + len_code len) ll <> 0 /\
      dist_code dist < Zlength dl /\ Znth (dist_code dist) dl <> 0
  end.
Fixpoint syms_ok (wmax: Z) (ll dl: list Z) (out: list Z) (syms: list sym) : Prop :=
  match syms with
  | [] => True
  | s :: r => sym_ok wmax ll dl out s /\ syms_ok wmax ll dl (sym_data out s) r
  end.

(* a token after the lengths prev, with the code length code cl *)
Definition tok_ok (cl: list Z) (prev: list Z) (t: cltok) : Prop :=
  match t with
  | CLen l => 0 <= l <= 15 /\ Znth l cl <> 0
  | CRep r => prev <> [] /\ 3 <= r <= 6 /\ Znth 16 cl <> 0
  | CZeros r => 3 <= r <= 138 /\ Znth (if r <=? 10 then 17 else 18) cl <> 0
  end.
Fixpoint toks_ok (cl: list Z) (prev: list Z) (toks: list cltok) : Prop :=
  match toks with
  | [] => True
  | t :: r => tok_ok cl prev t /\ toks_ok cl (prev ++ tok_vals prev t) r
  end.

(* the codes inflate accepts (inftrees.c, inflate.c): the code length code complete; the literal/length code
   with a code for 256, complete or a single code of length 1; the distance code complete, a single code of
   length 1, or empty *)
Definition cl_code_ok (cl: list Z) : Prop := Forall (fun l => 0 <= l <= 7) cl /\ complete cl.
Definition ll_code_ok (ll: list Z) : Prop := lens_ok ll /\ Znth 256 ll <> 0 /\ (complete ll \/ single ll).
Definition dl_code_ok (dl: list Z) : Prop := lens_ok dl /\ (complete dl \/ single dl \/ empty_code dl).

Definition block_ok (wmax: Z) (out: list Z) (b: block) : Prop :=
  match b with
  | Stored bytes => Zlength bytes <= 65535 /\ Forall byte_ok bytes
  | Fixed syms => syms_ok wmax fixed_ll fixed_dl out syms
  | Dynamic nlen ndist clsent toks syms =>
      257 <= nlen <= 286 /\ 1 <= ndist <= 30 /\
      4 <= Zlength clsent <= 19 /\ Forall (fun c => 0 <= c <= 7) clsent /\ cl_code_ok (cl_lens clsent) /\
      toks_ok (cl_lens clsent) [] toks /\ Zlength (dyn_lens toks) = nlen + ndist /\
      ll_code_ok (dyn_ll nlen toks) /\ dl_code_ok (dyn_dl nlen ndist toks) /\
      syms_ok wmax (dyn_ll nlen toks) (dyn_dl nlen ndist toks) out syms
  end.
Fixpoint blocks_ok (wmax: Z) (out: list Z) (bs: list block) : Prop :=
  match bs with
  | [] => True
  | b :: r => block_ok wmax out b /\ blocks_ok wmax (block_data out b) r
  end.

Definition wf (wmax: Z) (hist: list Z) (bs: list block) : Prop :=
  bs <> [] /\ Forall byte_ok hist /\ blocks_ok wmax hist bs.

(* the data of the first k blocks (block boundaries) *)
Definition data_upto (hist: list Z) (bs: list block) (k: nat) : list Z := data hist (firstn k bs).

(* ---------------------------------------------------------------------------------------------- *)
(* Wrappers (RFC 1950, RFC 1952)                                                                  *)

(* v as n bytes, little-endian / big-endian *)
Definition le_bytes (v n: Z) : list Z := map (fun i => Z.shiftr v (8 * Z.of_nat i) mod 256) (seq 0 (Z.to_nat n)).
Definition be_bytes (v n: Z) : list Z := rev (le_bytes v n).

(* the zlib header (RFC 1950 2.2): CMF = CINFO (wb - 8), CM 8; FLG = FLEVEL, FDICT, FCHECK *)
Definition zlib_hdr (wb flevel: Z) (fdict: bool) : list Z :=
  let cmf := (wb - 8) * 16 + 8 in
  let flg0 := flevel * 64 + (if fdict then 32 else 0) in
  [cmf; flg0 + (31 - (cmf * 256 + flg0) mod 31) mod 31].

(* a gzip header (RFC 1952 2.3) *)
Record gzhdr := GzHdr {
  gz_text : bool; gz_mtime : Z; gz_xfl : Z; gz_os : Z;
  gz_extra : option (list Z); gz_name : option (list Z); gz_comment : option (list Z); gz_hcrc : bool }.

Definition gz_flg (h: gzhdr) : Z :=
  (if gz_text h then 1 else 0) + (if gz_hcrc h then 2 else 0) + (match gz_extra h with Some _ => 4 | None => 0 end)
  + (match gz_name h with Some _ => 8 | None => 0 end) + (match gz_comment h with Some _ => 16 | None => 0 end).
Definition gz_bytes0 (h: gzhdr) : list Z :=
  [31; 139; 8; gz_flg h] ++ le_bytes (gz_mtime h) 4 ++ [gz_xfl h; gz_os h] ++
  match gz_extra h with Some x => le_bytes (Zlength x) 2 ++ x | None => [] end ++
  match gz_name h with Some n => n ++ [0] | None => [] end ++
  match gz_comment h with Some c => c ++ [0] | None => [] end.
(* with FHCRC: the low 16 bits of the CRC-32 of the header before it *)
Definition gz_bytes (h: gzhdr) : list Z :=
  let b := gz_bytes0 h in
  if gz_hcrc h then b ++ le_bytes (Zlib.proof.crc32.Model.ref_crc32 0 b) 2 else b.
Definition gz_ok (h: gzhdr) : Prop :=
  0 <= gz_mtime h < 2 ^ 32 /\ byte_ok (gz_xfl h) /\ byte_ok (gz_os h) /\
  match gz_extra h with Some x => Zlength x <= 65535 /\ Forall byte_ok x | None => True end /\
  match gz_name h with Some n => Forall (fun b => 0 < b < 256) n | None => True end /\
  match gz_comment h with Some c => Forall (fun b => 0 < b < 256) c | None => True end.

(* the harness's minimal gzip header 1f 8b 08 00 00000000 00 03 *)
Definition gz_min : gzhdr := GzHdr false 0 0 3 None None None false.

Inductive wrapper :=
| WRaw
(* window bits 8..15, FLEVEL 0..3, the dictionary id when FDICT *)
| WZlib (wb flevel: Z) (dictid: option Z)
| WGzip (h: gzhdr).

(* the stream: the wrapper's header, the deflate bytes, the wrapper's trailer (checks of the data, not of the
   history) *)
Definition stream_bytes (w: wrapper) (hist: list Z) (bs: list block) : list Z :=
  let d := data hist bs in
  match w with
  | WRaw => deflate_bytes bs
  | WZlib wb flevel did =>
      zlib_hdr wb flevel (match did with Some _ => true | None => false end) ++
      match did with Some i => be_bytes i 4 | None => [] end ++
      deflate_bytes bs ++ be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 d) 4
  | WGzip h =>
      gz_bytes h ++ deflate_bytes bs ++
      le_bytes (Zlib.proof.crc32.Model.ref_crc32 0 d) 4 ++ le_bytes (Zlength d mod 2 ^ 32) 4
  end.

(* the wrapper and the history agree: zlib with a dictionary id has the history whose Adler-32 it is (the
   dictionary), zlib without one and gzip have none; raw: any history (inflateSetDictionary) *)
Definition wrapper_ok (w: wrapper) (hist: list Z) : Prop :=
  match w with
  | WRaw => True
  | WZlib wb flevel did =>
      8 <= wb <= 15 /\ 0 <= flevel <= 3 /\
      match did with Some i => i = Zlib.proof.adler32.Model.ref_adler32 1 hist | None => hist = [] end
  | WGzip h => gz_ok h /\ hist = []
  end.

(* a complete stream description: wrapper, history, blocks, window bits wb (zlib: the header's) *)
Definition stream_ok (w: wrapper) (wb: Z) (hist: list Z) (bs: list block) : Prop :=
  8 <= wb <= 15 /\ wrapper_ok w hist /\ (match w with WZlib wb' _ _ => wb' = wb | _ => True end) /\
  wf (2 ^ wb) hist bs.

(* ---------------------------------------------------------------------------------------------- *)
(* Sanity checks (zlib's output for "a": raw 4b 04 00; zlib 78 9c 4b 04 00 00 62 00 62)            *)

Example fmt_raw_a : deflate_bytes [Fixed [Lit 97]] = [75; 4; 0].
Proof. vm_compute. reflexivity. Qed.
Example fmt_zlib_a : stream_bytes (WZlib 15 2 None) [] [Fixed [Lit 97]] = [120; 156; 75; 4; 0; 0; 98; 0; 98].
Proof. vm_compute. reflexivity. Qed.
Example fmt_fixed_codes :
  map (code fixed_ll) [0; 143; 144; 255; 256; 279; 280; 287] = [48; 191; 400; 511; 0; 23; 192; 199].
Proof. vm_compute. reflexivity. Qed.
Example fmt_codes : map len_code [3; 10; 11; 12; 257; 258] = [0; 7; 8; 8; 27; 28] /\
                    map dist_code [1; 4; 5; 6; 7; 24577; 32768] = [0; 3; 4; 4; 5; 29; 29].
Proof. vm_compute. split; reflexivity. Qed.
