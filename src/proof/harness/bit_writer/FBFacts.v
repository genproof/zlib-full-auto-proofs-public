(* Law rj_far_back: THE interface between main (FBMain.v, VST) and the theory (FBTheory.v).  Pure Coq.

   main chooses the literals lits (< 32768), the length code lc (257..285), the distance code dc (0..29), the
   32-bit values fin (BFINAL), lx (the length's extra bits) and extra (the distance's), assumes that the distance
   fb_dist dc extra is more than |lits|, writes the block with put_bits / put_literal into the n arbitrary bytes S0
   (fb_bytes: the bytes after the writes), and calls inflate() twice: first offered any first part S[0 .. take)
   and any output space, then (unless the first returned Z_MEM_ERROR) the rest S[read ..] (at most 2^32 - 1 bytes
   of it), read being what the first call consumed, with room for the literals and one byte more and a flush
   other than Z_TREES.  The theory says: what the calls write is never more than the literals, and the second
   call returns Z_DATA_ERROR (or Z_MEM_ERROR, which ends the run). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.bit_writer.BWModel.
Require Export Zlib.proof.rfc1951.Format.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.inflate.Model2.
Require Import Zlib.proof.adler32.Bytes.
Import ListNotations.
Local Open Scope Z_scope.

(* length_bits: (code - 261) / 4 for the codes 265..284; distance_bits: d / 2 - 1 for d >= 4 *)
Definition fb_lbits (lc: Z) : Z := if andb (265 <=? lc) (lc <=? 284) then (lc - 261) / 4 else 0.
Definition fb_dbits (dc: Z) : Z := if 4 <=? dc then dc / 2 - 1 else 0.
(* distance = ((2u | (distance_code & 1)) << distance_bits) + 1 + (extra & ((1u << distance_bits) - 1)) for
   d >= 4, else d + 1 *)
Definition fb_dist (dc extra: Z) : Z :=
  if 4 <=? dc then Z.shiftl (Z.lor 2 (Z.land dc 1)) (fb_dbits dc) + 1 + Z.land extra (2 ^ fb_dbits dc - 1)
  else dc + 1.

(* the stream after main's writes from bit 0: BFINAL, BTYPE 01, the literals, the length code (7 bits from
   0000000 for 256..279, 8 bits from 11000000 for 280..287), its extra bits, the distance code (5 bits), its extra
   bits *)
Definition fb_bytes (S0: list Z) (fin: Z) (lits: list Z) (lc lx dc extra: Z) : list Z :=
  let S := put_bits_m S0 0 fin 1 0 in
  let S := put_bits_m S 1 1 2 0 in
  let S := put_lits S 3 lits in
  let b := 3 + lits_len lits in
  let S := if lc <? 280 then put_bits_m S b (lc - 256) 7 1 else put_bits_m S b (192 + lc - 280) 8 1 in
  let b := b + (if lc <? 280 then 7 else 8) in
  let S := put_bits_m S b lx (fb_lbits lc) 0 in
  let b := b + fb_lbits lc in
  let S := put_bits_m S b dc 5 1 in
  put_bits_m S (b + 5) extra (fb_dbits dc) 0.

(* the inputs main reaches inflate() with *)
Definition fb_ok (S0: list Z) (fin: Z) (lits: list Z) (lc lx dc extra: Z) : Prop :=
  0 <= fin <= 1 /\ is_bytes lits /\ Zlength lits <= 32767 /\
  257 <= lc <= 285 /\ 0 <= lx <= Int.max_unsigned /\ 0 <= dc <= 29 /\ 0 <= extra <= Int.max_unsigned /\
  Zlength lits < fb_dist dc extra /\
  is_bytes S0 /\ 6 + 2 * Zlength lits <= Zlength S0 <= Int64.max_signed.

(* inflateInit2_(strm, w) returned Z_OK (state l_s (init_live sp w)); the first call is offered S[0 .. take) and
   zf_ao z bytes of space; the second the next bytes from S[read], read = m_snx of the first call's result, and
   room >= |lits| + 1 *)
Definition fb_theory_stmt : Prop :=
  forall S0 fin lits lc lx dc extra w sp L z take flush res,
    fb_ok S0 fin lits lc lx dc extra -> -15 <= w <= -8 ->
    let S := fb_bytes S0 fin lits lc lx dc extra in
    l_s L = l_s (init_live sp w) -> live_ok L -> zf_ok z ->
    0 <= take <= Z.min (Zlength S) Int.max_unsigned -> Int.min_signed <= flush <= Int.max_signed ->
    run2 flush lenfix_list distfix_list (m_init z L (sublist 0 take S)) res ->
    r_ret res = Z_MEM_ERROR \/
    (Zlength (m_ow (r_m res)) <= Zlength lits /\ m_sow (r_m res) = Zlength (m_ow (r_m res)) /\
     0 <= m_snx (r_m res) <= take /\
     forall L' z' flush' res',
       let read := m_snx (r_m res) in
       let inp := sublist read (read + Z.min (Zlength S - read) Int.max_unsigned) S in
       l_s L' = m_s (r_m res) -> live_ok L' -> zf_ok z' -> Zlength lits + 1 <= zf_ao z' ->
       Int.min_signed <= flush' <= Int.max_signed -> flush' <> Z_TREES ->
       run2 flush' lenfix_list distfix_list (m_init z' L' inp) res' ->
       r_ret res' = Z_MEM_ERROR \/
       (r_ret res' = Z_DATA_ERROR /\ m_sow (r_m res') = Zlength (m_ow (r_m res')) /\
        Zlength (m_ow (r_m res)) + Zlength (m_ow (r_m res')) <= Zlength lits)).

(* the bits main writes from bit 0, from the model of the bit writer (BWBits.v proves it) *)
Definition fb_bits (fin: Z) (lits: list Z) (lc lx dc extra: Z) : list bool :=
  bits_le fin 1 ++ bits_le 1 2 ++ concat (map (send_sym fixed_ll) lits) ++
  (if lc <? 280 then bits_msb (lc - 256) 7 else bits_msb (192 + lc - 280) 8) ++
  bits_le lx (fb_lbits lc) ++ bits_msb dc 5 ++ bits_le extra (fb_dbits dc).

Definition fb_bits_stmt : Prop :=
  forall S0 fin lits lc lx dc extra, fb_ok S0 fin lits lc lx dc extra ->
    let S := fb_bytes S0 fin lits lc lx dc extra in
    let B := fb_bits fin lits lc lx dc extra in
    Zlength S = Zlength S0 /\ is_bytes S /\ Zlength B <= 8 * Zlength S0 /\
    sublist 0 (Zlength B) (bytes_bits S) = B.
