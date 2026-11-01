(* Law rj_bad_block: THE interface between main (BBMain.v, VST) and the theory (BBTheory.v).  Pure Coq.

   main chooses kind (0 stored, 1 reserved, 2 bad literal/length code, 3 bad distance code, 4 HLIT too large),
   which (0/1), the literals lits (kinds 2 and 3 only) and the n arbitrary bytes S0 of the stream, writes the block
   with put_bits / put_literal (bb_bytes: the bytes after the writes), then calls inflate() once on the whole stream,
   and a second time on the rest if the first returned Z_OK with flush = Z_TREES.  The theory says that the code
   checked is Z_DATA_ERROR. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.bit_writer.BWModel.
Require Export Zlib.proof.rfc1951.Format.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.inflate.Model2.
Require Import Zlib.proof.adler32.Bytes.
Import ListNotations.
Local Open Scope Z_scope.

(* unsigned btype[5] = {0, 3, 1, 1, 2}; *)
Definition bb_btype (kind: Z) : Z := Znth kind [0; 3; 1; 1; 2].

(* the stream after main's writes: BTYPE at bit 1, the literals from bit 3, then the bad element *)
Definition bb_bytes (S0: list Z) (kind which: Z) (lits: list Z) : list Z :=
  let S := put_bits_m S0 1 (bb_btype kind) 2 0 in
  let S := put_lits S 3 lits in
  let b := 3 + lits_len lits in
  if kind =? 2 then put_bits_m S b (198 + which) 8 1
  else if kind =? 3 then put_bits_m (put_bits_m S b 1 7 1) (b + 7) (30 + which) 5 1
  else if kind =? 4 then put_bits_m S b (30 + which) 5 0
  else S.

(* the inputs main reaches inflate() with; for kind 0 its gp_assume:
   (stream[1] | stream[2] << 8) != (~(stream[3] | stream[4] << 8) & 0xffff) *)
Definition bb_ok (S0: list Z) (kind which: Z) (lits: list Z) : Prop :=
  0 <= kind <= 4 /\ 0 <= which <= 1 /\ (kind <> 2 -> kind <> 3 -> lits = []) /\
  is_bytes lits /\ Zlength lits <= 2 ^ 20 /\
  is_bytes S0 /\ 5 + 2 * Zlength lits <= Zlength S0 <= Int.max_unsigned /\
  (kind = 0 ->
   let S := bb_bytes S0 kind which lits in
   Z.lor (Znth 1 S) (Z.shiftl (Znth 2 S) 8) <> Z.land (Z.lnot (Z.lor (Znth 3 S) (Z.shiftl (Znth 4 S) 8))) 65535).

(* inflateInit2_(strm, w) returned Z_OK (state l_s (init_live sp w)); the first call is offered the whole stream
   and room >= |lits| bytes of output space; the second (if any) the rest, with the stream fields the first left *)
Definition bb_theory_stmt : Prop :=
  forall S0 kind which lits w sp L z flush res,
    bb_ok S0 kind which lits -> -15 <= w <= -8 ->
    l_s L = l_s (init_live sp w) -> live_ok L -> zf_ok z ->
    Zlength lits <= zf_ao z -> Int.min_signed <= flush <= Int.max_signed ->
    let S := bb_bytes S0 kind which lits in
    run2 flush lenfix_list distfix_list (m_init z L S) res ->
    r_ret res = Z_DATA_ERROR \/
    (r_ret res = Z_OK /\ flush = Z_TREES /\ m_ow (r_m res) = [] /\
     forall L' z' res',
       l_s L' = m_s (r_m res) -> live_ok L' -> zf_ok z' -> Zlength lits <= zf_ao z' ->
       run2 flush lenfix_list distfix_list (m_init z' L' (sublist (m_snx (r_m res)) (Zlength S) S)) res' ->
       r_ret res' = Z_DATA_ERROR).

(* the bits main writes (from bit 1: BTYPE, the literals' fixed codes, the bad element), from the model of the
   bit writer (BWBits.v proves it) *)
Definition bb_tail_bits (kind which: Z) : list bool :=
  if kind =? 2 then bits_msb (198 + which) 8
  else if kind =? 3 then bits_msb 1 7 ++ bits_msb (30 + which) 5
  else if kind =? 4 then bits_le (30 + which) 5
  else [].

Definition bb_bits_stmt : Prop :=
  forall S0 kind which lits, bb_ok S0 kind which lits ->
    let S := bb_bytes S0 kind which lits in
    let B := bits_le (bb_btype kind) 2 ++ concat (map (send_sym fixed_ll) lits) ++ bb_tail_bits kind which in
    Zlength S = Zlength S0 /\ is_bytes S /\ 1 + Zlength B <= 8 * Zlength S0 /\
    sublist 1 (1 + Zlength B) (bytes_bits S) = B.
