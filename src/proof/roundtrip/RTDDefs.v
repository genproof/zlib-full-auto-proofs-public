(* Round-trip part RT-D: the functional invariant of a live deflate stream.

   With H = dict ++ D the history (the preset dictionary, then the data consumed so far):
   - [kwin]: the window holds the last strstart + lookahead bytes of H;
   - [kdata]: the blocks BS emitted so far are well formed and expand to the bytes of H below block_start, the
     symbols tallied since (sym_buf, [wtrees] of the deflate laws' invariant) are valid and expand from there
     to the bytes below strstart (- 1 while deflate_slow holds a pending byte), and deflate_slow's lazy candidate
     is a real match;
   - [khash]: the hash chains are hash-consistent (longest_match does not compare the third byte of a candidate:
     zlib relies on the hash, deflate.c "It is not necessary to compare scan[2] and match[2]"), and ins_h is
     primed for strstart when deflate_fast / deflate_slow will insert it;
   - [allbits]: all the bits produced (output, pending bytes, bit buffer), which the stage invariants equate with
     the header's bytes and Format's encoding of BS. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDBits.
Require Export Zlib.proof.roundtrip.RTDLTCW.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Bits *)

(* the bits waiting in the bit buffer *)
Definition bibits (s : dstate) : list bool := F.bits_le (o_bi_buf (tr_out (d_tr s))) (d_bi_valid s).

(* all the bits produced: the output O so far, the pending bytes pending_buf[pending_out ..), the bit buffer *)
Definition allbits (O : list Z) (s : dstate) : list bool := F.bytes_bits (O ++ pend s) ++ bibits s.

(** ** Data *)

(* the window holds the last strstart + lookahead bytes of the history H *)
Definition kwin (H : list Z) (s : dstate) : Prop :=
  let wl := d_strstart s + d_lookahead s in
  wl <= Zlength H /\
  forall i, 0 <= i < wl -> Znth i (mb_val (d_window s)) = Znth (Zlength H - wl + i) H.

(* deflate_slow's lazy candidate (match_length >= MIN_MATCH at match_start, found at strstart - 1) is a match *)
Definition kmatch (s : dstate) : Prop :=
  d_match_available s = 1 -> MIN_MATCH <= d_match_length s ->
  forall i, 0 <= i < d_match_length s ->
    Znth (d_match_start s + i) (mb_val (d_window s)) = Znth (d_strstart s - 1 + i) (mb_val (d_window s)).

(* the blocks BS and the symbols syms of the current block, for the history H = dict ++ D *)
Definition kdata (dict D : list Z) (BS : list F.block) (syms : list (Z * Z)) (s : dstate) : Prop :=
  let H := dict ++ D in
  let off := Zlength H - (d_strstart s + d_lookahead s) in
  kwin H s /\ kmatch s /\ wtrees s syms /\
  F.blocks_ok (2 ^ d_w_bits s) dict BS /\
  F.expand dict BS = sublist 0 (off + d_block_start s) H /\
  syms_rok (2 ^ d_w_bits s) (F.expand dict BS) syms /\
  F.syms_data (F.expand dict BS) (map fsym syms) = sublist 0 (off + d_strstart s - d_match_available s) H.

(** ** Hash chains *)

(* the hash of the three bytes at window position p (UPDATE_HASH from window[p], as fill_window primes it) *)
Definition h3 (s : dstate) (p : Z) : Z :=
  let w := mb_val (d_window s) in
  update_hash s (update_hash s (Znth p w) (Znth (p + 1) w)) (Znth (p + 2) w).

(* from every bucket b, the chain entries longest_match may visit (above its limit [lim s]) are strings of
   data bytes whose hash is b *)
Definition chain_hok (s : dstate) : Prop :=
  forall b, 0 <= b < d_hash_size s ->
  exists Gb : Z -> Prop,
    Gb (Znth b (d_head s)) /\
    forall q, Gb q -> 0 < q -> lim s <= q ->
      q + 2 < d_strstart s + d_lookahead s /\ h3 s q = b /\ Gb (Znth (Z.land q (d_w_mask s)) (d_prev s)).

(* ins_h is primed for position p: two UPDATE_HASHes with window[p], window[p + 1] (so that INSERT_STRING(p)
   computes h3 p) *)
Definition primed (s : dstate) (p : Z) : Prop :=
  exists h0, d_ins_h s = update_hash s (update_hash s h0 (Znth p (mb_val (d_window s))))
                                     (Znth (p + 1) (mb_val (d_window s))).

(* as the deflate laws' [whash]: at level 0 [matches] counts the slides since the chains were valid *)
Definition khash (s : dstate) : Prop :=
  (if d_level s =? 0 then
     (d_matches s = 0 /\ chain_hok s) \/ (d_matches s = 1 /\ chain_hok (slide_hc s)) \/ d_matches s = 2
   else chain_hok s) /\
  ((fn_of s = 1 \/ fn_of s = 2) -> MIN_MATCH <= d_lookahead s -> d_insert s = 0 /\ primed s (d_strstart s)).

(* everything the compression functions keep *)
Definition kcore (dict D : list Z) (BS : list F.block) (syms : list (Z * Z)) (s : dstate) : Prop :=
  kdata dict D BS syms s /\ khash s.

(* the bstate of a compression function that emitted the final block *)
Definition fin_bs (bs : bstate) : bool :=
  match bs with finish_started | finish_done => true | _ => false end.
