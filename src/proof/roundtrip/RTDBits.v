(* Round-trip part RT-D: the bit CONTENTS of trees.c's output.

   The huffman / trees areas only count bits (Bits.bitpos).  Here: [obits o], the bits an output state holds
   (the pending bytes from pending_buf[0] -- every writer runs with pending_out at the start of pending_buf --
   then the bi_valid low bits of bi_buf), and what each block writer of trees.c appends to them, in terms of
   Format.v's encoding (RFC 1951).  The specs below are proved in their own files: the writers in RTDWriter.v
   (rtd_writer_ok), _tr_flush_block in RTDFlush2.v against RTDFix.flush_block_fspec2 (flush_block_fspec is
   false for a stored block of values that are not bytes). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDIface.
Require Zlib.proof.huffman.Overlay.
Require Export Zlib.proof.huffman.Bits.
Import ListNotations.
Local Open Scope Z_scope.

(** ** zlib's symbols as Format's *)

(* _tr_tally's symbol (dist, lc): a literal lc (dist = 0) or a match of length lc + 3 at distance dist *)
Definition fsym (x : Z * Z) : F.sym := if fst x =? 0 then F.Lit (snd x) else F.Ref (snd x + 3) (fst x).

(* the symbols are valid deflate symbols after the output [out] (history included) in a window of [wmax]
   bytes: literals are bytes; matches have length 3..258 and a distance 1..min(|out|, wmax) *)
Fixpoint syms_rok (wmax : Z) (out : list Z) (syms : list (Z * Z)) : Prop :=
  match syms with
  | [] => True
  | x :: r =>
      (if fst x =? 0 then 0 <= snd x < 256
       else 0 <= snd x <= 255 /\ 1 <= fst x <= Zlength out /\ fst x <= wmax) /\
      syms_rok wmax (F.sym_data out (fsym x)) r
  end.

(** ** Encoding of a run of blocks *)

(* blocks [bs] from bit position [p] of the deflate stream: none final (fin = false), or the last one final
   (fin = true) *)
Fixpoint enc_from (p : Z) (bs : list F.block) (fin : bool) : list bool :=
  match bs with
  | [] => []
  | b :: r =>
      let e := F.enc_block p (fin && match r with [] => true | _ => false end) b in
      e ++ enc_from (p + Zlength e) r fin
  end.

(* ... and, after a final block, the zero bits up to the byte boundary (bi_windup) *)
Definition enc_out (p : Z) (bs : list F.block) (fin : bool) : list bool :=
  let e := enc_from p bs fin in if fin then e ++ F.zeros (F.pad8 (p + Zlength e)) else e.

(** ** The bits of an output state *)

(* pending_buf[0 .. pending) as bits, then the bi_valid bits of bi_buf (least significant first) *)
Definition obits (o : outbuf) : list bool :=
  F.bytes_bits (sublist 0 (o_pending o) (o_buf o)) ++ F.bits_le (o_bi_buf o) (o_bi_valid o).

(** ** The specifications (each proved in its own file; hypotheses of the assembly) *)

(* the bit writer: send_bits, put_byte (on a whole byte boundary), bi_flush (_tr_flush_bits), bi_windup *)
Definition writer_fspec : Prop :=
  (forall o m v n o' m',
     bits_ok o -> 1 <= n <= 16 -> 0 <= v < 2 ^ n -> c_send_bits (o, m) v n = Some (o', m') ->
     bits_ok o' /\ obits o' = obits o ++ F.bits_le v n) /\
  (forall o m c o' m',
     bits_ok o -> o_bi_valid o = 0 -> 0 <= c < 256 -> c_put_byte (o, m) c = Some (o', m') ->
     bits_ok o' /\ o_bi_valid o' = 0 /\ obits o' = obits o ++ F.bits_le c 8) /\
  (forall o m o' m',
     bits_ok o -> c_tr_flush_bits (o, m) = Some (o', m') ->
     bits_ok o' /\ o_bi_valid o' <= 7 /\ obits o' = obits o) /\
  (forall o m o' m',
     bits_ok o -> c_bi_windup (o, m) = Some (o', m') ->
     bits_ok o' /\ o_bi_valid o' = 0 /\ obits o' = obits o ++ F.zeros (F.pad8 (o_bi_valid o))).

(* _tr_stored_block(s, buf, len, last) from bit position p of the deflate stream (p and the bits in the bit
   buffer agree mod 8: everything before them is whole bytes) *)
Definition stored_block_fspec : Prop :=
  forall o m buf len last o' m' p,
    bits_ok o -> 0 <= last <= 1 -> 0 <= len <= 65535 -> (len = 0 \/ len <= Zlength buf) ->
    Forall F.byte_ok (sublist 0 len buf) ->
    0 <= p -> (p - o_bi_valid o) mod 8 = 0 ->
    c_tr_stored_block (o, m) buf len last = Some (o', m') ->
    bits_ok o' /\ o_bi_valid o' = 0 /\
    obits o' = obits o ++ F.enc_block p (last =? 1) (F.Stored (sublist 0 len buf)).

(* _tr_align: an empty fixed-Huffman block (not final), then bi_flush *)
Definition align_fspec : Prop :=
  forall o m o' m' p,
    bits_ok o -> c_tr_align (o, m) = Some (o', m') ->
    bits_ok o' /\ o_bi_valid o' <= 7 /\ obits o' = obits o ++ F.enc_block p false (F.Fixed []).

(* _tr_flush_block on the symbols [syms] of the block (Overlay.flush_pre: nothing pending, the symbols in
   sym_buf, their frequencies), with the window bytes [buf] of the block when block_start >= 0: one deflate
   block, well formed after the output [out] (history included), whose data is what the symbols expand to,
   appended to the bits (the last one final, then padded) *)
Definition flush_block_fspec : Prop :=
  forall t m buf sl last t' m' kind syms out wmax p,
    Overlay.flush_pre t syms -> 0 <= last <= 1 -> 0 <= p -> (p - o_bi_valid (tr_out t)) mod 8 = 0 ->
    syms_rok wmax out syms ->
    (forall b, buf = Some b -> Zlength b = sl /\ sl <= 65535 /\ F.syms_data out (map fsym syms) = out ++ b) ->
    c_tr_flush_block (t, m) buf sl last = Some ((t', m'), kind) ->
    exists blk,
      F.block_ok wmax out blk /\ F.block_data out blk = F.syms_data out (map fsym syms) /\
      bits_ok (tr_out t') /\ (last = 1 -> o_bi_valid (tr_out t') = 0) /\
      obits (tr_out t') = obits (tr_out t) ++ enc_out p [blk] (last =? 1).
