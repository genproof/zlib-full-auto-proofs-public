(* The laws rt_partial, rj_truncated, rj_bad_checksum and rfc_trailing_bytes: the decode context (DecodeDefs.dctx)
   of the stream deflate wrote.

   [dctx_stmt]: the bytes O of a deflate run started with windowBits wbits (DFacts.dfinal_of: no dictionary, no
   gzip header), followed by any bytes in the input [src], are a context of the decode theory for inputs of any
   length (Decode7.dctx_ok7) with inflateInit2's windowBits [iwb wbits]: the stream is O (slen = |O|), its data
   is D, no history, a zlib stream without FDICT (deflate's zlib header without a dictionary never has
   FCHECK = 31), a gzip stream with zlib's default header (gz_simple), the trailer of length [trl_of wbits]
   for zlib and gzip. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.rfc1951.Decode7.
Require Import Zlib.proof.harness.clip_streams.IFacts.
Import ListNotations.
Local Open Scope Z_scope.

Definition dctx_stmt : Prop :=
  forall wbits D O src,
    dfinal_of wbits D O -> Zlength O <= Zlength src <= 2 ^ 64 - 1 -> sublist 0 (Zlength O) src = O ->
    bytes_ok src ->
    exists G, dctx_ok7 G /\ dc_src G = src /\ slen G = Zlength O /\ full G = D /\ dc_hist G = [] /\
      dc_iw G = iwb wbits /\ (forall wb fl did, dc_w G = WZlib wb fl did -> did = None) /\
      trl_len (dc_w G) = (if wbits <? 0 then 0 else trl_of wbits).
