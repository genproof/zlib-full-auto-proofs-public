(* uncompress2 for any sizes on a zlib stream that deflate wrote: what the laws api_short_output and
   rt_roundtrip need of the model (UModelW.uncompressw_rel).

   O is the zlib stream (windowBits 15, no dictionary, no gzip header) of the data D (RTFinal.dfinal, the form
   compress2's output has: RTC2WFinal.c2w_final_stmt).  The source src is O followed by any bytes (src = O when
   nothing follows it).  uncompress2 of src into cap bytes of space, uncompress2_z's loop of inflate() calls
   offered pieces of at most 2^32-1 bytes, ends in one of three ways:
   - Z_MEM_ERROR (an allocation failed);
   - Z_OK when the space holds the data (cap >= |D|): the data written, exactly the bytes of O read (inflate()
     stops at the end of the stream, Z_STREAM_END, and none of the bytes after it is consumed);
   - Z_BUF_ERROR when it does not (cap < |D|): the space filled with the first cap bytes of D, with bytes of O left.
   It follows from the decode theory for calls of up to 2^32-1 bytes (wide/Decode7: each call extends a prefix
   of the data, a call that stops before the stream's end with input left has filled its output space, and
   Z_STREAM_END comes exactly at the end of the stream). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.uncompr.UModelW.
Require Zlib.proof.roundtrip.RTFinal.
Require Import Zlib.proof.roundtrip.RTDIface.
Require Zlib.proof.zutil.Libc.
Import ListNotations.
Local Open Scope Z_scope.

Definition uw_theory_stmt : Prop :=
  forall D O src cap r slen dlen out,
    Zlib.proof.roundtrip.RTFinal.dfinal [] 1 15 None D O -> rbytes D -> Zlength D <= 9223372036854775807 ->
    sublist 0 (Zlength O) src = O -> Zlength O <= Zlength src ->
    Zlib.proof.zutil.Libc.bytes_ok src ->
    Zlength src <= 18446744073709551615 -> 0 <= cap <= 18446744073709551615 ->
    uncompressw_rel src cap r slen dlen out ->
    r = Z_MEM_ERROR \/
    (r = Z_OK /\ Zlength D <= cap /\ dlen = Zlength D /\ out = D /\ slen = Zlength O) \/
    (r = Z_BUF_ERROR /\ cap < Zlength D /\ dlen = cap /\ out = sublist 0 cap D /\ 0 <= slen < Zlength O).
