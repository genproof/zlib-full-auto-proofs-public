(** * compress2_z's output for any sizes is the zlib stream of its data

    RTC2.c2_ok says it for at most 2^20 bytes (one deflate(Z_FINISH) call).  The laws rt_roundtrip and
    api_short_output give compress2 data of up to PTRDIFF_MAX = 2^63-1 bytes with destLen = compressBound_z(n):
    compress2_z's loop (RTC2.c2_run) then gives deflate() pieces of at most (uInt)-1 bytes of input and of output
    space, Z_NO_FLUSH while input remains, then Z_FINISH.  When the model's result is Z_OK, the bytes written are
    the zlib stream (windowBits 15, no dictionary, no gzip header) of the whole data.

    That the run is defined and returns Z_OK or Z_MEM_ERROR is RTC2W.c2w_bound_stmt; this is what its output is.
    It follows from the deflate side of the round trips without size limits (RTK7.kfacts7, whose calls take their
    input piece as the whole object: InSlice.deflate_slice cuts compress2_z's source down to it) and the
    per-call counters of compress2_z's loop (LawFactsC2W.c2f_split). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTC2.
Import ListNotations.
Local Open Scope Z_scope.

Definition c2w_final_stmt : Prop :=
  forall src level a1 a2 a3 a4 a5 z0 r out,
    rbytes src -> Zlength src <= 9223372036854775807 -> -1 <= level <= 9 ->
    c2_res src (compressBound_z (Zlength src)) level a1 a2 a3 a4 a5 z0 r out ->
    r = Z_OK -> dfinal [] 1 15 None src out.
