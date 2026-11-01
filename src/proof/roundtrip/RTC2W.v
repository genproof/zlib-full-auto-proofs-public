(** * compress.c's compress2_z over the model for any sizes: what res_compress_bound needs

    RTC2.c2_res is compress2_z's result for any sizes: its loop (RTC2.c2_run) gives deflate pieces of at most
    (uInt)-1 bytes of input and of output space, Z_NO_FLUSH while input remains, then Z_FINISH.  RTC2.c2_ok
    states what compress_roundtrip needs for at most 2^20 bytes; here, for data of up to 2^63-1 bytes (the most
    an object can have, PTRDIFF_MAX) and destLen = compressBound_z(n) (harness/res_compress_bound.c):

    - the model run is defined for every outcome of deflateInit2_'s five allocations;
    - compress2_z returns Z_OK or Z_MEM_ERROR (never Z_BUF_ERROR: compressBound_z(n) is deflateBound of its
      stream), and the output fits.

    Proved from the deflateBound accounting of compress2_z's loop (LawFactsC2W.c2_facts) by
    RTC2WLoop.c2w_bound. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTC2.
Import ListNotations.
Local Open Scope Z_scope.

Definition c2w_bound_stmt : Prop :=
  forall src level a1 a2 a3 a4 a5 z0,
    rbytes src -> Zlength src <= 9223372036854775807 -> -1 <= level <= 9 ->
    (exists r out, c2_res src (compressBound_z (Zlength src)) level a1 a2 a3 a4 a5 z0 r out) /\
    forall r out, c2_res src (compressBound_z (Zlength src)) level a1 a2 a3 a4 a5 z0 r out ->
      (r = Z_OK \/ r = Z_MEM_ERROR) /\ Zlength out <= compressBound_z (Zlength src).
