(** * deflate() calls of any kind, in any number, after a successful deflateInit2_

    harness/res_memory_deflate.c (law res_memory_deflate) calls deflateInit2 with any parameters and then, as
    long as it likes, deflate() with any piece of its data (at most 2^32 - 1 bytes at a time, the data below
    2^63 bytes in all), any output space (at most 2^32 - 1 bytes) and any flush (any int: also invalid ones, also
    Z_NO_FLUSH after Z_FINISH, also more calls after Z_STREAM_END).  The specification of deflate()
    (DSpec.deflate_spec, za/deflate/DSpec.v deflate_spec_za) is functional: its precondition is that the
    checked model of the call is defined, [c_deflate s z flush = Some r] (None stands for an unsafe execution).
    So main's loop needs an invariant [K s tin adler] of the abstract state [s] (with [tin] the field total_in
    and [adler] the field strm->adler; total_out is any 64-bit value, the model only counts it) that:
    - holds after every successful deflateInit2_ ([ac_init]),
    - keeps strm->adler a 32-bit value and the state without a gzip header (the stream's ranges of the next call;
      [hdr_at] of a state without header is empty) ([ac_adler], [ac_gzhead]),
    - makes every call defined, whatever its flush, input and output space, and holds again after it, whatever
      its result ([ac_deflate]); the stream after the call is described by [call_okw] (DetWide.v): next_in
      advanced by the bytes consumed (all of them at most), total_in counting them, the bytes written, total_out
      counting them modulo 2^64.

    The input of a call is the piece [inb] offered (next_in at its start, avail_in its length): the harness
    offers data + read, take bytes.

    [any_calls_stmt] is proved in AnyCallsProof.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetWide.
Import ListNotations.
Local Open Scope Z_scope.

Record any_calls (K : dstate -> Z -> Z -> Prop) : Prop := {
  (** deflateInit2(strm, level, Z_DEFLATED, windowBits, memLevel, strategy) with any int parameters, for every
      outcome of the five allocations and any stream before it: on Z_OK the invariant holds *)
  ac_init : forall level wbits mem strategy a1 a2 a3 a4 a5 z s z',
    s32 level -> s32 wbits -> s32 mem -> s32 strategy ->
    c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (Some s, z', Z_OK) ->
    K s (z_total_in z') (z_adler z');
  (** strm->adler stays a 32-bit value *)
  ac_adler : forall s tin adler, K s tin adler -> 0 <= adler < 4294967296;
  (** the state has no gzip header (deflateSetHeader is never called) *)
  ac_gzhead : forall s tin adler, K s tin adler -> d_gzhead s = None;
  (** deflate(strm, flush) with any int flush, the piece [inb] (at most 2^32 - 1 bytes; total_in plus the piece
      below 2^63), [aout] bytes of output space (at most 2^32 - 1), any total_out and any msg: defined, and the
      invariant holds after it, whatever it returned *)
  ac_deflate : forall s tin adler inb aout tout flush msg,
    K s tin adler -> s32 flush -> bytes inb -> Zlength inb <= 4294967295 ->
    0 <= tin -> tin + Zlength inb <= 9223372036854775807 ->
    0 <= aout <= 4294967295 -> u64r tout ->
    exists s' z' code,
      c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) /\
      call_okw inb 0 aout tin tout z' /\
      K s' (z_total_in z') (z_adler z')
}.

Definition any_calls_stmt : Prop := exists K, any_calls K.
