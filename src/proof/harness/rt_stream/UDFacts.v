(* Law rt_stream: what main's deflate loop needs from the model of deflate.c (data of any length).

   harness/rt_stream.c calls deflateInit2 with any level, windowBits, memLevel and strategy (method Z_DEFLATED),
   then deflate() until Z_STREAM_END, each call offered the next piece of the data (data of any length up to
   PTRDIFF_MAX; each call's input object is exactly the bytes offered and not yet consumed, at most 2^32 - 1 of
   them: clip()), any flush Z_NO_FLUSH .. Z_BLOCK (Z_FINISH only once the rest of the data fits in one call, then
   repeated with the rest) and any output space below 2^32 (clip()) in an output object of any size up to
   PTRDIFF_MAX.  The shared specifications of deflate.c (DSpec9.deflateInit2__spec_v9, DSpecV.deflate_specV) are
   functional: a call's result is the checked model run, which must be defined.

   [urts_dfacts J]: an invariant [J wbits D O fin s tin tout adler] between the calls (windowBits [wbits] of
   deflateInit2, the data consumed [D], the output so far [O], [fin = Some R] once Z_FINISH was given with [R]
   the data not consumed since, the state [s], the fields total_in, total_out, adler) such that every call is
   defined, and the call that returns Z_STREAM_END ends a stream that inflate decodes ([RTFinal.dfinal], no
   dictionary, no gzip header).  It is DFacts.rts_dfacts (round 1: data at most 2^20 bytes, output at most 2^22)
   with the sizes of the harness.  [J] is abstract: UDTheory.v chooses it from the deflate side of the round trips
   (RTK7.kfacts7) and deflate() on the wide deflate_api invariant (RTK7Api.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7.
Import ListNotations.
Local Open Scope Z_scope.

(* PTRDIFF_MAX: the largest object the harness asks for *)
Definition max_size : Z := 9223372036854775807.

Definition urts_dinv : Type :=
  Z -> list Z -> list Z -> option (list Z) -> dstate -> Z -> Z -> Z -> Prop.

Record urts_dfacts (J : urts_dinv) : Prop := {
  (** deflateInit2(strm, level, Z_DEFLATED, windowBits, memLevel, strategy) (deflateInit2_ with the right
      version and stream size) is defined for every outcome of the five allocations; on Z_OK the parameters
      were accepted and the invariant holds *)
  ud_init : forall level wbits mem strategy a1 a2 a3 a4 a5 z,
    rs32 level -> rs32 wbits -> rs32 mem -> rs32 strategy ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      code = Z_OK ->
      rparams_ok level 8 wbits mem strategy = true /\
      exists s, os = Some s /\ J wbits [] [] None s (z_total_in z') (z_total_out z') (z_adler z');
  (** for parameters in zlib.h's ranges (harness: gp_assume(deflate_params_ok(...))) deflateInit2 returns Z_OK or
      Z_MEM_ERROR *)
  ud_init_code : forall level wbits mem strategy a1 a2 a3 a4 a5 z os z' code,
    rparams_ok level 8 wbits mem strategy = true ->
    c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
    code = Z_OK \/ code = Z_MEM_ERROR;
  (** the fields total_in, total_out, adler between the calls are 64-bit values; no gzip header *)
  ud_range : forall wbits D O fin s tin tout adler,
    J wbits D O fin s tin tout adler ->
    0 <= tin <= 18446744073709551615 /\ 0 <= tout <= 18446744073709551615 /\
    0 <= adler <= 18446744073709551615 /\ d_gzhead s = None;
  (** deflate(strm, flush): the input object [inb] (next_in at its start, avail_in its length, at most
      2^32 - 1), [aout] < 2^32 bytes of output space, the data and the output at most PTRDIFF_MAX bytes in all;
      once Z_FINISH was given, only Z_FINISH with the rest of the data *)
  ud_deflate : forall wbits D O fin s tin tout adler inb aout flush msg,
    J wbits D O fin s tin tout adler ->
    0 <= flush <= 5 -> rbytes inb -> Zlength inb <= 4294967295 -> Zlength D + Zlength inb <= max_size ->
    0 <= aout <= 4294967295 -> Zlength O + aout <= max_size ->
    (forall R, fin = Some R -> flush = Z_FINISH /\ inb = R) ->
    exists s' z' code,
      c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) /\
      rcall_ok inb aout tin tout z' /\ d_gzhead s' = None /\
      (* no output space: Z_BUF_ERROR, nothing consumed (and, by rcall_ok, nothing written, the counters kept) *)
      (aout = 0 -> code = Z_BUF_ERROR /\ z_avail_in z' = Zlength inb) /\
      (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) /\
      (let used := Zlength inb - z_avail_in z' in
       let D' := D ++ sublist 0 used inb in
       let O' := O ++ z_out z' in
       if code =? Z_STREAM_END then dfinal [] (rwrap_of wbits) (rwbe wbits) None D' O'
       else J wbits D' O' (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
              s' (z_total_in z') (z_total_out z') (z_adler z'))
}.

Definition urts_dtheory_stmt : Prop := exists J, urts_dfacts J.
