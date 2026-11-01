(* Law rt_stream, round 1's bounded harness: what main's deflate loop needs from the model of
   deflate.c.  UDFacts.v states it for the harness of any length (urts_dfacts).

   harness/rt_stream.c calls deflateInit2 with any level, windowBits, memLevel and strategy (method Z_DEFLATED),
   then deflate() until Z_STREAM_END, each call offered the next piece of the data (at most 2^20 bytes in all: the
   input object of the call is exactly the bytes offered and not yet consumed), any flush Z_NO_FLUSH .. Z_BLOCK
   (Z_FINISH, once given, repeated with the rest of the data) and any output space (at most 2^22 bytes of output
   in all).  The shared specifications of deflate.c (DSpec9.deflateInit2__spec_v9, DSpec.deflate_spec) are
   functional: a call's result is the checked model run, which must be defined.

   [rts_dfacts J]: an invariant [J wbits D O fin s tin tout adler] between the calls (windowBits [wbits] of
   deflateInit2, the data consumed [D], the output so far [O], [fin = Some R] once Z_FINISH was given with [R]
   the data not consumed since, the state [s], the fields total_in, total_out, adler) such that every call is
   defined, and the call that returns Z_STREAM_END ends a stream that inflate decodes ([RTFinal.dfinal], no
   dictionary, no gzip header).  [J] is abstract (round 1's DTheory.v chose it from the deflate side of the
   round trips; for any length, UDTheory.v does). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7.
Import ListNotations.
Local Open Scope Z_scope.

Definition rts_dinv : Type :=
  Z -> list Z -> list Z -> option (list Z) -> dstate -> Z -> Z -> Z -> Prop.

Record rts_dfacts (J : rts_dinv) : Prop := {
  (** deflateInit2(strm, level, Z_DEFLATED, windowBits, memLevel, strategy) (deflateInit2_ with the right
      version and stream size) is defined for every outcome of the five allocations; on Z_OK the parameters
      were accepted and the invariant holds *)
  rd_init : forall level wbits mem strategy a1 a2 a3 a4 a5 z,
    rs32 level -> rs32 wbits -> rs32 mem -> rs32 strategy ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      code = Z_OK ->
      rparams_ok level 8 wbits mem strategy = true /\
      exists s, os = Some s /\ J wbits [] [] None s (z_total_in z') (z_total_out z') (z_adler z');
  (** the fields total_in, total_out, adler between the calls are 64-bit values *)
  rd_range : forall wbits D O fin s tin tout adler,
    J wbits D O fin s tin tout adler ->
    0 <= tin <= 18446744073709551615 /\ 0 <= tout <= 18446744073709551615 /\
    0 <= adler <= 18446744073709551615;
  (** deflate(strm, flush): the input object [inb] (next_in at its start, avail_in its length), [aout] bytes of
      output space; once Z_FINISH was given, only Z_FINISH with the rest of the data *)
  rd_deflate : forall wbits D O fin s tin tout adler inb aout flush msg,
    J wbits D O fin s tin tout adler ->
    0 <= flush <= 5 -> rbytes inb -> Zlength D + Zlength inb <= 1048576 ->
    0 <= aout -> Zlength O + aout <= 4194304 ->
    (forall R, fin = Some R -> flush = Z_FINISH /\ inb = R) ->
    exists s' z' code,
      c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) /\
      rcall_ok inb aout tin tout z' /\
      (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) /\
      (let used := Zlength inb - z_avail_in z' in
       let D' := D ++ sublist 0 used inb in
       let O' := O ++ z_out z' in
       if code =? Z_STREAM_END then dfinal [] (rwrap_of wbits) (rwbe wbits) None D' O'
       else J wbits D' O' (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
              s' (z_total_in z') (z_total_out z') (z_adler z'))
}.

Definition rts_dtheory_stmt : Prop := exists J, rts_dfacts J.
