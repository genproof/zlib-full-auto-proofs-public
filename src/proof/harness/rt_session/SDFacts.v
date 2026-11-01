(* Law rt_session (harness/rt_session.c): what main's deflate part needs from the model of deflate.c.

   The harness calls deflateInit2 with level, windowBits, memLevel and strategy in zlib.h's ranges (method
   Z_DEFLATED), then, with a raw or zlib wrapper and the choice of a dictionary, deflateSetDictionary of 1 to
   2^32 - 1 bytes, or, with a gzip wrapper and the choice of a header, deflateSetHeader of a gzip header
   (RTK7.rhdr_ok7: text, hcrc, os any ints, time below 2^32, an extra field of up to 65535 bytes, a name and a
   comment of up to 2^32 - 2 nonzero bytes and their zero byte, each present or not), then deflate() until
   Z_STREAM_END exactly as rt_stream does (the next piece of data of any length, at most 2^32 - 1 bytes per call,
   any flush Z_NO_FLUSH .. Z_BLOCK, Z_FINISH once the rest fits in one call and then repeated, any output space
   below 2^32, none included).

   [ses_dfacts J] is rt_stream's UDFacts.urts_dfacts (round 4) for streams with a dictionary or a gzip header: an
   invariant [J wbits dict gh D O fin s tin tout adler] between the calls (windowBits [wbits] of deflateInit2, the
   dictionary [dict] given to deflateSetDictionary ([] without one), the gzip header [gh] given to
   deflateSetHeader (None without one), the data consumed [D], the output so far [O], [fin = Some R] once
   Z_FINISH was given with [R] the data not consumed since, the state [s], the fields total_in, total_out,
   adler) such that every call is defined, a call offered no output space returns Z_BUF_ERROR having consumed
   nothing, and the call that returns Z_STREAM_END ends a stream that inflate decodes with that dictionary and
   that header ([RTFinal.dfinal dict wrap wb gh]).  [J] is abstract: SDTheory.v chooses it from the deflate side
   of the round trips (RTK7.kfacts7, whose invariant K7 already takes a dictionary and a header) and deflate() on
   the wide deflate_api invariant (RTK7Api.api7_deflate_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7.
Require Export Zlib.proof.harness.rt_stream.UDFacts.
Import ListNotations.
Local Open Scope Z_scope.

Definition ses_dinv : Type :=
  Z -> list Z -> option DS7.gzh -> list Z -> list Z -> option (list Z) -> dstate -> Z -> Z -> Z -> Prop.

Record ses_dfacts (J : ses_dinv) : Prop := {
  (** deflateInit2(strm, level, Z_DEFLATED, windowBits, memLevel, strategy) (deflateInit2_ with the right
      version and stream size) is defined for every outcome of the five allocations; on Z_OK the parameters
      were accepted and the invariant holds, without a dictionary and without a header *)
  sd_init : forall level wbits mem strategy a1 a2 a3 a4 a5 z,
    rs32 level -> rs32 wbits -> rs32 mem -> rs32 strategy ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      code = Z_OK ->
      rparams_ok level 8 wbits mem strategy = true /\
      exists s, os = Some s /\ J wbits [] None [] [] None s (z_total_in z') (z_total_out z') (z_adler z');
  (** for parameters in zlib.h's ranges (harness: gp_assume(deflate_params_ok(...))) deflateInit2 returns Z_OK or
      Z_MEM_ERROR *)
  sd_init_code : forall level wbits mem strategy a1 a2 a3 a4 a5 z os z' code,
    rparams_ok level 8 wbits mem strategy = true ->
    c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
    code = Z_OK \/ code = Z_MEM_ERROR;
  (** the fields total_in, total_out, adler between the calls are 64-bit values; the state holds the header *)
  sd_range : forall wbits dict gh D O fin s tin tout adler,
    J wbits dict gh D O fin s tin tout adler ->
    0 <= tin <= 18446744073709551615 /\ 0 <= tout <= 18446744073709551615 /\
    0 <= adler <= 18446744073709551615 /\ d_gzhead s = gh;
  (** deflateSetDictionary(strm, dict, |dict|) right after deflateInit2 on a raw or zlib stream (any avail_in and
      avail_out: new_stream's): Z_OK, the invariant with the dictionary *)
  sd_dict : forall wbits s tin tout adler d ain aout msg,
    J wbits [] None [] [] None s tin tout adler -> rwrap_of wbits <> 2 ->
    rbytes d -> 1 <= Zlength d <= 4294967295 -> 0 <= ain <= 4294967295 -> 0 <= aout <= 4294967295 ->
    exists s' z',
      c_deflateSetDictionary s (rzcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', Z_OK) /\
      J wbits d None [] [] None s' (z_total_in z') (z_total_out z') (z_adler z');
  (** deflateSetHeader(strm, &head) right after deflateInit2 on a gzip stream: Z_OK, the invariant with the
      header *)
  sd_head : forall wbits s tin tout adler h z,
    J wbits [] None [] [] None s tin tout adler -> rwrap_of wbits = 2 -> rhdr_ok7 h ->
    c_deflateSetHeader s z (Some h) = Some (set_d_gzhead s (Some h), z, Z_OK) /\
    J wbits [] (Some h) [] [] None (set_d_gzhead s (Some h)) tin tout adler;
  (** deflate(strm, flush): the input object [inb] (next_in at its start, avail_in its length, at most
      2^32 - 1), [aout] < 2^32 bytes of output space, the data and the output at most PTRDIFF_MAX bytes in all;
      once Z_FINISH was given, only Z_FINISH with the rest of the data *)
  sd_deflate : forall wbits dict gh D O fin s tin tout adler inb aout flush msg,
    J wbits dict gh D O fin s tin tout adler ->
    0 <= flush <= 5 -> rbytes inb -> Zlength inb <= 4294967295 -> Zlength D + Zlength inb <= max_size ->
    0 <= aout <= 4294967295 -> Zlength O + aout <= max_size ->
    (forall R, fin = Some R -> flush = Z_FINISH /\ inb = R) ->
    exists s' z' code,
      c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) /\
      rcall_ok inb aout tin tout z' /\ d_gzhead s' = gh /\
      (* no output space: Z_BUF_ERROR, nothing consumed (and, by rcall_ok, nothing written, the counters kept) *)
      (aout = 0 -> code = Z_BUF_ERROR /\ z_avail_in z' = Zlength inb) /\
      (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) /\
      (let used := Zlength inb - z_avail_in z' in
       let D' := D ++ sublist 0 used inb in
       let O' := O ++ z_out z' in
       if code =? Z_STREAM_END then dfinal dict (rwrap_of wbits) (rwbe wbits) gh D' O'
       else J wbits dict gh D' O' (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
              s' (z_total_in z') (z_total_out z') (z_adler z'))
}.

Definition ses_dtheory_stmt : Prop := exists J, ses_dfacts J.
