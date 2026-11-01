(** * The deflateBound accounting for compress2_z's loop (harness/res_compress_bound.c), as the loop uses it

    compress2_z (compress.c) gives deflate() its data of up to 2^63-1 bytes in pieces of at most (uInt)-1 bytes of
    input and of output space: Z_NO_FLUSH while input remains, then Z_FINISH; a piece of input is given again
    (the rest of it) when the output space ran out, a piece of output space when the input ran out.  With
    destLen = compressBound_z(n), which is deflateBound of its stream (level -1..9, windowBits 15, memLevel 8, the
    default strategy, no dictionary), the loop must end with Z_STREAM_END and an output that fits.

    [c2_facts Bpre Brun] is what RTC2WLoop.c2w_bound needs from the model:
    - [c2f_init]: deflateInit2_ with compress2_z's parameters ([Bpre] after it);
    - [c2f_start]: the accounting [Brun] starts at compressBound_z(n), for any n < 2^63;
    - [c2f_range]: what [Brun] says of the position in the data and of the output so far;
    - [c2f_split]: one call of the loop: its codes, progress, and the output space never full before the end of
      the stream when the bound is above 2^32-1 (then n >= 2^25, and the accounting has a margin of a byte); with
      a bound below 2^32 the first call is offered all the data and all of the output space, and ends the stream.

    The output space can be full exactly at the end of the stream only for small n: a stream of exactly
    deflateBound bytes exists (level 1, n = 2^18-1), and a deflate(Z_FINISH) call whose output space ends inside
    its trailer returns Z_OK with total_out = deflateBound; compress2_z gives all of the output space at once
    when the bound is below 2^32, so this case does not arise in its loop.

    These facts hold only with fix F9: without it, deflate_stored compared a block length with
    left + avail_in in 32 bits, and at level 0 a Z_FINISH call with left + avail_in >= 2^32 could write a last
    stored block with input left (n = 56298431302699 in compress2_z's loop). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LawFactsW.
Import ListNotations.
Local Open Scope Z_scope.

Record c2_facts (Bpre : bpre_inv) (Brun : brun_inv) : Prop := {
  (** deflateInit2_ with compress2_z's parameters (method Z_DEFLATED, windowBits 15, memLevel 8, the default
      strategy): defined for every outcome of its allocations, and [Bpre] after a Z_OK *)
  c2f_init : forall level a1 a2 a3 a4 a5 z,
    -1 <= level <= 9 ->
    (exists r, c_deflateInit2_ true true false level 8 15 8 0 a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 15 8 0 a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      code = Z_OK ->
      exists s, os = Some s /\ d_gzhead s = None /\
                Bpre level 15 8 0 false s (z_total_in z') (z_total_out z') (z_adler z');
  (** the accounting starts at compressBound_z(n), nothing written yet, for any n < 2^63 *)
  c2f_start : forall level s tin tout adler n,
    Bpre level 15 8 0 false s tin tout adler -> -1 <= level <= 9 -> 0 <= n <= 9223372036854775807 ->
    tout = 0 /\ Brun n (compressBound_z n) 0 false s tin tout adler;
  (** what [Brun] says of the position in the data and of the output so far *)
  c2f_range : forall n b pos fin s tin tout adler,
    Brun n b pos fin s tin tout adler -> 0 <= pos <= n /\ 0 <= tout <= b;
  (** one call of the loop, offered [ain] bytes at [nin] of the object [inb] and [aout] bytes of output space,
      both < 2^32; Z_FINISH exactly when the rest of the data is offered *)
  c2f_split : forall n b pos fin s tin tout adler inb nin ain aout flush msg,
    Brun n b pos fin s tin tout adler ->
    (flush = Z_NO_FLUSH \/ flush = Z_FINISH) -> (fin = true -> flush = Z_FINISH) ->
    bytes inb -> 0 <= nin -> 0 <= ain <= 4294967295 -> nin + ain <= Zlength inb ->
    pos + ain <= n -> (flush = Z_FINISH -> pos + ain = n) -> 0 <= aout <= 4294967295 ->
    exists s' z' code,
      c_deflate s (mkST inb nin ain tin [] aout tout adler msg) flush = Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\
      z_in z' = inb /\ 0 <= z_avail_in z' <= ain /\ z_next_in z' = nin + (ain - z_avail_in z') /\
      0 <= z_avail_out z' <= aout /\ Zlength (z_out z') = aout - z_avail_out z' /\ bytes (z_out z') /\
      z_total_in z' = tin + (ain - z_avail_in z') /\ z_total_out z' = tout + (aout - z_avail_out z') /\
      z_total_out z' <= b /\
      (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_END) /\
      (code = Z_BUF_ERROR -> aout = 0 \/ (ain = 0 /\ flush = Z_NO_FLUSH)) /\
      (code = Z_OK -> 0 < aout -> (0 < ain \/ flush = Z_FINISH) ->
       0 < (ain - z_avail_in z') + (aout - z_avail_out z')) /\
      (4294967295 < b -> code = Z_OK -> z_avail_out z' = 0 -> z_total_out z' < b) /\
      (flush = Z_FINISH -> fin = false -> pos = 0 -> b <= tout + aout -> code = Z_STREAM_END) /\
      (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) /\
      (code <> Z_STREAM_END ->
       Brun n b (pos + (ain - z_avail_in z')) (flush =? Z_FINISH) s' (z_total_in z') (z_total_out z') (z_adler z'))
}.

Definition c2_facts_stmt : Prop := exists Bpre Brun, c2_facts Bpre Brun.
