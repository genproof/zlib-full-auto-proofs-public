(* The laws rt_partial, rj_truncated, rj_bad_checksum and rfc_trailing_bytes: THE interface between the deflate
   part of their mains (VST) and the model theory of deflate.

   The four harnesses compress the same way:
     deflateInit2(&c, level, Z_DEFLATED, wbits, mem, strategy)        any ints; not Z_OK ends the run
     capacity = deflateBound_z(&c, n)                                   n = data_len <= PTRDIFF_MAX = 2^63 - 1
     do { rest = n - consumed; flush = rest <= UINT_MAX ? Z_FINISH : Z_NO_FLUSH;
          avail_in = clip(rest); avail_out = clip(capacity - produced); code = deflate(&c, flush); }
     while (code == Z_OK);                                              not Z_STREAM_END ends the run
   Each deflate() call is given the next piece of the data as its own input object (the slice [next_in,
   next_in + avail_in) of the data, at most 2^32 - 1 bytes: DSpec.deflate_spec bounds the object) and the next
   clip(capacity - produced) bytes of the output object.

   The theory chooses two invariants (existential, so that the mains and the theory are independent):
   [J0 wbits s tin tout adler] after deflateInit2, [J wbits data b pos O s tin tout adler] at the head of the
   loop (data: the n bytes, b: the capacity, pos: the bytes consumed, O: the bytes produced; s and tin, tout,
   adler: the state and the z_stream's fields).  The facts give what deflateInit2_ / deflateBound_z / deflate's
   specifications need (the model runs are defined) and what the mains need of the outcome; at Z_STREAM_END
   the output is the deflate stream of the data ([RTFinal.dfinal], no dictionary, no gzip header). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7.
Import ListNotations.
Local Open Scope Z_scope.

(* laws_common.h's clip(n): the most one call can take *)
Definition clipz (n : Z) : Z := Z.min n umax.

(* the flush of the call made with [rest] bytes of data not consumed *)
Definition dflush (rest : Z) : Z := if rest <=? umax then Z_FINISH else Z_NO_FLUSH.

(* the input object of the call made after [pos] bytes were consumed *)
Definition dpiece (data : list Z) (pos : Z) : list Z := sublist pos (pos + clipz (Zlength data - pos)) data.

(* the stream deflateInit2_'s model runs on (DSpec9.zrst0: the fields it neither reads nor keeps) *)
Definition dz0 : strm := rzcall [] 0 0 0 0 0 0 None.

(* deflateInit2_ accepts windowBits wbits (the windowBits part of RTDIface.rparams_ok) *)
Definition wbits_acc (wbits : Z) : bool :=
  negb (wbits <? -15) && (8 <=? rwb_of wbits) && (rwb_of wbits <=? 15) &&
  (negb (rwb_of wbits =? 8) || (rwrap_of wbits =? 1)).

(* the deflate stream of the data that ended a run started with windowBits wbits *)
Definition dfinal_of (wbits : Z) (data O : list Z) : Prop :=
  wbits_acc wbits = true /\ dfinal [] (rwrap_of wbits) (rwbe wbits) None data O.

Definition max_size : Z := 9223372036854775807.   (* PTRDIFF_MAX *)
Definition max_u64 : Z := 18446744073709551615.

Record clip_dfacts (J0 : Z -> dstate -> Z -> Z -> Z -> Prop)
                   (J : Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop) : Prop := {
  (** deflateInit2 (right version and stream size) with any ints and method Z_DEFLATED: the model run is
      defined for every outcome of the five allocations; on Z_OK the stream is live and J0 holds *)
  cd_init : forall level wbits mem strategy a1 a2 a3 a4 a5,
    rs32 level -> rs32 wbits -> rs32 mem -> rs32 strategy ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 = Some (os, z', code) ->
      code = Z_OK ->
      exists s, os = Some s /\ J0 wbits s (z_total_in z') (z_total_out z') (z_adler z');
  (** capacity = deflateBound_z(strm, n) right after deflateInit2, for any n <= PTRDIFF_MAX; the loop then
      starts from J for any n bytes of data *)
  cd_bound : forall wbits s tin tout adler n,
    J0 wbits s tin tout adler -> 0 <= n <= max_size ->
    exists b, c_deflateBound_z (Some s) n = Some b /\ 0 <= b <= max_u64 /\
      forall data, Zlength data = n -> rbytes data -> J wbits data b 0 [] s tin tout adler;
  (** what J says of the quantities at the head of the loop *)
  cd_range : forall wbits data b pos O s tin tout adler,
    J wbits data b pos O s tin tout adler ->
    0 <= pos <= Zlength data /\ Zlength data <= max_size /\ 0 <= Zlength O <= b /\ b <= max_u64 /\
    rbytes data /\ rbytes O /\ d_gzhead s = None /\
    0 <= tin <= max_u64 /\ 0 <= tout <= max_u64 /\ 0 <= adler <= max_u64;
  (** one iteration of the loop: deflate(strm, dflush rest) offered the object [dpiece data pos] and
      clip(b - |O|) bytes of output space, any msg; the run is defined; the stream moves on as rcall_ok says;
      Z_OK keeps J, Z_STREAM_END comes with all the data consumed and the deflate stream of the data *)
  cd_call : forall wbits data b pos O s tin tout adler msg,
    J wbits data b pos O s tin tout adler ->
    let inb := dpiece data pos in
    let aout := clipz (b - Zlength O) in
    exists s' z' code,
      c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) (dflush (Zlength data - pos)) =
        Some (s', z', code) /\
      rcall_ok inb aout tin tout z' /\ d_gzhead s' = None /\
      (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) /\
      (code = Z_OK ->
         J wbits data b (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s'
           (z_total_in z') (z_total_out z') (z_adler z')) /\
      (code = Z_STREAM_END ->
         z_avail_in z' = 0 /\ pos + Zlength inb = Zlength data /\ dfinal_of wbits data (O ++ z_out z'))
}.

Definition clip_dfacts_stmt : Prop := exists J0 J, clip_dfacts J0 J.
