(* Law rt_gzip_header on the round-2 harness: THE interface between the deflate part of main (VST) and the model
   theory of deflate.

   The harness compresses nothing with a gzip header:
     deflateInit2(&c, level, Z_DEFLATED, wbits, mem, strategy)      wbits in 25..31, the others any ints
     deflateSetHeader(&c, &head)                                     head: G2Defs.g2_hdr_ok
     capacity = deflateBound_z(&c, 0)
     c.next_out = compressed;
     do { c.avail_out = clip(capacity - produced); code = deflate(&c, Z_FINISH); } while (code == Z_OK);
     not Z_STREAM_END ends the run
   new_stream() left next_in = Z_NULL and avail_in = 0 (DSpecN.deflate_specN: no input object).

   The theory chooses two invariants (existential, so that main and the theory are independent): [J0 wbits s tin
   tout adler] after deflateInit2 (before the header is set), and [J wbits gh b O s tin tout adler] at the head of
   the loop (gh: the header, b: the capacity, O: the bytes produced so far; s and tin, tout, adler: the state and
   the z_stream's fields).  The facts give what the specifications of deflateInit2_ (DSpec9), deflateSetHeader,
   deflateBound_z (DSpec) and deflate (DSpecN) need (the model runs are defined) and what main needs of the
   outcome; at Z_STREAM_END the output is the gzip stream of no data with the header gh ([RTFinal.dfinal]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7.
Require Export Zlib.proof.harness.rt_gzip_header.G2Defs.
Import ListNotations.
Local Open Scope Z_scope.

(* the stream deflateInit2_'s model runs on (DSpec9.zrst0: the fields it neither reads nor keeps) *)
Definition dz0 : strm := rzcall [] 0 0 0 0 0 0 None.

Record g2_dfacts (J0 : Z -> dstate -> Z -> Z -> Z -> Prop)
                 (J : Z -> DS7.gzh -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop) : Prop := {
  (** deflateInit2 (right version and stream size) with windowBits 25..31, method Z_DEFLATED and any other ints:
      the model run is defined for every outcome of the five allocations; on Z_OK the stream is live and J0 holds *)
  gd_init : forall level wbits mem strategy a1 a2 a3 a4 a5,
    rs32 level -> 25 <= wbits <= 31 -> rs32 mem -> rs32 strategy ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 = Some (os, z', code) ->
      code = Z_OK ->
      exists s, os = Some s /\ J0 wbits s (z_total_in z') (z_total_out z') (z_adler z');
  (** deflateSetHeader right after deflateInit2 sets the header and returns Z_OK *)
  gd_head : forall wbits s tin tout adler gh z,
    J0 wbits s tin tout adler -> g2_hdr_ok gh ->
    c_deflateSetHeader s z (Some gh) = Some (set_d_gzhead s (Some gh), z, Z_OK);
  (** capacity = deflateBound_z(strm, 0) after deflateSetHeader; the loop then starts from J *)
  gd_bound : forall wbits s tin tout adler gh,
    J0 wbits s tin tout adler -> g2_hdr_ok gh ->
    exists b, c_deflateBound_z (Some (set_d_gzhead s (Some gh))) 0 = Some b /\ 0 <= b <= max_u64 /\
      J wbits gh b [] (set_d_gzhead s (Some gh)) tin tout adler;
  (** what J says of the quantities at the head of the loop *)
  gd_range : forall wbits gh b O s tin tout adler,
    J wbits gh b O s tin tout adler ->
    25 <= wbits <= 31 /\ g2_hdr_ok gh /\ 0 <= Zlength O <= b /\ b <= max_u64 /\ rbytes O /\
    d_gzhead s = Some gh /\ 0 <= tin <= max_u64 /\ 0 <= tout <= max_u64 /\ 0 <= adler <= max_u64;
  (** one iteration of the loop: deflate(strm, Z_FINISH) with no input and clip(b - |O|) bytes of output space,
      any msg; the run is defined; the stream moves on as rcall_ok says; Z_OK keeps J, Z_STREAM_END comes with
      the gzip stream of no data with the header gh *)
  gd_call : forall wbits gh b O s tin tout adler msg,
    J wbits gh b O s tin tout adler ->
    let aout := clipz (b - Zlength O) in
    exists s' z' code,
      c_deflate s (rzcall [] 0 0 tin aout tout adler msg) Z_FINISH = Some (s', z', code) /\
      rcall_ok [] aout tin tout z' /\ d_gzhead s' = Some gh /\
      (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) /\
      (code = Z_OK ->
         J wbits gh b (O ++ z_out z') s' (z_total_in z') (z_total_out z') (z_adler z')) /\
      (code = Z_STREAM_END -> dfinal [] 2 (rwbe wbits) (Some gh) [] (O ++ z_out z'))
}.

Definition g2_dfacts_stmt : Prop := exists J0 J, g2_dfacts J0 J.
