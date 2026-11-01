(* The round-trip laws: compress.c's compress2_z over the model, v2: as
   RTDIface's c2_loop / c2_rel / c2_fact, with what the body proof needs between the loop's deflate calls: each
   call keeps the gzip header (none: d_gzhead s = None after deflateInit2) and moves the counters as [c2_step]
   says (the deflate laws' call_ok).  [c2_res] is compress2_z's result (RTCSpec.v), [c2_ok] what
   compress_roundtrip needs (RTCTheory.rt_c2_fact). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDIface.
Import ListNotations.
Local Open Scope Z_scope.

(* what one deflate call of the loop did to the counters it was offered (the deflate laws' call_ok, which the
   loop needs between calls: next_in / avail_in and the output space stay consistent) *)
Definition c2_step (z1 z' : strm) : Prop :=
  0 <= z_avail_in z' <= z_avail_in z1 /\ z_next_in z' = z_next_in z1 + (z_avail_in z1 - z_avail_in z') /\
  0 <= z_avail_out z' <= z_avail_out z1 /\ Zlength (z_out z') = z_avail_out z1 - z_avail_out z'.

(* the loop: [do { ... err = deflate(&stream, ...); } while (err == Z_OK);] from the state s and stream z with
   the output out so far; ends with err, the output, the state and stream for deflateEnd; each call keeps the
   gzip header (none) and moves the counters as c2_step says *)
Inductive c2_run (src : list Z) : dstate -> strm -> Z -> Z -> list Z -> Z -> list Z -> dstate -> strm -> Prop :=
| c2r_more : forall s z left srcleft out z1 left' srcleft' flush s' z' err out' sf zf,
    c2_give src z left srcleft = (z1, left', srcleft', flush) ->
    c_deflate s z1 flush = Some (s', z', Z_OK) -> d_gzhead s' = d_gzhead s -> c2_step z1 z' ->
    c2_run src s' z' left' srcleft' (out ++ z_out z') err out' sf zf ->
    c2_run src s z left srcleft out err out' sf zf
| c2r_last : forall s z left srcleft out z1 left' srcleft' flush s' z' err,
    c2_give src z left srcleft = (z1, left', srcleft', flush) ->
    c_deflate s z1 flush = Some (s', z', err) -> d_gzhead s' = d_gzhead s -> c2_step z1 z' -> err <> Z_OK ->
    c2_run src s z left srcleft out err (out ++ z_out z') s' z'.

(* compress2_z with destLen = cap, the allocation outcomes a1..a5 of deflateInit2_ and the stream z0 deflateInit
   sees: return value r and the bytes out written at dest ( *destLen = |out| ) *)
Definition c2_res (src : list Z) (cap level : Z) (a1 a2 a3 a4 a5 : bool) (z0 : strm) (r : Z) (out : list Z) : Prop :=
  exists os z1 code,
    c_deflateInit2_ true true false level 8 15 8 0 a1 a2 a3 a4 a5 z0 = Some (os, z1, code) /\
    ((code <> Z_OK /\ r = code /\ out = []) \/
     (code = Z_OK /\ exists s err sf zf,
        os = Some s /\ d_gzhead s = None /\
        c2_run src s (mkST src 0 0 (z_total_in z1) [] 0 (z_total_out z1) (z_adler z1) (z_msg z1)) cap
          (Zlength src) [] err out sf zf /\
        r = (if err =? Z_STREAM_END then Z_OK else err))).

(* what compress_roundtrip needs: for n <= 2^20 bytes and destLen = compressBound(n), compress2_z succeeds
   (the model runs are defined) and returns Z_STREAM_ERROR exactly for a level not in -1..9, else Z_OK or
   Z_MEM_ERROR; the output fits and, on Z_OK, is the zlib stream of the data *)
Definition c2_ok : Prop :=
  forall src level a1 a2 a3 a4 a5 z0,
    rbytes src -> Zlength src <= 1048576 -> rs32 level ->
    (exists r out, c2_res src (c_compressBound (Zlength src)) level a1 a2 a3 a4 a5 z0 r out) /\
    forall r out, c2_res src (c_compressBound (Zlength src)) level a1 a2 a3 a4 a5 z0 r out ->
      (r = Z_OK \/ r = Z_STREAM_ERROR \/ r = Z_MEM_ERROR) /\
      (r = Z_STREAM_ERROR <-> ~ (-1 <= level <= 9)) /\
      Zlength out <= c_compressBound (Zlength src) /\
      (r = Z_OK -> dfinal [] 1 15 None src out).
