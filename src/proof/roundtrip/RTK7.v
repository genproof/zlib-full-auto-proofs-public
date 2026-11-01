(* The deflate side of the round trips without the size limits of deflate_roundtrip.

   RTDIface.kfacts (proved by RTDTheory.rt_kfacts) is stated for deflate_roundtrip's quantities: at most 2^20
   bytes of data, 2^21 bytes of output space per call, 2^22 bytes of output in all, a dictionary of at most
   2^15 bytes, gzip header fields of at most 2^12 bytes with text and hcrc 0/1 and os a byte.  The short
   round-trip laws go beyond them: rt_stream (up to 2^22 bytes of output space in one call), rt_dictionary and
   api_dict_id (a dictionary of up to 2^20 bytes), rt_gzip_header (an extra field of up to 65535 bytes, a name
   and a comment of up to 2^20 bytes, text, hcrc and os any ints), rt_partial, rj_truncated, rj_bad_checksum
   and rfc_trailing_bytes (data of any length the allocator provides, in calls of up to 2^32 - 1 bytes of
   input and of output space).

   [kfacts7 K] is kfacts for these: the same invariant shape (RTDIface.rinv) and conclusions, for deflateInit2,
   deflateSetDictionary, deflateSetHeader and deflate(), with only the limits of the C types and of the
   address space (each call's input object and output space at most 2^32 - 1 bytes, the data and the output
   at most 2^64 - 1 bytes in all, the dictionary at most 2^32 - 1 bytes). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDIface.
Import ListNotations.
Local Open Scope Z_scope.

Module DS7 := Zlib.proof.deflate.DState.

(* the gzip headers the short laws give to deflateSetHeader: text, hcrc, os any ints, time 32 bits, the extra
   field the whole object of extra_len <= 65535 bytes, the name and the comment whole objects of at most 2^32-2
   non-zero bytes followed by their zero byte *)
Definition rcstr_ok7 (o : option (list Z)) : Prop :=
  forall l, o = Some l -> exists l0, l = l0 ++ [0] /\ Zlength l0 <= 4294967294 /\ Forall (fun b => 0 < b < 256) l0.
Definition rhdr_ok7 (h : DS7.gzh) : Prop :=
  rs32 (DS7.gz_text h) /\ rs32 (DS7.gz_hcrc h) /\ rs32 (DS7.gz_os h) /\
  0 <= DS7.gz_time h <= 4294967295 /\ 0 <= DS7.gz_extra_len h <= 65535 /\
  (forall x, DS7.gz_extra h = Some x -> Zlength x = DS7.gz_extra_len h /\ Forall (fun b => 0 <= b < 256) x) /\
  rcstr_ok7 (DS7.gz_name h) /\ rcstr_ok7 (DS7.gz_comment h).

Record kfacts7 (K : rinv) : Prop := {
  (** deflateInit2 (right version and stream size) accepted the parameters *)
  kf7_init : forall level method wbits mem strategy a1 a2 a3 a4 a5 z s z',
    rs32 level -> rs32 method -> rs32 wbits -> rs32 mem -> rs32 strategy ->
    c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (Some s, z', Z_OK) ->
    d_w_bits s = rwbe wbits /\ d_gzhead s = None /\
    K [] (rwrap_of wbits) [] [] None s (z_total_in z') (z_total_out z') (z_adler z');
  (** deflateSetDictionary right after deflateInit2; Z_STREAM_ERROR exactly for gzip *)
  kf7_dict : forall wrap s tin tout adler d ain aout msg s' z' code,
    K [] wrap [] [] None s tin tout adler -> rbytes d -> Zlength d <= 4294967295 ->
    0 <= ain <= 4294967295 -> 0 <= aout <= 4294967295 ->
    c_deflateSetDictionary s (rzcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', code) ->
    (code = Z_OK \/ code = Z_STREAM_ERROR) -> (code = Z_STREAM_ERROR <-> wrap = 2) ->
    d_w_bits s' = d_w_bits s /\ d_gzhead s' = d_gzhead s /\
    K (if wrap =? 2 then [] else d) wrap [] [] None s' (z_total_in z') (z_total_out z') (z_adler z');
  (** deflateSetHeader on a gzip stream, before any deflate() call *)
  kf7_head : forall dict s tin tout adler h,
    K dict 2 [] [] None s tin tout adler -> rhdr_ok7 h ->
    K dict 2 [] [] None (set_d_gzhead s (Some h)) tin tout adler;
  (** deflate(strm, flush): any flush of zlib.h, any input object and output space; once Z_FINISH was given,
      only Z_FINISH with the rest of the input *)
  kf7_deflate : forall dict wrap D O fin s tin tout adler inb aout flush msg s' z' code,
    K dict wrap D O fin s tin tout adler ->
    0 <= flush <= 5 -> rbytes inb -> Zlength inb <= 4294967295 -> Zlength D + Zlength inb <= 2 ^ 64 - 1 ->
    0 <= aout <= 4294967295 -> Zlength O + aout <= 2 ^ 64 - 1 ->
    (forall R, fin = Some R -> flush = Z_FINISH /\ inb = R) ->
    c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) ->
    d_gzhead s' = d_gzhead s -> rcall_ok inb aout tin tout z' ->
    (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) ->
    (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) ->
    (code = Z_BUF_ERROR -> z_avail_in z' = Zlength inb /\ z_avail_out z' = aout) ->
    d_w_bits s' = d_w_bits s /\
    (let used := Zlength inb - z_avail_in z' in
     let D' := D ++ sublist 0 used inb in
     let O' := O ++ z_out z' in
     if code =? Z_STREAM_END then dfinal dict wrap (d_w_bits s) (d_gzhead s) D' O'
     else K dict wrap D' O' (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
            s' (z_total_in z') (z_total_out z') (z_adler z'))
}.

Definition rt_k7_stmt : Prop := exists K, kfacts7 K.
