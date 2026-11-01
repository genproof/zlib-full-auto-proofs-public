(* The decode theory (Decode.v) for calls of any size and inputs of any length.

   Decode.v's theorems take an input of at most 2^31 - 1 bytes in all (dctx_ok) and at most 2^31 - 1 bytes of
   output space per call.  The laws that compress data of any length the allocator provides (rt_partial,
   rj_truncated, rj_bad_checksum, rfc_trailing_bytes) give inflate() a stream of any length, in calls of up
   to UINT_MAX = 2^32 - 1 bytes of input and of output space (laws_common.h's clip()).  [dctx_ok7] is
   dctx_ok with the input's length bounded only by the address space (2^64 - 1);
   [decode_init7_stmt] and [decode_call7_stmt] are Decode.v's statements over dctx_ok7, with calls of up to
   2^32 - 1 bytes of input and of output space.  [inflate_big7_stmt] gathers them with the body of
   inflate() against Spec7.inflate_spec7. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.rfc1951.Decode.
Require Export Zlib.proof.inflate_api.Spec7.
Import ListNotations.
Local Open Scope Z_scope.

Definition dctx_ok7 (G: dctx) : Prop :=
  stream_ok (dc_w G) (dc_wb G) (dc_hist G) (dc_bs G) /\ accepts G /\
  (forall h, dc_w G = WGzip h -> gz_simple h) /\
  (forall wb fl did, dc_w G = WZlib wb fl did ->
     did = None \/ did = Some (Zlib.proof.adler32.Model.ref_adler32 1 (dc_hist G))) /\
  slen G <= Zlength (dc_src G) /\ Zlength (dc_src G) <= 2 ^ 64 - 1 /\ bytes_ok (dc_src G) /\
  sublist 0 (slen G) (dc_src G) = stream_bytes (dc_w G) (dc_hist G) (dc_bs G).

Definition decode_init7_stmt : Prop :=
  forall G sp, dctx_ok7 G -> dc_hist G = [] -> (forall wb fl did, dc_w G = WZlib wb fl did -> did = None) ->
    dinv G 0 [] (l_s (init_live sp (dc_iw G))) 0.

Definition decode_call7_stmt : Prop :=
  forall G pos out L z inp flush res,
    dctx_ok7 G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z ->
    zf_ao z <= 2 ^ 32 - 1 -> Zlength inp <= 2 ^ 32 - 1 ->
    0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) -> inp = sublist pos (pos + Zlength inp) (dc_src G) ->
    run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    let m := r_m res in
    r_ret res = Z_MEM_ERROR \/
    ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
     0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = zf_ao z /\
     (exists rest, full G = out ++ m_ow m ++ rest) /\
     dinv G (pos + m_snx m) (out ++ m_ow m) (m_s m) (m_tout m) /\
     ((forall h, dc_w G <> WGzip h) -> i_wsize (l_s L) <> 0 -> win_ok G (l_s L) out ->
      (r_ret res <> Z_STREAM_END \/ wrapped G = false) ->
      i_wsize (m_s m) <> 0 /\ win_ok G (m_s m) (out ++ m_ow m)) /\
     (r_ret res = Z_STREAM_END -> out ++ m_ow m = full G /\ pos + m_snx m = slen G) /\
     (r_ret res <> Z_STREAM_END ->
        (m_snx m = Zlength inp /\ pos + Zlength inp < slen G) \/
        (Zlength (m_ow m) = zf_ao z /\ Zlength (out ++ m_ow m) < Zlength (full G)) \/
        flush = Z_BLOCK \/ flush = Z_TREES) /\
     exists dt, r_dtype res = Some dt /\ dtype_ok G (out ++ m_ow m) dt).

(* what the laws with calls of any size use of inflate *)
Definition inflate_big7_stmt : Prop := inflate_body7_stmt /\ decode_init7_stmt /\ decode_call7_stmt.
