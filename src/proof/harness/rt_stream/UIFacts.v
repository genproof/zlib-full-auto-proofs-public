(* Law rt_stream: what main's inflate loop needs from the model of inflate.c (data of any length).

   After deflate's Z_STREAM_END the compressed bytes [O] are a finished stream of the data [D]
   (RTFinal.dfinal, no dictionary, no gzip header, deflate's window bits rwbe wbits).  harness/rt_stream.c then
   calls inflateInit2 with the same windowBits (8 changed to 9, as zlib.h asks) and inflate() until
   Z_STREAM_END, each call offered the next piece of [O] (at most 2^32 - 1 bytes: clip()), at most 2^32 - 1
   bytes of output space and any flush (any int).  inflate()'s shared specification (SpecW.inflate_specW) gives
   the call as Spec5.inflate_rel: the model run Model2.run2 from Spec5.m_init.

   [urts_ifacts P]: IFacts.rts_ifacts (round 1: data at most 2^20 bytes, O at most 2^22, output space below
   2^31) for data and streams of any length up to PTRDIFF_MAX and calls of the sizes of the C types.  An invariant
   [P D O pos out s tout] between the calls ([pos] the bytes of [O] consumed, [out] the bytes produced, [s] the
   saved state strm->state, [tout] the field total_out) that holds after inflateInit2 and is kept by every call;
   a call returns Z_OK, Z_BUF_ERROR or Z_STREAM_END (or Z_MEM_ERROR, which ends the run), produces the next bytes
   of [D], and returns Z_STREAM_END only having consumed exactly [O] and produced exactly [D].  [P] is abstract:
   UITheory.v chooses it from the decode theory for calls of any size (Decode7). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTK7.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.inflate.InvW.
Require Export Zlib.proof.harness.rt_stream.IFacts.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Import ListNotations.
Local Open Scope Z_scope.

Record urts_ifacts (P : rts_iinv) : Prop := {
  (** after inflateInit2(strm, rts_iw wbits) for parameters deflateInit2 accepted, on the output of the
      finished deflate run: nothing consumed, nothing produced, total_out 0 *)
  ui_init : forall level mem strategy wbits D O sp,
    rparams_ok level 8 wbits mem strategy = true ->
    dfinal [] (rwrap_of wbits) (rwbe wbits) None D O -> Zlength D <= max_size -> Zlength O <= max_size ->
    swfW (l_s (init_live sp (rts_iw wbits))) /\
    P D O 0 [] (l_s (init_live sp (rts_iw wbits))) 0;
  (** the windowBits main gives inflateInit2 (8 changed to 9) for parameters deflateInit2 accepted are valid:
      inflateInit2 returns Z_OK or Z_MEM_ERROR *)
  ui_wbits : forall level mem strategy wbits,
    rparams_ok level 8 wbits mem strategy = true -> wbits_ok (rts_iw wbits) = true;
  (** one inflate() call offered the next [Zlength inp] <= 2^32 - 1 bytes of [O] and [zf_ao z] <= 2^32 - 1
      bytes of output space, any flush *)
  ui_call : forall D O pos out L z inp flush res,
    P D O pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z -> zf_ao z <= 4294967295 ->
    Zlength inp <= 4294967295 ->
    0 <= pos -> pos + Zlength inp <= Zlength O -> inp = sublist pos (pos + Zlength inp) O ->
    Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    let m := r_m res in
    r_ret res = Z_MEM_ERROR \/
    ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
     0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = zf_ao z /\
     (exists rest, D = out ++ m_ow m ++ rest) /\
     P D O (pos + m_snx m) (out ++ m_ow m) (m_s m) (m_tout m) /\
     (r_ret res = Z_STREAM_END -> out ++ m_ow m = D /\ pos + m_snx m = Zlength O) /\
     (* offered neither input nor output space: not Z_OK, nothing produced, the counters kept *)
     (Zlength inp = 0 -> zf_ao z = 0 ->
        r_ret res <> Z_OK /\ m_ow m = [] /\ m_tin m = zf_tin z /\ m_tout m = zf_tout z))
}.

Definition urts_itheory_stmt : Prop := exists P, urts_ifacts P.
