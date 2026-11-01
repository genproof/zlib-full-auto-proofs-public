(* Law rt_stream_trailing: what main's inflate loop needs from the model of inflate.c.

   After deflate's Z_STREAM_END the compressed bytes [O] are a finished stream of the data [D]
   (RTFinal.dfinal, no dictionary, no gzip header, deflate's window bits rwbe wbits).
   harness/rt_stream_trailing.c then copies O to the start of an object [src] of |O| + after bytes (the bytes after
   O are any bytes: alloc_any_bytes), calls inflateInit2 with the same windowBits (8 changed to 9) and inflate()
   until Z_STREAM_END, each call offered the next piece of [src] (at most 2^32 - 1 bytes: clip()), at most
   2^32 - 1 bytes of output space and any flush.  inflate()'s shared specification (SpecW.inflate_specW) gives
   the call as Spec5.inflate_rel: the model run Model2.run2 from Spec5.m_init.

   [trl_ifacts P]: rt_stream's UIFacts.urts_ifacts with the input [src] = O followed by any bytes: an invariant
   [P D O src pos out s tout] between the calls ([pos] the bytes of [src] consumed, [out] the bytes produced,
   [s] the saved state strm->state, [tout] the field total_out) that holds after inflateInit2 and is kept by
   every call; a call returns Z_OK, Z_BUF_ERROR or Z_STREAM_END (or Z_MEM_ERROR, which ends the run), produces
   the next bytes of [D], and returns Z_STREAM_END only having consumed exactly [O] (none of the bytes after it)
   and produced exactly [D]; offered neither input nor output space it does not return Z_OK and moves nothing.
   [P] is abstract: TITheory.v chooses it from the decode theory for calls of any size (Decode7), whose context
   has the input src and the stream's length |O|. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTK7.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.inflate.InvW.
Require Export Zlib.proof.harness.rt_stream.IFacts.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Zlib.proof.zutil.Libc.
Import ListNotations.
Local Open Scope Z_scope.

Definition trl_iinv : Type := list Z -> list Z -> list Z -> Z -> list Z -> istate -> Z -> Prop.

Record trl_ifacts (P : trl_iinv) : Prop := {
  (** after inflateInit2(strm, rts_iw wbits) for parameters deflateInit2 accepted, on the output O of the
      finished deflate run at the start of the input src: nothing consumed, nothing produced, total_out 0 *)
  ti_init : forall level mem strategy wbits D O src sp,
    rparams_ok level 8 wbits mem strategy = true ->
    dfinal [] (rwrap_of wbits) (rwbe wbits) None D O -> Zlength D <= max_size ->
    Zlength O <= Zlength src <= max_size -> sublist 0 (Zlength O) src = O ->
    Zlib.proof.zutil.Libc.bytes_ok src ->
    swfW (l_s (init_live sp (rts_iw wbits))) /\
    P D O src 0 [] (l_s (init_live sp (rts_iw wbits))) 0;
  (** the windowBits main gives inflateInit2 (8 changed to 9) for parameters deflateInit2 accepted are valid:
      inflateInit2 returns Z_OK or Z_MEM_ERROR *)
  ti_wbits : forall level mem strategy wbits,
    rparams_ok level 8 wbits mem strategy = true -> wbits_ok (rts_iw wbits) = true;
  (** one inflate() call offered the next [Zlength inp] <= 2^32 - 1 bytes of [src] and [zf_ao z] <= 2^32 - 1
      bytes of output space, any flush *)
  ti_call : forall D O src pos out L z inp flush res,
    P D O src pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z -> zf_ao z <= 4294967295 ->
    Zlength inp <= 4294967295 ->
    0 <= pos -> pos + Zlength inp <= Zlength src -> inp = sublist pos (pos + Zlength inp) src ->
    Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    let m := r_m res in
    r_ret res = Z_MEM_ERROR \/
    ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
     0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = zf_ao z /\
     (exists rest, D = out ++ m_ow m ++ rest) /\
     P D O src (pos + m_snx m) (out ++ m_ow m) (m_s m) (m_tout m) /\
     (r_ret res = Z_STREAM_END -> out ++ m_ow m = D /\ pos + m_snx m = Zlength O) /\
     (* offered neither input nor output space: not Z_OK, nothing produced, the counters kept *)
     (Zlength inp = 0 -> zf_ao z = 0 ->
        r_ret res <> Z_OK /\ m_ow m = [] /\ m_tin m = zf_tin z /\ m_tout m = zf_tout z))
}.

Definition trl_itheory_stmt : Prop := exists P, trl_ifacts P.
