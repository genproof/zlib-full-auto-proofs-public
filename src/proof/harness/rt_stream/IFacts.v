(* Law rt_stream, round 1's bounded harness: what main's inflate loop needs from the model of
   inflate.c.  UIFacts.v states it for the harness of any length (urts_ifacts).

   After deflate's Z_STREAM_END the compressed bytes [O] are a finished stream of the data [D]
   (RTFinal.dfinal, no dictionary, no gzip header, deflate's window bits rwbe wbits).  harness/rt_stream.c then
   calls inflateInit2 with the same windowBits (8 changed to 9, as zlib.h asks) and inflate() until
   Z_STREAM_END, each call offered the next piece of [O] (any length), any output space and any flush (any int).
   inflate()'s shared specification (SpecW.inflate_specW) gives the call as Spec5.inflate_rel: the model run
   Model2.run2 from Spec5.m_init.

   [rts_ifacts P]: an invariant [P D O pos out s tout] between the calls ([pos] the bytes of [O] consumed, [out]
   the bytes produced, [s] the saved state strm->state, [tout] the field total_out) that holds after
   inflateInit2 and is kept by every call; a call returns Z_OK, Z_BUF_ERROR or Z_STREAM_END (or Z_MEM_ERROR,
   which ends the run), produces the next bytes of [D], and returns Z_STREAM_END only having consumed exactly [O]
   and produced exactly [D].  [P] is abstract (round 1's ITheory.v chose it from the decode theory,
   rfc1951/Decode.v; for any length, UITheory.v does). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTK7.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.inflate.InvW.
Import ListNotations.
Local Open Scope Z_scope.

(* inflateInit2's windowBits in the harness: deflate's windowBits, 8 changed to 9 *)
Definition rts_iw (wbits : Z) : Z := if wbits =? 8 then 9 else wbits.

Definition rts_iinv : Type := list Z -> list Z -> Z -> list Z -> istate -> Z -> Prop.

Record rts_ifacts (P : rts_iinv) : Prop := {
  (** after inflateInit2(strm, rts_iw wbits) for parameters deflateInit2 accepted, on the output of the
      finished deflate run: nothing consumed, nothing produced, total_out 0 *)
  ri_init : forall level mem strategy wbits D O sp,
    rparams_ok level 8 wbits mem strategy = true ->
    dfinal [] (rwrap_of wbits) (rwbe wbits) None D O -> Zlength D <= 1048576 -> Zlength O <= 4194304 ->
    swfW (l_s (init_live sp (rts_iw wbits))) /\
    P D O 0 [] (l_s (init_live sp (rts_iw wbits))) 0;
  (** one inflate() call offered the next [Zlength inp] bytes of [O] and [zf_ao z] bytes of output space, any
      flush *)
  ri_call : forall D O pos out L z inp flush res,
    P D O pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z -> zf_ao z <= 2147483647 ->
    0 <= pos -> pos + Zlength inp <= Zlength O -> inp = sublist pos (pos + Zlength inp) O ->
    Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    let m := r_m res in
    r_ret res = Z_MEM_ERROR \/
    ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
     m_sow m = Zlength (m_ow m) /\ m_aout m = zf_ao z /\
     (exists rest, D = out ++ m_ow m ++ rest) /\
     P D O (pos + m_snx m) (out ++ m_ow m) (m_s m) (m_tout m) /\
     (r_ret res = Z_STREAM_END -> out ++ m_ow m = D /\ pos + m_snx m = Zlength O))
}.

Definition rts_itheory_stmt : Prop := exists P, rts_ifacts P.
