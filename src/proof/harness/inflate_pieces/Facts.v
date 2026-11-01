(* The laws rj_any_input, api_counters and api_untouched_output (harness/rj_any_input.c, api_counters.c,
   api_untouched_output.c): THE interface between their mains (VST) and the pure theory over the model.

   The three mains are the same loop: after inflateInit2_ returned Z_OK, any number of inflate() calls, each
   offered a new object holding the next piece of the input and a new object of any size as output space,
   with any flush; between calls inflateSetDictionary of any bytes, or not.  Z_MEM_ERROR ends the run.

   The theory chooses an invariant P z L of the stream at the call boundaries (z: the application's fields,
   L: the live part; existential, so that the mains and the theory are independent) and proves the facts
   below; each main is proved for ANY P with pieces_facts P.  Everything is stated over Spec5's relations
   (inflate_rel over Model2.run2, setdict_f, init_live), for inputs and output spaces of up to 2^32-1 bytes. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.inflate.InvW.
Import ListNotations.
Local Open Scope Z_scope.

(* the return codes zlib.h documents for inflate() on a valid stream with valid buffers, but Z_MEM_ERROR *)
Definition code_doc (r: Z) : Prop :=
  r = Z_OK \/ r = Z_STREAM_END \/ r = Z_NEED_DICT \/ r = Z_DATA_ERROR \/ r = Z_BUF_ERROR.

(* the stream fields after the harness's offer(strm, in, ai, out, ao) *)
Definition offer_z (z: zfields) (ni: val) (ai: Z) (no: val) (ao: Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

(* the wrapper of the stream (0: raw; strm->adler is then never written) *)
Definition wrap_of (L: live) : Z := i_wrap (l_s L).

Record pieces_facts (P: zfields -> live -> Prop) : Prop := {
  (* after inflateInit2_(strm, w) returned Z_OK (z: the stream fields then) *)
  pf_init : forall w z sp,
    wbits_ok w = true -> isptr sp -> zf_ok z -> zf_msg z = None -> zf_tin z = 0 -> zf_tout z = 0 ->
    live_ok (init_live sp w) -> P z (init_live sp w);
  (* inflate() and inflateSetDictionary see no gz_header *)
  pf_head : forall z L, P z L -> i_head (l_s L) = false;
  (* the live state is one SpecW's inflate_specW accepts (the extra field's length, the bit buffer) *)
  pf_swf : forall z L, P z L -> swfW (l_s L);
  (* inflateSetDictionary(strm, dict, |dict|) that did not run out of memory *)
  pf_setdict : forall z L dict alloc_ok winp,
    P z L -> live_ok L -> zf_ok z -> bytes_ok dict -> Zlength dict <= Int.max_unsigned ->
    fst3 (setdict_f dict alloc_ok winp z L) <> Z_MEM_ERROR ->
    snd3 (setdict_f dict alloc_ok winp z L) = z /\ P z (thd3 (setdict_f dict alloc_ok winp z L)) /\
    wrap_of (thd3 (setdict_f dict alloc_ok winp z L)) = wrap_of L;
  (* inflate(strm, flush) offered the bytes inp (an object) and aout bytes of output space (an object) that
     did not run out of memory: a documented code, the stream still live, the pointers and counters moved on
     by exactly the bytes consumed and produced, the bytes written are the first ones of the space *)
  pf_inflate : forall z L strmp flush ib inp o aout r z' st' ow,
    P z L -> live_ok L -> zf_ok z -> strmp <> nullval -> Int.min_signed <= flush <= Int.max_signed ->
    ib <> InNull -> in_ok ib inp -> out_ok o aout ->
    Zlength inp <= Int.max_unsigned -> aout <= Int.max_unsigned ->
    inflate_rel flush strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) (Some L) ib inp (Some o)
      r z' st' ow ->
    r <> Z_MEM_ERROR ->
    exists L', st' = Some L' /\ P z' L' /\ wrap_of L' = wrap_of L /\ code_doc r /\
      0 <= zf_ai z' <= Zlength inp /\ 0 <= zf_ao z' <= aout /\
      zf_ni z' = in_ptr ib (Zlength inp - zf_ai z') /\ zf_no z' = out_ptr o (aout - zf_ao z') /\
      zf_tin z' = (zf_tin z + (Zlength inp - zf_ai z')) mod 2 ^ 64 /\
      zf_tout z' = (zf_tout z + (aout - zf_ao z')) mod 2 ^ 64 /\
      Zlength ow = aout - zf_ao z'
}.
