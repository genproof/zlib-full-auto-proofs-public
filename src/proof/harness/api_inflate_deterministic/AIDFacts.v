(* Law api_inflate_deterministic (harness/api_inflate_deterministic.c): THE interface between its main (VST,
   AIDMain*.v) and the pure theory over the model (AIDTheory.v).  Pure Coq over Spec5's relations (inflate_rel
   over Model2.run2, init_live), for inputs and output spaces of up to 2^32-1 bytes per call.

   The harness: streams `first` and `second` are both made by inflateInit2_(strm, w) with the same w.  Then any
   number of rounds: inflate(&first, flush) and inflate(&second, flush) are offered the same next piece of the
   input src (each a new object of take <= 2^32-1 bytes) and each a new object of aout <= 2^32-1 bytes of output
   space, with the same flush; the harness checks that both calls agree.  pos = the bytes of src consumed so
   far.  Z_MEM_ERROR ends the run.  The theory chooses the invariant J of the two streams at the call
   boundaries (existential: `aid_theory_stmt`) and proves the facts below; the main is proved for ANY J with
   aid_facts J.

   A raw stream's strm->adler is never set by zlib: the harness compares adler only for windowBits >= 0, and the
   main chooses the same model value of adler for both raw streams (SpecW.istreamA ignores it). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.inflate.InvW.
Require Export Zlib.proof.harness.inflate_reset.IRFacts.
Import ListNotations.
Local Open Scope Z_scope.

(* IRFacts.ir_call z ni ai no ao: the stream fields after the harness's set_buffer(strm, ni, ai, no, ao) *)

Record aid_facts (J: Z -> list Z -> Z -> zfields -> live -> zfields -> live -> Prop) : Prop := {
  (* after inflateInit2_(&first, w) and inflateInit2_(&second, w) returned Z_OK (za, zb: the stream fields
     then, which agree on the counters, msg, data_type and the model's adler), at position 0 of the input *)
  df_init : forall w src za zb spa spb,
    wbits_ok w = true -> isptr spa -> isptr spb -> zf_ok za -> zf_ok zb ->
    zf_msg za = None -> zf_msg zb = None -> zf_tin za = 0 -> zf_tin zb = 0 -> zf_tout za = 0 ->
    zf_tout zb = 0 -> zf_dt za = zf_dt zb -> zf_adler za = zf_adler zb ->
    live_ok (init_live spa w) -> live_ok (init_live spb w) -> bytes_ok src ->
    J w src 0 za (init_live spa w) zb (init_live spb w);
  (* a stream made by inflateInit2_ is one that SpecW's inflate_specW accepts *)
  df_init_swf : forall w sp, wbits_ok w = true -> swfW (l_s (init_live sp w));
  (* inflate() sees no gz_header *)
  df_head : forall w src pos za La zb Lb, J w src pos za La zb Lb ->
    i_head (l_s La) = false /\ i_head (l_s Lb) = false;
  (* inflate(&first, flush) then inflate(&second, flush), both offered src[pos .. pos + ain) (each in its own
     object) and aout bytes of space; unless one returns Z_MEM_ERROR: the same code, the same bytes consumed and
     produced (the first aout - avail_out bytes of the output space), the same counters, data_type, msg, and for
     windowBits >= 0 adler *)
  df_inflate : forall w src pos za La zb Lb strma strmb flush iba ibb inp oa ob ain aout
                      ra za' sta' owa rb zb' stb' owb,
    J w src pos za La zb Lb -> live_ok La -> live_ok Lb -> zf_ok za -> zf_ok zb ->
    swfW (l_s La) -> swfW (l_s Lb) -> strma <> nullval -> strmb <> nullval ->
    0 <= pos -> 0 <= ain <= Int.max_unsigned -> pos + ain <= Zlength src -> bytes_ok src ->
    0 <= aout <= Int.max_unsigned -> Int.min_signed <= flush <= Int.max_signed ->
    iba <> InNull -> ibb <> InNull -> inp = sublist pos (pos + ain) src ->
    inflate_rel flush strma (ir_call za (in_ptr iba 0) ain (out_ptr oa 0) aout) (Some La) iba inp (Some oa)
      ra za' sta' owa ->
    ra <> Z_MEM_ERROR ->
    inflate_rel flush strmb (ir_call zb (in_ptr ibb 0) ain (out_ptr ob 0) aout) (Some Lb) ibb inp (Some ob)
      rb zb' stb' owb ->
    rb <> Z_MEM_ERROR ->
    exists La' Lb', sta' = Some La' /\ stb' = Some Lb' /\
      ra = rb /\ zf_ai za' = zf_ai zb' /\ zf_ao za' = zf_ao zb' /\ owa = owb /\
      Zlength owa = aout - zf_ao za' /\
      zf_tin za' = zf_tin zb' /\ zf_tout za' = zf_tout zb' /\ zf_dt za' = zf_dt zb' /\
      zf_msg za' = zf_msg zb' /\ (0 <= w -> zf_adler za' = zf_adler zb') /\
      0 <= zf_ai za' <= ain /\ 0 <= zf_ao za' <= aout /\
      J w src (pos + (ain - zf_ai za')) za' La' zb' Lb'
}.

(* The theory (AIDTheory.v) *)
Definition aid_theory_stmt : Prop := exists J, aid_facts J.
