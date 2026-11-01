(* Law api_reset (harness/api_reset.c): THE interface between its main (VST, ARMain*.v) and the pure theory over
   the model (ARTheory*.v, ARSim*.v, ARRun*.v).  Pure Coq over Spec5's relations (inflate_rel over Model2.run2,
   reset_f, init_live), for inputs and output spaces of up to 2^32-1 bytes per call.

   The harness: stream `used` is made by inflateInit2_(&used, w).  Phase 0: any number of inflate() calls on
   used, each offered the next piece of an input src (a new object of take <= 2^32-1 bytes) and a new object of
   aout <= 2^32-1 bytes of output space, with any flush; pos = the bytes of src consumed so far.  Then
   inflateReset(&used), which must return Z_OK, and inflateInit2_(&fresh, w).  Phase 1: a new input src; every
   inflate() call on used is followed by the same call on fresh (the same bytes, each in its own object, the
   same flush and amount of output space), and the harness checks that both calls agree.  Z_MEM_ERROR ends the
   run.  The theory chooses the invariants J0 (phase 0, stream used) and J1 (phase 1, used and fresh)
   (existential: `ar_theory_stmt`) and proves the facts below; the main is proved for ANY J0, J1 with
   ar_facts J0 J1.

   A raw stream's strm->adler is never written by zlib: the harness compares adler only for windowBits >= 0,
   and the main may choose the model value of fresh's adler on a raw stream (SpecW.istreamA ignores it): it
   chooses used's (af_reset). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.inflate.InvW.
Require Export Zlib.proof.harness.inflate_reset.IRFacts.
Import ListNotations.
Local Open Scope Z_scope.

(* IRFacts.ir_call z ni ai no ao: the stream fields after the harness's offer(strm, ni, ai, no, ao) *)

Record ar_facts (J0: Z -> list Z -> Z -> zfields -> live -> Prop)
                (J1: Z -> list Z -> Z -> zfields -> live -> zfields -> live -> Prop) : Prop := {
  (* after inflateInit2_(&used, w) returned Z_OK (z: the stream fields then), for the input of phase 0 *)
  af_init : forall w src z sp,
    wbits_ok w = true -> isptr sp -> zf_ok z -> zf_msg z = None -> zf_tin z = 0 -> zf_tout z = 0 ->
    zf_dt z = 0 -> live_ok (init_live sp w) -> Int.min_signed <= w <= Int.max_signed -> bytes_ok src ->
    J0 w src 0 z (init_live sp w);
  (* a stream made by inflateInit2_ is one that SpecW's inflate_specW accepts *)
  af_init_swf : forall w sp, wbits_ok w = true -> swfW (l_s (init_live sp w));
  (* inflate() sees no gz_header *)
  af_head0 : forall w src pos z L, J0 w src pos z L -> i_head (l_s L) = false;
  af_head1 : forall w src pos za La zb Lb, J1 w src pos za La zb Lb ->
    i_head (l_s La) = false /\ i_head (l_s Lb) = false;
  (* phase 0: inflate(&used, flush) offered src[pos .. pos + ain) and aout bytes of space; unless it returns
     Z_MEM_ERROR (the harness then returns) *)
  af_inflate0 : forall w src pos z L strmp flush ib inp o ain aout r z' st' ow,
    J0 w src pos z L -> live_ok L -> zf_ok z -> swfW (l_s L) -> strmp <> nullval ->
    0 <= pos -> 0 <= ain <= Int.max_unsigned -> pos + ain <= Zlength src -> bytes_ok src ->
    0 <= aout <= Int.max_unsigned -> Int.min_signed <= flush <= Int.max_signed ->
    ib <> InNull -> inp = sublist pos (pos + ain) src ->
    inflate_rel flush strmp (ir_call z (in_ptr ib 0) ain (out_ptr o 0) aout) (Some L) ib inp (Some o) r z' st' ow ->
    r <> Z_MEM_ERROR ->
    exists L', st' = Some L' /\ 0 <= zf_ai z' <= ain /\ 0 <= zf_ao z' <= aout /\
      J0 w src (pos + (ain - zf_ai z')) z' L';
  (* inflateReset(&used): it returns Z_OK, the reset stream is live and one that inflate_specW accepts, and with
     fresh just made by inflateInit2_(&fresh, w) (fresh's fields: totals 0, msg NULL, data_type 0; adler: for
     windowBits >= 0 the value inflateInit2_ sets, for a raw stream the model value used has) the phase-1
     invariant holds at pos = 0 of any input of phase 1 *)
  af_reset : forall w src pos za La,
    J0 w src pos za La -> live_ok La -> zf_ok za ->
    fst3 (reset_f za La) = Z_OK /\ live_ok (thd3 (reset_f za La)) /\ swfW (l_s (thd3 (reset_f za La))) /\
    forall src' zb sp,
      isptr sp -> live_ok (init_live sp w) -> zf_ok zb -> zf_tin zb = 0 -> zf_tout zb = 0 ->
      zf_msg zb = None -> zf_dt zb = 0 ->
      (w < 0 -> zf_adler zb = zf_adler (snd3 (reset_f za La))) ->
      (0 <= w -> zf_adler zb = Z.land (i_wrap (l_s (init_live sp w))) 1) ->
      bytes_ok src' ->
      J1 w src' 0 (snd3 (reset_f za La)) (thd3 (reset_f za La)) zb (init_live sp w);
  (* phase 1: inflate(&used, flush) then inflate(&fresh, flush), both offered src[pos .. pos + ain) (each in its
     own object) and aout bytes of space; unless one returns Z_MEM_ERROR: the same code, the same bytes
     consumed and produced (the first aout - avail_out bytes of the output space), the same counters,
     data_type, msg, and for windowBits >= 0 adler *)
  af_inflate1 : forall w src pos za La zb Lb strma strmb flush iba ibb inp oa ob ain aout
                       ra za' sta' owa rb zb' stb' owb,
    J1 w src pos za La zb Lb -> live_ok La -> live_ok Lb -> zf_ok za -> zf_ok zb ->
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
      J1 w src (pos + (ain - zf_ai za')) za' La' zb' Lb'
}.

(* The theory (ARTheory.v) *)
Definition ar_theory_stmt : Prop := exists J0 J1, ar_facts J0 J1.
