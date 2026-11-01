(* The laws rt_partial, rj_truncated, rj_bad_checksum and rfc_trailing_bytes: THE interface between the inflate
   part of their mains (VST) and the decode theory.

   After the deflate loop (DFacts.v) ended with Z_STREAM_END, the n bytes D of data were compressed into the bytes
   O ([DFacts.dfinal_of wbits D O]).  The harness then sets up a new stream with new_stream() and
   inflateInit2(windowBits) (8 is given as 9: [iwb]), and calls inflate() in a loop on an input object holding
   the bytes [src], each call offered the next clip()-sized piece of src (inp = src[pos .. pos + |inp|)), the
   next clip(n - written) bytes of the output object of n bytes, and any flush:
   - rt_partial, rj_truncated: src = O, the calls read at most a proper prefix of O ([pfx_facts]): no call
     returns Z_STREAM_END and the bytes written are always the first bytes of D;
   - rfc_trailing_bytes: src = O followed by any bytes ([trl_facts]): Z_STREAM_END comes with exactly the bytes
     of O consumed;
   - rj_bad_checksum: a zlib or gzip stream (windowBits >= 8), src = O with its trailer (the last 4 bytes for
     zlib, 8 for gzip: [trl_of]) changed ([bad_facts]): every call returns Z_OK, Z_BUF_ERROR or Z_DATA_ERROR.
   Z_MEM_ERROR ends every run.  In each case the theory chooses an invariant [P wbits D O src pos out z L] of
   the call boundaries (pos: the bytes of src consumed, out: the bytes written, z / L: the application's fields
   and the live part of the stream), existential so that the mains and the theory are independent.  Everything
   is over Spec5's relations (inflate_rel over Model2.run2, init_live), the same for Spec7's and SpecW's inflate
   specifications. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.harness.clip_streams.DFacts.
Import ListNotations.
Local Open Scope Z_scope.

Definition umax : Z := 4294967295.
Definition clipz (n : Z) : Z := Z.min n umax.

(* inflateInit2's windowBits in the harnesses (zlib.h: "a request for 8 will result in 9") *)
Definition iwb (wbits : Z) : Z := if wbits =? 8 then 9 else wbits.

(* the trailer's length of the stream deflateInit2(windowBits) writes, windowBits >= 8 (harness/rj_bad_checksum.c) *)
Definition trl_of (wbits : Z) : Z := if wbits >? 15 then 8 else 4.

Definition dfinal_of (wbits : Z) (D O : list Z) : Prop := Zlib.proof.harness.clip_streams.DFacts.dfinal_of wbits D O.

(* the stream fields the harness sets before a call: next_in, avail_in, next_out, avail_out *)
Definition offer_z (z: zfields) (ni: val) (ai: Z) (no: val) (ao: Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

(* the stream after inflateInit2_ returned Z_OK: what the mains know of it *)
Definition init_ok (w: Z) (z: zfields) (sp: val) : Prop :=
  wbits_ok w = true /\ isptr sp /\ zf_ok z /\ zf_msg z = None /\ zf_tin z = 0 /\ zf_tout z = 0 /\
  live_ok (init_live sp w).

(* a call of the loop: offered inp = src[pos .. pos + |inp|) (an object) and aout bytes of output space (an
   object), from a live stream with the fields z *)
Definition call_pre (src: list Z) (pos: Z) (z: zfields) (L: live) (strmp: val) (flush: Z) (ib: inbuf)
    (inp: list Z) (o: outbuf) (aout: Z) : Prop :=
  live_ok L /\ zf_ok z /\ strmp <> nullval /\ Int.min_signed <= flush <= Int.max_signed /\
  ib <> InNull /\ in_ok ib inp /\ out_ok o aout /\
  Zlength inp <= umax /\ aout <= umax /\ inp = sublist pos (pos + Zlength inp) src.

(* the outcome of a call that did not run out of memory, besides the code: the stream still live, the pointers
   moved on by exactly the bytes consumed and produced, the bytes written *)
Definition call_post (ib: inbuf) (inp: list Z) (o: outbuf) (aout: Z) (z': zfields) (st': option live)
    (ow: list Z) (L': live) : Prop :=
  st' = Some L' /\ 0 <= zf_ai z' <= Zlength inp /\ 0 <= zf_ao z' <= aout /\
  zf_ni z' = in_ptr ib (Zlength inp - zf_ai z') /\ zf_no z' = out_ptr o (aout - zf_ao z') /\
  Zlength ow = aout - zf_ao z'.

Definition inv_t : Type := Z -> list Z -> list Z -> list Z -> Z -> list Z -> zfields -> live -> Prop.

(* what every invariant says: no gz_header, the position in src, the output a prefix of D *)
Definition inv_ok (P: inv_t) : Prop :=
  forall wbits D O src pos out z L, P wbits D O src pos out z L ->
    i_head (l_s L) = false /\ 0 <= pos <= Zlength src /\ exists rest, D = out ++ rest.

(** rt_partial, rj_truncated: the input is O; the calls read at most [lim] < |O| bytes *)
Record pfx_facts (P: inv_t) : Prop := {
  px_ok : inv_ok P;
  px_len : forall wbits D O, dfinal_of wbits D O -> 1 <= Zlength O;
  px_init : forall wbits D O z sp,
    dfinal_of wbits D O -> Zlength O <= 2 ^ 64 - 1 -> Int.min_signed <= wbits <= Int.max_signed ->
    init_ok (iwb wbits) z sp ->
    P wbits D O O 0 [] z (init_live sp (iwb wbits));
  px_call : forall wbits D O pos out z L strmp flush ib inp o aout lim r z' st' ow,
    P wbits D O O pos out z L -> call_pre O pos z L strmp flush ib inp o aout ->
    pos + Zlength inp <= lim -> lim < Zlength O ->
    inflate_rel flush strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) (Some L) ib inp (Some o)
      r z' st' ow ->
    r <> Z_MEM_ERROR -> zf_ok z' ->
    exists L', call_post ib inp o aout z' st' ow L' /\ r <> Z_STREAM_END /\
      P wbits D O O (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L'
}.

(** rfc_trailing_bytes: the input is O followed by any bytes *)
Record trl_facts (P: inv_t) : Prop := {
  tr_ok : inv_ok P;
  tr_init : forall wbits D O src z sp,
    dfinal_of wbits D O -> Zlength O <= 2 ^ 64 - 1 -> Int.min_signed <= wbits <= Int.max_signed ->
    init_ok (iwb wbits) z sp ->
    Zlength O <= Zlength src <= DFacts.max_size -> sublist 0 (Zlength O) src = O -> bytes_ok src ->
    P wbits D O src 0 [] z (init_live sp (iwb wbits));
  tr_call : forall wbits D O src pos out z L strmp flush ib inp o aout r z' st' ow,
    P wbits D O src pos out z L -> call_pre src pos z L strmp flush ib inp o aout ->
    pos + Zlength inp <= Zlength src ->
    inflate_rel flush strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) (Some L) ib inp (Some o)
      r z' st' ow ->
    r <> Z_MEM_ERROR -> zf_ok z' ->
    exists L', call_post ib inp o aout z' st' ow L' /\
      (r = Z_STREAM_END -> pos + (Zlength inp - zf_ai z') = Zlength O) /\
      (r <> Z_STREAM_END -> P wbits D O src (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L')
}.

(** rj_bad_checksum: a zlib or gzip stream whose trailer was changed (and nothing else) *)
Record bad_facts (P: inv_t) : Prop := {
  bd_ok : inv_ok P;
  bd_len : forall wbits D O, dfinal_of wbits D O -> 8 <= wbits -> trl_of wbits <= Zlength O;
  bd_init : forall wbits D O src z sp,
    dfinal_of wbits D O -> Zlength O <= 2 ^ 64 - 1 -> Int.min_signed <= wbits <= Int.max_signed ->
    8 <= wbits -> init_ok (iwb wbits) z sp ->
    Zlength src = Zlength O -> bytes_ok src ->
    sublist 0 (Zlength O - trl_of wbits) src = sublist 0 (Zlength O - trl_of wbits) O ->
    sublist (Zlength O - trl_of wbits) (Zlength O) src <> sublist (Zlength O - trl_of wbits) (Zlength O) O ->
    P wbits D O src 0 [] z (init_live sp (iwb wbits));
  bd_call : forall wbits D O src pos out z L strmp flush ib inp o aout r z' st' ow,
    P wbits D O src pos out z L -> call_pre src pos z L strmp flush ib inp o aout ->
    pos + Zlength inp <= Zlength src ->
    inflate_rel flush strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) (Some L) ib inp (Some o)
      r z' st' ow ->
    r <> Z_MEM_ERROR -> zf_ok z' ->
    exists L', call_post ib inp o aout z' st' ow L' /\
      (r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_DATA_ERROR) /\
      (r <> Z_DATA_ERROR -> P wbits D O src (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L')
}.

Definition pfx_stmt : Prop := exists P, pfx_facts P.
Definition trl_stmt : Prop := exists P, trl_facts P.
Definition bad_stmt : Prop := exists P, bad_facts P.
