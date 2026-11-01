(* Law rfc_stored: THE interface between the main of harness/rfc_stored.c (RSMain*.v, VST) and the pure theory
   over the model (RSTheory.v), as inflate_check/IKFacts.v.  Pure Coq over Spec5's relation inflate_rel (the
   relation of SpecW.inflate_specW, the specification main calls inflate() with).

   The harness's inflate loop keeps, besides the stream (z, L): src (the whole buffer it built, RSModel.rs_src),
   d (the data), pos (the input consumed: next_in = stream + pos) and out (the output so far: next_out =
   out + |out|).  The theory chooses an invariant P src d pos out z L (existential: rs_theory_stmt); main is
   proved for ANY P with rs_facts P. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.harness.rfc_stored.RSModel.
Import ListNotations.
Local Open Scope Z_scope.

(* the stream fields main sets before an inflate() call: next_in, avail_in, next_out, avail_out *)
Definition rs_set_call (z: zfields) (ni: val) (ai: Z) (no: val) (ao: Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

(* what main learns from an inflate() call that did not return Z_MEM_ERROR, offered ain bytes of input and
   aout bytes of output space (the call wrote ow at its start), and the invariant afterwards *)
Definition rs_post (P: list Z -> list Z -> Z -> list Z -> zfields -> live -> Prop)
    (src d: list Z) (pos: Z) (out: list Z) (ain aout r: Z) (ib: inbuf) (o: outbuf) (z': zfields) (L': live)
    (ow: list Z) : Prop :=
  let used := ain - zf_ai z' in
  (r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END) /\
  0 <= zf_ai z' <= ain /\ Zlength ow <= aout /\ zf_ao z' = aout - Zlength ow /\
  zf_ni z' = in_ptr ib used /\ zf_no z' = out_ptr o (Zlength ow) /\ bytes_ok ow /\
  (exists rest, d = out ++ ow ++ rest) /\
  (r = Z_STREAM_END -> out ++ ow = d) /\
  P src d (pos + used) (out ++ ow) z' L'.

Record rs_facts (P: list Z -> list Z -> Z -> list Z -> zfields -> live -> Prop) : Prop := {
  (* after inflateInit2_(window_bits[wrapper]) returned Z_OK (z: the stream fields then; total_out 0, msg
     NULL); the buffer as the harness built it *)
  rf_init : forall wr window c s0 lens d sp z,
    rs_ok wr window c s0 lens d -> Zlength s0 <= Ptrofs.max_unsigned ->
    isptr sp -> zf_ok z -> zf_msg z = None -> zf_tout z = 0 ->
    live_ok (init_live sp (rs_iw wr window)) ->
    P (rs_src wr c s0 (rs_pads wr s0 lens) lens d) d 0 [] z (init_live sp (rs_iw wr window));
  (* where the loop is: inside the buffer, the output a prefix of the data; inflate() sees no gz_header *)
  rf_pos : forall src d pos out z L, P src d pos out z L ->
    0 <= pos <= Zlength src /\ (exists rest, d = out ++ rest) /\ i_head (l_s L) = false;
  (* inflate(&strm, flush) on the live stream, offered src[pos .. pos + ain) (inside the buffer: the object
     ib) and aout bytes of space (in the object o) *)
  rf_inflate : forall src d pos out z L strmp flush ib o ain aout r z' st' ow,
    P src d pos out z L -> live_ok L -> zf_ok z -> strmp <> nullval ->
    0 <= ain <= Int.max_unsigned -> pos + ain <= Zlength src ->
    0 <= aout <= Int.max_unsigned -> Zlength out + aout <= Zlength d ->
    Int.min_signed <= flush <= Int.max_signed -> ib <> InNull ->
    inflate_rel flush strmp (rs_set_call z (in_ptr ib 0) ain (out_ptr o 0) aout) (Some L) ib
      (sublist pos (pos + ain) src) (Some o) r z' st' ow ->
    exists L', st' = Some L' /\ (r <> Z_MEM_ERROR -> rs_post P src d pos out ain aout r ib o z' L' ow)
}.

(* The theory (RSTheory.v). *)
Definition rs_theory_stmt : Prop := exists P, rs_facts P.
