(* Law inflate_check: THE interface between the main of harness/inflate_check.c (IKMain.v, VST) and the pure
   theory over the model (IKTheory*.v), as inflate_codes/Facts.v.  Pure Coq over Spec5's relations
   (inflate_rel over Model2.run2, init_live).

   The harness's loop keeps, besides the stream (z, L), pos (input bytes consumed so far), tout (the length of
   out mod 2^64), ra / rc (the Adler-32 / CRC-32 of out by the reference functions), where out is all the
   bytes inflate() has produced so far (a ghost list here).  w is the windowBits given to inflateInit2
   (accepted: wbits_ok w), src the n input bytes.  The theory chooses an invariant I w src pos out z L
   (existential: ik_theory_stmt) and proves the facts below; IKMain.v proves main for ANY I with
   check_facts I.  Main keeps itself: tout = |out| mod 2^64, ra = ref_adler32 1 out, rc = ref_crc32 0 out,
   and for a raw stream (w < 0) zf_adler z = adler0 (the value stream_defaults left). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.harness.inflate_common.HDefs.
Require Export Zlib.proof.harness.inflate_common.HarnessLe32.
Require Export Zlib.proof.adler32.Model Zlib.proof.crc32.Model.
Import ListNotations.
Local Open Scope Z_scope.

(* the stream fields the harness sets before an inflate() call: next_in, avail_in, next_out, avail_out *)
Definition ik_set_zf_call (z: zfields) (ni: val) (ai: Z) (no: val) (ao: Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

(* the harness's gz (for w >= 0): a gzip wrapper, given (16..31) or detected (32..47) from the first two bytes *)
Definition ik_gz (w: Z) (src: list Z) : bool :=
  ((16 <=? w) && (w <? 32)) ||
  ((32 <=? w) && (2 <=? Zlength src) && (Znth 0 src =? 31) && (Znth 1 src =? 139)).

(* the header checks of the harness (the bytes exist: main reads them) *)
Definition ik_ghdr (src: list Z) : Prop :=
  4 <= Zlength src /\ Znth 0 src = 31 /\ Znth 1 src = 139 /\ Znth 2 src = 8 /\ Z.land (Znth 3 src) 224 = 0.
Definition ik_zhdr (src: list Z) : Prop :=
  2 <= Zlength src /\ Z.land (Znth 0 src) 15 = 8 /\ Z.shiftr (Znth 0 src) 4 <= 7 /\
  (Znth 0 src * 256 + Znth 1 src) mod 31 = 0.
Definition ik_hdr (gz: bool) (src: list Z) : Prop := if gz then ik_ghdr src else ik_zhdr src.

(* the check value of out by the reference definitions *)
Definition ik_chk (gz: bool) (out: list Z) : Z := if gz then ref_crc32 0 out else ref_adler32 1 out.

(* the trailer before pos' (the end of the consumed input) at Z_STREAM_END *)
Definition ik_trailer (gz: bool) (src: list Z) (pos': Z) (out': list Z) : Prop :=
  if gz then
    18 <= pos' /\ le32 (sublist (pos' - 8) (pos' - 4) src) = ref_crc32 0 out' /\
    le32 (sublist (pos' - 4) pos' src) = Zlength out' mod 2 ^ 32
  else 6 <= pos' /\ be32 (sublist (pos' - 4) pos' src) = ref_adler32 1 out'.

(* what the harness checks after an inflate() call that did not return Z_MEM_ERROR (the output space held
   aout bytes, the call wrote ow at its start), and the invariant afterwards *)
Definition check_post (I: Z -> list Z -> Z -> list Z -> zfields -> live -> Prop)
    (w: Z) (src: list Z) (pos: Z) (out: list Z) (ain aout r: Z) (z z': zfields) (L': live) (ow: list Z)
    : Prop :=
  let used := ain - zf_ai z' in
  let made := aout - zf_ao z' in
  let out' := out ++ ow in
  0 <= zf_ai z' <= ain /\ 0 <= zf_ao z' <= aout /\ Zlength ow = made /\ bytes_ok ow /\
  (w < 0 -> zf_adler z' = zf_adler z) /\
  (0 <= w -> out' <> [] -> ik_hdr (ik_gz w src) src) /\
  (0 <= w -> (out' <> [] \/ r = Z_STREAM_END) -> zf_adler z' = ik_chk (ik_gz w src) out') /\
  (0 <= w -> r = Z_STREAM_END ->
     zf_tout z' = Zlength out' mod 2 ^ 64 /\ ik_trailer (ik_gz w src) src (pos + used) out') /\
  I w src (pos + used) out' z' L'.

Record check_facts (I: Z -> list Z -> Z -> list Z -> zfields -> live -> Prop) : Prop := {
  (* after inflateInit2_ returned Z_OK (z: the stream fields then; msg NULL, total_out 0) *)
  ck_init : forall w src z sp,
    wbits_ok w = true -> isptr sp -> zf_ok z -> zf_msg z = None -> zf_tout z = 0 ->
    live_ok (init_live sp w) -> Int.min_signed <= w <= Int.max_signed ->
    Zlength src <= 2 ^ 24 -> bytes_ok src ->
    I w src 0 [] z (init_live sp w);
  (* inflate() sees no gz_header *)
  ck_head : forall w src pos out z L, I w src pos out z L -> i_head (l_s L) = false;
  (* inflate(&s, flush) on the live stream, offered src[pos .. pos + ain) (in an object of its own) and aout
     bytes of space *)
  ck_inflate : forall w src pos out z L strmp flush ib inp o ain aout r z' st' ow,
    I w src pos out z L -> live_ok L -> zf_ok z -> strmp <> nullval ->
    0 <= pos -> 0 <= ain -> pos + ain <= Zlength src -> Zlength src <= 2 ^ 24 -> bytes_ok src ->
    0 <= aout <= 2 ^ 20 -> Int.min_signed <= flush <= Int.max_signed ->
    ib <> InNull -> inp = sublist pos (pos + ain) src ->
    inflate_rel flush strmp (ik_set_zf_call z (in_ptr ib 0) ain (out_ptr o 0) aout) (Some L) ib inp (Some o)
      r z' st' ow ->
    exists L', st' = Some L' /\ (r <> Z_MEM_ERROR -> check_post I w src pos out ain aout r z z' L' ow)
}.

(* The theory (IKTheory.v). *)
Definition ik_theory_stmt : Prop := exists I, check_facts I.
