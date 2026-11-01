(* Law inflate_codes: THE interface between the main of harness/inflate_codes.c (Main.v, VST) and the pure theory
   over the model (Theory*.v).  Pure Coq over Spec5's relations (inflate_rel over Model2.run2, setdict_f,
   init_live).

   The harness's loop keeps, besides the stream (z, L), the variables pos (input bytes consumed so far),
   final (the final code once returned, else Z_OK) and in_dict (inflate() just returned Z_NEED_DICT); w is the
   windowBits given to inflateInit2_ (accepted: wbits_ok w) and src the n input bytes.  The theory chooses an
   invariant I w src pos final in_dict z L (existential: `codes_theory`) and proves the facts below; Main.v
   proves main for ANY I with codes_facts I. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.harness.inflate_common.HDefs.
Require Zlib.proof.adler32.Model.
Import ListNotations.
Local Open Scope Z_scope.

(* the stream fields the harness sets before an inflate() call: next_in, avail_in, next_out, avail_out *)
Definition set_zf_call (z: zfields) (ni: val) (ai: Z) (no: val) (ao: Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

Definition ob_ptr (ob: option outbuf) : val := match ob with None => nullval | Some o => out_ptr o 0 end.

(* the input of a call: Z_NULL (no bytes), or an object holding src[pos .. pos + ain) *)
Definition call_in_ok (src: list Z) (pos ain: Z) (ib: inbuf) (inp: list Z) : Prop :=
  (ib = InNull /\ inp = []) \/ (ib <> InNull /\ inp = sublist pos (pos + ain) src).

(* the harness's badptr: next_out Z_NULL, or next_in Z_NULL with avail_in > 0 *)
Definition badptr (ib: inbuf) (ob: option outbuf) (ain: Z) : bool :=
  match ob with
  | None => true
  | Some _ => match ib with InNull => negb (ain =? 0) | InBuf _ _ _ _ _ => false end
  end.

(* the harness's updates of final and in_dict after an inflate() call *)
Definition final_after (bad: bool) (final r: Z) : Z :=
  if bad then final
  else if orb (orb (r =? Z_STREAM_END) (r =? Z_DATA_ERROR)) (r =? Z_MEM_ERROR) then r else final.
Definition indict_after (bad: bool) (indict r: Z) : Z :=
  if bad then indict else if r =? Z_NEED_DICT then 1 else 0.

(* what the harness checks after an inflate() call, and the invariant afterwards *)
Definition inflate_post (I: Z -> list Z -> Z -> Z -> Z -> zfields -> live -> Prop)
    (w: Z) (src: list Z) (pos final indict ain aout flush: Z) (bad: bool) (r: Z) (z': zfields) (L': live)
    : Prop :=
  let used := ain - zf_ai z' in
  let made := aout - zf_ao z' in
  code_okb r = true /\
  0 <= zf_ai z' <= ain /\ 0 <= zf_ao z' <= aout /\
  (r = Z_STREAM_ERROR <-> bad = true) /\
  (r = Z_OK -> (used <> 0 \/ made <> 0) /\ flush <> Z_FINISH) /\
  (r = Z_BUF_ERROR -> (used = 0 /\ made = 0) \/ flush = Z_FINISH) /\
  (r = Z_DATA_ERROR -> zf_msg z' <> None) /\
  (bad = false -> final <> Z_OK -> r = final /\ used = 0 /\ made = 0) /\
  (r = Z_NEED_DICT ->
     zlib_okb w = true /\ pos + used = 6 /\ Z.land (Znth 1 src) 32 <> 0 /\
     zf_adler z' = be32 (sublist 2 6 src) /\ (indict <> 0 -> used = 0 /\ made = 0)) /\
  I w src (pos + used) (final_after bad final r) (indict_after bad indict r) z' L'.

(* what the harness checks after an inflateSetDictionary call (the dictionary: aout bytes), and the
   invariant afterwards *)
Definition setdict_post (I: Z -> list Z -> Z -> Z -> Z -> zfields -> live -> Prop)
    (w: Z) (src: list Z) (pos final indict: Z) (dict: list Z) (z: zfields) (res: Z * zfields * live) : Prop :=
  let '(r, z', L') := res in
  (w < 0 -> r = Z_OK \/ r = Z_MEM_ERROR) /\
  (0 <= w -> indict = 0 -> r = Z_STREAM_ERROR) /\
  (0 <= w -> indict <> 0 ->
     (r = Z_DATA_ERROR <-> Zlib.proof.adler32.Model.ref_adler32 1 dict <> zf_adler z') /\
     (r = Z_OK \/ r = Z_DATA_ERROR \/ r = Z_MEM_ERROR)) /\
  I w src pos (if r =? Z_MEM_ERROR then Z_MEM_ERROR else final) (if r =? Z_MEM_ERROR then 0 else indict) z' L'.

Record codes_facts (I: Z -> list Z -> Z -> Z -> Z -> zfields -> live -> Prop) : Prop := {
  (* after inflateInit2_ returned Z_OK (z: the stream fields then; msg NULL) *)
  cf_init : forall w src z sp,
    wbits_ok w = true -> isptr sp -> zf_ok z -> zf_msg z = None -> live_ok (init_live sp w) ->
    Int.min_signed <= w <= Int.max_signed -> Zlength src <= 2 ^ 24 -> bytes_ok src ->
    I w src 0 Z_OK 0 z (init_live sp w);
  (* the invariant's consequences main needs: inflate() and inflateSetDictionary see no gz_header; the
     harness's variables stay in range *)
  cf_head : forall w src pos final indict z L,
    I w src pos final indict z L -> i_head (l_s L) = false;
  cf_range : forall w src pos final indict z L,
    I w src pos final indict z L ->
    (final = Z_OK \/ final = Z_STREAM_END \/ final = Z_DATA_ERROR \/ final = Z_MEM_ERROR) /\
    (indict = 0 \/ indict = 1);
  (* inflateSetDictionary(&s, dict, |dict|) on the live stream *)
  cf_setdict : forall w src pos final indict z L dict alloc_ok winp,
    I w src pos final indict z L -> live_ok L -> zf_ok z ->
    bytes_ok dict -> Zlength dict <= 2 ^ 20 ->
    setdict_post I w src pos final indict dict z (setdict_f dict alloc_ok winp z L);
  (* inflate(&s, flush) on the live stream, offered src[pos .. pos + ain) (or Z_NULL) and aout bytes of space
     (or Z_NULL) *)
  cf_inflate : forall w src pos final indict z L strmp flush ib inp ob ain aout r z' st' ow,
    I w src pos final indict z L -> live_ok L -> zf_ok z -> strmp <> nullval ->
    0 <= pos -> 0 <= ain -> pos + ain <= Zlength src -> Zlength src <= 2 ^ 24 -> bytes_ok src ->
    0 <= aout <= 2 ^ 20 -> Int.min_signed <= flush <= Int.max_signed ->
    call_in_ok src pos ain ib inp ->
    inflate_rel flush strmp (set_zf_call z (in_ptr ib 0) ain (ob_ptr ob) aout) (Some L) ib inp ob r z' st' ow ->
    exists L', st' = Some L' /\ inflate_post I w src pos final indict ain aout flush (badptr ib ob ain) r z' L'
}.

(* The theory (Theory.v).  stepf2_mwf3_stmt (CaseHyps5.v: one pass of the switch keeps mwf3) is the
   intra-call invariant of the model; its proof is the inflate area's (StepMwf5.v). *)
Definition codes_theory_stmt : Prop :=
  stepf2_mwf3_stmt -> exists I, codes_facts I.
