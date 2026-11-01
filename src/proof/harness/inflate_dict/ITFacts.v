(* Law inflate_dict: THE interface between the main of harness/inflate_dict.c (ITMain*.v, VST) and the pure
   theory over the model (ITTheory*.v), as inflate_codes/Facts.v.  Pure Coq over Spec5's relations (inflate_rel
   over Model2.run2, setdict_f, dict_bytes, init_live) and the abstract stream format rfc1951/Format.v.

   The encoder half of main (the harness builds the stream with deflate_ref.h) ends with a ghost G (it_ghost):
   the wrapper choice, the window bits wb, FLEVEL, the windowBits iw given to inflateInit2, the dictionary and
   the blocks; src[0..slen) = it_src G, data[0..n) = it_data G, it_ok G.  In the inflate half the harness keeps,
   besides the stream (z, L), pos (input bytes consumed), opos (output bytes produced), dict_set (dset) and,
   between an inflate() call that returned Z_NEED_DICT and the dictionary, nd.  The theory chooses an invariant
   I G pos opos dset nd z L (existential: it_theory_stmt) and proves the facts below; ITMain*.v prove main for
   ANY I with it_facts I. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.harness.inflate_common.HDefs.
Require Export Zlib.proof.rfc1951.Format.
Require Export Zlib.proof.adler32.Model.
Import ListNotations.
Local Open Scope Z_scope.

(* the harness's choices: zlib (wrap <> 0) or raw, wb (8..15), flevel (the byte drawn), iw (inflateInit2's
   windowBits), the dictionary, the blocks *)
Record it_ghost := ITG {
  g_zlib : bool; g_wb : Z; g_flevel : Z; g_iw : Z; g_dict : list Z; g_bs : list block }.

Definition it_dictid (G: it_ghost) : Z := ref_adler32 1 (g_dict G).
Definition it_wrapper (G: it_ghost) : wrapper :=
  if g_zlib G then WZlib (g_wb G) (Z.land (g_flevel G) 3) (Some (it_dictid G)) else WRaw.
(* the stream bytes and the data *)
Definition it_src (G: it_ghost) : list Z := stream_bytes (it_wrapper G) (g_dict G) (g_bs G).
Definition it_data (G: it_ghost) : list Z := data (g_dict G) (g_bs G).
(* the wrong dictionary: the right one with its first byte ^ 1, or one zero byte for an empty one *)
Definition it_bad (G: it_ghost) : list Z :=
  match g_dict G with [] => [0] | b :: r => Z.lxor b 1 :: r end.

(* what the encoder half establishes: the harness's ranges, a well-formed stream (stored and fixed blocks with
   references within min(dlen + bytes so far, 2^wb)), and the windowBits the harness picks *)
Definition it_ok (G: it_ghost) : Prop :=
  8 <= g_wb G <= 15 /\ 0 <= g_flevel G < 256 /\
  Zlength (g_dict G) <= 2 ^ 16 /\ Zlength (it_data G) <= 2 ^ 18 /\ Zlength (it_src G) <= 2 ^ 19 /\
  Forall (fun b => match b with Dynamic _ _ _ _ _ => False | _ => True end) (g_bs G) /\
  stream_ok (it_wrapper G) (g_wb G) (g_dict G) (g_bs G) /\
  (if g_zlib G then g_iw G = g_wb G \/ g_iw G = 0 \/ g_iw G = 32 + g_wb G else g_iw G = - g_wb G).

(* the sliding window after k bytes of output: inflateGetDictionary's length and bytes *)
Definition it_win (G: it_ghost) (k: Z) (L: live) : Prop :=
  let h := g_dict G ++ sublist 0 k (it_data G) in
  i_whave (l_s L) = Z.min (Zlength h) (2 ^ g_wb G) /\
  dict_bytes (l_s L) = sublist (Zlength h - i_whave (l_s L)) (Zlength h) h.

(* the stream fields the harness sets before an inflate() call: next_in, avail_in, next_out, avail_out *)
Definition it_set_zf_call (z: zfields) (ni: val) (ai: Z) (no: val) (ao: Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

Definition it_inv := it_ghost -> Z -> Z -> bool -> bool -> zfields -> live -> Prop.

(* what the harness checks after an inflate() call that did not return Z_MEM_ERROR (offered ain bytes and aout
   bytes of space; the call wrote ow at the start of the space), and the invariant afterwards *)
Definition it_post (I: it_inv) (G: it_ghost) (pos opos: Z) (dset: bool) (ain aout r: Z) (z': zfields)
    (L': live) (ow: list Z) : Prop :=
  let used := ain - zf_ai z' in
  let made := aout - zf_ao z' in
  0 <= zf_ai z' <= ain /\ 0 <= zf_ao z' <= aout /\ Zlength ow = made /\ bytes_ok ow /\
  ((r = Z_NEED_DICT /\ g_zlib G = true /\ dset = false /\ made = 0 /\ opos = 0 /\
    zf_adler z' = it_dictid G /\ I G (pos + used) 0 false true z' L') \/
   ((r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END) /\
    made <= Zlength (it_data G) - opos /\ ow = sublist opos (opos + made) (it_data G) /\
    (r = Z_STREAM_END -> opos + made = Zlength (it_data G) /\ pos + used = Zlength (it_src G) /\
                         (dset = true -> g_zlib G = false -> it_win G (opos + made) L')) /\
    (r <> Z_STREAM_END -> I G (pos + used) (opos + made) dset false z' L'))).

Record it_facts (I: it_inv) : Prop := {
  (* after inflateInit2_ returned Z_OK on a zlib stream (z: the stream fields then; msg NULL) *)
  it_init : forall G z sp,
    it_ok G -> g_zlib G = true -> wbits_ok (g_iw G) = true -> isptr sp -> zf_ok z -> zf_msg z = None -> zf_tout z = 0 ->
    live_ok (init_live sp (g_iw G)) ->
    I G 0 0 false false z (init_live sp (g_iw G));
  (* a raw stream: inflateSetDictionary(&s, dict, dlen) right after inflateInit2_ returned Z_OK *)
  it_raw : forall G z sp alloc_ok winp,
    it_ok G -> g_zlib G = false -> wbits_ok (g_iw G) = true -> isptr sp -> zf_ok z -> zf_msg z = None -> zf_tout z = 0 ->
    live_ok (init_live sp (g_iw G)) ->
    let '(r, z', L') := setdict_f (g_dict G) alloc_ok winp z (init_live sp (g_iw G)) in
    (r = Z_OK \/ r = Z_MEM_ERROR) /\ (r = Z_OK -> I G 0 0 true false z' L');
  (* the invariant's consequences main needs *)
  it_head : forall G pos opos dset nd z L, I G pos opos dset nd z L -> i_head (l_s L) = false;
  it_range : forall G pos opos dset nd z L, I G pos opos dset nd z L ->
    it_ok G /\ 0 <= pos <= Zlength (it_src G) /\ 0 <= opos <= Zlength (it_data G);
  (* once the dictionary is set (and before Z_STREAM_END): the window *)
  it_window : forall G pos opos nd z L, I G pos opos true nd z L -> it_win G opos L;
  (* after Z_NEED_DICT: the wrong dictionary is rejected and changes nothing *)
  it_bad_dict : forall G pos z L alloc_ok winp,
    I G pos 0 false true z L -> setdict_f (it_bad G) alloc_ok winp z L = (Z_DATA_ERROR, z, L);
  (* after Z_NEED_DICT: the right dictionary *)
  it_good_dict : forall G pos z L alloc_ok winp,
    I G pos 0 false true z L -> live_ok L -> zf_ok z ->
    let '(r, z', L') := setdict_f (g_dict G) alloc_ok winp z L in
    (r = Z_OK \/ r = Z_MEM_ERROR) /\ (r = Z_OK -> I G pos 0 true false z' L');
  (* inflate(&s, flush) on the live stream, offered src[pos .. lim) (in an object of its own) and aout bytes of
     space *)
  it_inflate : forall G pos opos dset z L strmp flush lim ib inp o aout r z' st' ow,
    I G pos opos dset false z L -> live_ok L -> zf_ok z -> strmp <> nullval ->
    pos <= lim <= Zlength (it_src G) -> 0 <= aout <= 2 ^ 20 -> Int.min_signed <= flush <= Int.max_signed ->
    ib <> InNull -> inp = sublist pos lim (it_src G) ->
    inflate_rel flush strmp (it_set_zf_call z (in_ptr ib 0) (lim - pos) (out_ptr o 0) aout) (Some L) ib inp
      (Some o) r z' st' ow ->
    exists L', st' = Some L' /\ (r <> Z_MEM_ERROR -> it_post I G pos opos dset (lim - pos) aout r z' L' ow)
}.

(* The theory (ITTheory.v). *)
Definition it_theory_stmt : Prop := exists I, it_facts I.
