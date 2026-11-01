(* Round-trip part RT-D: the specifications of the parts of the compression stage.  Each spec is the
   functional companion of the deflate laws' part spec of the same function (RTDLTCSpecs.v / RTDLTCSpecs2.v,
   copied Qed theory): it ASSUMES the model run's result and the laws' preconditions, and concludes the
   functional facts (RTDDefs.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDDefs.
Require Export Zlib.proof.roundtrip.RTDLTCSpecs Zlib.proof.roundtrip.RTDLTCSpecs2.
Require Export Zlib.proof.roundtrip.RTDLTCore.
Import ListNotations.
Local Open Scope Z_scope.

(** ** fill_window: the bytes read are appended to the history; the chains stay hash-consistent; ins_h is
    primed for strstart once the bytes read leave lookahead >= MIN_MATCH *)
Definition fill_fspec : Prop :=
  forall s z s' z' H,
    fill_pre s -> zall z -> adler_ok (d_wrap s) (z_adler z) ->
    c_fill_window s z = Some (s', z') ->
    kwin H s ->
    exists k,
      zstep (d_wrap s) z z' k [] /\
      kwin (H ++ sublist (z_next_in z) (z_next_in z + k) (z_in z)) s' /\
      (chain_hok s -> chain_hok s') /\
      (MIN_MATCH <= d_lookahead s' -> (0 < k \/ (d_insert s = 0 /\ primed s (d_strstart s))) ->
       d_insert s' = 0 /\ primed s' (d_strstart s')).

(** ** INSERT_STRING(s, p, hash_head) with ins_h primed for p, p's three bytes data, p the newest position
    (its prev slot holds no entry longest_match may still visit) *)
Definition ins_fspec : Prop :=
  forall s p s' h,
    prm s -> wstruct s -> chain_hok s -> primed s p ->
    0 <= p <= d_strstart s -> p + 2 < d_strstart s + d_lookahead s -> p - d_w_size s < lim s ->
    c_insert_string s p = Some (s', h) ->
    d_ins_h s' = h3 s p /\ h = Znth (h3 s p) (d_head s) /\ chain_hok s' /\ primed s' (p + 1).

(** ** longest_match(s, cur) from a chain entry cur of the bucket of strstart's string: a match longer than
    prev_length is a real match (bytes equal) *)
Definition lm_fspec : Prop :=
  forall s cur s' ml (G : Z -> Prop),
    prm s -> wstruct s -> wpos s -> wwin s -> chain_ok s ->
    MIN_MATCH <= d_lookahead s -> 0 <= d_prev_length s <= MAX_MATCH ->
    0 < cur -> lim s <= cur -> cur < d_strstart s -> G cur ->
    (forall q, G q -> 0 < q -> lim s <= q ->
       q + 2 < d_strstart s + d_lookahead s /\ h3 s q = h3 s (d_strstart s) /\
       G (Znth (Z.land q (d_w_mask s)) (d_prev s))) ->
    c_longest_match s cur = Some (s', ml) ->
    d_prev_length s < ml ->
    forall i, 0 <= i < ml ->
      Znth (d_match_start s' + i) (mb_val (d_window s)) = Znth (d_strstart s + i) (mb_val (d_window s)).

(** ** flush_pending: the bytes written to next_out are the first pending bytes (no bit is lost or added) *)
Definition fpend_fspec : Prop :=
  forall s z s' z',
    outok s -> zout_ok z -> c_flush_pending s z = Some (s', z') ->
    exists x, zout_only z z' x /\ F.bytes_bits (x ++ pend s') ++ bibits s' = F.bytes_bits (pend s) ++ bibits s.

(** ** FLUSH_BLOCK_ONLY(s, last) where the symbols cover the window bytes [block_start, strstart) (H the
    history, the blocks BS before): one more block, its data the bytes of H below strstart *)
Definition fbo_fspec : Prop :=
  forall s z s' z' syms last dict D BS p,
    fbo_pre s z syms last ->
    let H := dict ++ D in
    let off := Zlength H - (d_strstart s + d_lookahead s) in
    let wmax := 2 ^ d_w_bits s in
    kwin H s -> F.blocks_ok wmax dict BS -> F.expand dict BS = sublist 0 (off + d_block_start s) H ->
    syms_rok wmax (F.expand dict BS) syms ->
    F.syms_data (F.expand dict BS) (map fsym syms) = sublist 0 (off + d_strstart s) H ->
    0 <= p -> (p - d_bi_valid s) mod 8 = 0 ->
    c_flush_block_only s z last = Some (s', z') ->
    exists x blk,
      zout_only z z' x /\
      F.blocks_ok wmax dict (BS ++ [blk]) /\ F.expand dict (BS ++ [blk]) = sublist 0 (off + d_strstart s) H /\
      F.bytes_bits (x ++ pend s') ++ bibits s' = bibits s ++ enc_out p [blk] (last =? 1).

(** ** A compression function (0 deflate_stored, 1 fast, 2 slow, 3 huff, 4 rle, as [fn_of]) on a state of the
    laws' invariant W3 and of [kcore]: the bytes consumed extend the history, the blocks BS' it emits follow BS,
    and the bits it adds (written to next_out, pending, in the bit buffer) are their encoding *)
Definition comp_fspec (f : Z) (c : dstate -> strm -> Z -> option (dstate * strm * bstate)) : Prop :=
  forall s z flush s' z' bs dict D BS syms p,
    W3 s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_ok z -> 0 <= d_wrap s <= 2 ->
    adler_pre (d_wrap s) (z_adler z) -> fn_of s = f ->
    Forall F.byte_ok dict -> bytes D -> kcore dict D BS syms s ->
    0 <= p -> (p - d_bi_valid s) mod 8 = 0 ->
    c s z flush = Some (s', z', bs) ->
    exists k x BS' syms',
      zstep (d_wrap s) z z' k x /\
      kcore dict (D ++ sublist (z_next_in z) (z_next_in z + k) (z_in z)) (BS ++ BS') syms' s' /\
      F.bytes_bits (x ++ pend s') ++ bibits s' = bibits s ++ enc_out p BS' (fin_bs bs) /\
      (fin_bs bs = true -> BS' <> []).
