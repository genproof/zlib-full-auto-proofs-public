(** * The model theory of deflate without the size limits of the deflate laws: interfaces of its parts

    LTIface.v states [core_facts W] and [hdr_facts HI] for the streams of the x_ deflate laws: each call offered at
    most 2^30 bytes of input and of output space, total_in / total_out below 2^40, a dictionary of at most 32768
    bytes, gzip header fields of at most 4096 bytes (LawFacts.hdr_ok).  Those limits keep the arithmetic far from
    any wrap-around; the code needs none of them.  Here are the same facts for what the C types allow:

    - [zin_okw]: avail_in and avail_out any uInt (< 2^32), total_in any uLong (the model adds to it modulo 2^64,
      see [zstep]), total_out with room for the output space (cpost counts the bits produced, [Gb], on total_out:
      it must not wrap inside a call), the input object of any length;
    - [core_facts_w W]: [core_facts] with [zin_okw], a dictionary of up to 2^32-1 bytes, any total_in; and, for
      the compression stage at level 0 with a flush other than Z_NO_FLUSH, [ub s + avail_in < 2^32]: deflate_stored
      compares a block length with [left + strm->avail_in] in 32-bit unsigned arithmetic, and when the sum wraps
      it can write a LAST stored block with input left (a real behaviour of deflate.c, which makes
      the law res_compress_bound false: CONTRACT.md);
    - [hdr_facts_w HI]: [hdr_facts] for the headers [LawFactsW.hdr_ok_w] and any output space / total_out.

    Everything else (cpost, the events, hdr_post, ...) is LTDefs.v / LTIface.v unchanged.  Proved by LTWCore.v
    ([core_theory_w]) and LTWHdr.v ([hdr_theory_w]); used by LTWBound.v ([bound_theory_w]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTIface Zlib.proof.deflate.LawFactsW.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The stream during a call, any sizes *)
Definition zin_okw (z : strm) : Prop :=
  bytes (z_in z) /\ 0 <= z_next_in z /\ 0 <= z_avail_in z <= 4294967295 /\
  z_next_in z + z_avail_in z <= Zlength (z_in z) /\ 0 <= z_avail_out z <= 4294967295 /\
  0 <= z_total_in z <= 18446744073709551615 /\ 0 <= z_total_out z /\
  z_total_out z + z_avail_out z <= 18446744073709551615.

(** ** The core part *)
Record core_facts_w (W : dstate -> Prop) : Prop := {
  cw_prm : forall s, W s -> prm s;
  cw_pos : forall s, W s ->
    0 <= d_lookahead s /\ 0 <= d_strstart s /\ - 1099511627776 <= d_block_start s <= d_strstart s /\
    d_strstart s + d_lookahead s <= 2 * d_w_size s;
  cw_frame : forall s s', W s -> core_eq s s' -> W s';
  cw_init : forall level method wbits mem strategy z,
    params_ok level method wbits mem strategy = true ->
    exists s z',
      c_deflateInit2_ true true false level method wbits mem strategy true true true true true z =
        Some (Some s, z', Z_OK) /\
      W s /\ outok s /\
      d_status s = (if wrap_of wbits =? 2 then GZIP_STATE else INIT_STATE) /\ d_wrap s = wrap_of wbits /\
      d_gzhead s = None /\ d_gzindex s = 0 /\ d_last_flush s = -2 /\
      d_po s = 0 /\ d_pending s = 0 /\ d_bi_valid s = 0 /\
      d_strstart s = 0 /\ d_lookahead s = 0 /\ d_block_start s = 0 /\ d_sym_next s = 0 /\
      d_level s = (if level =? -1 then 6 else level) /\ d_strategy s = strategy /\
      d_w_bits s = Z.max 9 (wb_of wbits) /\ d_hash_bits s = mem + 7 /\
      z' = mkST (z_in z) (z_next_in z) (z_avail_in z) 0 (z_out z) (z_avail_out z) 0
                (if wrap_of wbits =? 2 then 0 else 1) None;
  cw_tune : forall s good lazy nice chain, W s -> s32 nice -> W (tune_set s good lazy nice chain);
  (** deflateSetDictionary: a dictionary of up to 2^32-1 bytes (the last w_size bytes are used when it is
      longer; the Adler-32 is of the whole dictionary); total_in moves modulo 2^64 *)
  cw_dict : forall s z d,
    W s -> 0 <= d_wrap s <= 1 -> bad_state s = false -> (d_wrap s = 1 -> d_status s = INIT_STATE) ->
    d_strstart s = 0 -> d_lookahead s = 0 -> d_block_start s = 0 ->
    bytes d -> Zlength d <= 4294967295 -> 0 <= z_total_in z <= 18446744073709551615 ->
    adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' k,
      c_deflateSetDictionary s z (Some d) = Some (s', z', Z_OK) /\ W s' /\
      api_eq s s' /\ out_eq s s' /\ same_prm s s' /\
      d_lookahead s' = 0 /\ d_strstart s' = d_block_start s' /\
      (d_strstart s' = 0 <-> d = []) /\
      d_sym_next s' = d_sym_next s /\ 0 <= k <= Zlength d /\
      z' = mkST (z_in z) (z_next_in z) (z_avail_in z) (u64 (z_total_in z + k)) (z_out z) (z_avail_out z)
                (z_total_out z)
                (if d_wrap s =? 1 then Zlib.proof.adler32.Model.ref_adler32 (z_adler z) d else z_adler z)
                (z_msg z);
  cw_compress : forall s z flush,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_okw z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W s z flush s' z' bs evs;
  cw_still : forall s z flush s' z' bs,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_okw z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    c_compress_func s z flush = Some (s', z', bs) ->
    ub s = 0 -> d_strstart s = 0 -> z_next_in z' = z_next_in z -> d_strstart s' = 0;
  cw_stored_live : forall s z s' z' bs,
    W s -> outok s -> quiet s -> zin_okw z -> 0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    d_level s = 0 ->
    stored_hdr s + 5 * ((ub s + z_avail_in z) / MAX_STORED) + ub s + z_avail_in z <= z_avail_out z ->
    c_compress_func s z Z_FINISH = Some (s', z', bs) -> bs = finish_done;
  cw_full : forall s,
    W s -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
    exists s1, c_clear_hash s = Some s1 /\ W (full_reset s1) /\
      api_eq s s1 /\ out_eq s s1 /\ same_prm s s1 /\ d_sym_next s1 = d_sym_next s;
  cw_params : forall s level strategy,
    W s -> 0 <= level <= 9 -> 0 <= strategy <= 4 ->
    (cfg_f level = cfg_f (d_level s) /\ strategy = d_strategy s) \/
    (d_lookahead s = 0 /\ d_strstart s = d_block_start s) ->
    exists s1, params_tail s level strategy = Some s1 /\ W s1 /\ api_eq s s1 /\ out_eq s s1 /\
      d_level s1 = level /\ d_strategy s1 = strategy /\
      d_w_bits s1 = d_w_bits s /\ d_hash_bits s1 = d_hash_bits s /\
      d_strstart s1 = d_strstart s /\ d_lookahead s1 = d_lookahead s /\ d_block_start s1 = d_block_start s /\
      d_sym_next s1 = d_sym_next s
}.

Definition core_w_stmt : Prop := exists W, core_facts_w W.

(** ** The header part: [hdr_pre] for the headers [hdr_ok_w] and any output space *)
Definition hdr_pre_w (HI : hdr_inv) (s : dstate) (z : strm) (H : list Z) (k : Z) : Prop :=
  prm s /\ outok s /\ d_pending s = 0 /\ d_sym_next s = 0 /\ d_bi_valid s = 0 /\
  0 <= z_avail_out z <= 4294967295 /\ 0 <= z_total_out z <= 18446744073709551615 /\
  (forall h, d_gzhead s = Some h -> hdr_ok_w h) /\
  ((d_status s = INIT_STATE /\ 0 <= d_wrap s <= 1 /\ H = hdr_bytes s (z_adler z) /\ k = 0) \/
   (d_status s = GZIP_STATE /\ d_wrap s = 2 /\ H = hdr_bytes s (z_adler z) /\ k = 0) \/
   HI s (z_adler z) H k).

Record hdr_facts_w (HI : hdr_inv) : Prop := {
  hw_frame : forall s s' a H k, HI s a H k ->
    d_status s' = d_status s -> d_gzindex s' = d_gzindex s -> d_gzhead s' = d_gzhead s ->
    d_wrap s' = d_wrap s -> d_pending_buf_size s' = d_pending_buf_size s -> HI s' a H k;
  hw_status : forall s a H k, HI s a H k ->
    d_wrap s = 2 /\ (exists h, d_gzhead s = Some h) /\
    (d_status s = EXTRA_STATE \/ d_status s = NAME_STATE \/ d_status s = COMMENT_STATE \/
     d_status s = HCRC_STATE) /\
    (exists xfl, H = gz_hdr_bytes (d_gzhead s) xfl) /\ 10 <= k < Zlength H;
  hw_run : forall s z H k, hdr_pre_w HI s z H k ->
    exists s' z' r, hdr_stages s z = Some (s', z', r) /\ hdr_post HI s z H k s' z' r
}.

Definition hdr_w_stmt : Prop := exists HI, hdr_facts_w HI.
