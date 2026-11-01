(** * The model theory of the deflate laws: the interfaces between its four parts

    [core_facts W]: what the compressors and the functions that touch the window / hash chains / trees state
    guarantee, for an invariant [W] of the state chosen by the core part (RTDLTCore.v: [core_theory]).
    [hdr_facts HI]: what the header stages of deflate() guarantee, for an invariant [HI] of a stream in the
    middle of a gzip header chosen by the header part (RTDLTHdr.v: [hdr_theory]).
    LTApi.v ([api_theory]) and LTBound.v ([bound_theory]) use only these facts.  Definitions: RTDLTDefs.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTDefs.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The core part *)
Record core_facts (W : dstate -> Prop) : Prop := {
  (** the state invariant gives the parameters and the positions *)
  cf_prm : forall s, W s -> prm s;
  cf_pos : forall s, W s ->
    0 <= d_lookahead s /\ 0 <= d_strstart s /\ - 1099511627776 <= d_block_start s <= d_strstart s /\
    d_strstart s + d_lookahead s <= 2 * d_w_size s;
  (** it does not depend on what deflate()'s own stages change *)
  cf_frame : forall s s', W s -> core_eq s s' -> W s';
  (** deflateInit2_ with accepted parameters and successful allocations (it ends with deflateReset) *)
  cf_init : forall level method wbits mem strategy z,
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
  (** deflateTune's assignments, any values *)
  cf_tune : forall s good lazy nice chain, W s -> s32 nice -> W (tune_set s good lazy nice chain);
  (** deflateSetDictionary at strstart 0 with nothing read (v3): a fresh zlib stream, or a raw stream in any valid
      status (also after deflate() calls that read nothing, e.g. deflate(Z_BLOCK) without input) *)
  cf_dict : forall s z d,
    W s -> 0 <= d_wrap s <= 1 -> bad_state s = false -> (d_wrap s = 1 -> d_status s = INIT_STATE) ->
    d_strstart s = 0 -> d_lookahead s = 0 -> d_block_start s = 0 ->
    bytes d -> Zlength d <= 32768 -> 0 <= z_total_in z <= 1099511627776 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' k,
      c_deflateSetDictionary s z (Some d) = Some (s', z', Z_OK) /\ W s' /\
      api_eq s s' /\ out_eq s s' /\ same_prm s s' /\
      d_lookahead s' = 0 /\ d_strstart s' = d_block_start s' /\
      (d_strstart s' = 0 <-> d = []) /\
      d_sym_next s' = d_sym_next s /\ 0 <= k <= Zlength d /\
      z' = mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z + k) (z_out z) (z_avail_out z)
                (z_total_out z)
                (if d_wrap s =? 1 then Zlib.proof.adler32.Model.ref_adler32 (z_adler z) d else z_adler z)
                (z_msg z);
  (** the compression stage: one call of the compression function the level / strategy selects *)
  cf_compress : forall s z flush,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_ok z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W s z flush s' z' bs evs;
  (** (v3) a compression call that consumes no input, from a state with everything in blocks at strstart 0, leaves
      strstart at 0 *)
  cf_still : forall s z flush s' z' bs,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_ok z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    c_compress_func s z flush = Some (s', z', bs) ->
    ub s = 0 -> d_strstart s = 0 -> z_next_in z' = z_next_in z -> d_strstart s' = 0;
  (** deflate_stored with Z_FINISH and room for every stored block finishes in the call *)
  cf_stored_live : forall s z s' z' bs,
    W s -> outok s -> quiet s -> zin_ok z -> 0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    d_level s = 0 ->
    stored_hdr s + 5 * ((ub s + z_avail_in z) / MAX_STORED) + ub s + z_avail_in z <= z_avail_out z ->
    c_compress_func s z Z_FINISH = Some (s', z', bs) -> bs = finish_done;
  (** Z_FULL_FLUSH after block_done: CLEAR_HASH and the reset of the positions *)
  cf_full : forall s,
    W s -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
    exists s1, c_clear_hash s = Some s1 /\ W (full_reset s1) /\
      api_eq s s1 /\ out_eq s s1 /\ same_prm s s1 /\ d_sym_next s1 = d_sym_next s;
  (** deflateParams' level / strategy change, after its deflate(strm, Z_BLOCK) when the function or the strategy
      changes (then everything read is in blocks) *)
  cf_params : forall s level strategy,
    W s -> 0 <= level <= 9 -> 0 <= strategy <= 4 ->
    (cfg_f level = cfg_f (d_level s) /\ strategy = d_strategy s) \/
    (d_lookahead s = 0 /\ d_strstart s = d_block_start s) ->
    exists s1, params_tail s level strategy = Some s1 /\ W s1 /\ api_eq s s1 /\ out_eq s s1 /\
      d_level s1 = level /\ d_strategy s1 = strategy /\
      d_w_bits s1 = d_w_bits s /\ d_hash_bits s1 = d_hash_bits s /\
      d_strstart s1 = d_strstart s /\ d_lookahead s1 = d_lookahead s /\ d_block_start s1 = d_block_start s /\
      d_sym_next s1 = d_sym_next s
}.

(** ** The header part *)

(** [HI s a H k]: in the middle of the gzip header [H] (status EXTRA .. HCRC), its first [k] bytes handed to
    pending_buf, strm->adler = [a]. *)
Definition hdr_inv : Type := dstate -> Z -> list Z -> Z -> Prop.

(** The header stages are reached with nothing pending (deflate()'s entry stage flushed it), no symbols, no bits:
    either at the start of the header ([k = 0], [H] the header of the state) or resuming it. *)
Definition hdr_pre (HI : hdr_inv) (s : dstate) (z : strm) (H : list Z) (k : Z) : Prop :=
  prm s /\ outok s /\ d_pending s = 0 /\ d_sym_next s = 0 /\ d_bi_valid s = 0 /\
  0 <= z_avail_out z <= 1073741824 /\ 0 <= z_total_out z <= 1099511627776 /\
  (forall h, d_gzhead s = Some h -> hdr_ok h) /\
  ((d_status s = INIT_STATE /\ 0 <= d_wrap s <= 1 /\ H = hdr_bytes s (z_adler z) /\ k = 0) \/
   (d_status s = GZIP_STATE /\ d_wrap s = 2 /\ H = hdr_bytes s (z_adler z) /\ k = 0) \/
   HI s (z_adler z) H k).

(** After the header stages: bytes [k, k') of [H] were put; those not flushed are pending; either the header is
    done ([None]: BUSY, nothing pending) or the call returns Z_OK with the output space full. *)
Definition hdr_post (HI : hdr_inv) (s : dstate) (z : strm) (H : list Z) (k : Z)
    (s' : dstate) (z' : strm) (r : option Z) : Prop :=
  core_eq s s' /\ outok s' /\ d_wrap s' = d_wrap s /\ d_gzhead s' = d_gzhead s /\ d_bi_valid s' = d_bi_valid s /\
  exists x k', k <= k' <= Zlength H /\ x ++ pend s' = sublist k k' H /\ zout_step z z' x (z_adler z') /\
  match r with
  | None => k' = Zlength H /\ d_status s' = BUSY_STATE /\ d_pending s' = 0 /\ d_po s' = 0 /\
            z_adler z' = hdr_adler (d_wrap s) (z_adler z) /\ d_last_flush s' = d_last_flush s
  | Some c => c = Z_OK /\ z_avail_out z' = 0 /\ d_pending s' <> 0 /\ d_last_flush s' = -1 /\
              ((d_status s' = BUSY_STATE /\ k' = Zlength H /\ z_adler z' = hdr_adler (d_wrap s) (z_adler z)) \/
               HI s' (z_adler z') H k')
  end.

Record hdr_facts (HI : hdr_inv) : Prop := {
  hf_frame : forall s s' a H k, HI s a H k ->
    d_status s' = d_status s -> d_gzindex s' = d_gzindex s -> d_gzhead s' = d_gzhead s ->
    d_wrap s' = d_wrap s -> d_pending_buf_size s' = d_pending_buf_size s -> HI s' a H k;
  hf_status : forall s a H k, HI s a H k ->
    d_wrap s = 2 /\ (exists h, d_gzhead s = Some h) /\
    (d_status s = EXTRA_STATE \/ d_status s = NAME_STATE \/ d_status s = COMMENT_STATE \/
     d_status s = HCRC_STATE) /\
    (exists xfl, H = gz_hdr_bytes (d_gzhead s) xfl) /\ 10 <= k < Zlength H;
  hf_run : forall s z H k, hdr_pre HI s z H k ->
    exists s' z' r, hdr_stages s z = Some (s', z', r) /\ hdr_post HI s z H k s' z' r
}.
