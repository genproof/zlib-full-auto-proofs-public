(** * Core part of the deflate law theory: the specifications of the parts

    Each part is a [Prop] proved in its own file (as a theorem with the parts it uses as hypotheses, e.g.
    [fast_ok : fill_spec -> ins_spec -> lm_spec -> tally_spec -> fbo_spec -> fpend_spec -> fast_spec]), so that
    the parts are independent and every part's theorem is closed.  LTCore.v assembles them. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCW.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Streams during a call *)

(** strm->adler is a checksum of the stream's kind (wrap 1: a valid Adler-32, wrap 2: 32 bits). *)
Definition adler_ok (wrap a : Z) : Prop :=
  (wrap = 1 -> Zlib.proof.adler32.Model.adler_valid a) /\ (wrap = 2 -> 0 <= a < 4294967296).

(** The input side and the output side of the stream during a call (no wrap-around of the counters). *)
Definition zin_in (z : strm) : Prop :=
  bytes (z_in z) /\ 0 <= z_next_in z /\ 0 <= z_avail_in z <= 1073741824 /\
  z_next_in z + z_avail_in z <= Zlength (z_in z) /\ 0 <= z_total_in z < 18446744073709551616.
Definition zout_ok (z : strm) : Prop :=
  0 <= z_avail_out z /\ 0 <= z_total_out z /\ z_total_out z + z_avail_out z <= 2199023255552.
Definition zall (z : strm) : Prop := zin_in z /\ zout_ok z.

(** [z'] is [z] after writing [x] at next_out, nothing else. *)
Definition zout_only (z z' : strm) (x : list Z) : Prop :=
  z_in z' = z_in z /\ z_next_in z' = z_next_in z /\ z_avail_in z' = z_avail_in z /\
  z_total_in z' = z_total_in z /\ z_adler z' = z_adler z /\ z_msg z' = z_msg z /\
  z_out z' = z_out z ++ x /\ z_avail_out z' = z_avail_out z - Zlength x /\
  z_total_out z' = z_total_out z + Zlength x.

(** pending_buf only grows: same length, defined bytes stay defined, the defined bytes stay bytes. *)
Definition pb_grow (o : outbuf) (m : list bool) (o' : outbuf) (m' : list bool) : Prop :=
  Zlength (o_buf o') = Zlength (o_buf o) /\ Zlength m' = Zlength m /\
  (forall i, Znth i m = true -> Znth i m' = true) /\
  (mb_ok (mkMB (o_buf o) m) -> mb_ok (mkMB (o_buf o') m')).

(** The configuration part of the trees state. *)
Definition tr_cfg (t : tstate) : Z * Z * Z * Z :=
  (tr_lit_bufsize t, tr_sym_end t, tr_level t, tr_strategy t).

(** ** Field frames: the state with the fields a function may change blanked *)

(** fill_window changes the window, ins_h, prev, head, block_start, strstart, match_start, lookahead, insert,
    high_water, slid. *)
Definition fw_keep (s : dstate) : dstate :=
  mkDS (d_status s) (d_po s) (d_wrap s) (d_gzhead s) (d_gzindex s) (d_method s) (d_last_flush s)
       (d_w_size s) (d_w_bits s) (d_w_mask s) (mkMB [] []) (d_window_size s) [] [] 0
       (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s)
       0 (d_match_length s) (d_prev_match s) (d_match_available s) 0 0 0 (d_prev_length s)
       (d_max_chain_length s) (d_max_lazy_match s) (d_good_match s) (d_nice_match s) 0 0 0
       (d_pending_buf_size s) (d_tr s) (d_pbm s).

(** INSERT_STRING changes ins_h, prev, head. *)
Definition hc_keep (s : dstate) : dstate := set_d_ins_h (set_d_prev (set_d_head s []) []) 0.

(** flush_pending changes pending_out and the output part of the trees state (pending_buf, pending, the bits)
    with its mask. *)
Definition fp_keep (s : dstate) : dstate :=
  set_d_po (set_d_pbm (set_d_tr s (set_out (d_tr s) (mkOut [] 0 0 0 0))) []) 0.

(** FLUSH_BLOCK_ONLY changes the trees state, its mask, pending_out and block_start. *)
Definition fbo_keep (s : dstate) : dstate :=
  set_d_block_start (set_d_po (set_d_pbm (set_d_tr s (init_tstate 0)) []) 0) 0.

(** ** fill_window (part FILL) *)
Definition fill_pre (s : dstate) : Prop := prm s /\ wstruct s /\ wpos s /\ wwin s /\ chain_ok s.

Definition fill_spec : Prop :=
  forall s z, fill_pre s -> zall z -> adler_ok (d_wrap s) (z_adler z) ->
  exists s' z' k d,
    c_fill_window s z = Some (s', z') /\
    fill_pre s' /\ fw_keep s' = fw_keep s /\ zstep (d_wrap s) z z' k [] /\
    (d = 0 \/ (d = d_w_size s /\ d_w_size s + MAX_DIST s <= d_strstart s)) /\
    d_strstart s' = d_strstart s - d /\ d_block_start s' = d_block_start s - d /\
    (d = 0 -> d_match_start s' = d_match_start s) /\
    (d <> 0 -> d_match_start s' = u32 (d_match_start s - d)) /\
    d_lookahead s' = d_lookahead s + k /\
    d_strstart s' < d_w_size s + MAX_DIST s /\
    (MIN_LOOKAHEAD <= d_lookahead s' \/ z_avail_in z' = 0) /\
    Z.min (d_window_size s) (d_strstart s' + d_lookahead s' + WIN_INIT) <= d_high_water s'.

(** ** INSERT_STRING and longest_match (part LM) *)

(** The closure part of [chain_with] (no condition on head). *)
Definition chain_closed (s : dstate) (n l : Z) (G : Z -> Prop) : Prop :=
  (forall v, G v -> v = 0 \/ 0 < v < n) /\
  (forall q, G q -> 0 < q -> l <= q -> G (Znth (Z.land q (d_w_mask s)) (d_prev s))).

(** INSERT_STRING(s, p, h) for a position [p] whose slot [p & w_mask] holds no other live entry. *)
Definition ins_spec : Prop :=
  forall s p n l G,
    prm s -> wstruct s -> chain_with s n l G ->
    0 <= p < 65536 -> p + 2 < Zlength (mb_val (d_window s)) -> Znth (p + 2) (mb_def (d_window s)) = true ->
    n - d_w_size s <= p -> p - d_w_size s < l ->
    exists s' h,
      c_insert_string s p = Some (s', h) /\
      hc_keep s' = hc_keep s /\ wstruct s' /\ G h /\
      chain_with s' (Z.max n (p + 1)) l (fun v => G v \/ v = p) /\
      chain_closed s' n l G.

(** longest_match(s, cur) from a chain entry [cur] in [lim s, strstart), with the window defined up to
    strstart + MAX_MATCH. *)
Definition lm_spec : Prop :=
  forall s cur n l G,
    prm s -> wstruct s -> chain_closed s n l G -> n <= d_strstart s -> l <= lim s ->
    G cur -> 0 < cur -> lim s <= cur ->
    0 <= d_prev_length s <= MAX_MATCH -> MIN_MATCH <= d_lookahead s ->
    d_strstart s + d_lookahead s <= d_window_size s ->
    d_strstart s + MAX_MATCH < Zlength (mb_val (d_window s)) ->
    (forall i, 0 <= i <= d_strstart s + MAX_MATCH -> Znth i (mb_def (d_window s)) = true) ->
    exists ms ml,
      c_longest_match s cur = Some (set_d_match_start s ms, ml) /\
      0 <= ml <= MAX_MATCH /\ ml <= d_lookahead s /\
      (ms = d_match_start s \/ (lim s <= ms /\ 0 < ms < d_strstart s)) /\
      (d_prev_length s < ml -> lim s <= ms /\ 0 < ms < d_strstart s).

(** ** The trees part (part TREES): the _tr_tally macros and _tr_flush_block *)

Definition tally_frame (t : tstate) (m : list bool) (t' : tstate) (m' : list bool) : Prop :=
  tr_cfg t' = tr_cfg t /\ tr_matches t' = tr_matches t /\
  o_pending (tr_out t') = o_pending (tr_out t) /\ o_bi_buf (tr_out t') = o_bi_buf (tr_out t) /\
  o_bi_valid (tr_out t') = o_bi_valid (tr_out t) /\ o_bi_used (tr_out t') = o_bi_used (tr_out t) /\
  pb_grow (tr_out t) m (tr_out t') m'.

Definition tally_spec : Prop :=
  (forall t m syms c,
     tree_ok t m syms -> Zlength syms <= tr_lit_bufsize t - 2 -> 0 <= c < 256 ->
     exists t' m',
       c_tr_tally_lit (t, m) c = Some ((t', m'), 3 * Zlength syms + 3 =? tr_sym_end t) /\
       tree_ok t' m' (syms ++ [(0, c)]) /\ tally_frame t m t' m') /\
  (forall t m syms dist len,
     tree_ok t m syms -> Zlength syms <= tr_lit_bufsize t - 2 -> 1 <= dist <= 32768 -> 0 <= len <= 255 ->
     exists t' m',
       c_tr_tally_dist (t, m) dist len = Some ((t', m'), 3 * Zlength syms + 3 =? tr_sym_end t) /\
       tree_ok t' m' (syms ++ [(dist, len)]) /\ tally_frame t m t' m').

(** _tr_flush_block on a state with a block of symbols (level > 0: deflate_fast / slow / rle / huff). *)
Definition trflush_spec : Prop :=
  forall t m syms buf sl last,
    flush_pre t syms -> tree_ok t m syms -> 0 < tr_level t -> 0 <= last <= 1 ->
    mb_ok (mkMB (o_buf (tr_out t)) m) -> sl = blk_len syms ->
    match buf with Some b => Zlength b = sl /\ bytes b /\ sl <= 65535 | None => True end ->
    exists t' m' kind,
      c_tr_flush_block (t, m) buf sl last = Some ((t', m'), kind) /\
      (t', kind) = tr_flush_block t buf sl last /\
      tree_ok t' m' [] /\ tr_cfg t' = tr_cfg t /\ tr_matches t' = 0 /\
      bits_ok (tr_out t') /\ (last = 1 -> o_bi_valid (tr_out t') = 0) /\
      pb_grow (tr_out t) m (tr_out t') m' /\
      mb_defined (mkMB (o_buf (tr_out t')) m') 0 (o_pending (tr_out t')).

(** ** flush_pending and FLUSH_BLOCK_ONLY (part FLUSH) *)
Definition fpend_spec : Prop :=
  forall s z, outok s -> zout_ok z ->
  exists s' z' x,
    c_flush_pending s z = Some (s', z') /\ zout_only z z' x /\ bytes x /\
    Zlength x = Z.min (d_pending s + d_bi_valid s / 8) (z_avail_out z) /\
    d_pending s' = d_pending s + d_bi_valid s / 8 - Zlength x /\
    d_bi_valid s' = d_bi_valid s mod 8 /\
    outok s' /\ Gb s' (z_total_out z') = Gb s (z_total_out z) /\
    fp_keep s' = fp_keep s /\
    pb_grow (tr_out (d_tr s)) (d_pbm s) (tr_out (d_tr s')) (d_pbm s').

(** FLUSH_BLOCK_ONLY(s, last) at a point where the symbols [syms] cover [block_start, strstart). *)
Definition fbo_pre (s : dstate) (z : strm) (syms : list (Z * Z)) (last : Z) : Prop :=
  prm s /\ wstruct s /\ 0 < d_level s /\
  tree_ok (d_tr s) (d_pbm s) syms /\ Zlength syms <= d_L s - 1 /\
  blk_len syms = d_strstart s - d_block_start s /\
  d_block_start s <= d_strstart s /\ d_strstart s - d_block_start s <= 16777216 /\
  (0 <= d_block_start s ->
     d_strstart s - d_block_start s <= 65535 /\ d_strstart s <= Zlength (mb_val (d_window s)) /\
     forall i, d_block_start s <= i < d_strstart s -> Znth i (mb_def (d_window s)) = true) /\
  outok s /\ quiet s /\ 0 <= last <= 1 /\ zout_ok z.

Definition fbo_spec : Prop :=
  forall s z syms last, fbo_pre s z syms last ->
  exists s' z' x buf,
    c_flush_block_only s z last = Some (s', z') /\
    (0 <= d_block_start s ->
       exists b, buf = Some b /\ Zlength b = d_strstart s - d_block_start s /\ bytes b) /\
    (d_block_start s < 0 -> buf = None) /\
    zout_only z z' x /\ bytes x /\
    Gb s' (z_total_out z') =
      ev_after (DFlush (Gb s (z_total_out z)) (d_tr s) syms buf (d_strstart s - d_block_start s) last) /\
    fbo_keep s' = fbo_keep s /\ d_block_start s' = d_strstart s /\
    tree_ok (d_tr s') (d_pbm s') [] /\ tr_cfg (d_tr s') = tr_cfg (d_tr s) /\ d_matches s' = 0 /\
    outok s' /\ d_bi_valid s' <= 7 /\ (last = 1 -> d_bi_valid s' = 0) /\
    (d_pending s' = 0 \/ z_avail_out z' = 0).

(** ** The compression functions (parts STORED, FAST, SLOW, HUFF, RLE) *)
Definition compress_pre (s : dstate) (z : strm) (flush : Z) : Prop :=
  W s /\ outok s /\ quiet s /\ 0 <= flush <= 5 /\ zin_ok z /\ 0 <= d_wrap s <= 2 /\
  adler_ok (d_wrap s) (z_adler z).

Definition comp_spec (f : Z) (c : dstate -> strm -> Z -> option (dstate * strm * bstate)) : Prop :=
  forall s z flush, compress_pre s z flush -> fn_of s = f ->
    exists s' z' bs evs, c s z flush = Some (s', z', bs) /\ cpost W s z flush s' z' bs evs.

Definition stored_spec : Prop := comp_spec 0 c_deflate_stored.
Definition fast_spec : Prop := comp_spec 1 c_deflate_fast.
Definition slow_spec : Prop := comp_spec 2 c_deflate_slow.
Definition huff_spec : Prop := comp_spec 3 c_deflate_huff.
Definition rle_spec : Prop := comp_spec 4 c_deflate_rle.

(** ** deflate_stored with Z_FINISH and room for everything finishes (part LIVE) *)
Definition live_spec : Prop :=
  forall s z s' z' bs,
    W s -> outok s -> quiet s -> zin_ok z -> 0 <= d_wrap s <= 2 -> adler_ok (d_wrap s) (z_adler z) ->
    d_level s = 0 ->
    stored_hdr s + 5 * ((ub s + z_avail_in z) / MAX_STORED) + ub s + z_avail_in z <= z_avail_out z ->
    c_deflate_stored s z Z_FINISH = Some (s', z', bs) -> bs = finish_done.

(** ** deflateInit2_ (part INIT), deflateSetDictionary (part DICT): the facts of core_facts for [W] *)
Definition init_spec : Prop :=
  forall level method wbits mem strategy z,
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
                (if wrap_of wbits =? 2 then 0 else 1) None.

Definition dict_spec : Prop :=
  forall s z d,
    W s -> d_status s = INIT_STATE -> 0 <= d_wrap s <= 1 ->
    d_strstart s = 0 -> d_lookahead s = 0 -> d_block_start s = 0 -> d_sym_next s = 0 ->
    bytes d -> Zlength d <= 32768 -> 0 <= z_total_in z <= 1099511627776 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' k,
      c_deflateSetDictionary s z (Some d) = Some (s', z', Z_OK) /\ W s' /\
      api_eq s s' /\ out_eq s s' /\ same_prm s s' /\
      d_lookahead s' = 0 /\ d_strstart s' = d_block_start s' /\ (d_strstart s' = 0 <-> d = []) /\
      d_sym_next s' = 0 /\ 0 <= k <= Zlength d /\
      z' = mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z + k) (z_out z) (z_avail_out z)
                (z_total_out z)
                (if d_wrap s =? 1 then Zlib.proof.adler32.Model.ref_adler32 (z_adler z) d else z_adler z)
                (z_msg z).
