(** * Core part of the deflate law theory: the invariant [W] of a live deflate state

    [W s] is what holds of the state between two API calls (and at the entry / exit of the compression
    functions).  It does not depend on what [core_eq] lets change (status, pending_out, wrap, gzhead, gzindex,
    last_flush, the output part of the trees state) nor on the configuration fields deflateTune sets
    (good_match, max_lazy_match, nice_match, max_chain_length).

    Window contents are NOT tracked: no fact of [core_facts] relates the output to the input bytes, only
    safety (the runs are [Some]), the bit / byte accounting and the block events. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTDefs.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The compression function of a state (c_compress_func's dispatch):
    0 deflate_stored, 1 deflate_fast, 2 deflate_slow, 3 deflate_huff, 4 deflate_rle *)
Definition fn_of (s : dstate) : Z :=
  if d_level s =? 0 then 0
  else if d_strategy s =? Z_HUFFMAN_ONLY then 3
  else if d_strategy s =? Z_RLE then 4
  else cfg_f (d_level s).

(** ** Sizes of the window and the hash arrays; the defined window bytes are bytes *)
Definition wstruct (s : dstate) : Prop :=
  Zlength (mb_val (d_window s)) = 2 * d_w_size s /\ mb_ok (d_window s) /\
  d_window_size s = 2 * d_w_size s /\
  Zlength (d_prev s) = d_w_size s /\ Zlength (d_head s) = d_hash_size s.

(** ** Positions *)
Definition wpos (s : dstate) : Prop :=
  0 <= d_lookahead s /\ 0 <= d_strstart s /\ d_strstart s + d_lookahead s <= d_window_size s /\
  d_block_start s <= d_strstart s /\ d_strstart s - d_block_start s <= 16777216 /\
  (d_block_start s < 0 -> MAX_DIST s < d_strstart s - d_block_start s) /\
  0 <= d_insert s <= d_strstart s /\ d_insert s <= d_w_size s /\
  0 <= d_high_water s <= d_window_size s.

(** ** Defined window bytes: everything read so far, and everything below high_water *)
Definition wwin (s : dstate) : Prop :=
  forall i, 0 <= i < Z.max (d_strstart s + d_lookahead s) (d_high_water s) ->
    Znth i (mb_def (d_window s)) = true.

(** ** Hash chains.  longest_match follows cur -> prev[cur & w_mask] while cur > limit
    ([lim s] = limit = strstart - MAX_DIST, or NIL); it is safe when every cur it visits is below strstart.
    [chain_with s n l G]: [G] is a set of chain entries, all NIL or in (0, n), containing every head entry and
    closed under prev for the entries >= l.  Stale prev entries (Z_FULL_FLUSH resets strstart to 0, deflate_fast
    skips insertions) are allowed: only the entries reachable from head matter. *)
Definition lim (s : dstate) : Z :=
  if d_strstart s >? MAX_DIST s then d_strstart s - MAX_DIST s else 0.

Definition chain_with (s : dstate) (n l : Z) (G : Z -> Prop) : Prop :=
  (forall v, G v -> v = 0 \/ 0 < v < n) /\
  (forall h, 0 <= h < d_hash_size s -> G (Znth h (d_head s))) /\
  (forall q, G q -> 0 < q -> l <= q -> G (Znth (Z.land q (d_w_mask s)) (d_prev s))).

Definition chain_ok (s : dstate) : Prop := exists G, chain_with s (d_strstart s) (lim s) G.

(** slide_hash's effect on head and prev (c_slide_hash also sets slid). *)
Definition slide_hc (s : dstate) : dstate :=
  set_d_prev (set_d_head s (map (slide_entry (d_w_size s)) (d_head s)))
             (map (slide_entry (d_w_size s)) (d_prev s)).

(** At level 0 the chains are not maintained; [matches] counts the window slides since (0: the chains are
    valid, 1: valid after one slide_hash, 2: deflateParams will CLEAR_HASH).  At a level > 0, [matches] is
    trees.c's counter, which the _tr_tally macros never increment: 0. *)
Definition whash (s : dstate) : Prop :=
  if d_level s =? 0 then
    (d_matches s = 0 /\ chain_ok s) \/ (d_matches s = 1 /\ chain_ok (slide_hc s)) \/ d_matches s = 2
  else d_matches s = 0 /\ chain_ok s.

(** ** The trees state with the symbols [syms] tallied since the last block (Overlay.flush_pre without the
    output part): sizes, the symbols in sym_buf (with their mask), the frequencies. *)
Definition tree_ok (t : tstate) (m : list bool) (syms : list (Z * Z)) : Prop :=
  let L := tr_lit_bufsize t in
  Zlength (o_buf (tr_out t)) = 4 * L /\ Zlength m = 4 * L /\
  tr_sym_next t = 3 * Zlength syms /\
  (forall x, In x syms -> valid_sym (fst x) (snd x)) /\
  sublist L (L + 3 * Zlength syms) (o_buf (tr_out t)) = sym_bytes syms /\
  sublist L (L + 3 * Zlength syms) m = repeat true (Z.to_nat (3 * Zlength syms)) /\
  (Zlength (fc (tr_ltree t)) = HEAP_SIZE /\ Zlength (dl (tr_ltree t)) = HEAP_SIZE /\
   (forall n, 0 <= n < HEAP_SIZE -> 0 <= Znth n (fc (tr_ltree t)) < 65536) /\
   forall c, 0 <= c < L_CODES -> Znth c (fc (tr_ltree t)) = lfreq syms c) /\
  (Zlength (fc (tr_dtree t)) = 2 * D_CODES + 1 /\ Zlength (dl (tr_dtree t)) = 2 * D_CODES + 1 /\
   (forall n, 0 <= n < 2 * D_CODES + 1 -> 0 <= Znth n (fc (tr_dtree t)) < 65536) /\
   forall c, 0 <= c < D_CODES -> Znth c (fc (tr_dtree t)) = dfreq syms c) /\
  (Zlength (fc (tr_bltree t)) = 2 * BL_CODES + 1 /\ Zlength (dl (tr_bltree t)) = 2 * BL_CODES + 1 /\
   (forall n, 0 <= n < 2 * BL_CODES + 1 -> 0 <= Znth n (fc (tr_bltree t)) < 65536) /\
   forall c, 0 <= c < BL_CODES -> Znth c (fc (tr_bltree t)) = 0) /\
  (Zlength (w_heap (tr_wk t)) = HEAP_SIZE /\ Zlength (w_depth (tr_wk t)) = HEAP_SIZE /\
   Zlength (w_bl_count (tr_wk t)) = MAX_BITS + 1 /\
   w_opt_len (tr_wk t) = 0 /\ w_static_len (tr_wk t) = 0).

(** What ev_ok requires of every symbol of a block, for the state's window size / level / strategy. *)
Definition sym_ok (s : dstate) (x : Z * Z) : Prop :=
  valid_sym (fst x) (snd x) /\
  (fst x <> 0 -> fst x <= MAX_DIST s) /\
  (4 <= d_level s -> d_strategy s <> Z_FILTERED -> fst x <> 0 -> snd x = 0 -> fst x <= TOO_FAR).

(** The symbols cover the window bytes [block_start, strstart - match_available) (deflate_slow keeps the byte
    at strstart - 1 pending while match_available); at level 0 there are none. *)
Definition wtrees (s : dstate) (syms : list (Z * Z)) : Prop :=
  tree_ok (d_tr s) (d_pbm s) syms /\ Zlength syms <= d_L s - 2 /\ Forall (sym_ok s) syms /\
  (d_level s = 0 -> syms = []) /\
  (d_level s <> 0 -> blk_len syms = d_strstart s - d_block_start s - d_match_available s).

(** ** The match state.  Without a pending byte, match_length and prev_length are below MIN_MATCH (deflate_fast
    tests match_length without a new search when hash_head is NIL; longest_match starts from prev_length).
    With one (deflate_slow only), the lazy candidate match_length / match_start found at strstart - 1. *)
Definition wmatch (s : dstate) : Prop :=
  0 <= d_match_length s <= MAX_MATCH /\ 0 <= d_prev_length s <= MAX_MATCH /\
  (d_match_available s = 0 \/ d_match_available s = 1) /\
  (d_match_available s = 0 -> d_match_length s < MIN_MATCH /\ d_prev_length s < MIN_MATCH) /\
  (d_match_available s = 1 ->
     fn_of s = 2 /\ 1 <= d_strstart s /\
     (MIN_MATCH <= d_match_length s ->
        d_match_length s <= d_lookahead s + 1 /\
        1 <= u32 (d_strstart s - 1 - d_match_start s) <= MAX_DIST s /\
        (d_match_length s = MIN_MATCH -> d_strategy s <> Z_FILTERED ->
         u32 (d_strstart s - 1 - d_match_start s) <= TOO_FAR))).

(** ** The invariant *)
Definition W (s : dstate) : Prop :=
  prm s /\ wstruct s /\ wpos s /\ wwin s /\ whash s /\ wmatch s /\
  (d_level s = 0 -> d_lookahead s = 0 /\ 0 <= d_block_start s) /\
  exists syms, wtrees s syms.
