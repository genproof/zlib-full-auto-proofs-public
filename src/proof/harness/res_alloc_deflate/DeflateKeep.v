(* One deflate() call keeps the sizes of the stream's allocations: the window (2 * w_size bytes), prev (w_size
   Pos), head (hash_size Pos) and pending_buf (4 * lit_bufsize bytes) are those deflateInit2_ allocated, so
   deflateEnd gives back the bytes deflateInit2_ took (law res_free_deflate), and the gzip header pointer is
   unchanged ([DeflateKit.dkeep]).  From the stage facts of deflate()'s body proof (DeflateFacts.v, MainDeflate.v,
   GrowCompressR.v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
Require Import Zlib.proof.deflate.DSpec.
(* deflate()'s body proof loads the stage facts (DeflateFacts) and the facts of the compressors (GrowCompressR). *)
Require Zlib.proof.deflate.Body_deflate.
Import Zlib.proof.deflate.DeflateFacts Zlib.proof.deflate.GrowCompressR.
#[local] Existing Instance DCS.CS.

(** The same opacity settings as GrowCompressR.v: the kernel must not unfold the loops (binary fuel). *)
Local Strategy expand [bind].
Local Strategy opaque [loop loop2].
#[local] Typeclasses Opaque rd wr guard bind
  c_put_byte c_put_short c_send_bits c_send_code c_bi_flush c_bi_windup c_send_codes c_send_tree_loop
  c_send_tree c_send_bl_lens c_send_all_trees c_d_code c_send_symbol c_compress_loop c_compress_block
  c_tr_stored_block c_tr_flush_bits.
#[local] Hint Rewrite dproj_set_d_status dproj_set_d_po dproj_set_d_wrap dproj_set_d_gzindex dproj_set_d_method
  dproj_set_d_last_flush dproj_set_d_w_bits dproj_set_d_w_mask dproj_set_d_window_size dproj_set_d_ins_h
  dproj_set_d_hash_bits dproj_set_d_hash_mask dproj_set_d_hash_shift dproj_set_d_block_start
  dproj_set_d_match_length dproj_set_d_prev_match dproj_set_d_match_available dproj_set_d_strstart
  dproj_set_d_match_start dproj_set_d_lookahead dproj_set_d_prev_length dproj_set_d_max_chain_length
  dproj_set_d_max_lazy_match dproj_set_d_good_match dproj_set_d_nice_match dproj_set_d_insert dproj_set_d_high_water
  dproj_set_d_slid dproj_set_d_pending_buf_size dproj_set_d_pbm dproj_incr_matches dproj_clamp_insert
  dproj_add_insert dproj_upd_high_water dproj_set_insert_end dproj_set_d_bi_used dproj_set_d_matches : dprdb.

(** ** deflate_stored keeps the sizes for any avail_out

    GrowCompressR proves deflate_stored's facts with avail_out a uInt, which the output facts need; the sizes
    of the state do not depend on it.  Here the state half alone, so that the compression stage needs no
    range of the stream after the header stages. *)
Lemma ds_body_dlen flush mb s z x : ds_body flush mb (s, z) = Some x ->
  match x with inl (s', _) => dlen s s' | inr (s', _, _) => dlen s s' end.
Proof.
  unfold ds_body. intros H. gdec; gfacts.
  all: repeat match goal with
       | E : c_tr_stored_block (d_out _) _ _ _ = Some _ |- _ =>
           let A := fresh "A" in
           pose proof (ol_tr_stored_block _ _ _ _ _ _ E) as A; cbn [fst] in A; clear E
       | E : c_pb_wr _ _ _ = Some _ |- _ => apply gc_pb_wr in E
       | E : out_put _ _ = Some _ |- _ => apply gc_out_put in E
       | E : mb_read _ _ _ = Some _ |- _ => apply DeflateKit.mb_read_length in E
       | E : guard (_ =? _) = Some _ |- _ => apply gc_guard_eq in E
       end.
  all: gconj; dclose.
Qed.

Lemma ds_loop_dlen flush mb s z s' z' last : loop FUEL (ds_body flush mb) (s, z) = Some (s', z', last) ->
  dlen s s'.
Proof.
  intros H.
  refine (loop_pre FUEL (ds_body flush mb) (fun a a' => dlen (fst a) (fst a'))
            (fun r => (fst (fst r), snd (fst r))) _ _ (s, z) (s', z', last) H).
  - intros a b c H1 H2. exact (dlen_trans _ _ _ H1 H2).
  - intros [s1 z1] x E. apply ds_body_dlen in E. destruct x as [[s2 z2]|[[s2 z2] r2]]; exact E.
Qed.

Lemma ds_tail_dlen s z f last r : ds_tail s z f last = Some r -> dlen s (fst (fst r)).
Proof.
  intros H. unfold ds_tail in H. gdec; gfacts.
  all: repeat match goal with
       | E : c_tr_stored_block (d_out _) _ _ _ = Some _ |- _ =>
           let A := fresh "A" in
           pose proof (ol_tr_stored_block _ _ _ _ _ _ E) as A; cbn [fst] in A; clear E
       end.
  all: gconj; cbn [fst snd].
  all: repeat match goal with
       | H : _ = true |- _ => clear H | H : _ = false |- _ => clear H | H : guard _ = _ |- _ => clear H
       | H : rds _ _ _ = _ |- _ => clear H | H : out_grow _ _ |- _ => clear H | H : zpos _ _ |- _ => clear H
       | H : zsame _ _ |- _ => clear H
       end.
  all: dpr.
Qed.

Lemma stored_dkeep s z f r : c_deflate_stored s z f = Some r -> dkeep s (fst (fst r)).
Proof.
  intros H. rewrite c_deflate_stored_split in H.
  destruct (loop _ _ _) as [[[s1 z1] last]|] eqn:E1; [|discriminate].
  destruct (c_ds_window _ _ _) as [s2|] eqn:E2; [|discriminate].
  apply ds_loop_dlen in E1. apply gc_ds_window in E2. apply ds_tail_dlen in H. apply dlen_dkeep.
  exact (dlen_trans _ _ _ E1 (dlen_trans _ _ _ E2 (dlen_trans _ _ _ (dlen_upd_high_water _) H))).
Qed.

(** ** The compression stage keeps the sizes *)
Lemma compress_func_dkeep s z f r : c_compress_func s z f = Some r -> dkeep s (fst (fst r)).
Proof.
  intros H. unfold c_compress_func in H.
  destruct (d_level s =? 0); [exact (stored_dkeep _ _ _ _ H)|].
  destruct (d_strategy s =? Z_HUFFMAN_ONLY); [exact (proj2 (grow_deflate_huff _ _ _ _ H))|].
  destruct (d_strategy s =? Z_RLE); [exact (proj2 (grow_deflate_rle _ _ _ _ H))|].
  inv_bind H. destruct (x =? 0); [exact (stored_dkeep _ _ _ _ H)|].
  destruct (x =? 1); [exact (proj2 (grow_deflate_fast _ _ _ _ H)) | exact (proj2 (grow_deflate_slow _ _ _ _ H))].
Qed.

Lemma compress_dkeep f s z s' z' o : c_deflate_compress s z f = Some (s', z', o) -> dkeep s s'.
Proof.
  intros H. cbv [c_deflate_compress] in H.
  match type of H with (if ?b then _ else _) = _ => destruct b end;
    [|inversion H; subst; apply dkeep_refl].
  inv_bind H. destruct x as [[s1 z1] bs]. apply compress_func_dkeep in Ha. cbn [fst snd] in Ha.
  destruct bs; crunch;
    (repeat match goal with |- context [if ?b then _ else _] => destruct b end);
    apply (dkeep_dsame _ _ _ Ha); ds_close.
Qed.

(** ** deflate() *)
Lemma then_stage_dkeep r k s s' z' o :
  (forall s1 z1 o1, r = Some (s1, z1, o1) -> dkeep s s1) ->
  (forall s1 z1 s2 z2 o2, r = Some (s1, z1, None) -> k s1 z1 = Some (s2, z2, o2) -> dkeep s1 s2) ->
  then_stage r k = Some (s', z', o) -> dkeep s s'.
Proof.
  intros H1 H2 H. apply then_stage_inv in H.
  destruct H as (s1 & z1 & o1 & E & [(_ & -> & _) | (-> & K)]).
  - exact (H1 _ _ _ E).
  - exact (dkeep_trans _ _ _ (H1 _ _ _ E) (H2 _ _ _ _ _ E K)).
Qed.

Lemma c_deflate_dkeep : forall s z flush s' z' code,
  strm_ranges z -> c_deflate s z flush = Some (s', z', code) -> dkeep s s'.
Proof.
  intros s z flush s' z' code _ H. unfold c_deflate in H.
  match type of H with (if ?b then _ else _) = _ => destruct b end; [inversion H; subst; apply dkeep_refl|].
  inv_bind H. destruct x as [[s1 z1] o].
  assert (K : dkeep s s1).
  { clear H. apply then_stage_inv in Ha. destruct Ha as (sa & za & oa & Ea & [(Hn & -> & _) | (-> & Ka)]).
    - destruct oa as [c|]; [|congruence].
      refine (proj2 (facts_entry flush s z sa za (Some c) _)). unfold c_entry2. rewrite Ea. reflexivity.
    - apply (dkeep_trans _ (init_busy sa)).
      { refine (proj2 (facts_entry flush s z (init_busy sa) za None _)). unfold c_entry2. rewrite Ea. reflexivity. }
      rewrite c_deflate_zlib_header_eq in Ka.
      repeat (revert Ka; apply then_stage_dkeep;
        [ intros ? ? ? E;
          first [ exact (proj2 (facts_zlib 0 _ _ _ _ _ E)) | exact (proj2 (facts_gzip 0 _ _ _ _ _ E))
                | exact (proj2 (facts_extra 0 _ _ _ _ _ E)) | exact (proj2 (facts_name 0 _ _ _ _ _ E))
                | exact (proj2 (facts_comment 0 _ _ _ _ _ E)) | exact (proj2 (facts_hcrc 0 _ _ _ _ _ E)) ]
        | intros ? ? ? ? ? _ Ka ]).
      exact (compress_dkeep _ _ _ _ _ _ Ka). }
  destruct o as [r|]; [inversion H; subst; exact K|].
  apply (dkeep_trans _ _ _ K). refine (proj2 (facts_trailer flush s1 z1 s' z' (Some code) _)).
  unfold c_trailer2. rewrite H. reflexivity.
Qed.
