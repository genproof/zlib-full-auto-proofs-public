(** * The gzip header pointer of the model state: set by deflateInit2_ to none, kept by deflate and deflateParams

    deflateSetHeader is the only function that sets [d_gzhead]; deflate and deflateParams only read it (the gzip
    header stages of deflate).  Main of law api_deterministic needs it for its two streams (no header: DSpec's
    [hdr_at (Some s)] is then empty). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DRep.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DModel4.
Require Import Zlib.proof.deflate.DeflateKit Zlib.proof.deflate.GrowCompress Zlib.proof.deflate.DeflateFacts.
Require Import Zlib.proof.deflate.GrowCompressR.
Require Zlib.proof.deflate.MainDeflate.

(** The kernel must not unfold the loops of the model (their fuel is huge). *)
Local Strategy expand [bind].
Local Strategy opaque [loop loop2].

(** ** deflate_stored keeps the gz_header

    GrowCompressR proves it together with [out_grow], which needs avail_out to be a uInt; the header pointer
    alone needs no hypothesis on the stream. *)
Lemma gz_ds_body flush mb s z x : ds_body flush mb (s, z) = Some x ->
  match x with
  | inl (s', _) => dlen s s'
  | inr (s', _, _) => dlen s s'
  end.
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

Lemma gz_ds_loop flush mb s z s' z' last : loop FUEL (ds_body flush mb) (s, z) = Some (s', z', last) -> dlen s s'.
Proof.
  intros H.
  refine (loop_gen FUEL (ds_body flush mb) (fun a r => dlen (fst a) (fst (fst r))) _ _ (s, z) (s', z', last) H).
  - intros [s1 z1] [[s2 z2] l2] E. apply gz_ds_body in E. exact E.
  - intros [s1 z1] [s2 z2] r E D. apply gz_ds_body in E. exact (dlen_trans _ _ _ E D).
Qed.

(** The projection rewrites of [dpr] (local to GrowCompressR). *)
#[local] Hint Rewrite dproj_set_d_status dproj_set_d_po dproj_set_d_wrap dproj_set_d_gzindex dproj_set_d_method dproj_set_d_last_flush dproj_set_d_w_bits dproj_set_d_w_mask dproj_set_d_window_size dproj_set_d_ins_h dproj_set_d_hash_bits dproj_set_d_hash_mask dproj_set_d_hash_shift dproj_set_d_block_start dproj_set_d_match_length dproj_set_d_prev_match dproj_set_d_match_available dproj_set_d_strstart dproj_set_d_match_start dproj_set_d_lookahead dproj_set_d_prev_length dproj_set_d_max_chain_length dproj_set_d_max_lazy_match dproj_set_d_good_match dproj_set_d_nice_match dproj_set_d_insert dproj_set_d_high_water dproj_set_d_slid dproj_set_d_pending_buf_size dproj_set_d_pbm dproj_incr_matches dproj_clamp_insert dproj_add_insert dproj_upd_high_water dproj_set_insert_end dproj_set_d_bi_used dproj_set_d_matches : dprdb.

Lemma gz_ds_tail s z f last r : ds_tail s z f last = Some r -> dlen s (fst (fst r)).
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

Lemma gz_stored s z f r : c_deflate_stored s z f = Some r -> d_gzhead (fst (fst r)) = d_gzhead s.
Proof.
  intros H. rewrite c_deflate_stored_split in H.
  destruct (loop _ _ _) as [[[s1 z1] last]|] eqn:E1; [|discriminate].
  destruct (c_ds_window _ _ _) as [s2|] eqn:E2; [|discriminate].
  apply gz_ds_loop in E1. apply gc_ds_window in E2. apply gz_ds_tail in H.
  exact (proj1 (dlen_trans _ _ _ E1 (dlen_trans _ _ _ E2 (dlen_trans _ _ _ (dlen_upd_high_water _) H)))).
Qed.

(** ** The compression stage keeps it *)
Lemma gz_compress_func s z f r : c_compress_func s z f = Some r -> d_gzhead (fst (fst r)) = d_gzhead s.
Proof.
  intros H. unfold c_compress_func in H.
  assert (K : forall c, compress_facts c -> c s z f = Some r -> d_gzhead (fst (fst r)) = d_gzhead s)
    by (intros c Hc E; exact (proj1 (proj2 (Hc s z f r E)))).
  destruct (d_level s =? 0); [exact (gz_stored _ _ _ _ H)|].
  destruct (d_strategy s =? Z_HUFFMAN_ONLY); [exact (K _ grow_deflate_huff H)|].
  destruct (d_strategy s =? Z_RLE); [exact (K _ grow_deflate_rle H)|].
  inv_bind H. destruct (x =? 0); [exact (gz_stored _ _ _ _ H)|].
  destruct (x =? 1); [exact (K _ grow_deflate_fast H) | exact (K _ grow_deflate_slow H)].
Qed.

(** A stage's result keeps the gz_header of the state [s]. *)
Definition gz_kept (r : option dres) (s : dstate) : Prop :=
  forall s' z' o, r = Some (s', z', o) -> d_gzhead s' = d_gzhead s.

Lemma gz_then r k s : gz_kept r s -> (forall s1 z1, r = Some (s1, z1, None) -> gz_kept (k s1 z1) s1) ->
  gz_kept (then_stage r k) s.
Proof.
  intros H1 H2 s' z' o E. apply then_stage_inv in E.
  destruct E as (s1 & z1 & o1 & E & [(_ & -> & ->) | (-> & E2)]).
  - exact (H1 _ _ _ E).
  - rewrite (H2 s1 z1 E s' z' o E2). exact (H1 _ _ _ E).
Qed.

Lemma gz_of_facts c : stage_facts c -> forall f s z, gz_kept (c f s z) s.
Proof. intros H f s z s' z' o E. exact (proj1 (proj2 (H f s z s' z' o E))). Qed.

Lemma gz_compress f s z : gz_kept (c_deflate_compress s z f) s.
Proof.
  intros s' z' o H. cbv [c_deflate_compress] in H.
  match type of H with (if ?b then _ else _) = _ => destruct b end; [|inversion H; subst; reflexivity].
  inv_bind H. destruct x as [[s1 z1] bs]. apply gz_compress_func in Ha. cbn [fst snd] in Ha.
  destruct bs; crunch;
    (repeat match goal with |- context [if ?b then _ else _] => destruct b end);
    (match goal with Ha : d_gzhead ?S1 = d_gzhead s |- d_gzhead ?X = _ =>
       assert (D : dsame S1 X) by ds_close; exact (eq_trans (proj1 D) Ha) end).
Qed.

(** ** deflate() keeps it *)
Lemma gz_chain f s z : gz_kept (MainDeflate.chain_model (fun f => f) f s z) s.
Proof.
  pose proof deflate_facts_proved as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _ & F9).
  unfold MainDeflate.chain_model.
  apply gz_then; [exact (gz_of_facts _ F1 f s z)|]; intros s1 z1 _.
  apply gz_then; [exact (gz_of_facts _ F2 f s1 z1)|]; intros s2 z2 _.
  apply gz_then; [exact (gz_of_facts _ F3 f s2 z2)|]; intros s3 z3 _.
  apply gz_then; [exact (gz_of_facts _ F4 f s3 z3)|]; intros s4 z4 _.
  apply gz_then; [exact (gz_of_facts _ F5 f s4 z4)|]; intros s5 z5 _.
  apply gz_then; [exact (gz_of_facts _ F6 f s5 z5)|]; intros s6 z6 _.
  apply gz_then; [exact (gz_of_facts _ F7 f s6 z6)|]; intros s7 z7 _.
  apply gz_then; [exact (gz_compress f s7 z7)|]; intros s8 z8 _.
  exact (gz_of_facts _ F9 f s8 z8).
Qed.

Lemma gz_deflate s z f s' z' rc : c_deflate s z f = Some (s', z', rc) -> d_gzhead s' = d_gzhead s.
Proof.
  unfold c_deflate. intros H.
  match type of H with (if ?b then _ else _) = _ => destruct b end; [inversion H; reflexivity|].
  apply (MainDeflate.chain_of_deflate (fun f => f)) in H.
  exact (gz_chain f s z _ _ _ H).
Qed.


(** ** deflateReset keeps it *)
Lemma gz_reset s z s' z' r : c_deflateReset s z = Some (s', z', r) -> d_gzhead s' = d_gzhead s.
Proof.
  unfold c_deflateReset, c_deflateResetKeep, c_lm_init. intros H. gdec.
  all: repeat match goal with E : c_clear_hash _ = Some _ |- _ => apply dsame_clear_hash, proj1 in E end.
  all: gnorm; congruence.
Qed.

(** The setters of deflateParams leave the header pointer alone. *)
Lemma gz_set_strategy s x : d_gzhead (set_d_strategy s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma gz_set_chain s x : d_gzhead (set_d_max_chain_length s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma gz_set_nice s x : d_gzhead (set_d_nice_match s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma gz_set_good s x : d_gzhead (set_d_good_match s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma gz_set_lazy s x : d_gzhead (set_d_max_lazy_match s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma gz_set_level s x : d_gzhead (set_d_level s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma gz_set_matches s x : d_gzhead (set_d_matches s x) = d_gzhead s. Proof. reflexivity. Qed.

Lemma det_gz_all :
  (forall vok sok sn level method wbits mem strategy a1 a2 a3 a4 a5 z s z' code,
     c_deflateInit2_ vok sok sn level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (Some s, z', code) ->
     d_gzhead s = None) /\
  (forall s z flush s' z' code,
     strm_ranges z -> c_deflate s z flush = Some (s', z', code) -> d_gzhead s' = d_gzhead s) /\
  (forall s z level strategy s' z' code,
     strm_ranges z -> c_deflateParams s z level strategy = Some (s', z', code) -> d_gzhead s' = d_gzhead s).
Proof.
  split; [|split].
  - intros vok sok sn level method wbits mem strategy a1 a2 a3 a4 a5 z s z' code H.
    unfold c_deflateInit2_ in H. gdec.
    all: try match goal with E : c_deflateReset _ _ = Some _ |- _ => apply gz_reset in E; rewrite E end.
    all: try match goal with E : c_deflateEnd _ _ = Some _ |- _ =>
           unfold c_deflateEnd in E; destruct (bad_state _); inversion E; subst end.
    all: reflexivity.
  - intros s z flush s' z' code _ H. exact (gz_deflate _ _ _ _ _ _ H).
  - intros s z level strategy s' z' code _ H.
    unfold c_deflateParams in H. gdec.
    all: try match goal with E : c_deflate _ _ _ = Some _ |- _ => apply gz_deflate in E end.
    all: repeat match goal with
         | E : c_clear_hash _ = Some _ |- _ => apply dsame_clear_hash, proj1 in E
         | E : c_slide_hash _ = Some _ |- _ => apply gc_slide_hash, proj1 in E
         end.
    all: rewrite ?gz_set_strategy, ?gz_set_chain, ?gz_set_nice, ?gz_set_good, ?gz_set_lazy, ?gz_set_level,
           ?gz_set_matches.
    all: repeat match goal with H : d_gzhead ?a = d_gzhead _ |- d_gzhead ?a = _ => rewrite H; clear H end.
    all: reflexivity.
Qed.

Lemma det_gz_init : forall vok sok sn level method wbits mem strategy a1 a2 a3 a4 a5 z s z' code,
  c_deflateInit2_ vok sok sn level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (Some s, z', code) ->
  d_gzhead s = None.
Proof. apply det_gz_all. Qed.

Lemma det_gz_deflate : forall s z flush s' z' code,
  strm_ranges z -> c_deflate s z flush = Some (s', z', code) -> d_gzhead s' = d_gzhead s.
Proof. apply det_gz_all. Qed.

Lemma det_gz_params : forall s z level strategy s' z' code,
  strm_ranges z -> c_deflateParams s z level strategy = Some (s', z', code) -> d_gzhead s' = d_gzhead s.
Proof. apply det_gz_all. Qed.
