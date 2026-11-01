(** * deflateSetDictionary: model facts.  CLEAR_HASH, fill_window and the dictionary loop keep the sizes of the
    allocations and the lengths of the buffers ([DictKit.dlen]), and fill_window and the loop keep the input
    object and the output side of the stream ([DictKit.zkeep]). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DictKit.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** Helpers (from GrowCompressR.v) *)

(** The kernel must never unfold the loops (binary fuel 2^40) when it compares a hypothesis before and after a
    [cbv]: the monad's [bind] is unfolded first. *)
Local Strategy expand [bind].
Local Strategy opaque [loop loop2].

Lemma gc_some_inj {A} (a b : A) : Some a = Some b -> a = b.
Proof. congruence. Qed.

Lemma gc_Zlength_upd {A} i (l : list A) v : Zlength (upd_Znth i l v) = Zlength l.
Proof.
  destruct (Z_le_gt_dec 0 i); [destruct (Z_lt_ge_dec i (Zlength l))|].
  - apply upd_Znth_Zlength; lia.
  - rewrite upd_Znth_out_of_range; auto; lia.
  - rewrite upd_Znth_out_of_range; auto; lia.
Qed.

Lemma gc_wr_len l i v l' : wr l i v = Some l' -> Zlength l' = Zlength l.
Proof. unfold wr. destruct (in_range i (Zlength l)); intros H; inversion H. apply gc_Zlength_upd. Qed.

Lemma gc_mb_write_len b lo src b' : mb_write b lo src = Some b' -> Zlength (mb_val b') = Zlength (mb_val b).
Proof.
  unfold mb_write. destruct (andb (0 <=? lo) (lo + Zlength src <=? Zlength (mb_val b))) eqn:E; intros H; inversion H.
  apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  cbn [mb_val]. pose proof (Zlength_nonneg src).
  rewrite !Zlength_app, !Zlength_sublist by lia. lia.
Qed.

Lemma loop_gen {A B} d (body : A -> option (A + B)) (P : A -> B -> Prop) :
  (forall a r, body a = Some (inr r) -> P a r) ->
  (forall a a' r, body a = Some (inl a') -> P a' r -> P a r) ->
  forall a r, loop d body a = Some r -> P a r.
Proof.
  intros H1 H2 a r H. apply loop_runs in H. induction H; eauto.
Qed.

Ltac gnorm := cbn [d_status d_po d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_block_start d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size d_tr d_pbm set_d_status set_d_po set_d_wrap set_d_gzhead set_d_gzindex set_d_method set_d_last_flush set_d_w_size set_d_w_bits set_d_w_mask set_d_window set_d_window_size set_d_prev set_d_head set_d_ins_h set_d_hash_size set_d_hash_bits set_d_hash_mask set_d_hash_shift set_d_block_start set_d_match_length set_d_prev_match set_d_match_available set_d_strstart set_d_match_start set_d_lookahead set_d_prev_length set_d_max_chain_length set_d_max_lazy_match set_d_good_match set_d_nice_match set_d_insert set_d_high_water set_d_slid set_d_pending_buf_size set_d_tr set_d_pbm set_d_trm z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg set_z_in set_z_next_in set_z_avail_in set_z_total_in set_z_out set_z_avail_out set_z_total_out set_z_adler set_z_msg set_d_out set_d_pb set_d_bi_used set_d_matches d_trm d_out d_pb fst snd tr_out tr_lit_bufsize set_out set_matches o_buf mb_val lm_s] in *.

Ltac gstep :=
  match goal with
  | x : (_ * _)%type |- _ => destruct x
  | x : cstate |- _ => destruct x
  | x : cout |- _ => destruct x
  | x : dexit |- _ => destruct x
  | H : Some _ = Some _ |- _ => apply gc_some_inj in H
  | H : None = Some _ |- _ => discriminate H
  | H : inl _ = inl _ |- _ => injection H as H
  | H : inr _ = inr _ |- _ => injection H as H
  | H : inl _ = inr _ |- _ => discriminate H
  | H : inr _ = inl _ |- _ => discriminate H
  | H : (_, _) = (_, _) |- _ => injection H as; subst
  | H : ?x = _ |- _ => is_var x; subst x
  | H : _ = ?x |- _ => is_var x; subst x
  | H : bind ?a _ = Some _ |- _ =>
      let E := fresh "E" in
      destruct a eqn:E; unfold bind at 1 in H; cbv beta iota zeta in H; [| discriminate H]
  | H : (if ?b then _ else _) = Some _ |- _ => destruct b eqn:?
  | H : match ?x with _ => _ end = Some _ |- _ => destruct x eqn:?
  end.

Ltac gdec := repeat (gstep; cbv beta iota zeta in *).

Ltac gconj := repeat match goal with H : _ /\ _ |- _ => destruct H end.

Ltac gclose :=
  unfold dlen, zkeep, incr_matches, clamp_insert, upd_high_water, add_insert, set_insert_end in *; gconj;
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b
  | H : context [if ?b then _ else _] |- _ => destruct b
  end;
  gnorm; repeat split; try congruence.


Lemma gc_read_buf s z n z' d : c_read_buf s z n = Some (z', d) -> zkeep z z'.
Proof. unfold c_read_buf. intros H. gdec; gclose. Qed.

Lemma gc_insert_string s str s' h : c_insert_string s str = Some (s', h) -> dlen s s'.
Proof.
  unfold c_insert_string. intros H. gdec.
  repeat match goal with E : wr _ _ _ = Some _ |- _ => apply gc_wr_len in E end. gclose.
Qed.

Lemma gc_slide_hash s s' : c_slide_hash s = Some s' -> dlen s s'.
Proof. unfold c_slide_hash. intros H. gdec. gclose; rewrite Zlength_map; reflexivity. Qed.

Lemma gc_fw_slide s more s' m : c_fw_slide s more = Some (s', m) -> dlen s s'.
Proof.
  unfold c_fw_slide. intros H. gdec.
  all: repeat match goal with
       | E : mb_write _ _ _ = Some _ |- _ => apply gc_mb_write_len in E
       | E : c_slide_hash _ = Some _ |- _ => apply gc_slide_hash in E end.
  all: try apply dlen_refl.
  all: gclose.
Qed.


Lemma loop_pre {A B} d (body : A -> option (A + B)) (R : A -> A -> Prop) (g : B -> A) :
  (forall a b c, R a b -> R b c -> R a c) ->
  (forall a x, body a = Some x -> R a (match x with inl a' => a' | inr r => g r end)) ->
  forall a r, loop d body a = Some r -> R a (g r).
Proof.
  intros T H. apply (loop_gen d body (fun a r => R a (g r))).
  - intros a r E. apply (H _ _ E).
  - intros a a' r E Hr. eapply T; [apply (H _ _ E) | exact Hr].
Qed.

Lemma gc_fw_insert_body a x : fw_insert_body a = Some x ->
  dlen (fst a) (fst (match x with inl a' => a' | inr r => (r, 0) end)).
Proof.
  destruct a as [s1 str]. intros Hb. unfold fw_insert_body in Hb. gdec.
  all: repeat match goal with E : wr _ _ _ = Some _ |- _ => apply gc_wr_len in E end.
  all: gclose.
Qed.

Lemma gc_fw_insert_loop a s' : loop FUEL fw_insert_body a = Some s' -> dlen (fst a) s'.
Proof.
  intros H. apply (loop_pre _ _ (fun a a' => dlen (fst a) (fst a')) (fun r => (r, 0))) in H.
  - exact H.
  - intros a1 b c H1 H2. exact (dlen_trans _ _ _ H1 H2).
  - exact gc_fw_insert_body.
Qed.

Lemma gc_fw_insert s s' : c_fw_insert s = Some s' -> dlen s s'.
Proof.
  unfold c_fw_insert. intros H. gdec; [|apply dlen_refl].
  apply gc_fw_insert_loop in H. eapply dlen_trans; [|eassumption]. gclose.
Qed.

Lemma gc_fw_body a x : fw_body a = Some x ->
  (fun a a' => dlen (fst a) (fst a') /\ zkeep (snd a) (snd a')) a (match x with inl a' => a' | inr r => r end).
Proof.
  destruct a as [s z]. unfold fw_body. intros H. gdec.
  all: repeat match goal with
       | E : mb_write _ _ _ = Some _ |- _ => apply gc_mb_write_len in E
       | E : c_fw_slide _ _ = Some _ |- _ => apply gc_fw_slide in E
       | E : c_fw_insert _ = Some _ |- _ => apply gc_fw_insert in E
       | E : c_read_buf _ _ _ = Some _ |- _ => apply gc_read_buf in E end.
  all: cbn beta; gclose.
Qed.

Lemma gc_fw_high_water s s' : c_fw_high_water s = Some s' -> dlen s s'.
Proof.
  unfold c_fw_high_water. intros H. gdec.
  all: repeat match goal with E : mb_write _ _ _ = Some _ |- _ => apply gc_mb_write_len in E end.
  all: gclose.
Qed.

Lemma gc_fill_window s z s' z' : c_fill_window s z = Some (s', z') -> dlen s s' /\ zkeep z z'.
Proof.
  unfold c_fill_window. intros H. gdec.
  match goal with E : loop _ _ _ = Some _ |- _ =>
    apply (loop_pre _ _ (fun a a' => dlen (fst a) (fst a') /\ zkeep (snd a) (snd a')) (fun r => r)) in E end.
  - apply gc_fw_high_water in E0. cbn [fst snd] in *. gclose.
  - intros. gclose.
  - apply gc_fw_body.
Qed.


(** ** CLEAR_HASH and the dictionary loops *)

Lemma sd_clear_hash s s1 : c_clear_hash s = Some s1 -> dlen s s1.
Proof.
  unfold c_clear_hash. intros H. gdec.
  repeat match goal with E : wr _ _ _ = Some _ |- _ => apply gc_wr_len in E end.
  match goal with E : guard _ = Some _ |- _ => unfold guard in E end.
  match goal with E : (if ?b then _ else _) = Some _ |- _ => destruct b eqn:B; [|discriminate E] end.
  gclose. pose proof (Zlength_nonneg l). rewrite Zlength_correct, repeat_length. lia.
Qed.

Lemma sd_insert_body_dlen a x : sd_insert_body a = Some x ->
  dlen (fst (fst a)) (match x with inl a' => fst (fst a') | inr r => fst r end).
Proof.
  destruct a as [[s1 str] n]. intros Hb. unfold sd_insert_body in Hb. gdec.
  all: repeat match goal with E : wr _ _ _ = Some _ |- _ => apply gc_wr_len in E end.
  all: gclose.
Qed.

Lemma sd_insert_loop a s' str' : loop FUEL sd_insert_body a = Some (s', str') -> dlen (fst (fst a)) s'.
Proof.
  intros H. apply (loop_pre _ _ (fun a a' => dlen (fst (fst a)) (fst (fst a'))) (fun r => (r, 0))) in H.
  - exact H.
  - intros a1 b c H1 H2. exact (dlen_trans _ _ _ H1 H2).
  - intros a1 x E. apply sd_insert_body_dlen in E. destruct x as [[[? ?] ?]|[? ?]]; exact E.
Qed.

Lemma sd_body_keep a x : sd_body a = Some x ->
  (fun a a' => dlen (fst a) (fst a') /\ zkeep (snd a) (snd a')) a (match x with inl a' => a' | inr r => r end).
Proof.
  destruct a as [s z]. unfold sd_body. intros H.
  destruct (d_lookahead s >=? MIN_MATCH).
  - destruct (loop FUEL sd_insert_body _) as [[s1 str]|] eqn:E1; unfold bind at 1 in H; cbv beta iota zeta in H;
      [|discriminate H].
    destruct (c_fill_window _ z) as [[s2 z2]|] eqn:E2; unfold bind at 1 in H; cbv beta iota zeta in H;
      [|discriminate H].
    inversion H; subst. apply sd_insert_loop in E1. apply gc_fill_window in E2. cbn [fst snd] in *.
    destruct E2 as [E2 Z2]. split; [|exact Z2]. eapply dlen_trans; [exact E1|]. eapply dlen_trans; [|exact E2].
    gclose.
  - inversion H; subst. cbn. split; [apply dlen_refl | apply zkeep_refl].
Qed.

Lemma sd_keep_facts :
  (forall s s1, c_clear_hash s = Some s1 -> dlen s s1) /\
  (forall s z s' z', c_fill_window s z = Some (s', z') -> dlen s s' /\ zkeep z z') /\
  (forall s z s' z', loop FUEL sd_body (s, z) = Some (s', z') -> dlen s s' /\ zkeep z z').
Proof.
  split; [exact sd_clear_hash|]. split; [exact gc_fill_window|].
  intros s z s' z' H.
  apply (loop_pre _ _ (fun a a' => dlen (fst a) (fst a') /\ zkeep (snd a) (snd a')) (fun r => r)) in H.
  - exact H.
  - intros a1 b c [H1 H2] [H3 H4]. split; [exact (dlen_trans _ _ _ H1 H3) | exact (zkeep_trans _ _ _ H2 H4)].
  - apply sd_body_keep.
Qed.
