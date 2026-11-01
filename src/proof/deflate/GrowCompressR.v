(** * The compression functions of deflate.c (DModel2: deflate_stored, deflate_fast, deflate_slow, deflate_rle,
    deflate_huff) only append to the output ([out_grow z z'], DeflateKit) and keep the gz_header and the sizes
    of the allocations ([dkeep s s'], DeflateKit). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

Definition compress_facts (c : dstate -> strm -> Z -> option (dstate * strm * bstate)) : Prop :=
  forall s z f r, c s z f = Some r -> out_grow z (snd (fst r)) /\ dkeep s (fst (fst r)).

(** v4 fix: deflate_stored's direct copies compute [u32 (avail_out - n)], so the facts need
    avail_out to be a uInt; [compress_facts_r] assumes [strm_ranges z] (the other four do not use it). *)
Definition compress_facts_r (c : dstate -> strm -> Z -> option (dstate * strm * bstate)) : Prop :=
  forall s z f r, strm_ranges z -> c s z f = Some r -> out_grow z (snd (fst r)) /\ dkeep s (fst (fst r)).

Definition grow_compress_all_r : Prop :=
  compress_facts_r c_deflate_stored /\ compress_facts_r c_deflate_fast /\ compress_facts_r c_deflate_slow /\
  compress_facts_r c_deflate_rle /\ compress_facts_r c_deflate_huff.


(** ** Helpers *)

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

Lemma gc_mb_wr_len b i v b' : mb_wr b i v = Some b' -> Zlength (mb_val b') = Zlength (mb_val b).
Proof. unfold mb_wr. destruct (in_range i (Zlength (mb_val b))); intros H; inversion H. apply gc_Zlength_upd. Qed.

Lemma gc_mb_write_len b lo src b' : mb_write b lo src = Some b' -> Zlength (mb_val b') = Zlength (mb_val b).
Proof.
  unfold mb_write. destruct (andb (0 <=? lo) (lo + Zlength src <=? Zlength (mb_val b))) eqn:E; intros H; inversion H.
  apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  cbn [mb_val]. pose proof (Zlength_nonneg src).
  rewrite !Zlength_app, !Zlength_sublist by lia. lia.
Qed.

Lemma gc_mb_move_len b d sr n b' : mb_move b d sr n = Some b' -> Zlength (mb_val b') = Zlength (mb_val b).
Proof.
  unfold mb_move. intros H.
  destruct (guard _); [|discriminate]. cbn [bind] in H.
  destruct (mb_read b sr n); [|discriminate]. cbn [bind] in H. eapply gc_mb_write_len; eauto.
Qed.

Lemma gc_copy_bytes_len dst pos src : 0 <= pos -> pos + Zlength src <= Zlength dst ->
  Zlength (copy_bytes dst pos src) = Zlength dst.
Proof.
  intros. unfold copy_bytes. pose proof (Zlength_nonneg src).
  rewrite !Zlength_app, !Zlength_sublist by lia. lia.
Qed.

(** *** The output functions of trees.c keep the length of pending_buf *)

Class OL (n : Z) (c : option cout) : Prop := ol : forall r, c = Some r -> Zlength (o_buf (fst r)) = n.

#[local] Typeclasses Opaque rd wr guard bind
  c_put_byte c_put_short c_send_bits c_send_code c_bi_flush c_bi_windup c_send_codes c_send_tree_loop
  c_send_tree c_send_bl_lens c_send_all_trees c_d_code c_send_symbol c_compress_loop c_compress_block
  c_tr_stored_block c_tr_flush_bits.

Ltac tstep E := fail.

Ltac lstep :=
  match goal with
  | x : (_ * _)%type |- _ => destruct x
  | H : Some _ = Some _ |- _ => apply gc_some_inj in H; subst
  | H : None = Some _ |- _ => discriminate H
  | H : bind ?a _ = Some _ |- _ =>
      let E := fresh "E" in
      destruct a eqn:E; unfold bind at 1 in H; cbv beta iota zeta in H; [| discriminate H]
  | Q : (_, _) = (_, _) |- _ => injection Q as; subst
  | E : wr _ _ _ = Some _ |- _ => apply gc_wr_len in E
  | E : ?c = Some ?r |- _ =>
      lazymatch type of r with
      | Z => clear E | unit => clear E | bool => clear E | list Z => clear E
      | _ => first [let A := fresh "A" in pose proof (ol _ E) as A; clear E; cbn [fst] in A | tstep E]
      end
  | H : context [match ?x with _ => _ end] |- _ => destruct x eqn:?
  end.

Ltac lrun := repeat (lstep; cbv beta iota zeta delta [andb orb negb fst snd] in *);
  cbn [o_buf set_bits fst snd] in *; try congruence.

Ltac lstart := intros ? ?; cbv beta iota zeta delta [fst snd] in *.

#[local] Instance ol_put_byte o m c : OL (Zlength (o_buf o)) (c_put_byte (o, m) c).
Proof. lstart. unfold c_put_byte in *. lrun. Qed.
#[local] Instance ol_put_short o m w : OL (Zlength (o_buf o)) (c_put_short (o, m) w).
Proof. lstart. unfold c_put_short in *. lrun. Qed.
#[local] Instance ol_send_bits o m v l : OL (Zlength (o_buf o)) (c_send_bits (o, m) v l).
Proof. lstart. unfold c_send_bits in *. lrun. Qed.
#[local] Instance ol_send_code o m c codes lens : OL (Zlength (o_buf o)) (c_send_code (o, m) c codes lens).
Proof. lstart. unfold c_send_code in *. lrun. Qed.
#[local] Instance ol_bi_flush o m : OL (Zlength (o_buf o)) (c_bi_flush (o, m)).
Proof. lstart. unfold c_bi_flush in *. lrun. Qed.
#[local] Instance ol_bi_windup o m : OL (Zlength (o_buf o)) (c_bi_windup (o, m)).
Proof. lstart. unfold c_bi_windup in *. lrun. Qed.
#[local] Instance ol_send_codes : forall fuel o m c codes lens count,
  OL (Zlength (o_buf o)) (c_send_codes fuel (o, m) c codes lens count).
Proof. induction fuel; intros; lstart; cbn [c_send_codes] in *; lrun. Qed.
#[local] Instance ol_send_tree_loop : forall fuel t max_code blc bll o m n prevlen nextlen count max_count min_count,
  OL (Zlength (o_buf o)) (c_send_tree_loop fuel t max_code blc bll (o, m) n prevlen nextlen count max_count min_count).
Proof. induction fuel; intros; lstart; cbn [c_send_tree_loop] in *; lrun. Qed.
#[local] Instance ol_send_tree o m t max_code bl : OL (Zlength (o_buf o)) (c_send_tree (o, m) t max_code bl).
Proof. lstart. unfold c_send_tree in *. lrun. Qed.
#[local] Instance ol_send_bl_lens : forall fuel bl o m rank blcodes,
  OL (Zlength (o_buf o)) (c_send_bl_lens fuel bl (o, m) rank blcodes).
Proof. induction fuel; intros; lstart; cbn [c_send_bl_lens] in *; lrun. Qed.
#[local] Instance ol_send_all_trees o m lt dt bl lcodes dcodes blcodes :
  OL (Zlength (o_buf o)) (c_send_all_trees (o, m) lt dt bl lcodes dcodes blcodes).
Proof. lstart. unfold c_send_all_trees in *. lrun. Qed.
#[local] Instance ol_send_symbol o m lcodes llens dcodes dlens dist lc :
  OL (Zlength (o_buf o)) (c_send_symbol (o, m) lcodes llens dcodes dlens dist lc).
Proof. lstart. unfold c_send_symbol in *. lrun. Qed.
#[local] Instance ol_compress_loop : forall fuel lit_bufsize sym_next lcodes llens dcodes dlens o m sx,
  OL (Zlength (o_buf o)) (c_compress_loop fuel lit_bufsize sym_next lcodes llens dcodes dlens (o, m) sx).
Proof. induction fuel; intros; lstart; cbn [c_compress_loop] in *; lrun. Qed.
#[local] Instance ol_compress_block o m lit_bufsize sym_next lcodes llens dcodes dlens :
  OL (Zlength (o_buf o)) (c_compress_block (o, m) lit_bufsize sym_next lcodes llens dcodes dlens).
Proof. lstart. unfold c_compress_block in *. lrun. Qed.
#[local] Instance ol_tr_flush_bits o m : OL (Zlength (o_buf o)) (c_tr_flush_bits (o, m)).
Proof. lstart. unfold c_tr_flush_bits in *. lrun. Qed.


Lemma gc_put_byte_pend o m c r : c_put_byte (o, m) c = Some r -> 0 <= o_pending o /\ o_pending (fst r) = o_pending o + 1.
Proof.
  unfold c_put_byte, wr, in_range. destruct (andb (0 <=? o_pending o) (o_pending o <? Zlength (o_buf o))) eqn:E;
    intros H; cbn [bind] in H; inversion H; subst. cbn. apply andb_true_iff in E. destruct E as [E _].
  apply Z.leb_le in E. lia.
Qed.

Lemma gc_put_short_pend o m w r : c_put_short (o, m) w = Some r -> 1 <= o_pending (fst r).
Proof.
  unfold c_put_short. intros H.
  destruct (c_put_byte (o, m) (Z.land w 255)) as [[o1 m1]|] eqn:E1; [|discriminate]. cbn [bind] in H.
  apply gc_put_byte_pend in E1. apply gc_put_byte_pend in H. cbn [fst] in *. lia.
Qed.

#[local] Instance ol_tr_stored_block o m buf stored_len last :
  OL (Zlength (o_buf o)) (c_tr_stored_block (o, m) buf stored_len last).
Proof.
  lstart. unfold c_tr_stored_block in *.
  destruct (c_send_bits (o, m) _ 3) as [om1|] eqn:E1; [|discriminate]. cbn [bind] in H.
  destruct (c_bi_windup om1) as [om2|] eqn:E2; [|discriminate]. cbn [bind] in H.
  destruct (c_put_short om2 _) as [om3|] eqn:E3; [|discriminate]. cbn [bind] in H.
  destruct (c_put_short om3 _) as [[o4 m4]|] eqn:E4; [|discriminate]. cbn [bind] in H.
  destruct om1 as [o1 m1], om2 as [o2 m2], om3 as [o3 m3].
  pose proof (ol _ E1) as A1. pose proof (ol _ E2) as A2. pose proof (ol _ E3) as A3. pose proof (ol _ E4) as A4.
  pose proof (gc_put_short_pend _ _ _ _ E4) as P4. cbn [fst] in *.
  destruct (negb (stored_len =? 0)).
  - destruct (guard _) eqn:G1; [|discriminate]. cbn [bind] in H.
    destruct (guard (o_pending o4 + stored_len <=? Zlength (o_buf o4))) eqn:G2; [|discriminate]. cbn [bind] in H.
    inversion H; subst. cbn [fst o_buf]. unfold guard in G1, G2.
    destruct (andb (0 <? stored_len) (stored_len <=? Zlength buf)) eqn:B1; [|discriminate].
    destruct (o_pending o4 + stored_len <=? Zlength (o_buf o4)) eqn:B2; [|discriminate].
    apply andb_true_iff in B1. destruct B1 as [B1 B3]. apply Z.ltb_lt in B1. apply Z.leb_le in B3.
    apply Z.leb_le in B2.
    rewrite gc_copy_bytes_len; [lia | lia |]. rewrite Zlength_sublist by lia. lia.
  - cbn [bind] in H. inversion H; subst. cbn [fst o_buf]. lia.
Qed.

Lemma gc_init_block s s' : c_init_block s = Some s' -> tr_out s' = tr_out s /\ tr_lit_bufsize s' = tr_lit_bufsize s.
Proof. intros H. unfold c_init_block in H. lrun. subst. cbn. auto. Qed.

Lemma gc_build_bl_tree s s' x : c_build_bl_tree s = Some (s', x) ->
  tr_out s' = tr_out s /\ tr_lit_bufsize s' = tr_lit_bufsize s.
Proof. intros H. unfold c_build_bl_tree in H. lrun. subst. cbn. auto. Qed.

Lemma gc_put_sym s m b s' m' : c_put_sym (s, m) b = Some (s', m') ->
  Zlength (o_buf (tr_out s')) = Zlength (o_buf (tr_out s)) /\ tr_lit_bufsize s' = tr_lit_bufsize s.
Proof. intros H. unfold c_put_sym in H. lrun. subst. cbn. auto. Qed.

Lemma gc_incr_lfreq s i s' : c_incr_lfreq s i = Some s' -> tr_out s' = tr_out s /\ tr_lit_bufsize s' = tr_lit_bufsize s.
Proof. intros H. unfold c_incr_lfreq in H. lrun. subst. cbn. auto. Qed.

Lemma gc_incr_dfreq s i s' : c_incr_dfreq s i = Some s' -> tr_out s' = tr_out s /\ tr_lit_bufsize s' = tr_lit_bufsize s.
Proof. intros H. unfold c_incr_dfreq in H. lrun. subst. cbn. auto. Qed.


Lemma gc_tr_tally_lit cs c s' m' b : c_tr_tally_lit cs c = Some ((s', m'), b) ->
  Zlength (o_buf (tr_out s')) = Zlength (o_buf (tr_out (fst cs))) /\ tr_lit_bufsize s' = tr_lit_bufsize (fst cs).
Proof.
  destruct cs as [s m]. intros H. unfold c_tr_tally_lit in H.
  destruct (c_put_sym (s, m) 0) as [[s1 m1]|] eqn:E1; [|discriminate]. cbn [bind] in H.
  destruct (c_put_sym (s1, m1) 0) as [[s2 m2]|] eqn:E2; [|discriminate]. cbn [bind] in H.
  destruct (c_put_sym (s2, m2) _) as [[s3 m3]|] eqn:E3; [|discriminate]. cbn [bind] in H.
  destruct (c_incr_lfreq s3 _) as [s4|] eqn:E4; [|discriminate]. cbn [bind] in H.
  inversion H; subst. apply gc_put_sym in E1, E2, E3. apply gc_incr_lfreq in E4. cbn [fst].
  destruct E1, E2, E3, E4. split; congruence.
Qed.

Lemma gc_tr_tally_dist cs d l s' m' b : c_tr_tally_dist cs d l = Some ((s', m'), b) ->
  Zlength (o_buf (tr_out s')) = Zlength (o_buf (tr_out (fst cs))) /\ tr_lit_bufsize s' = tr_lit_bufsize (fst cs).
Proof.
  destruct cs as [s m]. intros H. unfold c_tr_tally_dist in H.
  destruct (c_put_sym (s, m) _) as [[s1 m1]|] eqn:E1; [|discriminate]. cbn [bind] in H.
  destruct (c_put_sym (s1, m1) _) as [[s2 m2]|] eqn:E2; [|discriminate]. cbn [bind] in H.
  destruct (c_put_sym (s2, m2) _) as [[s3 m3]|] eqn:E3; [|discriminate]. cbn [bind] in H.
  destruct (rd length_code_tab _) as [code|]; [|discriminate]. cbn [bind] in H.
  destruct (c_incr_lfreq s3 _) as [s4|] eqn:E4; [|discriminate]. cbn [bind] in H.
  destruct (c_d_code _) as [dc|]; [|discriminate]. cbn [bind] in H.
  destruct (c_incr_dfreq s4 _) as [s5|] eqn:E5; [|discriminate]. cbn [bind] in H.
  inversion H; subst. apply gc_put_sym in E1, E2, E3. apply gc_incr_lfreq in E4. apply gc_incr_dfreq in E5.
  cbn [fst]. destruct E1, E2, E3, E4, E5. split; congruence.
Qed.

Lemma gc_tr_flush_block cs buf sl last s' m' k : c_tr_flush_block cs buf sl last = Some ((s', m'), k) ->
  Zlength (o_buf (tr_out s')) = Zlength (o_buf (tr_out (fst cs))) /\ tr_lit_bufsize s' = tr_lit_bufsize (fst cs).
Proof.
  destruct cs as [s m]. intros H. unfold c_tr_flush_block in H. cbn [fst].
  destruct (if tr_level s >? 0 then _ else _) as [[[[s1 ol1] sl1] mb]|] eqn:E1;
    unfold bind at 1 in H; cbv beta iota zeta in H; [|discriminate H].
  assert (O1 : tr_out s1 = tr_out s /\ tr_lit_bufsize s1 = tr_lit_bufsize s).
  { clear H. destruct (tr_level s >? 0); [|inversion E1; subst; auto].
    repeat match goal with
    | E : bind ?a _ = Some _ |- _ =>
        let E' := fresh "E" in
        destruct a eqn:E'; unfold bind at 1 in E; cbv beta iota zeta in E; [| discriminate E]
    | x : (_ * _)%type |- _ => destruct x
    | E : (if ?b then _ else _) = Some _ |- _ => destruct b
    end.
    all: repeat match goal with E : Some _ = Some _ |- _ => apply gc_some_inj in E end.
    all: repeat match goal with E : (_, _) = (_, _) |- _ => injection E as; subst end.
    all: repeat match goal with E : c_build_bl_tree _ = Some _ |- _ => apply gc_build_bl_tree in E end.
    all: cbn in *; intuition congruence. }
  destruct O1 as [O1 L1]. clear E1.
  destruct (match buf with Some _ => _ | None => _ end) as [[[o2 m2] kd]|] eqn:E2;
    unfold bind at 1 in H; cbv beta iota zeta in H; [|discriminate H].
  assert (A2 : Zlength (o_buf o2) = Zlength (o_buf (tr_out s1))).
  { clear H. destruct (tr_out s1) as [o m0] eqn:Eo. lrun. }
  destruct (c_init_block (set_out s1 o2)) as [s3|] eqn:E3;
    unfold bind at 1 in H; cbv beta iota zeta in H; [|discriminate H].
  apply gc_init_block in E3. cbn [tr_out set_out tr_lit_bufsize] in E3. destruct E3 as [E3 L3].
  destruct (negb (last =? 0)).
  - destruct (c_bi_windup (tr_out s3, m2)) as [[o4 m4]|] eqn:E4;
      cbv beta iota zeta delta [bind] in H; [|discriminate H].
    inversion H; subst. pose proof (ol _ E4) as A4. cbn [fst] in A4.
    cbn [tr_out set_out tr_lit_bufsize]. split; congruence.
  - cbv beta iota zeta delta [bind] in H. inversion H; subst. split; congruence.
Qed.


(** ** The relation kept by every step: the gz_header, the sizes and the lengths of the buffers *)

Definition dlen (s s' : dstate) : Prop :=
  d_gzhead s' = d_gzhead s /\ d_w_size s' = d_w_size s /\ d_hash_size s' = d_hash_size s /\
  tr_lit_bufsize (d_tr s') = tr_lit_bufsize (d_tr s) /\
  Zlength (mb_val (d_window s')) = Zlength (mb_val (d_window s)) /\
  Zlength (d_prev s') = Zlength (d_prev s) /\ Zlength (d_head s') = Zlength (d_head s) /\
  Zlength (o_buf (tr_out (d_tr s'))) = Zlength (o_buf (tr_out (d_tr s))).

Lemma dlen_refl s : dlen s s.
Proof. unfold dlen. repeat split. Qed.

Lemma dlen_trans s1 s2 s3 : dlen s1 s2 -> dlen s2 s3 -> dlen s1 s3.
Proof. unfold dlen. intros. repeat match goal with H : _ /\ _ |- _ => destruct H end. repeat split; congruence. Qed.

Lemma dlen_dkeep s s' : dlen s s' -> dkeep s s'.
Proof.
  unfold dlen, dkeep, dsizes. intros. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; try congruence. all: intros; repeat match goal with H : _ /\ _ |- _ => destruct H end; congruence.
Qed.

(** The output object: unchanged ([zsame]) or appended to ([out_grow]). *)
Definition zsame (z z' : strm) : Prop := z_out z' = z_out z /\ z_avail_out z' = z_avail_out z.

Lemma zsame_grow z z' : zsame z z' -> out_grow z z'.
Proof. intros [A B]. apply out_grow_same; auto. Qed.

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
  unfold dlen, zsame, incr_matches, clamp_insert, upd_high_water, add_insert, set_insert_end in *; gconj;
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b
  | H : context [if ?b then _ else _] |- _ => destruct b
  end;
  gnorm; repeat split; try congruence.


(** *** read_buf, the hash, fill_window *)

Lemma gc_read_buf s z n z' d : c_read_buf s z n = Some (z', d) -> zsame z z'.
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
  (fun a a' => dlen (fst a) (fst a') /\ zsame (snd a) (snd a')) a (match x with inl a' => a' | inr r => r end).
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

Lemma gc_fill_window s z s' z' : c_fill_window s z = Some (s', z') -> dlen s s' /\ zsame z z'.
Proof.
  unfold c_fill_window. intros H. gdec.
  match goal with E : loop _ _ _ = Some _ |- _ =>
    apply (loop_pre _ _ (fun a a' => dlen (fst a) (fst a') /\ zsame (snd a) (snd a')) (fun r => r)) in E end.
  - apply gc_fw_high_water in E0. cbn [fst snd] in *. gclose.
  - intros. gclose.
  - apply gc_fw_body.
Qed.


(** *** longest_match *)

Lemma gc_lm_body nice limit a x : lm_body nice limit a = Some x ->
  dlen (lm_s a) (lm_s (match x with inl a' => a' | inr r => mkLM 0 0 0 0 0 (snd r) end)).
Proof. destruct a. unfold lm_body. intros H. gdec. all: gclose. Qed.

Lemma gc_lm_loop nice limit a b s' : loop FUEL (lm_body nice limit) a = Some (b, s') -> dlen (lm_s a) s'.
Proof.
  intros H. apply (loop_pre _ _ (fun a a' => dlen (lm_s a) (lm_s a')) (fun r => mkLM 0 0 0 0 0 (snd r))) in H.
  - exact H.
  - intros a1 b1 c H1 H2. exact (dlen_trans _ _ _ H1 H2).
  - apply gc_lm_body.
Qed.

Lemma gc_longest_match s cur s' ml : c_longest_match s cur = Some (s', ml) -> dlen s s'.
Proof.
  unfold c_longest_match. intros H. gdec.
  match goal with E : loop _ _ _ = Some _ |- _ => apply gc_lm_loop in E end. gclose.
Qed.

(** *** flush_pending, FLUSH_BLOCK, the tallies *)

Lemma gc_out_put z b z1 : out_put z b = Some z1 ->
  z_out z1 = z_out z ++ b /\ z_avail_out z1 = z_avail_out z /\ Zlength b <= z_avail_out z.
Proof.
  unfold out_put. destruct (Zlength b <=? z_avail_out z) eqn:E; intros H; inversion H; subst.
  apply Z.leb_le in E. cbn. auto.
Qed.

Definition zpos (z z' : strm) : Prop := 0 <= z_avail_out z -> 0 <= z_avail_out z'.

Lemma gc_flush_pending s z s' z' : c_flush_pending s z = Some (s', z') ->
  dlen s s' /\ out_grow z z' /\ zpos z z'.
Proof.
  unfold c_flush_pending, zpos. intros H. gdec.
  all: match goal with E : c_tr_flush_bits _ = Some _ |- _ =>
         pose proof (ol_tr_flush_bits (tr_out (d_tr s)) (d_pbm s) _ E) as A; cbn [fst] in A end.
  - split; [gclose|]. split; [apply out_grow_refl | auto].
  - match goal with E : out_put _ _ = Some _ |- _ => apply gc_out_put in E end.
    match goal with E : mb_read _ _ _ = Some _ |- _ => apply DeflateKit.mb_read_length in E end. gconj.
    split; [gclose|]. split.
    + eexists. gnorm. split; [eassumption | lia].
    + gnorm. intros. lia.
Qed.

Ltac og := first [apply out_grow_refl | assumption | apply zsame_grow; assumption
                 | eapply out_grow_trans; [first [eassumption | apply zsame_grow; eassumption] | og]].

Lemma gc_flush_block_only s z last s' z' : c_flush_block_only s z last = Some (s', z') ->
  dlen s s' /\ out_grow z z' /\ zpos z z'.
Proof.
  unfold c_flush_block_only. intros H. gdec.
  all: match goal with E : c_tr_flush_block _ _ _ _ = Some _ |- _ => apply gc_tr_flush_block in E end.
  all: apply gc_flush_pending in H; gconj; split; [gclose | auto].
Qed.

Lemma gc_flush_block s z last s' z' r : c_flush_block s z last = Some (s', z', r) ->
  dlen s s' /\ out_grow z z' /\ zpos z z'.
Proof. unfold c_flush_block. intros H. gdec. all: apply gc_flush_block_only in E; exact E. Qed.

Lemma gc_dtally_lit s c s' b : c_dtally_lit s c = Some (s', b) -> dlen s s'.
Proof.
  unfold c_dtally_lit. intros H. gdec.
  match goal with E : c_tr_tally_lit _ _ = Some _ |- _ => apply gc_tr_tally_lit in E end. gclose.
Qed.

Lemma gc_dtally_dist s d l s' b : c_dtally_dist s d l = Some (s', b) -> dlen s s'.
Proof.
  unfold c_dtally_dist. intros H. gdec.
  match goal with E : c_tr_tally_dist _ _ _ = Some _ |- _ => apply gc_tr_tally_dist in E end. gclose.
Qed.


(** *** The common pieces of the compression functions *)

Definition stepR (s : dstate) (z : strm) (x : (dstate * strm) + dexit) : Prop :=
  match x with
  | inl (s', z') => dlen s s' /\ out_grow z z'
  | inr (s', z', _) => dlen s s' /\ out_grow z z'
  end.

Lemma stepR_pre s z s1 z1 x : dlen s s1 -> out_grow z z1 -> stepR s1 z1 x -> stepR s z x.
Proof.
  intros D G. destruct x as [[s2 z2]|[[s2 z2] r]]; cbn; intros [D2 G2];
    (split; [eapply dlen_trans; eassumption | eapply out_grow_trans; eassumption]).
Qed.

Ltac gfacts :=
  repeat match goal with
  | E : c_read_buf _ _ _ = Some _ |- _ => apply gc_read_buf in E
  | E : c_fill_window _ _ = Some _ |- _ => apply gc_fill_window in E
  | E : c_insert_string _ _ = Some _ |- _ => apply gc_insert_string in E
  | E : c_longest_match _ _ = Some _ |- _ => apply gc_longest_match in E
  | E : c_flush_pending _ _ = Some _ |- _ => apply gc_flush_pending in E
  | E : c_flush_block_only _ _ _ = Some _ |- _ => apply gc_flush_block_only in E
  | E : c_flush_block _ _ _ = Some _ |- _ => apply gc_flush_block in E
  | E : c_dtally_lit _ _ = Some _ |- _ => apply gc_dtally_lit in E
  | E : c_dtally_dist _ _ _ = Some _ |- _ => apply gc_dtally_dist in E
  | E : mb_write _ _ _ = Some _ |- _ => apply gc_mb_write_len in E
  | E : mb_move _ _ _ _ = Some _ |- _ => apply gc_mb_move_len in E
  | E : mb_wr _ _ _ = Some _ |- _ => apply gc_mb_wr_len in E
  | E : wr _ _ _ = Some _ |- _ => apply gc_wr_len in E
  | E : _ /\ _ |- _ => destruct E
  end.

(** Close [stepR s z x] from a hypothesis [stepR s1 z1 x], or a [stepR] / [dlen /\ out_grow] goal on a known
    exit. *)
Ltac sclose :=
  first
  [ match goal with H : stepR ?s1 ?z1 ?x |- stepR _ _ ?x =>
      apply (stepR_pre _ _ s1 z1 _); [gclose | og | exact H] end
  | cbn [stepR]; split; [gclose | og]
  | split; [gclose | og] ].

Lemma gc_bflush s z b x : c_bflush s z b = Some x -> stepR s z x.
Proof. unfold c_bflush. intros H. gdec; gfacts; sclose. Qed.

Lemma gc_refill need flush s z x : c_refill need flush s z = Some x -> stepR s z x.
Proof. unfold c_refill. intros H. gdec; gfacts; sclose. Qed.

Lemma gc_deflate_tail s z f s' z' r : c_deflate_tail s z f = Some (s', z', r) -> dlen s s' /\ out_grow z z'.
Proof. unfold c_deflate_tail. intros H. gdec; gfacts; sclose. Qed.


Lemma gc_main_loop {B} (body : dstate * strm -> option ((dstate * strm) + (dstate * strm * B))) :
  (forall a x, body a = Some x ->
     match x with
     | inl (s', z') => dlen (fst a) s' /\ out_grow (snd a) z'
     | inr (s', z', _) => dlen (fst a) s' /\ out_grow (snd a) z'
     end) ->
  forall a s' z' r, loop FUEL body a = Some (s', z', r) -> dlen (fst a) s' /\ out_grow (snd a) z'.
Proof.
  intros Hb a s' z' r H.
  apply (loop_pre _ _ (fun a a' => dlen (fst a) (fst a') /\ out_grow (snd a) (snd a'))
           (fun r => (fst (fst r), snd (fst r)))) in H.
  - exact H.
  - intros a1 b c [D1 G1] [D2 G2]. split; [exact (dlen_trans _ _ _ D1 D2) | exact (out_grow_trans _ _ _ G1 G2)].
  - intros a1 x E. specialize (Hb _ _ E). destruct x as [[s2 z2]|[[s2 z2] r2]]; exact Hb.
Qed.

Lemma gc_insert_head s s' h : c_insert_head s = Some (s', h) -> dlen s s'.
Proof. unfold c_insert_head. intros H. gdec; gfacts; gclose. Qed.

(** ** deflate_fast *)

Lemma gc_df_insert_loop s s' : loop FUEL df_insert_body s = Some s' -> dlen s s'.
Proof.
  intros H. apply (loop_pre _ _ dlen (fun r => r)) in H.
  - exact H.
  - intros a b c H1 H2. exact (dlen_trans _ _ _ H1 H2).
  - intros a x E. unfold df_insert_body in E. gdec; gfacts; gclose.
Qed.

Lemma gc_df_step s z x : df_step s z = Some x -> stepR s z x.
Proof.
  unfold df_step. intros H. gdec; gfacts.
  all: repeat match goal with
       | E : c_insert_head _ = Some _ |- _ => apply gc_insert_head in E
       | E : loop FUEL df_insert_body _ = Some _ |- _ => apply gc_df_insert_loop in E
       | E : c_bflush _ _ _ = Some _ |- _ => apply gc_bflush in E
       end.
  all: sclose.
Qed.

Lemma gc_df_body flush a x : DModel2.df_body flush a = Some x -> stepR (fst a) (snd a) x.
Proof.
  destruct a as [s z]. unfold DModel2.df_body. intros H. gdec.
  all: repeat match goal with
       | E : c_refill _ _ _ _ = Some _ |- _ => apply gc_refill in E; cbn [stepR] in E
       | E : df_step _ _ = Some _ |- _ => apply gc_df_step in E
       end.
  all: gdec; gconj; cbn [fst snd]; sclose.
Qed.

Ltac cfin := cbn [fst snd]; split; [og | apply dlen_dkeep; gclose].

Lemma gc_deflate_fast : compress_facts c_deflate_fast.
Proof.
  intros s z f r H. unfold c_deflate_fast in H. gdec.
  all: match goal with E : loop FUEL _ _ = Some _ |- _ =>
         apply (gc_main_loop _ (gc_df_body f)) in E; cbn [fst snd] in E end.
  all: gfacts.
  all: try match goal with E : c_deflate_tail _ _ _ = Some _ |- _ => apply gc_deflate_tail in E end.
  all: gconj; cfin.
Qed.


(** ** deflate_slow *)

Lemma gc_dsl_insert_loop m s s' : loop FUEL (dsl_insert_body m) s = Some s' -> dlen s s'.
Proof.
  intros H. apply (loop_pre _ _ dlen (fun r => r)) in H.
  - exact H.
  - intros a b c H1 H2. exact (dlen_trans _ _ _ H1 H2).
  - intros a x E. unfold dsl_insert_body in E. gdec; gfacts; gclose.
Qed.

Lemma gc_dsl_step s z x : dsl_step s z = Some x -> stepR s z x.
Proof.
  unfold dsl_step. intros H. gdec; gfacts.
  all: repeat match goal with
       | E : c_insert_head _ = Some _ |- _ => apply gc_insert_head in E
       | E : loop FUEL (dsl_insert_body _) _ = Some _ |- _ => apply gc_dsl_insert_loop in E
       | E : c_bflush _ _ _ = Some _ |- _ => apply gc_bflush in E
       end.
  all: gconj; sclose.
Qed.

Lemma gc_dsl_body flush a x : dsl_body flush a = Some x -> stepR (fst a) (snd a) x.
Proof.
  destruct a as [s z]. unfold dsl_body. intros H. gdec.
  all: repeat match goal with
       | E : c_refill _ _ _ _ = Some _ |- _ => apply gc_refill in E; cbn [stepR] in E
       | E : dsl_step _ _ = Some _ |- _ => apply gc_dsl_step in E
       end.
  all: gdec; gconj; cbn [fst snd]; sclose.
Qed.

Lemma gc_deflate_slow : compress_facts c_deflate_slow.
Proof.
  intros s z f r H. unfold c_deflate_slow in H. gdec.
  all: match goal with E : loop FUEL _ _ = Some _ |- _ =>
         apply (gc_main_loop _ (gc_dsl_body f)) in E; cbn [fst snd] in E end.
  all: gfacts.
  all: try match goal with E : c_deflate_tail _ _ _ = Some _ |- _ => apply gc_deflate_tail in E end.
  all: gconj; cfin.
Qed.

(** ** deflate_rle *)

Lemma gc_rle_step s z x : rle_step s z = Some x -> stepR s z x.
Proof.
  unfold rle_step. intros H. gdec; gfacts.
  all: repeat match goal with E : c_bflush _ _ _ = Some _ |- _ => apply gc_bflush in E end.
  all: gconj; sclose.
Qed.

Lemma gc_rle_body flush a x : rle_body flush a = Some x -> stepR (fst a) (snd a) x.
Proof.
  destruct a as [s z]. unfold rle_body. intros H. gdec.
  all: repeat match goal with
       | E : c_refill _ _ _ _ = Some _ |- _ => apply gc_refill in E; cbn [stepR] in E
       | E : rle_step _ _ = Some _ |- _ => apply gc_rle_step in E
       end.
  all: gdec; gconj; cbn [fst snd]; sclose.
Qed.

Lemma gc_deflate_rle : compress_facts c_deflate_rle.
Proof.
  intros s z f r H. unfold c_deflate_rle in H. gdec.
  all: match goal with E : loop FUEL _ _ = Some _ |- _ =>
         apply (gc_main_loop _ (gc_rle_body f)) in E; cbn [fst snd] in E end.
  all: gfacts.
  all: try match goal with E : c_deflate_tail _ _ _ = Some _ |- _ => apply gc_deflate_tail in E end.
  all: gconj; cfin.
Qed.

(** ** deflate_huff *)

Lemma gc_huff_body flush a x : huff_body flush a = Some x -> stepR (fst a) (snd a) x.
Proof.
  destruct a as [s z]. unfold huff_body. intros H. gdec; gfacts.
  all: repeat match goal with E : c_bflush _ _ _ = Some _ |- _ => apply gc_bflush in E end.
  all: gconj; cbn [fst snd]; sclose.
Qed.

Lemma gc_deflate_huff : compress_facts c_deflate_huff.
Proof.
  intros s z f r H. unfold c_deflate_huff in H. gdec.
  all: match goal with E : loop FUEL _ _ = Some _ |- _ =>
         apply (gc_main_loop _ (gc_huff_body f)) in E; cbn [fst snd] in E end.
  all: gfacts.
  all: try match goal with E : c_deflate_tail _ _ _ = Some _ |- _ => apply gc_deflate_tail in E end.
  all: gconj; cfin.
Qed.


(** ** deflate_stored (with avail_out a valid uInt: the direct copies compute [u32 (avail_out - n)]) *)

Definition av (z : strm) : Prop := 0 <= z_avail_out z <= Int.max_unsigned.

Lemma gc_pb_wr s i v s' : c_pb_wr s i v = Some s' -> dlen s s'.
Proof. unfold c_pb_wr. intros H. gdec; gfacts. gclose. Qed.

Lemma gc_guard_eq a b u : guard (a =? b) = Some u -> a = b.
Proof. unfold guard. destruct (a =? b) eqn:E; intros H; inversion H. apply Z.eqb_eq; exact E. Qed.

(** [gclose] for a [dlen] goal, without case splits on the hypotheses. *)
Ltac dclose :=
  unfold dlen in *; gconj; unfold incr_matches, clamp_insert, upd_high_water, add_insert, set_insert_end;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  gnorm; repeat split; try congruence.

Ltac zu32 :=
  repeat match goal with
  | |- context [u32 (z_avail_out ?a - ?b)] => rewrite (u32_small (z_avail_out a - b)) in * by lia
  | H : context [u32 (z_avail_out ?a - ?b)] |- _ => rewrite (u32_small (z_avail_out a - b)) in * by lia
  end.

Ltac zlens :=
  repeat match goal with
  | l : list Z |- _ =>
      lazymatch goal with
      | _ : 0 <= Zlength l |- _ => fail
      | _ => pose proof (Zlength_nonneg l)
      end
  end.

Ltac zclose :=
  first
  [ og | assumption
  | unfold out_grow, av, zpos, zsame in *; gconj;
    repeat match goal with H : exists _, _ |- _ => destruct H as [? [? ?]] end;
    gnorm; zlens;
    repeat match goal with H : 0 <= ?a -> _, H2 : 0 <= ?a |- _ => specialize (H H2) end;
    zu32;
    first
    [ eexists; split;
      [ repeat match goal with H : z_out ?a = _ |- context [z_out ?a] => rewrite H end;
        rewrite <- ?app_assoc; reflexivity
      | rewrite ?Zlength_app; lia ]
    | lia ] ].

Lemma gc_ds_body flush mb s z x : ds_body flush mb (s, z) = Some x -> av z ->
  match x with
  | inl (s', z') => dlen s s' /\ out_grow z z' /\ av z'
  | inr (s', z', _) => dlen s s' /\ out_grow z z' /\ av z'
  end.
Proof.
  unfold ds_body. intros H Hav. gdec; gfacts.
  all: repeat match goal with
       | E : c_tr_stored_block (d_out _) _ _ _ = Some _ |- _ =>
           let A := fresh "A" in
           pose proof (ol_tr_stored_block _ _ _ _ _ _ E) as A; cbn [fst] in A; clear E
       | E : c_pb_wr _ _ _ = Some _ |- _ => apply gc_pb_wr in E
       | E : out_put _ _ = Some _ |- _ => apply gc_out_put in E
       | E : mb_read _ _ _ = Some _ |- _ => apply DeflateKit.mb_read_length in E
       | E : guard (_ =? _) = Some _ |- _ => apply gc_guard_eq in E
       end.
  all: gconj; split; [dclose | split; zclose].
Qed.

(** The conditional field updates of deflate_stored keep the buffers and sizes. *)
Lemma dlen_incr_matches s : dlen s (incr_matches s).
Proof. unfold incr_matches. destruct (_ <? _); [gclose | apply dlen_refl]. Qed.
Lemma dlen_clamp_insert s : dlen s (clamp_insert s).
Proof. unfold clamp_insert. destruct (_ >? _); [gclose | apply dlen_refl]. Qed.
Lemma dlen_add_insert s n : dlen s (add_insert s n).
Proof. gclose. Qed.
Lemma dlen_upd_high_water s : dlen s (upd_high_water s).
Proof. unfold upd_high_water. destruct (_ <? _); [gclose | apply dlen_refl]. Qed.

Lemma gc_ds_loop flush mb s z s' z' last : loop FUEL (ds_body flush mb) (s, z) = Some (s', z', last) -> av z ->
  dlen s s' /\ out_grow z z' /\ av z'.
Proof.
  intros H Ha.
  refine (loop_pre FUEL (ds_body flush mb)
            (fun a a' => av (snd a) -> dlen (fst a) (fst a') /\ out_grow (snd a) (snd a') /\ av (snd a'))
            (fun r => (fst (fst r), snd (fst r))) _ _ (s, z) (s', z', last) H Ha).
  - intros a b c H1 H2 Hb. destruct (H1 Hb) as (D1 & G1 & A1). destruct (H2 A1) as (D2 & G2 & A2).
    split; [exact (dlen_trans _ _ _ D1 D2) | split; [exact (out_grow_trans _ _ _ G1 G2) | exact A2]].
  - intros [s1 z1] x E Hb. apply gc_ds_body in E; [|exact Hb].
    destruct x as [[s2 z2]|[[s2 z2] r2]]; exact E.
Qed.

Lemma gc_ds_window s z used s' : c_ds_window s z used = Some s' -> dlen s s'.
Proof. unfold c_ds_window. intros H. gdec; gfacts. all: gclose. Qed.

(** ** [dlen] by rewriting: the projections it compares *)
Definition dproj (s : dstate) :=
  (d_gzhead s, d_w_size s, d_hash_size s, tr_lit_bufsize (d_tr s), Zlength (mb_val (d_window s)),
   Zlength (d_prev s), Zlength (d_head s), Zlength (o_buf (tr_out (d_tr s)))).

Lemma dlen_of_dproj s s' : dproj s' = dproj s -> dlen s s'.
Proof. unfold dproj, dlen. intros E. injection E as. repeat split; assumption. Qed.

Lemma dproj_of_dlen s s' : dlen s s' -> dproj s' = dproj s.
Proof. unfold dproj, dlen. intros (A & B & C & D & E & F & G & H). rewrite A, B, C, D, E, F, G, H. reflexivity. Qed.

Lemma dproj_set_d_status s v : dproj (set_d_status s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_po s v : dproj (set_d_po s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_wrap s v : dproj (set_d_wrap s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_gzindex s v : dproj (set_d_gzindex s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_method s v : dproj (set_d_method s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_last_flush s v : dproj (set_d_last_flush s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_w_bits s v : dproj (set_d_w_bits s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_w_mask s v : dproj (set_d_w_mask s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_window_size s v : dproj (set_d_window_size s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_ins_h s v : dproj (set_d_ins_h s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_hash_bits s v : dproj (set_d_hash_bits s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_hash_mask s v : dproj (set_d_hash_mask s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_hash_shift s v : dproj (set_d_hash_shift s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_block_start s v : dproj (set_d_block_start s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_match_length s v : dproj (set_d_match_length s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_prev_match s v : dproj (set_d_prev_match s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_match_available s v : dproj (set_d_match_available s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_strstart s v : dproj (set_d_strstart s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_match_start s v : dproj (set_d_match_start s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_lookahead s v : dproj (set_d_lookahead s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_prev_length s v : dproj (set_d_prev_length s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_max_chain_length s v : dproj (set_d_max_chain_length s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_max_lazy_match s v : dproj (set_d_max_lazy_match s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_good_match s v : dproj (set_d_good_match s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_nice_match s v : dproj (set_d_nice_match s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_insert s v : dproj (set_d_insert s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_high_water s v : dproj (set_d_high_water s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_slid s v : dproj (set_d_slid s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_pending_buf_size s v : dproj (set_d_pending_buf_size s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_pbm s v : dproj (set_d_pbm s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_incr_matches s : dproj (incr_matches s) = dproj s.
Proof. unfold incr_matches; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity. Qed.
Lemma dproj_clamp_insert s : dproj (clamp_insert s) = dproj s.
Proof. unfold clamp_insert; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity. Qed.
Lemma dproj_add_insert s n : dproj (add_insert s n) = dproj s.
Proof. unfold add_insert; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity. Qed.
Lemma dproj_upd_high_water s : dproj (upd_high_water s) = dproj s.
Proof. unfold upd_high_water; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity. Qed.
Lemma dproj_set_insert_end s : dproj (set_insert_end s) = dproj s.
Proof. unfold set_insert_end; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity. Qed.
Lemma dproj_set_d_bi_used s v : dproj (set_d_bi_used s v) = dproj s. Proof. reflexivity. Qed.
Lemma dproj_set_d_matches s v : dproj (set_d_matches s v) = dproj s. Proof. reflexivity. Qed.
#[local] Hint Rewrite dproj_set_d_status dproj_set_d_po dproj_set_d_wrap dproj_set_d_gzindex dproj_set_d_method dproj_set_d_last_flush dproj_set_d_w_bits dproj_set_d_w_mask dproj_set_d_window_size dproj_set_d_ins_h dproj_set_d_hash_bits dproj_set_d_hash_mask dproj_set_d_hash_shift dproj_set_d_block_start dproj_set_d_match_length dproj_set_d_prev_match dproj_set_d_match_available dproj_set_d_strstart dproj_set_d_match_start dproj_set_d_lookahead dproj_set_d_prev_length dproj_set_d_max_chain_length dproj_set_d_max_lazy_match dproj_set_d_good_match dproj_set_d_nice_match dproj_set_d_insert dproj_set_d_high_water dproj_set_d_slid dproj_set_d_pending_buf_size dproj_set_d_pbm dproj_incr_matches dproj_clamp_insert dproj_add_insert dproj_upd_high_water dproj_set_insert_end dproj_set_d_bi_used dproj_set_d_matches : dprdb.

Lemma dproj_set_d_window s w : Zlength (mb_val w) = Zlength (mb_val (d_window s)) ->
  dproj (set_d_window s w) = dproj s.
Proof. intros E. unfold dproj. cbn. rewrite E. reflexivity. Qed.
Lemma dproj_set_d_prev s l : Zlength l = Zlength (d_prev s) -> dproj (set_d_prev s l) = dproj s.
Proof. intros E. unfold dproj. cbn. rewrite E. reflexivity. Qed.
Lemma dproj_set_d_head s l : Zlength l = Zlength (d_head s) -> dproj (set_d_head s l) = dproj s.
Proof. intros E. unfold dproj. cbn. rewrite E. reflexivity. Qed.
Lemma dproj_set_d_out s o m : Zlength (o_buf o) = Zlength (o_buf (tr_out (d_tr s))) ->
  dproj (set_d_out s (o, m)) = dproj s.
Proof. intros E. unfold dproj. cbn. rewrite E. reflexivity. Qed.
Lemma dproj_set_d_pb s b : Zlength (mb_val b) = Zlength (o_buf (tr_out (d_tr s))) ->
  dproj (set_d_pb s b) = dproj s.
Proof. intros E. unfold dproj. cbn. rewrite E. reflexivity. Qed.
Lemma dproj_set_d_trm s t m : Zlength (o_buf (tr_out t)) = Zlength (o_buf (tr_out (d_tr s))) ->
  tr_lit_bufsize t = tr_lit_bufsize (d_tr s) -> dproj (set_d_trm s (t, m)) = dproj s.
Proof. intros E F. unfold dproj. cbn. rewrite E, F. reflexivity. Qed.

(** Close [dlen s X] for a state term [X] built by setters / helpers from variables with [dlen] facts. *)
Ltac dpr :=
  apply dlen_of_dproj;
  repeat match goal with H : dlen _ _ |- _ => apply dproj_of_dlen in H end;
  repeat first
  [ match goal with |- ?a = ?a => reflexivity end
  | progress (autorewrite with dprdb)
  | rewrite dproj_set_d_window by assumption
  | rewrite dproj_set_d_prev by assumption
  | rewrite dproj_set_d_head by assumption
  | rewrite dproj_set_d_out by assumption
  | rewrite dproj_set_d_pb by assumption
  | rewrite dproj_set_d_trm by assumption
  | match goal with H : dproj ?x = _ |- context [dproj ?x] => rewrite H end ].

Local Close Scope logic.
(** The part of deflate_stored after the window update (a copy of its text, [s] the state after
    [upd_high_water]). *)
Definition ds_tail (s : dstate) (z : strm) (flush last : Z) : option (dstate * strm * bstate) :=
  if negb (last =? 0) then Some (set_d_bi_used s 8, z, finish_done) else
  if negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH) && (z_avail_in z =? 0) &&
     (d_strstart s =? d_block_start s)
  then Some (s, z, block_done) else
  (* fill the window with any remaining input *)
  let have := u32 (u64 (d_window_size s - d_strstart s)) in
  let* (s, have) :=
    (if (z_avail_in z >? have) && (d_block_start s >=? d_w_size s) then
       let s := set_d_block_start s (d_block_start s - d_w_size s) in
       let s := set_d_strstart s (u32 (d_strstart s - d_w_size s)) in
       let* win := mb_move (d_window s) 0 (d_w_size s) (d_strstart s) in
       let s := set_d_window s win in
       let s := incr_matches s in
       let have := u32 (have + d_w_size s) in
       Some (clamp_insert s, have)
     else Some (s, have)) in
  let have := if have >? z_avail_in z then z_avail_in z else have in
  let* (s, z) :=
    (if have =? 0 then Some (s, z) else
     let* (z, data) := c_read_buf s z have in
     let* win := mb_write (d_window s) (d_strstart s) data in
     let s := set_d_window s win in
     let s := set_d_strstart s (u32 (d_strstart s + have)) in
     Some (add_insert s have, z)) in
  let s := upd_high_water s in
  (* a stored block from the window into pending *)
  let have := stored_hdr s in
  let have := u32 (let a := u64 (d_pending_buf_size s - have) in if a >? MAX_STORED then MAX_STORED else a) in
  let min_block := if have >? d_w_size s then d_w_size s else have in
  let* _ := guard (in_long (d_strstart s - d_block_start s)) in
  let left := u32 (d_strstart s - d_block_start s) in
  let* (s, z, last) :=
    (if (left >=? min_block) ||
        ((negb (left =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH) &&
         (z_avail_in z =? 0) && (left <=? have)) then
       let len := if left >? have then have else left in
       let last := if (flush =? Z_FINISH) && (z_avail_in z =? 0) && (len =? left) then 1 else 0 in
       let* buf := (if len =? 0 then Some [] else mb_read (d_window s) (d_block_start s) len) in
       let* o := c_tr_stored_block (d_out s) buf len last in
       let s := set_d_out s o in
       let* _ := guard (in_long (d_block_start s + len)) in
       let s := set_d_block_start s (d_block_start s + len) in
       let* (s, z) := c_flush_pending s z in
       Some (s, z, last)
     else Some (s, z, 0)) in
  if last =? 0 then Some (s, z, need_more) else Some (set_d_bi_used s 8, z, finish_started).

Lemma c_deflate_stored_split s z flush : c_deflate_stored s z flush =
  match loop FUEL (ds_body flush (u32 (let a := u64 (d_pending_buf_size s - 5) in
                                       if a >? d_w_size s then d_w_size s else a))) (s, z) with
  | Some (s1, z1, last) =>
      match c_ds_window s1 z1 (u32 (z_avail_in z - z_avail_in z1)) with
      | Some s2 => ds_tail (upd_high_water s2) z1 flush last
      | None => None
      end
  | None => None
  end.
Proof.
  unfold c_deflate_stored. destruct (loop _ _ _) as [[[s1 z1] last]|]; [|reflexivity].
  cbv beta iota delta [bind]. destruct (c_ds_window _ _ _); reflexivity.
Qed.

Lemma gc_ds_tail s z f last r : av z -> ds_tail s z f last = Some r ->
  out_grow z (snd (fst r)) /\ dlen s (fst (fst r)).
Proof.
  intros Hav H. unfold ds_tail in H. gdec; gfacts.
  all: repeat match goal with
       | E : c_tr_stored_block (d_out _) _ _ _ = Some _ |- _ =>
           let A := fresh "A" in
           pose proof (ol_tr_stored_block _ _ _ _ _ _ E) as A; cbn [fst] in A; clear E
       end.
  all: gconj; cbn [fst snd]; split; [og |].
  all: repeat match goal with
       | H : _ = true |- _ => clear H | H : _ = false |- _ => clear H | H : guard _ = _ |- _ => clear H
       | H : rds _ _ _ = _ |- _ => clear H | H : out_grow _ _ |- _ => clear H | H : zpos _ _ |- _ => clear H
       | H : zsame _ _ |- _ => clear H | H : av _ |- _ => clear H
       end.
  all: dpr.
Qed.



Lemma gc_deflate_stored_av s z f r : av z -> c_deflate_stored s z f = Some r ->
  out_grow z (snd (fst r)) /\ dkeep s (fst (fst r)).
Proof.
  intros Hav H. rewrite c_deflate_stored_split in H.
  destruct (loop _ _ _) as [[[s1 z1] last]|] eqn:E1; [|discriminate].
  destruct (c_ds_window _ _ _) as [s2|] eqn:E2; [|discriminate].
  apply gc_ds_loop in E1; [|exact Hav]. destruct E1 as (D1 & G1 & A1).
  apply gc_ds_window in E2. apply gc_ds_tail in H; [|exact A1]. destruct H as [G2 D2].
  split; [exact (out_grow_trans _ _ _ G1 G2)|]. apply dlen_dkeep.
  exact (dlen_trans _ _ _ D1 (dlen_trans _ _ _ E2 (dlen_trans _ _ _ (dlen_upd_high_water _) D2))).
Qed.


Lemma grow_deflate_fast : compress_facts c_deflate_fast.
Proof. exact gc_deflate_fast. Qed.

Lemma grow_deflate_slow : compress_facts c_deflate_slow.
Proof. exact gc_deflate_slow. Qed.

Lemma grow_deflate_rle : compress_facts c_deflate_rle.
Proof. exact gc_deflate_rle. Qed.

Lemma grow_deflate_huff : compress_facts c_deflate_huff.
Proof. exact gc_deflate_huff. Qed.

Lemma compress_facts_r_of c : compress_facts c -> compress_facts_r c.
Proof. intros F s z f r _ H. exact (F s z f r H). Qed.

Lemma grow_deflate_stored_r : compress_facts_r c_deflate_stored.
Proof.
  intros s z f r Hz H. apply (gc_deflate_stored_av s z f r); [|exact H].
  destruct Hz as (_ & _ & _ & _ & _ & _ & A & _). exact A.
Qed.

Theorem grow_compress_proved_r : grow_compress_all_r.
Proof.
  split; [exact grow_deflate_stored_r|].
  split; [exact (compress_facts_r_of _ grow_deflate_fast)|].
  split; [exact (compress_facts_r_of _ grow_deflate_slow)|].
  split; [exact (compress_facts_r_of _ grow_deflate_rle) | exact (compress_facts_r_of _ grow_deflate_huff)].
Qed.
