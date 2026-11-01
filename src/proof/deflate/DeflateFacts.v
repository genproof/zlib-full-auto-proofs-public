(** * Pure facts about the stages of deflate()'s model (DModel4, DeflateKit), used to chain the stage triples in
    Body_deflate.v: every stage only appends to the output ([out_grow]) and keeps the gz_header and the sizes of
    the allocations ([dkeep]); see [stage_facts] in DeflateKit.  The compression stage assumes the same of the
    five compression functions ([grow_compress_all], proved in GrowCompress.v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
Require Import Zlib.proof.deflate.GrowCompress.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** ** Output buffer length of the bit-output primitives *)
Definition olen (om : cout) : Z := Zlength (o_buf (fst om)).

Lemma wr_len l i v l' : wr l i v = Some l' -> Zlength l' = Zlength l.
Proof.
  unfold wr. destruct (in_range i (Zlength l)); intros H; inversion H; subst. apply Zlength_upd_Znth.
Qed.

Lemma put_byte_len om c om' : c_put_byte om c = Some om' -> olen om' = olen om.
Proof.
  destruct om as [o m]. unfold c_put_byte. intros H. inv_bind H. inversion H; subst.
  unfold olen; cbn. eapply wr_len; eauto.
Qed.

Lemma put_short_len om c om' : c_put_short om c = Some om' -> olen om' = olen om.
Proof.
  unfold c_put_short. intros H. inv_bind H. apply put_byte_len in Ha. apply put_byte_len in H. congruence.
Qed.

Lemma send_bits_len om v l om' : c_send_bits om v l = Some om' -> olen om' = olen om.
Proof.
  destruct om as [o m]. unfold c_send_bits. intros H. inv_bind H.
  destruct (o_bi_valid o >? Buf_size - l).
  - inv_bind H. destruct x0 as [o1 m1]. inversion H; subst. apply put_short_len in Ha0. exact Ha0.
  - inversion H; subst. reflexivity.
Qed.

Lemma send_code_len om c cs ls om' : c_send_code om c cs ls = Some om' -> olen om' = olen om.
Proof.
  unfold c_send_code. intros H. inv_bind H. inv_bind H. eapply send_bits_len; eauto.
Qed.

Lemma bi_flush_len om om' : c_bi_flush om = Some om' -> olen om' = olen om.
Proof.
  destruct om as [o m]. unfold c_bi_flush. intros H.
  destruct (o_bi_valid o =? 16).
  - inv_bind H. destruct x as [o1 m1]. inversion H; subst. apply put_short_len in Ha. exact Ha.
  - destruct (o_bi_valid o >=? 8).
    + inv_bind H. destruct x as [o1 m1]. inversion H; subst. apply put_byte_len in Ha. exact Ha.
    + inversion H; subst. reflexivity.
Qed.

Lemma bi_windup_len om om' : c_bi_windup om = Some om' -> olen om' = olen om.
Proof.
  destruct om as [o m]. unfold c_bi_windup. intros H. inv_bind H. inv_bind H. destruct x0 as [o1 m1].
  inversion H; subst. unfold olen; cbn. change (o_buf o1) with (o_buf (fst (o1, m1))).
  destruct (o_bi_valid o >? 8); [apply put_short_len in Ha0; exact Ha0|].
  destruct (o_bi_valid o >? 0); [apply put_byte_len in Ha0; exact Ha0|].
  inversion Ha0; subst. reflexivity.
Qed.

Lemma tr_align_len om om' : c_tr_align om = Some om' -> olen om' = olen om.
Proof.
  unfold c_tr_align. intros H. inv_bind H. inv_bind H.
  apply send_bits_len in Ha. apply send_code_len in Ha0. apply bi_flush_len in H. congruence.
Qed.

Lemma tr_stored_block_len om last om' : c_tr_stored_block om [] 0 last = Some om' -> olen om' = olen om.
Proof.
  unfold c_tr_stored_block. intros H. inv_bind H. inv_bind H. inv_bind H. inv_bind H.
  destruct x2 as [o2 m2]. cbn in H. inversion H; subst. unfold olen; cbn.
  apply send_bits_len in Ha. apply bi_windup_len in Ha0. apply put_short_len in Ha1. apply put_short_len in Ha2.
  unfold olen in *; cbn in *. congruence.
Qed.

(** ** What the stages keep: [dkeep] with equal buffer lengths *)
Definition dsame (s s' : dstate) : Prop :=
  d_gzhead s' = d_gzhead s /\ d_w_size s' = d_w_size s /\ d_hash_size s' = d_hash_size s /\
  tr_lit_bufsize (d_tr s') = tr_lit_bufsize (d_tr s) /\
  Zlength (mb_val (d_window s')) = Zlength (mb_val (d_window s)) /\ Zlength (d_prev s') = Zlength (d_prev s) /\
  Zlength (d_head s') = Zlength (d_head s) /\ Zlength (o_buf (tr_out (d_tr s'))) = Zlength (o_buf (tr_out (d_tr s))).

Lemma dsame_refl s : dsame s s.
Proof. unfold dsame. repeat split. Qed.

Lemma dsame_trans s1 s2 s3 : dsame s1 s2 -> dsame s2 s3 -> dsame s1 s3.
Proof. unfold dsame. intuition congruence. Qed.

Lemma dsame_dkeep s s' : dsame s s' -> dkeep s s'.
Proof.
  unfold dsame, dkeep, dsizes. intros (A & B & C & D & E & F & G & H).
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  intros (I & J & K & L). repeat split; congruence.
Qed.

Ltac dsame_triv := unfold dsame; cbn; repeat split.

Lemma dsame_set_out s o : Zlength (o_buf (fst o)) = Zlength (o_buf (tr_out (d_tr s))) -> dsame s (set_d_out s o).
Proof. intros. dsame_triv. exact H. Qed.

Lemma dsame_put_byte s c s' : c_dput_byte s c = Some s' -> dsame s s'.
Proof.
  unfold c_dput_byte. intros H. inv_bind H. inversion H; subst. apply dsame_set_out.
  apply put_byte_len in Ha. exact Ha.
Qed.

Lemma dsame_put_bytes l s s' : c_dput_bytes s l = Some s' -> dsame s s'.
Proof.
  revert s; induction l as [|c l IH]; intros s H; cbn in H.
  - inversion H; subst. apply dsame_refl.
  - inv_bind H. eapply dsame_trans; [eapply dsame_put_byte; eauto | eauto].
Qed.

Lemma dsame_putShortMSB s b s' : c_putShortMSB s b = Some s' -> dsame s s'.
Proof.
  unfold c_putShortMSB. intros H. inv_bind H. eapply dsame_trans; eapply dsame_put_byte; eauto.
Qed.

Lemma dsame_flush s z s' z' : c_flush_pending s z = Some (s', z') -> dsame s s'.
Proof.
  unfold c_flush_pending. intros H. inv_bind H. apply bi_flush_len in Ha.
  assert (D1 : dsame s (set_d_out s x)) by (apply dsame_set_out; exact Ha).
  case_if H; [inversion H; subst; exact D1|].
  inv_bind H. inv_bind H. inversion H; subst; clear H.
  eapply dsame_trans; [exact D1|].
  match goal with |- context [if ?b then _ else _] => destruct b end; dsame_triv.
Qed.

Lemma flush_facts s z s' z' : c_flush_pending s z = Some (s', z') -> out_grow z z' /\ dsame s s'.
Proof.
  intros H. split; [apply (c_flush_pending_grow _ _ _ H) | eapply dsame_flush; eauto].
Qed.

Lemma flush_or_return_facts s z s' z' o : c_flush_or_return s z = Some (s', z', o) -> out_grow z z' /\ dsame s s'.
Proof.
  unfold c_flush_or_return. intros H. inv_bind H. destruct x as [s1 z1]. apply flush_facts in Ha.
  destruct (negb _); inversion H; subst; [|exact Ha].
  destruct Ha as [G D]. split; [exact G|]. eapply dsame_trans; [exact D|]. dsame_triv.
Qed.

Lemma hcrc_update_grow h s z beg z' : c_hcrc_update h s z beg = Some z' -> out_grow z z'.
Proof.
  unfold c_hcrc_update. intros H. case_if H.
  - inv_bind H. inversion H; subst. apply out_grow_same; reflexivity.
  - inversion H; subst. apply out_grow_refl.
Qed.

Lemma dsame_mb_write s lo bytes pb : mb_write (d_pb s) lo bytes = Some pb -> dsame s (set_d_pb s pb).
Proof.
  unfold mb_write. intros H. case_if H; [|discriminate]. inversion H; subst; clear H.
  apply andb_true_iff in Heqb. destruct Heqb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  unfold d_pb in *; cbn [mb_val] in *. set (l := o_buf (tr_out (d_tr s))) in *.
  assert (L : Zlength (sublist 0 lo l ++ bytes ++ sublist (lo + Zlength bytes) (Zlength l) l) = Zlength l).
  { rewrite !Zlength_app, !Zlength_sublist by (pose proof (Zlength_nonneg bytes); lia). lia. }
  dsame_triv. exact L.
Qed.

Lemma dsame_set_pending s x : dsame s (set_d_pending s x).
Proof. dsame_triv. Qed.

(** ** The stages *)
Definition sfacts (z z' : strm) (s s' : dstate) : Prop := out_grow z z' /\ dsame s s'.

Lemma sfacts_refl z s : sfacts z z s s.
Proof. split; [apply out_grow_refl | apply dsame_refl]. Qed.

Lemma sfacts_trans z1 z2 z3 s1 s2 s3 : sfacts z1 z2 s1 s2 -> sfacts z2 z3 s2 s3 -> sfacts z1 z3 s1 s3.
Proof. intros [A B] [C D]. split; [eapply out_grow_trans | eapply dsame_trans]; eauto. Qed.

Lemma sfacts_stage_facts (c : Z -> dstate -> strm -> option dres) :
  (forall f s z s' z' o, c f s z = Some (s', z', o) -> sfacts z z' s s') -> stage_facts c.
Proof.
  intros H f s z s' z' o E. destruct (H _ _ _ _ _ _ E) as [A B]. split; [exact A | apply dsame_dkeep; exact B].
Qed.

Lemma then_stage_inv r k s' z' o :
  then_stage r k = Some (s', z', o) ->
  exists s1 z1 o1, r = Some (s1, z1, o1) /\
    ((o1 <> None /\ s' = s1 /\ z' = z1) \/ (o1 = None /\ k s1 z1 = Some (s', z', o))).
Proof.
  unfold then_stage. intros H. inv_bind H. destruct x as [[s1 z1] o1]. exists s1, z1, o1. split; [auto|].
  destruct o1; [left; inversion H; subst; split; [discriminate | auto] | right; auto].
Qed.



Lemma dsame_clear_hash s s' : c_clear_hash s = Some s' -> dsame s s'.
Proof.
  unfold c_clear_hash. intros H. inv_bind H. inv_bind H. inversion H; subst; clear H.
  unfold guard in Ha0. case_if Ha0; [|discriminate].
  apply andb_true_iff in Heqb. destruct Heqb as [H1 H2]. apply Z.leb_le in H1. apply Z.eqb_eq in H2.
  apply wr_len in Ha.
  dsame_triv. rewrite Zlength_repeat by lia. lia.
Qed.

Lemma dsame_init_busy s : dsame s (init_busy s).
Proof. unfold init_busy. destruct (_ && _)%bool; dsame_triv. Qed.

Lemma dsame_tr_align s om : c_tr_align (d_out s) = Some om -> dsame s (set_d_out s om).
Proof. intros H. apply dsame_set_out. apply tr_align_len in H. exact H. Qed.

Lemma dsame_tr_stored s om : c_tr_stored_block (d_out s) [] 0 0 = Some om -> dsame s (set_d_out s om).
Proof. intros H. apply dsame_set_out. apply tr_stored_block_len in H. exact H. Qed.

(** ** Automation: turn a model run into [out_grow] / [dsame] steps, then chain them. *)
Ltac crunch_step :=
  match goal with
  | H : Some _ = Some _ |- _ => inversion H; clear H; subst
  | H : None = Some _ |- _ => discriminate H
  | H : (_, _) = (_, _) |- _ => inversion H; clear H; subst
  | H : out_grow _ _ /\ dsame _ _ |- _ => destruct H
  | H : (if ?b then _ else _) = Some _ |- _ => destruct b
  | H : match ?x with None => _ | Some _ => _ end = Some _ |- _ => destruct x
  | H : match ?x with (_, _) => _ end = Some _ |- _ => destruct x
  | H : bind _ _ = Some _ |- _ => inv_bind H; cbv beta iota zeta in H
  | H : then_stage _ _ = Some _ |- _ =>
      apply then_stage_inv in H; destruct H as (? & ? & ? & ? & [(? & ? & ?) | (? & ?)]); subst
  | H : c_flush_pending _ _ = Some ?r |- _ => try (is_var r; destruct r); apply flush_facts in H
  | H : c_flush_or_return _ _ = Some ?r |- _ =>
      try (is_var r; destruct r as [[? ?] ?]); apply flush_or_return_facts in H
  | H : c_dput_byte _ _ = Some _ |- _ => apply dsame_put_byte in H
  | H : c_dput_bytes _ _ = Some _ |- _ => apply dsame_put_bytes in H
  | H : c_putShortMSB _ _ = Some _ |- _ => apply dsame_putShortMSB in H
  | H : c_hcrc_update _ _ _ _ = Some _ |- _ => apply hcrc_update_grow in H
  | H : mb_write (d_pb _) _ _ = Some _ |- _ => apply dsame_mb_write in H
  | H : c_clear_hash _ = Some _ |- _ => apply dsame_clear_hash in H
  | H : c_tr_align (d_out _) = Some _ |- _ => apply dsame_tr_align in H
  | H : c_tr_stored_block (d_out _) [] 0 0 = Some _ |- _ => apply dsame_tr_stored in H
  end.
Ltac crunch := repeat (crunch_step; cbv beta iota zeta in * ).

Ltac og_close := solve [ apply out_grow_same; reflexivity
  | match goal with H : out_grow ?za ?zb |- out_grow ?z ?z' =>
      apply (out_grow_trans z za z'); [apply out_grow_same; reflexivity |
        apply (out_grow_trans za zb z' H); clear H; og_close] end ].
Ltac ds_close := solve [ dsame_triv
  | match goal with |- dsame ?s (init_busy ?sb) => apply (dsame_trans s sb); [ds_close | apply dsame_init_busy] end
  | match goal with H : dsame ?sa ?sb |- dsame ?s ?s' =>
      apply (dsame_trans s sa s'); [solve [dsame_triv] |
        apply (dsame_trans sa sb s' H); clear H; ds_close] end ].
Ltac sf_close := repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  (split; [og_close | ds_close]).
Ltac stage_auto c := apply sfacts_stage_facts; intros ? ? ? ? ? ? H; cbv [c] in H; crunch; sf_close.

(** ** The EXTRA / NAME / COMMENT loops *)
Lemma extra_runs h x a e : runs (extra_body h x) a e ->
  match a with (s, z, _, _) =>
    match e with inl (s1, z1, _, _) => out_grow z z1 /\ dsame s s1 | inr (s1, z1) => out_grow z z1 /\ dsame s s1 end
  end.
Proof.
  induction 1 as [a r Hb | a a' r Hb Hr IH].
  - destruct a as [[[s z] beg] lft]. cbv [extra_body] in Hb. crunch; sf_close.
  - destruct a as [[[s z] beg] lft]. destruct a' as [[[s1 z1] beg1] lft1].
    destruct r as [[[[s2 z2] b2] l2] | [s2 z2]]; destruct IH;
    cbv [extra_body] in Hb; crunch; sf_close.
Qed.

Lemma str_runs h str a e : runs (str_body h str) a e ->
  match a with (s, z, _) =>
    match e with inl (s1, z1, _) => out_grow z z1 /\ dsame s s1 | inr (s1, z1) => out_grow z z1 /\ dsame s s1 end
  end.
Proof.
  induction 1 as [a r Hb | a a' r Hb Hr IH].
  - destruct a as [[s z] beg]. cbv [str_body] in Hb. crunch; sf_close.
  - destruct a as [[s z] beg]. destruct a' as [[s1 z1] beg1].
    destruct r as [[[s2 z2] b2] | [s2 z2]]; destruct IH;
    cbv [str_body] in Hb; crunch; sf_close.
Qed.

Ltac crunch_loop :=
  repeat (first [crunch_step
    | match goal with
      | H : loop _ (extra_body _ _) _ = Some ?e |- _ =>
          apply loop_runs, extra_runs in H; try (is_var e; destruct e as [[[[? ?] ?] ?] | [? ?]])
      | H : loop _ (str_body _ _) _ = Some ?e |- _ =>
          apply loop_runs, str_runs in H; try (is_var e; destruct e as [[[? ?] ?] | [? ?]])
      end]; cbv beta iota zeta in * ).

Lemma facts_entry : stage_facts c_entry2.
Proof.
  apply sfacts_stage_facts; intros ? ? ? ? ? ? H; cbv [c_entry2 c_deflate_entry] in H; crunch; sf_close.
Qed.

Lemma facts_zlib : stage_facts (fun _ => c_zlib2).
Proof.
  apply sfacts_stage_facts; intros ? ? ? ? ? ? H; cbv [c_zlib2] in H; crunch; sf_close.
Qed.

Lemma facts_gzip : stage_facts (fun _ => c_deflate_gzip_header).
Proof.
  apply sfacts_stage_facts; intros ? ? ? ? ? ? H; cbv [c_deflate_gzip_header] in H; crunch; sf_close.
Qed.

Lemma facts_extra : stage_facts (fun _ => c_deflate_extra).
Proof.
  apply sfacts_stage_facts; intros ? ? ? ? ? ? H; cbv [c_deflate_extra c_gzhead] in H; crunch_loop; sf_close.
Qed.

Lemma facts_name : stage_facts (fun _ => c_deflate_name).
Proof.
  apply sfacts_stage_facts; intros ? ? ? ? ? ? H; cbv [c_deflate_name c_deflate_str c_gzhead] in H; crunch_loop; sf_close.
Qed.

Lemma facts_comment : stage_facts (fun _ => c_deflate_comment).
Proof.
  apply sfacts_stage_facts; intros ? ? ? ? ? ? H; cbv [c_deflate_comment c_deflate_str c_gzhead] in H; crunch_loop; sf_close.
Qed.

Lemma facts_hcrc : stage_facts (fun _ => c_deflate_hcrc).
Proof.
  apply sfacts_stage_facts; intros ? ? ? ? ? ? H; cbv [c_deflate_hcrc] in H; crunch; sf_close.
Qed.

Lemma dkeep_dsame s1 s2 s3 : dkeep s1 s2 -> dsame s2 s3 -> dkeep s1 s3.
Proof. intros A B. eapply dkeep_trans; [exact A | apply dsame_dkeep; exact B]. Qed.

Lemma compress_func_facts s z f r : grow_compress_all -> c_compress_func s z f = Some r ->
  out_grow z (snd (fst r)) /\ dkeep s (fst (fst r)).
Proof.
  intros (Hst & Hfa & Hsl & Hrl & Hhf) H. unfold c_compress_func in H.
  destruct (d_level s =? 0); [eapply Hst; eauto|].
  destruct (d_strategy s =? Z_HUFFMAN_ONLY); [eapply Hhf; eauto|].
  destruct (d_strategy s =? Z_RLE); [eapply Hrl; eauto|].
  inv_bind H. destruct (x =? 0); [eapply Hst; eauto|]. destruct (x =? 1); [eapply Hfa; eauto | eapply Hsl; eauto].
Qed.

Lemma facts_compress : grow_compress_all -> stage_facts (fun f s z => c_deflate_compress s z f).
Proof.
  intros G f s z s' z' o H. cbv [c_deflate_compress] in H.
  match type of H with (if ?b then _ else _) = _ => destruct b end;
    [|inversion H; subst; split; [apply out_grow_refl | apply dkeep_refl]].
  inv_bind H. destruct x as [[s1 z1] bs]. apply (compress_func_facts _ _ _ _ G) in Ha. cbn [fst snd] in Ha.
  destruct Ha as [Ha1 Ha2].
  destruct bs; crunch;
    (repeat match goal with |- context [if ?b then _ else _] => destruct b end);
    (split; [og_close | apply (dkeep_dsame _ _ _ Ha2); ds_close]).
Qed.

Lemma facts_trailer : stage_facts (fun f s z => c_trailer2 s z f).
Proof.
  apply sfacts_stage_facts; intros ? ? ? ? ? ? H; cbv [c_trailer2 c_deflate_trailer] in H; crunch; sf_close.
Qed.

Theorem deflate_facts_proved :
  stage_facts c_entry2 /\ stage_facts (fun _ => c_zlib2) /\ stage_facts (fun _ => c_deflate_gzip_header) /\
  stage_facts (fun _ => c_deflate_extra) /\ stage_facts (fun _ => c_deflate_name) /\
  stage_facts (fun _ => c_deflate_comment) /\ stage_facts (fun _ => c_deflate_hcrc) /\
  (grow_compress_all -> stage_facts (fun f s z => c_deflate_compress s z f)) /\
  stage_facts (fun f s z => c_trailer2 s z f).
Proof.
  exact (conj facts_entry (conj facts_zlib (conj facts_gzip (conj facts_extra (conj facts_name (conj facts_comment
    (conj facts_hcrc (conj facts_compress facts_trailer)))))))).
Qed.
