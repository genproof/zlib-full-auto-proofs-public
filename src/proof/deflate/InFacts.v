(** * Pure facts about the stages of deflate()'s model (DModel4, DeflateKit): no stage changes the input object
    of the call ([z_in]; only next_in / avail_in / total_in move).  Used by Body_deflate.v to give back the
    caller's input object. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

Definition stage_in (c : Z -> dstate -> strm -> option dres) : Prop :=
  forall f s z s' z' o, c f s z = Some (s', z', o) -> z_in z' = z_in z.

Definition compress_in (c : dstate -> strm -> Z -> option (dstate * strm * bstate)) : Prop :=
  forall s z f r, c s z f = Some r -> z_in (snd (fst r)) = z_in z.


(** ** Helpers: every model function that returns a stream keeps its [z_in]. *)

(** The kernel must not compute [loop FUEL] (2^40 iterations) when it checks an unfolding of a model function. *)
Local Strategy opaque [loop loop2].
Lemma then_stage_inv' r k s' z' o :
  then_stage r k = Some (s', z', o) ->
  exists s1 z1 o1, r = Some (s1, z1, o1) /\
    ((o1 <> None /\ s' = s1 /\ z' = z1) \/ (o1 = None /\ k s1 z1 = Some (s', z', o))).
Proof.
  unfold then_stage. intros H. inv_bind H. destruct x as [[s1 z1] o1]. exists s1, z1, o1. split; [auto|].
  destruct o1; [left; inversion H; subst; split; [discriminate | auto] | right; auto].
Qed.

(** A loop whose every iteration keeps the input object of its stream. *)
Lemma loop_zin {A B} (body : A -> option (A + B)) (ga : A -> strm) (gb : B -> strm) :
  (forall a x, body a = Some x ->
     match x with inl a' => z_in (ga a') = z_in (ga a) | inr r => z_in (gb r) = z_in (ga a) end) ->
  forall a r, loop FUEL body a = Some r -> z_in (gb r) = z_in (ga a).
Proof.
  intros Hb a r H. apply loop_runs in H. induction H as [a r E | a a' r E _ IH].
  - exact (Hb _ _ E).
  - rewrite IH. exact (Hb _ _ E).
Qed.

Ltac zin_norm := cbn [z_in set_z_in set_z_next_in set_z_avail_in set_z_total_in set_z_out set_z_avail_out
  set_z_total_out set_z_adler set_z_msg fst snd] in *.

Ltac zin_close := repeat match goal with
  | |- context [if ?b then _ else _] => destruct b
  | |- context [match ?x with inl _ => _ | inr _ => _ end] => destruct x
  end;
  zin_norm; congruence.

Ltac zin_step := fail.

Ltac zcrunch_step :=
  match goal with
  | H : Some _ = Some _ |- _ => inversion H; clear H; subst
  | H : None = Some _ |- _ => discriminate H
  | H : (_, _) = (_, _) |- _ => inversion H; clear H; subst
  | H : inl _ = inl _ |- _ => inversion H; clear H; subst
  | H : inr _ = inr _ |- _ => inversion H; clear H; subst
  | H : inl _ = inr _ |- _ => discriminate H
  | H : inr _ = inl _ |- _ => discriminate H
  | H : (if ?b then _ else _) = Some _ |- _ => destruct b
  | H : match ?x with None => _ | Some _ => _ end = Some _ |- _ => destruct x
  | H : match ?x with inl _ => _ | inr _ => _ end = Some _ |- _ => destruct x
  | H : match ?x with (_, _) => _ end = Some _ |- _ => destruct x
  | H : match ?x with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end = Some _ |- _ =>
      destruct x
  | H : bind _ _ = Some _ |- _ => inv_bind H; cbv beta iota zeta in H
  | H : then_stage _ _ = Some _ |- _ =>
      apply then_stage_inv' in H; destruct H as (? & ? & ? & ? & [(? & ? & ?) | (? & ?)]); subst
  end.

Ltac zcrunch := repeat (first [zcrunch_step | zin_step]; cbv beta iota zeta in * ).

Lemma zin_read_buf s z n z' d : c_read_buf s z n = Some (z', d) -> z_in z' = z_in z.
Proof. unfold c_read_buf. intros H. zcrunch; zin_close. Qed.

Lemma zin_out_put z b z' : out_put z b = Some z' -> z_in z' = z_in z.
Proof. unfold out_put. intros H. zcrunch; zin_close. Qed.

Lemma zin_flush_pending s z s' z' : c_flush_pending s z = Some (s', z') -> z_in z' = z_in z.
Proof.
  unfold c_flush_pending. intros H. zcrunch;
  try match goal with H : out_put _ _ = Some _ |- _ => apply zin_out_put in H end; zin_close.
Qed.

Lemma zin_hcrc_update h s z beg z' : c_hcrc_update h s z beg = Some z' -> z_in z' = z_in z.
Proof. unfold c_hcrc_update. intros H. zcrunch; zin_close. Qed.

Lemma zin_fw_body a x : fw_body a = Some x ->
  match x with inl a' => z_in (snd a') = z_in (snd a) | inr r => z_in (snd r) = z_in (snd a) end.
Proof.
  destruct a as [s z]. unfold fw_body. intros H. zcrunch;
  try match goal with H : c_read_buf _ _ _ = Some _ |- _ => apply zin_read_buf in H end; zin_close.
Qed.

Lemma zin_fill_window s z s' z' : c_fill_window s z = Some (s', z') -> z_in z' = z_in z.
Proof.
  unfold c_fill_window. intros H. inv_bind H. destruct x as [s1 z1]. inv_bind H. inversion H; subst.
  apply (loop_zin fw_body snd snd zin_fw_body) in Ha. exact Ha.
Qed.

Lemma zin_flush_block_only s z l s' z' : c_flush_block_only s z l = Some (s', z') -> z_in z' = z_in z.
Proof.
  unfold c_flush_block_only. intros H. zcrunch; eapply zin_flush_pending; eauto.
Qed.

Lemma zin_flush_block s z l s' z' r : c_flush_block s z l = Some (s', z', r) -> z_in z' = z_in z.
Proof.
  unfold c_flush_block. intros H. inv_bind H. destruct x as [s1 z1]. apply zin_flush_block_only in Ha.
  zcrunch; zin_close.
Qed.

Definition zstep {B} (z : strm) (x : (dstate * strm) + (dstate * strm * B)) : Prop :=
  match x with inl a => z_in (snd a) = z_in z | inr e => z_in (snd (fst e)) = z_in z end.

Lemma zin_bflush s z b x : c_bflush s z b = Some x -> zstep z x.
Proof.
  unfold c_bflush. intros H. destruct b; [|inversion H; reflexivity].
  inv_bind H. destruct x0 as [[s1 z1] r]. apply zin_flush_block in Ha.
  destruct r; inversion H; subst; exact Ha.
Qed.

Lemma zin_refill need flush s z x : c_refill need flush s z = Some x -> zstep z x.
Proof.
  unfold c_refill. intros H. destruct (need s); [|inversion H; reflexivity].
  inv_bind H. destruct x0 as [s1 z1]. apply zin_fill_window in Ha. cbv beta iota in H.
  repeat match type of H with (if ?b then _ else _) = _ => destruct b end; inversion H; subst; exact Ha.
Qed.

Lemma zin_deflate_tail s z f s' z' r : c_deflate_tail s z f = Some (s', z', r) -> z_in z' = z_in z.
Proof.
  unfold c_deflate_tail. intros H.
  repeat match type of H with (if ?b then _ else _) = _ => destruct b end;
  try (inversion H; subst; reflexivity);
  inv_bind H; destruct x as [[s1 z1] o]; apply zin_flush_block in Ha;
  destruct o; inversion H; subst; exact Ha.
Qed.

Ltac zin_step ::=
  match goal with
  | H : c_read_buf _ _ _ = Some ?r |- _ => try (is_var r; destruct r); apply zin_read_buf in H
  | H : out_put _ _ = Some _ |- _ => apply zin_out_put in H
  | H : c_flush_pending _ _ = Some ?r |- _ => try (is_var r; destruct r); apply zin_flush_pending in H
  | H : c_hcrc_update _ _ _ _ = Some _ |- _ => apply zin_hcrc_update in H
  | H : c_fill_window _ _ = Some ?r |- _ => try (is_var r; destruct r); apply zin_fill_window in H
  | H : c_flush_block_only _ _ _ = Some ?r |- _ => try (is_var r; destruct r); apply zin_flush_block_only in H
  | H : c_flush_block _ _ _ = Some ?r |- _ => try (is_var r; destruct r as [[? ?] ?]); apply zin_flush_block in H
  | H : c_bflush _ _ _ = Some _ |- _ => apply zin_bflush in H; unfold zstep in H
  | H : c_refill _ _ _ _ = Some _ |- _ => apply zin_refill in H; unfold zstep in H
  | H : c_deflate_tail _ _ _ = Some ?r |- _ => try (is_var r; destruct r as [[? ?] ?]); apply zin_deflate_tail in H
  end.

Lemma zin_ds_body flush mb a x : ds_body flush mb a = Some x -> zstep (snd a) x.
Proof. destruct a as [s z]. unfold ds_body. intros H. zcrunch; unfold zstep; zin_close. Qed.

Lemma zin_df_step s z x : df_step s z = Some x -> zstep z x.
Proof. unfold df_step. intros H. zcrunch; unfold zstep; zin_close. Qed.

Lemma zin_dsl_step s z x : dsl_step s z = Some x -> zstep z x.
Proof. unfold dsl_step. intros H. zcrunch; unfold zstep; zin_close. Qed.

Lemma zin_rle_step s z x : rle_step s z = Some x -> zstep z x.
Proof. unfold rle_step. intros H. zcrunch; unfold zstep; zin_close. Qed.

Lemma zin_df_body flush a x : DModel2.df_body flush a = Some x -> zstep (snd a) x.
Proof.
  destruct a as [s z]. unfold DModel2.df_body. intros H. inv_bind H. apply zin_refill in Ha. unfold zstep in *.
  destruct x0 as [[s1 z1]|e]; [apply zin_df_step in H; destruct x | inversion H; subst]; cbn in *; congruence.
Qed.

Lemma zin_dsl_body flush a x : dsl_body flush a = Some x -> zstep (snd a) x.
Proof.
  destruct a as [s z]. unfold dsl_body. intros H. inv_bind H. apply zin_refill in Ha. unfold zstep in *.
  destruct x0 as [[s1 z1]|e]; [apply zin_dsl_step in H; destruct x | inversion H; subst]; cbn in *; congruence.
Qed.

Lemma zin_rle_body flush a x : rle_body flush a = Some x -> zstep (snd a) x.
Proof.
  destruct a as [s z]. unfold rle_body. intros H. inv_bind H. apply zin_refill in Ha. unfold zstep in *.
  destruct x0 as [[s1 z1]|e]; [apply zin_rle_step in H; destruct x | inversion H; subst]; cbn in *; congruence.
Qed.

Lemma zin_huff_body flush a x : huff_body flush a = Some x -> zstep (snd a) x.
Proof. destruct a as [s z]. unfold huff_body. intros H. zcrunch; unfold zstep; zin_close. Qed.

Lemma loop_zstep {B} (body : dstate * strm -> option ((dstate * strm) + (dstate * strm * B))) :
  (forall a x, body a = Some x -> zstep (snd a) x) ->
  forall a r, loop FUEL body a = Some r -> z_in (snd (fst r)) = z_in (snd a).
Proof.
  intros Hb. apply (loop_zin body snd (fun e => snd (fst e))). intros a x E. exact (Hb _ _ E).
Qed.

Ltac zin_loop :=
  match goal with
  | H : loop _ (ds_body _ _) _ = Some ?r |- _ =>
      try (is_var r; destruct r as [[? ?] ?]); apply (loop_zstep _ (zin_ds_body _ _)) in H
  | H : loop _ (DModel2.df_body _) _ = Some ?r |- _ =>
      try (is_var r; destruct r as [[? ?] ?]); apply (loop_zstep _ (zin_df_body _)) in H
  | H : loop _ (dsl_body _) _ = Some ?r |- _ =>
      try (is_var r; destruct r as [[? ?] ?]); apply (loop_zstep _ (zin_dsl_body _)) in H
  | H : loop _ (rle_body _) _ = Some ?r |- _ =>
      try (is_var r; destruct r as [[? ?] ?]); apply (loop_zstep _ (zin_rle_body _)) in H
  | H : loop _ (huff_body _) _ = Some ?r |- _ =>
      try (is_var r; destruct r as [[? ?] ?]); apply (loop_zstep _ (zin_huff_body _)) in H
  end.

Ltac zin_compress c :=
  intros s z f r H; cbv [c] in H; repeat (first [zcrunch_step | zin_step | zin_loop]; cbv beta iota zeta in * );
  zin_close.

Lemma in_deflate_stored : compress_in c_deflate_stored.
Proof. zin_compress c_deflate_stored. Qed.

Lemma in_deflate_fast : compress_in c_deflate_fast.
Proof. zin_compress c_deflate_fast. Qed.

Lemma in_deflate_slow : compress_in c_deflate_slow.
Proof. zin_compress c_deflate_slow. Qed.

Lemma in_deflate_rle : compress_in c_deflate_rle.
Proof. zin_compress c_deflate_rle. Qed.

Lemma in_deflate_huff : compress_in c_deflate_huff.
Proof. zin_compress c_deflate_huff. Qed.

Lemma zin_compress_func s z f r : c_compress_func s z f = Some r -> z_in (snd (fst r)) = z_in z.
Proof.
  unfold c_compress_func. intros H.
  destruct (d_level s =? 0); [eapply in_deflate_stored; eauto|].
  destruct (d_strategy s =? Z_HUFFMAN_ONLY); [eapply in_deflate_huff; eauto|].
  destruct (d_strategy s =? Z_RLE); [eapply in_deflate_rle; eauto|].
  inv_bind H. destruct (x =? 0); [eapply in_deflate_stored; eauto|].
  destruct (x =? 1); [eapply in_deflate_fast; eauto | eapply in_deflate_slow; eauto].
Qed.

(** v6: the dispatch with the functions [ef] (DModel5). *)
Lemma zin_compress_func_g ef s z f r : c_compress_func_g ef s z f = Some r -> z_in (snd (fst r)) = z_in z.
Proof.
  unfold c_compress_func_g, c_compressor. intros H.
  destruct (d_level s =? 0).
  { destruct (ef 0 =? 0); [eapply in_deflate_stored; eauto|].
    destruct (ef 0 =? 1); [eapply in_deflate_fast; eauto | eapply in_deflate_slow; eauto]. }
  destruct (d_strategy s =? Z_HUFFMAN_ONLY); [eapply in_deflate_huff; eauto|].
  destruct (d_strategy s =? Z_RLE); [eapply in_deflate_rle; eauto|].
  inv_bind H. destruct (ef x =? 0); [eapply in_deflate_stored; eauto|].
  destruct (ef x =? 1); [eapply in_deflate_fast; eauto | eapply in_deflate_slow; eauto].
Qed.

Lemma zin_extra_body h x a e : extra_body h x a = Some e ->
  match e with
  | inl a' => z_in (snd (fst (fst a'))) = z_in (snd (fst (fst a)))
  | inr (inl a') => z_in (snd (fst (fst a'))) = z_in (snd (fst (fst a)))
  | inr (inr p) => z_in (snd p) = z_in (snd (fst (fst a)))
  end.
Proof. destruct a as [[[s z] beg] lft]. unfold extra_body. intros H. zcrunch; zin_close. Qed.

Lemma zin_extra_loop h x s z beg lft e : loop FUEL (extra_body h x) (s, z, beg, lft) = Some e ->
  match e with inl a' => z_in (snd (fst (fst a'))) = z_in z | inr p => z_in (snd p) = z_in z end.
Proof.
  intros H.
  apply (loop_zin (extra_body h x) (fun a => snd (fst (fst a)))
           (fun e => match e with inl a' => snd (fst (fst a')) | inr p => snd p end)) in H;
    [destruct e; exact H|].
  intros a y E. apply zin_extra_body in E. destruct y as [a'|[a'|p]]; exact E.
Qed.

Lemma zin_str_body h str a e : str_body h str a = Some e ->
  match e with
  | inl a' => z_in (snd (fst a')) = z_in (snd (fst a))
  | inr (inl a') => z_in (snd (fst a')) = z_in (snd (fst a))
  | inr (inr p) => z_in (snd p) = z_in (snd (fst a))
  end.
Proof. destruct a as [[s z] beg]. unfold str_body. intros H. zcrunch; zin_close. Qed.

Lemma zin_str_loop h str s z beg e : loop FUEL (str_body h str) (s, z, beg) = Some e ->
  match e with inl a' => z_in (snd (fst a')) = z_in z | inr p => z_in (snd p) = z_in z end.
Proof.
  intros H.
  apply (loop_zin (str_body h str) (fun a => snd (fst a))
           (fun e => match e with inl a' => snd (fst a') | inr p => snd p end)) in H;
    [destruct e; exact H|].
  intros a y E. apply zin_str_body in E. destruct y as [a'|[a'|p]]; exact E.
Qed.

Ltac zin_step ::=
  match goal with
  | H : c_read_buf _ _ _ = Some ?r |- _ => try (is_var r; destruct r); apply zin_read_buf in H
  | H : out_put _ _ = Some _ |- _ => apply zin_out_put in H
  | H : c_flush_pending _ _ = Some ?r |- _ => try (is_var r; destruct r); apply zin_flush_pending in H
  | H : c_hcrc_update _ _ _ _ = Some _ |- _ => apply zin_hcrc_update in H
  | H : c_fill_window _ _ = Some ?r |- _ => try (is_var r; destruct r); apply zin_fill_window in H
  | H : c_flush_block_only _ _ _ = Some ?r |- _ => try (is_var r; destruct r); apply zin_flush_block_only in H
  | H : c_flush_block _ _ _ = Some ?r |- _ => try (is_var r; destruct r as [[? ?] ?]); apply zin_flush_block in H
  | H : c_bflush _ _ _ = Some _ |- _ => apply zin_bflush in H; unfold zstep in H
  | H : c_refill _ _ _ _ = Some _ |- _ => apply zin_refill in H; unfold zstep in H
  | H : c_deflate_tail _ _ _ = Some ?r |- _ => try (is_var r; destruct r as [[? ?] ?]); apply zin_deflate_tail in H
  | H : c_compress_func _ _ _ = Some ?r |- _ =>
      try (is_var r; destruct r as [[? ?] [| | |]]); apply zin_compress_func in H
  | H : c_compress_func_g _ _ _ _ = Some ?r |- _ =>
      try (is_var r; destruct r as [[? ?] [| | |]]); apply zin_compress_func_g in H
  | H : loop _ (extra_body _ _) _ = Some ?e |- _ =>
      apply zin_extra_loop in H; try (is_var e; destruct e as [[[[? ?] ?] ?] | [? ?]])
  | H : loop _ (str_body _ _) _ = Some ?e |- _ =>
      apply zin_str_loop in H; try (is_var e; destruct e as [[[? ?] ?] | [? ?]])
  end.

Ltac zin_stage := intros ? ? ? ? ? ? H; cbv [c_entry2 c_deflate_entry c_zlib2 c_flush_or_return c_deflate_gzip_header
  c_deflate_extra c_gzhead c_deflate_name c_deflate_comment c_deflate_str c_deflate_hcrc c_deflate_compress
  c_trailer2 c_deflate_trailer] in H; zcrunch; zin_close.

Lemma in_entry : stage_in c_entry2.
Proof. zin_stage. Qed.

Lemma in_zlib : stage_in (fun _ => c_zlib2).
Proof. zin_stage. Qed.

Lemma in_gzip : stage_in (fun _ => c_deflate_gzip_header).
Proof. zin_stage. Qed.

Lemma in_extra : stage_in (fun _ => c_deflate_extra).
Proof. zin_stage. Qed.

Lemma in_name : stage_in (fun _ => c_deflate_name).
Proof. zin_stage. Qed.

Lemma in_comment : stage_in (fun _ => c_deflate_comment).
Proof. zin_stage. Qed.

Lemma in_hcrc : stage_in (fun _ => c_deflate_hcrc).
Proof. zin_stage. Qed.

Lemma in_compress : stage_in (fun f s z => c_deflate_compress s z f).
Proof. zin_stage. Qed.

Lemma in_compress_g ef : stage_in (fun f s z => c_deflate_compress_g ef s z f).
Proof. intros ? ? ? ? ? ? H; cbv [c_deflate_compress_g] in H; zcrunch; zin_close. Qed.

Lemma in_trailer : stage_in (fun f s z => c_trailer2 s z f).
Proof. zin_stage. Qed.

Theorem deflate_in_proved :
  stage_in c_entry2 /\ stage_in (fun _ => c_zlib2) /\ stage_in (fun _ => c_deflate_gzip_header) /\
  stage_in (fun _ => c_deflate_extra) /\ stage_in (fun _ => c_deflate_name) /\
  stage_in (fun _ => c_deflate_comment) /\ stage_in (fun _ => c_deflate_hcrc) /\
  stage_in (fun f s z => c_deflate_compress s z f) /\ stage_in (fun f s z => c_trailer2 s z f).
Proof.
  exact (conj in_entry (conj in_zlib (conj in_gzip (conj in_extra (conj in_name (conj in_comment
    (conj in_hcrc (conj in_compress in_trailer)))))))).
Qed.
