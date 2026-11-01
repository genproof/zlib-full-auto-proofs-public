(* One deflate() call leaves a valid state valid: the status deflate() returns with is one deflateStateCheck
   accepts, so a deflateEnd after it frees the stream's blocks (law res_free_deflate).  deflate()'s own stages
   set the status only to the states of status_ok (BUSY_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE,
   HCRC_STATE, FINISH_STATE); the compression functions and trees.c do not touch it. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec.
#[local] Existing Instance DCS.CS.

(** The kernel must never unfold the loops (binary fuel 2^40) when it compares hypotheses. *)
Local Strategy expand [bind].
Local Strategy opaque [loop loop2].

(** ** The setters other than [set_d_status] keep the status *)

Lemma st_set_status s v : d_status (set_d_status s v) = v. Proof. reflexivity. Qed.
Lemma st_t_d_po s v : d_status (set_d_po s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_wrap s v : d_status (set_d_wrap s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_gzhead s v : d_status (set_d_gzhead s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_gzindex s v : d_status (set_d_gzindex s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_method s v : d_status (set_d_method s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_last_flush s v : d_status (set_d_last_flush s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_w_size s v : d_status (set_d_w_size s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_w_bits s v : d_status (set_d_w_bits s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_w_mask s v : d_status (set_d_w_mask s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_window s v : d_status (set_d_window s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_window_size s v : d_status (set_d_window_size s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_prev s v : d_status (set_d_prev s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_head s v : d_status (set_d_head s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_ins_h s v : d_status (set_d_ins_h s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_hash_size s v : d_status (set_d_hash_size s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_hash_bits s v : d_status (set_d_hash_bits s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_hash_mask s v : d_status (set_d_hash_mask s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_hash_shift s v : d_status (set_d_hash_shift s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_block_start s v : d_status (set_d_block_start s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_match_length s v : d_status (set_d_match_length s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_prev_match s v : d_status (set_d_prev_match s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_match_available s v : d_status (set_d_match_available s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_strstart s v : d_status (set_d_strstart s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_match_start s v : d_status (set_d_match_start s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_lookahead s v : d_status (set_d_lookahead s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_prev_length s v : d_status (set_d_prev_length s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_max_chain_length s v : d_status (set_d_max_chain_length s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_max_lazy_match s v : d_status (set_d_max_lazy_match s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_good_match s v : d_status (set_d_good_match s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_nice_match s v : d_status (set_d_nice_match s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_insert s v : d_status (set_d_insert s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_high_water s v : d_status (set_d_high_water s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_slid s v : d_status (set_d_slid s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_pending_buf_size s v : d_status (set_d_pending_buf_size s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_tr s v : d_status (set_d_tr s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_pbm s v : d_status (set_d_pbm s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_trm s v : d_status (set_d_trm s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_out s v : d_status (set_d_out s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_pb s v : d_status (set_d_pb s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_bi_used s v : d_status (set_d_bi_used s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_matches s v : d_status (set_d_matches s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_pending s v : d_status (set_d_pending s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_level s v : d_status (set_d_level s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_t_d_strategy s v : d_status (set_d_strategy s v) = d_status s. Proof. reflexivity. Qed.
Lemma st_incr_matches s : d_status (incr_matches s) = d_status s.
Proof. unfold incr_matches. destruct (_ <? _); reflexivity. Qed.
Lemma st_clamp_insert s : d_status (clamp_insert s) = d_status s.
Proof. unfold clamp_insert. destruct (_ >? _); reflexivity. Qed.
Lemma st_add_insert s n : d_status (add_insert s n) = d_status s. Proof. reflexivity. Qed.
Lemma st_upd_high_water s : d_status (upd_high_water s) = d_status s.
Proof. unfold upd_high_water. destruct (_ <? _); reflexivity. Qed.
Lemma st_set_insert_end s : d_status (set_insert_end s) = d_status s. Proof. reflexivity. Qed.
#[local] Hint Rewrite st_t_d_po st_t_d_wrap st_t_d_gzhead st_t_d_gzindex st_t_d_method st_t_d_last_flush st_t_d_w_size st_t_d_w_bits st_t_d_w_mask st_t_d_window st_t_d_window_size st_t_d_prev st_t_d_head st_t_d_ins_h st_t_d_hash_size st_t_d_hash_bits st_t_d_hash_mask st_t_d_hash_shift st_t_d_block_start st_t_d_match_length st_t_d_prev_match st_t_d_match_available st_t_d_strstart st_t_d_match_start st_t_d_lookahead st_t_d_prev_length st_t_d_max_chain_length st_t_d_max_lazy_match st_t_d_good_match st_t_d_nice_match st_t_d_insert st_t_d_high_water st_t_d_slid st_t_d_pending_buf_size st_t_d_tr st_t_d_pbm st_t_d_trm st_t_d_out st_t_d_pb st_t_d_bi_used st_t_d_matches st_t_d_pending st_t_d_level st_t_d_strategy st_set_status st_incr_matches st_clamp_insert st_add_insert st_upd_high_water st_set_insert_end : stdb.

(** ** Tactics: run a model function on a hypothesis [f .. = Some r] *)

Lemma ds_some_inj {A} (a b : A) : Some a = Some b -> a = b.
Proof. congruence. Qed.

Ltac sstep :=
  match goal with
  | x : (_ * _)%type |- _ => destruct x
  | x : cstate |- _ => destruct x
  | x : cout |- _ => destruct x
  | x : dexit |- _ => destruct x
  | H : Some _ = Some _ |- _ => apply ds_some_inj in H
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

Ltac sdec := repeat (sstep; cbv beta iota zeta in *).

(** Close a goal [d_status X = d_status s] or [status_ok (d_status X) = true] from the status equations of the
    context. *)
Ltac sclear :=
  repeat match goal with H : ?T |- _ =>
    match type of T with Prop => idtac end;
    lazymatch T with d_status _ = _ => fail | status_ok _ = _ => fail | _ = d_status _ => fail | _ => clear H end
  end.

Ltac sclose :=
  sclear; cbn [fst snd lm_s] in *; autorewrite with stdb in *;
  repeat match goal with
  | |- context [d_status (if ?b then _ else _)] => destruct b
  | H : context [d_status (if ?b then _ else _)] |- _ => destruct b
  end;
  autorewrite with stdb in *; cbn [fst snd] in *;
  first [reflexivity | congruence].

(** A loop whose body keeps the status keeps it. *)
Lemma loop_status {A B} d (body : A -> option (A + B)) (f : A -> dstate) (g : B -> dstate) :
  (forall a a', body a = Some (inl a') -> d_status (f a') = d_status (f a)) ->
  (forall a r, body a = Some (inr r) -> d_status (g r) = d_status (f a)) ->
  forall a r, loop d body a = Some r -> d_status (g r) = d_status (f a).
Proof.
  intros H1 H2 a r H. apply loop_runs in H. induction H as [a r E|a a' r E _ IH]; eauto.
  rewrite IH. eauto.
Qed.

(** ** The hash, fill_window, longest_match *)

Lemma st_insert_string s str s' h : c_insert_string s str = Some (s', h) -> d_status s' = d_status s.
Proof. unfold c_insert_string. intros H. sdec. sclose. Qed.

Lemma st_clear_hash s s' : c_clear_hash s = Some s' -> d_status s' = d_status s.
Proof. unfold c_clear_hash. intros H. sdec. sclose. Qed.

Lemma st_slide_hash s s' : c_slide_hash s = Some s' -> d_status s' = d_status s.
Proof. unfold c_slide_hash. intros H. sdec. sclose. Qed.

Lemma st_fw_slide s more s' m : c_fw_slide s more = Some (s', m) -> d_status s' = d_status s.
Proof.
  unfold c_fw_slide. intros H. sdec.
  all: repeat match goal with E : c_slide_hash _ = Some _ |- _ => apply st_slide_hash in E end.
  all: sclose.
Qed.

Lemma st_fw_insert s s' : c_fw_insert s = Some s' -> d_status s' = d_status s.
Proof.
  unfold c_fw_insert. intros H. sdec; [|sclose].
  apply (loop_status _ _ fst (fun r => r)) in H; [sclose| |].
  - intros [s1 str] a' Eb. unfold fw_insert_body in Eb. sdec. sclose.
  - intros [s1 str] r Eb. unfold fw_insert_body in Eb. sdec; sclose.
Qed.

Lemma st_fill_window s z s' z' : c_fill_window s z = Some (s', z') -> d_status s' = d_status s.
Proof.
  unfold c_fill_window. intros H. sdec.
  match goal with E : loop _ _ _ = Some _ |- _ => apply (loop_status _ _ fst fst) in E end.
  - assert (d_status s' = d_status d).
    { revert E0. unfold c_fw_high_water. intros H. sdec; sclose. }
    cbn [fst] in *. congruence.
  - intros [s1 z1] a' E1. unfold fw_body in E1. sdec.
    all: repeat match goal with
         | E : c_fw_slide _ _ = Some _ |- _ => apply st_fw_slide in E
         | E : c_fw_insert _ = Some _ |- _ => apply st_fw_insert in E end.
    all: sclose.
  - intros [s1 z1] r E1. unfold fw_body in E1. sdec.
    all: repeat match goal with
         | E : c_fw_slide _ _ = Some _ |- _ => apply st_fw_slide in E
         | E : c_fw_insert _ = Some _ |- _ => apply st_fw_insert in E end.
    all: sclose.
Qed.

Lemma st_longest_match s cur s' ml : c_longest_match s cur = Some (s', ml) -> d_status s' = d_status s.
Proof.
  unfold c_longest_match. intros H. sdec.
  match goal with E : loop _ _ _ = Some _ |- _ =>
    apply (loop_status _ _ lm_s (fun r => snd r)) in E end.
  - sclose.
  - intros [] a' Eb. unfold lm_body in Eb. sdec; sclose.
  - intros [] r Eb. unfold lm_body in Eb. sdec; sclose.
Qed.

(** ** flush_pending, FLUSH_BLOCK, the tallies *)

Lemma st_flush_pending s z s' z' : c_flush_pending s z = Some (s', z') -> d_status s' = d_status s.
Proof. unfold c_flush_pending. intros H. sdec; sclose. Qed.

Lemma st_flush_block_only s z last s' z' : c_flush_block_only s z last = Some (s', z') -> d_status s' = d_status s.
Proof.
  unfold c_flush_block_only. intros H. sdec.
  all: apply st_flush_pending in H; sclose.
Qed.

Lemma st_flush_block s z last s' z' r : c_flush_block s z last = Some (s', z', r) -> d_status s' = d_status s.
Proof. unfold c_flush_block. intros H. sdec. all: apply st_flush_block_only in E; sclose. Qed.

Lemma st_dtally_lit s c s' b : c_dtally_lit s c = Some (s', b) -> d_status s' = d_status s.
Proof. unfold c_dtally_lit. intros H. sdec. sclose. Qed.

Lemma st_dtally_dist s d l s' b : c_dtally_dist s d l = Some (s', b) -> d_status s' = d_status s.
Proof. unfold c_dtally_dist. intros H. sdec. sclose. Qed.

Lemma st_pb_wr s i v s' : c_pb_wr s i v = Some s' -> d_status s' = d_status s.
Proof. unfold c_pb_wr. intros H. sdec. sclose. Qed.

Ltac sfacts :=
  repeat match goal with
  | E : c_fill_window _ _ = Some _ |- _ => apply st_fill_window in E
  | E : c_insert_string _ _ = Some _ |- _ => apply st_insert_string in E
  | E : c_longest_match _ _ = Some _ |- _ => apply st_longest_match in E
  | E : c_flush_pending _ _ = Some _ |- _ => apply st_flush_pending in E
  | E : c_flush_block_only _ _ _ = Some _ |- _ => apply st_flush_block_only in E
  | E : c_flush_block _ _ _ = Some _ |- _ => apply st_flush_block in E
  | E : c_dtally_lit _ _ = Some _ |- _ => apply st_dtally_lit in E
  | E : c_dtally_dist _ _ _ = Some _ |- _ => apply st_dtally_dist in E
  | E : c_pb_wr _ _ _ = Some _ |- _ => apply st_pb_wr in E
  | E : c_clear_hash _ = Some _ |- _ => apply st_clear_hash in E
  | E : c_slide_hash _ = Some _ |- _ => apply st_slide_hash in E
  end.

(** ** The common pieces of the compression functions *)

(** The status after a step of a main loop: continue with [inl (s', z')] or leave with [inr (s', z', _)]. *)
Definition xst (x : (dstate * strm) + dexit) : Z :=
  match x with inl (s', _) => d_status s' | inr (s', _, _) => d_status s' end.

Lemma st_bflush s z b x : c_bflush s z b = Some x -> xst x = d_status s.
Proof. unfold c_bflush. intros H. sdec; sfacts; cbn [xst]; sclose. Qed.

Lemma st_refill need flush s z x : c_refill need flush s z = Some x -> xst x = d_status s.
Proof. unfold c_refill. intros H. sdec; sfacts; cbn [xst]; sclose. Qed.

Lemma st_deflate_tail s z f s' z' r : c_deflate_tail s z f = Some (s', z', r) -> d_status s' = d_status s.
Proof. unfold c_deflate_tail. intros H. sdec; sfacts; sclose. Qed.

Lemma st_insert_head s s' h : c_insert_head s = Some (s', h) -> d_status s' = d_status s.
Proof. unfold c_insert_head. intros H. sdec; sfacts; sclose. Qed.

Lemma st_main_loop {B} (body : dstate * strm -> option ((dstate * strm) + (dstate * strm * B))) :
  (forall a x, body a = Some x ->
     match x with inl (s', _) => d_status s' | inr (s', _, _) => d_status s' end = d_status (fst a)) ->
  forall a s' z' r, loop FUEL body a = Some (s', z', r) -> d_status s' = d_status (fst a).
Proof.
  intros Hb a s' z' r H.
  apply (loop_status _ _ fst (fun r => fst (fst r))) in H; [exact H| |].
  - intros a1 [s2 z2] E. exact (Hb _ _ E).
  - intros a1 [[s2 z2] r2] E. exact (Hb _ _ E).
Qed.

Ltac sloop L :=
  match goal with E : loop FUEL _ _ = Some _ |- _ => apply (st_main_loop _ L) in E; cbn [fst snd] in E end.

(** ** deflate_fast *)

Lemma st_df_insert_loop s s' : loop FUEL df_insert_body s = Some s' -> d_status s' = d_status s.
Proof.
  intros H. apply (loop_status _ _ (fun s => s) (fun r => r)) in H; [exact H| |].
  - intros a a' E. unfold df_insert_body in E. sdec; sfacts; sclose.
  - intros a r E. unfold df_insert_body in E. sdec; sfacts; sclose.
Qed.

Lemma st_df_step s z x : df_step s z = Some x -> xst x = d_status s.
Proof.
  unfold df_step. intros H. sdec; sfacts.
  all: repeat match goal with
       | E : c_insert_head _ = Some _ |- _ => apply st_insert_head in E
       | E : loop FUEL df_insert_body _ = Some _ |- _ => apply st_df_insert_loop in E
       | E : c_bflush _ _ _ = Some _ |- _ => apply st_bflush in E
       end.
  all: cbn [xst] in *; sclose.
Qed.

Lemma st_df_body flush a x : df_body flush a = Some x -> xst x = d_status (fst a).
Proof.
  destruct a as [s z]. unfold df_body. intros H. sdec.
  all: repeat match goal with
       | E : c_refill _ _ _ _ = Some _ |- _ => apply st_refill in E
       | E : df_step _ _ = Some _ |- _ => apply st_df_step in E
       end.
  all: cbn [xst] in *; sclose.
Qed.

Lemma st_deflate_fast s z f s' z' r : c_deflate_fast s z f = Some (s', z', r) -> d_status s' = d_status s.
Proof.
  unfold c_deflate_fast. intros H. sdec.
  all: sloop (st_df_body f); sfacts.
  all: try match goal with E : c_deflate_tail _ _ _ = Some _ |- _ => apply st_deflate_tail in E end.
  all: sclose.
Qed.

(** ** deflate_slow *)

Lemma st_dsl_insert_loop m s s' : loop FUEL (dsl_insert_body m) s = Some s' -> d_status s' = d_status s.
Proof.
  intros H. apply (loop_status _ _ (fun s => s) (fun r => r)) in H; [exact H| |].
  - intros a a' E. unfold dsl_insert_body in E. sdec; sfacts; sclose.
  - intros a r E. unfold dsl_insert_body in E. sdec; sfacts; sclose.
Qed.

Lemma st_dsl_step s z x : dsl_step s z = Some x -> xst x = d_status s.
Proof.
  unfold dsl_step. intros H. sdec; sfacts.
  all: repeat match goal with
       | E : c_insert_head _ = Some _ |- _ => apply st_insert_head in E
       | E : loop FUEL (dsl_insert_body _) _ = Some _ |- _ => apply st_dsl_insert_loop in E
       | E : c_bflush _ _ _ = Some _ |- _ => apply st_bflush in E
       end.
  all: cbn [xst] in *; sclose.
Qed.

Lemma st_dsl_body flush a x : dsl_body flush a = Some x -> xst x = d_status (fst a).
Proof.
  destruct a as [s z]. unfold dsl_body. intros H. sdec.
  all: repeat match goal with
       | E : c_refill _ _ _ _ = Some _ |- _ => apply st_refill in E
       | E : dsl_step _ _ = Some _ |- _ => apply st_dsl_step in E
       end.
  all: cbn [xst] in *; sclose.
Qed.

Lemma st_deflate_slow s z f s' z' r : c_deflate_slow s z f = Some (s', z', r) -> d_status s' = d_status s.
Proof.
  unfold c_deflate_slow. intros H. sdec.
  all: sloop (st_dsl_body f); sfacts.
  all: try match goal with E : c_deflate_tail _ _ _ = Some _ |- _ => apply st_deflate_tail in E end.
  all: sclose.
Qed.

(** ** deflate_rle *)

Lemma st_rle_step s z x : rle_step s z = Some x -> xst x = d_status s.
Proof.
  unfold rle_step. intros H. sdec; sfacts.
  all: repeat match goal with E : c_bflush _ _ _ = Some _ |- _ => apply st_bflush in E end.
  all: cbn [xst] in *; sclose.
Qed.

Lemma st_rle_body flush a x : rle_body flush a = Some x -> xst x = d_status (fst a).
Proof.
  destruct a as [s z]. unfold rle_body. intros H. sdec.
  all: repeat match goal with
       | E : c_refill _ _ _ _ = Some _ |- _ => apply st_refill in E
       | E : rle_step _ _ = Some _ |- _ => apply st_rle_step in E
       end.
  all: cbn [xst] in *; sclose.
Qed.

Lemma st_deflate_rle s z f s' z' r : c_deflate_rle s z f = Some (s', z', r) -> d_status s' = d_status s.
Proof.
  unfold c_deflate_rle. intros H. sdec.
  all: sloop (st_rle_body f); sfacts.
  all: try match goal with E : c_deflate_tail _ _ _ = Some _ |- _ => apply st_deflate_tail in E end.
  all: sclose.
Qed.

(** ** deflate_huff *)

Lemma st_huff_body flush a x : huff_body flush a = Some x -> xst x = d_status (fst a).
Proof.
  destruct a as [s z]. unfold huff_body. intros H. sdec; sfacts.
  all: repeat match goal with E : c_bflush _ _ _ = Some _ |- _ => apply st_bflush in E end.
  all: cbn [xst] in *; sclose.
Qed.

Lemma st_deflate_huff s z f s' z' r : c_deflate_huff s z f = Some (s', z', r) -> d_status s' = d_status s.
Proof.
  unfold c_deflate_huff. intros H. sdec.
  all: sloop (st_huff_body f); sfacts.
  all: try match goal with E : c_deflate_tail _ _ _ = Some _ |- _ => apply st_deflate_tail in E end.
  all: sclose.
Qed.

(** ** deflate_stored *)

Lemma st_ds_body flush mb a x : ds_body flush mb a = Some x ->
  match x with inl (s', _) => d_status s' | inr (s', _, _) => d_status s' end = d_status (fst a).
Proof. destruct a as [s z]. unfold ds_body. intros H. sdec; sfacts; sclose. Qed.

Lemma st_ds_window s z used s' : c_ds_window s z used = Some s' -> d_status s' = d_status s.
Proof. unfold c_ds_window. intros H. sdec; sfacts; sclose. Qed.

Lemma st_deflate_stored s z f s' z' r : c_deflate_stored s z f = Some (s', z', r) -> d_status s' = d_status s.
Proof.
  unfold c_deflate_stored. intros H. sdec.
  all: match goal with E : loop FUEL (ds_body _ ?mb) _ = Some _ |- _ =>
         apply (st_main_loop _ (st_ds_body f mb)) in E; cbn [fst snd] in E end.
  all: sfacts.
  all: repeat match goal with E : c_ds_window _ _ _ = Some _ |- _ => apply st_ds_window in E end.
  all: sclose.
Qed.

(** ** The dispatch of the compression function *)

Lemma st_compress_func s z f s' z' r : c_compress_func s z f = Some (s', z', r) -> d_status s' = d_status s.
Proof.
  unfold c_compress_func. intros H. sdec.
  all: first [ apply st_deflate_stored in H | apply st_deflate_fast in H | apply st_deflate_slow in H
             | apply st_deflate_rle in H | apply st_deflate_huff in H ].
  all: exact H.
Qed.

(** ** The stages of deflate() *)

Lemma st_dput_byte s c s' : c_dput_byte s c = Some s' -> d_status s' = d_status s.
Proof. unfold c_dput_byte. intros H. sdec. sclose. Qed.

Lemma st_dput_bytes l s s' : c_dput_bytes s l = Some s' -> d_status s' = d_status s.
Proof.
  revert s; induction l as [|c l IH]; intros s H; cbn [c_dput_bytes] in H; sdec; [reflexivity|].
  apply IH in H. apply st_dput_byte in E. congruence.
Qed.

Lemma st_putShortMSB s b s' : c_putShortMSB s b = Some s' -> d_status s' = d_status s.
Proof.
  unfold c_putShortMSB. intros H. sdec. apply st_dput_byte in H. apply st_dput_byte in E. congruence.
Qed.

Lemma st_flush_or_return s z s' z' o : c_flush_or_return s z = Some (s', z', o) -> d_status s' = d_status s.
Proof. unfold c_flush_or_return. intros H. sdec; sfacts; sclose. Qed.

Ltac sfacts2 :=
  sfacts;
  repeat match goal with
  | E : c_dput_byte _ _ = Some _ |- _ => apply st_dput_byte in E
  | E : c_dput_bytes _ _ = Some _ |- _ => apply st_dput_bytes in E
  | E : c_putShortMSB _ _ = Some _ |- _ => apply st_putShortMSB in E
  | E : c_flush_or_return _ _ = Some _ |- _ => apply st_flush_or_return in E
  | E : c_compress_func _ _ _ = Some _ |- _ => apply st_compress_func in E
  end.

(** The states a stage of deflate() may leave are all accepted by deflateStateCheck. *)
Ltac okclose :=
  pose proof (eq_refl : status_ok BUSY_STATE = true); pose proof (eq_refl : status_ok EXTRA_STATE = true);
  pose proof (eq_refl : status_ok NAME_STATE = true); pose proof (eq_refl : status_ok COMMENT_STATE = true);
  pose proof (eq_refl : status_ok HCRC_STATE = true); pose proof (eq_refl : status_ok FINISH_STATE = true);
  sclose.

(** A stage's result has a valid status. *)
Definition okr (r : option dres) : Prop :=
  forall s z o, r = Some (s, z, o) -> status_ok (d_status s) = true.

Lemma then_stage_ok r k :
  okr r -> (forall s z, status_ok (d_status s) = true -> okr (k s z)) -> okr (then_stage r k).
Proof.
  unfold okr, then_stage. intros Hr Hk s z o H.
  destruct r as [[[s1 z1] o1]|]; [|discriminate]. cbn [bind] in H.
  specialize (Hr _ _ _ eq_refl).
  destruct o1; [inversion H; subst; exact Hr | exact (Hk _ _ Hr _ _ _ H)].
Qed.

Lemma ok_entry s z f : status_ok (d_status s) = true -> okr (c_deflate_entry s z f).
Proof.
  intros Hok s' z' o H. unfold c_deflate_entry in H. sdec; sfacts2; try okclose.
  all: revert H; apply then_stage_ok; [intros ? ? ? Ex; inversion Ex; subst; okclose|].
  all: intros ? ? ? ? ? ? Ex; sdec; okclose.
Qed.

Lemma ok_zlib_header s z : status_ok (d_status s) = true -> okr (c_deflate_zlib_header s z).
Proof. intros Hok s' z' o H. unfold c_deflate_zlib_header in H. sdec; sfacts2; okclose. Qed.

Lemma ok_gzip_header s z : status_ok (d_status s) = true -> okr (c_deflate_gzip_header s z).
Proof. intros Hok s' z' o H. unfold c_deflate_gzip_header in H. sdec; sfacts2; okclose. Qed.

Lemma st_extra_loop h x a e : loop FUEL (extra_body h x) a = Some e ->
  match e with inl (s', _, _, _) => d_status s' | inr (s', _) => d_status s' end =
  d_status (fst (fst (fst a))).
Proof.
  intros H. apply (loop_status _ _ (fun a => fst (fst (fst a)))
    (fun e => match e with inl (s', _, _, _) => s' | inr (s', _) => s' end)) in H.
  - destruct e as [[[[]]]|[]]; exact H.
  - intros [[[s1 z1] b1] l1] a' E. unfold extra_body in E. sdec; sfacts2; sclose.
  - intros [[[s1 z1] b1] l1] r E. unfold extra_body in E. sdec; sfacts2; sclose.
Qed.

Lemma ok_extra s z : status_ok (d_status s) = true -> okr (c_deflate_extra s z).
Proof.
  intros Hok s' z' o H. unfold c_deflate_extra in H. sdec; try okclose.
  all: revert H; apply then_stage_ok; [|intros ? ? _ ? ? ? Ex; inversion Ex; subst; okclose].
  all: intros ? ? ? Ex; inversion Ex; subst; clear Ex.
  all: repeat match goal with E : loop FUEL (extra_body _ _) _ = Some _ |- _ => apply st_extra_loop in E end.
  all: okclose.
Qed.

Lemma st_deflate_str h o reset s z s' z' r : c_deflate_str h o reset s z = Some (s', z', r) ->
  d_status s' = d_status s.
Proof.
  unfold c_deflate_str. intros H. sdec; try sclose.
  all: match goal with E : loop FUEL (str_body _ _) _ = Some _ |- _ =>
         apply (loop_status _ _ (fun a => fst (fst a))
                  (fun e => match e with inl (s', _, _) => s' | inr (s', _) => s' end)) in E end.
  all: try (cbn [fst] in *; sclose).
  all: intros [[? ?] ?] ? Eb; unfold str_body in Eb; sdec; sfacts2; sclose.
Qed.

Lemma ok_name s z : status_ok (d_status s) = true -> okr (c_deflate_name s z).
Proof.
  intros Hok s' z' o H. unfold c_deflate_name in H. sdec; try okclose.
  revert H; apply then_stage_ok; [|intros ? ? _ ? ? ? Ex; inversion Ex; subst; okclose].
  intros ? ? ? Ex. apply st_deflate_str in Ex. okclose.
Qed.

Lemma ok_comment s z : status_ok (d_status s) = true -> okr (c_deflate_comment s z).
Proof.
  intros Hok s' z' o H. unfold c_deflate_comment in H. sdec; try okclose.
  revert H; apply then_stage_ok; [|intros ? ? _ ? ? ? Ex; inversion Ex; subst; okclose].
  intros ? ? ? Ex. apply st_deflate_str in Ex. okclose.
Qed.

Lemma ok_hcrc s z : status_ok (d_status s) = true -> okr (c_deflate_hcrc s z).
Proof.
  intros Hok s' z' o H. unfold c_deflate_hcrc in H. sdec; try okclose.
  all: revert H; apply then_stage_ok;
    [| intros ? ? _ ? ? ? Ex; apply st_flush_or_return in Ex; okclose].
  all: intros ? ? ? Ex; sdec; try okclose.
  all: match goal with E : then_stage _ _ = Some _ |- _ => revert E end.
  all: apply then_stage_ok; [intros ? ? ? Ex; sdec; sfacts2; okclose|].
  all: intros ? ? ? ? ? ? Ex; sdec; sfacts2; okclose.
Qed.

Lemma ok_compress s z f : status_ok (d_status s) = true -> okr (c_deflate_compress s z f).
Proof. intros Hok s' z' o H. unfold c_deflate_compress in H. sdec; sfacts2; okclose. Qed.

Lemma st_trailer s z f s' z' r : c_deflate_trailer s z f = Some (s', z', r) -> d_status s' = d_status s.
Proof. unfold c_deflate_trailer. intros H. sdec; sfacts2; sclose. Qed.

Lemma c_deflate_status_ok : forall s z flush s' z' code,
  strm_ranges z -> status_ok (d_status s) = true -> c_deflate s z flush = Some (s', z', code) ->
  status_ok (d_status s') = true.
Proof.
  intros s z flush s' z' code _ Hok H. unfold c_deflate in H.
  destruct (bad_state s || (flush >? Z_BLOCK) || (flush <? 0))%bool; [inversion H; subst; exact Hok|].
  match type of H with bind ?r _ = _ => destruct r as [[[s1 z1] o]|] eqn:E; [|discriminate] end.
  cbn [bind] in H.
  assert (O1 : status_ok (d_status s1) = true).
  { revert E. apply then_stage_ok; [apply ok_entry; exact Hok|]. intros ? ? ?.
    apply then_stage_ok; [apply ok_zlib_header; assumption|]. intros ? ? ?.
    apply then_stage_ok; [apply ok_gzip_header; assumption|]. intros ? ? ?.
    apply then_stage_ok; [apply ok_extra; assumption|]. intros ? ? ?.
    apply then_stage_ok; [apply ok_name; assumption|]. intros ? ? ?.
    apply then_stage_ok; [apply ok_comment; assumption|]. intros ? ? ?.
    apply then_stage_ok; [apply ok_hcrc; assumption|]. intros ? ? ?.
    apply ok_compress; assumption. }
  destruct o; [inversion H; subst; exact O1|].
  apply st_trailer in H. congruence.
Qed.
