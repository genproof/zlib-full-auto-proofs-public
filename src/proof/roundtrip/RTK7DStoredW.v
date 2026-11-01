(* deflate_stored never changes w_bits (the model sets it only in deflateInit2).  Needed where the stored
   function meets its defect (RTK7Defs.stored_cut): there cpost7 and comp_fspec7 say nothing of the state. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7DMid.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The loops of the model must never be unfolded (binary fuel): only [bind] is. *)
Local Strategy expand [bind].
Local Strategy opaque [loop loop2].

Lemma wb_some {A} (a b : A) : Some a = Some b -> a = b.
Proof. congruence. Qed.

(** Case analysis of a hypothesis [c = Some r], [c] a term of the option monad of the model. *)
Ltac wstep :=
  match goal with
  | x : (_ * _)%type |- _ => destruct x
  | H : Some _ = Some _ |- _ => apply wb_some in H
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

Ltac wdec := repeat (wstep; cbv beta iota zeta in *).

(** Reduce [d_w_bits] through the record setters. *)
Ltac wcbn :=
  cbn [d_w_bits set_d_status set_d_po set_d_wrap set_d_gzhead set_d_gzindex set_d_method set_d_last_flush
       set_d_w_size set_d_w_bits set_d_w_mask set_d_window set_d_window_size set_d_prev set_d_head set_d_ins_h
       set_d_hash_size set_d_hash_bits set_d_hash_mask set_d_hash_shift set_d_block_start set_d_match_length
       set_d_prev_match set_d_match_available set_d_strstart set_d_match_start set_d_lookahead set_d_prev_length
       set_d_max_chain_length set_d_max_lazy_match set_d_good_match set_d_nice_match set_d_insert set_d_high_water
       set_d_slid set_d_pending_buf_size set_d_tr set_d_pbm].

(** Close [d_w_bits X = d_w_bits s] for a state [X] built by the setters from states with known w_bits. *)
Ltac wclose :=
  repeat match goal with H : d_w_bits _ = d_w_bits _ |- _ => revert H end;
  unfold incr_matches, clamp_insert, add_insert, upd_high_water,
    set_d_pb, set_d_bi_used, set_d_matches, set_d_trm, set_d_out;
  wcbn;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  wcbn; intros; congruence.

(** flush_pending only moves pending output. *)
Lemma wb_flush_pending s z s' z' : c_flush_pending s z = Some (s', z') -> d_w_bits s' = d_w_bits s.
Proof. unfold c_flush_pending. intros H. wdec; wclose. Qed.

(** A byte store into pending_buf. *)
Lemma wb_pb_wr s i v s' : c_pb_wr s i v = Some s' -> d_w_bits s' = d_w_bits s.
Proof. unfold c_pb_wr. intros H. wdec; wclose. Qed.

Ltac wfacts :=
  repeat match goal with
  | E : c_pb_wr _ _ _ = Some _ |- _ => apply wb_pb_wr in E
  | E : c_flush_pending _ _ = Some _ |- _ => apply wb_flush_pending in E
  end.

(** One iteration of the direct-copy loop of deflate_stored. *)
Lemma wb_ds_body flush mb s z x : ds_body flush mb (s, z) = Some x ->
  match x with inl (s', _) => d_w_bits s' = d_w_bits s | inr (s', _, _) => d_w_bits s' = d_w_bits s end.
Proof. unfold ds_body. intros H. wdec; wfacts; wclose. Qed.

Lemma wb_ds_loop flush mb s z s' z' last : loop FUEL (ds_body flush mb) (s, z) = Some (s', z', last) ->
  d_w_bits s' = d_w_bits s.
Proof.
  intros H. apply loop_runs in H.
  enough (G : forall a r, runs (ds_body flush mb) a r -> d_w_bits (fst (fst r)) = d_w_bits (fst a))
    by exact (G _ _ H).
  clear. intros a r H. induction H as [[s1 z1] r E | [s1 z1] [s2 z2] r E _ IH].
  - apply wb_ds_body in E. destruct r as [[s2 z2] l2]. exact E.
  - apply wb_ds_body in E. cbn [fst] in *. congruence.
Qed.

Lemma wb_ds_window s z used s' : c_ds_window s z used = Some s' -> d_w_bits s' = d_w_bits s.
Proof. unfold c_ds_window. intros H. wdec; wclose. Qed.

Lemma stored_wbits : stored_wbits_stmt.
Proof.
  intros s z flush s' z' bs H. unfold c_deflate_stored in H.
  destruct (loop _ _ _) as [[[s1 z1] last]|] eqn:E1; [|discriminate]. cbv beta iota delta [bind] in H.
  apply wb_ds_loop in E1.
  destruct (c_ds_window _ _ _) as [s2|] eqn:E2; [|discriminate]. cbv beta iota in H.
  apply wb_ds_window in E2.
  set (s3 := upd_high_water s2) in H.
  assert (E3 : d_w_bits s3 = d_w_bits s2) by (subst s3; wclose).
  clearbody s3. cbv zeta in H.
  wdec; wfacts; wclose.
Qed.
