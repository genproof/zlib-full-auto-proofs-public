(** * Kit for RTDLTCLm.v: INSERT_STRING and longest_match on the checked model. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCLib.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** A loop terminates when a measure >= 0 decreases on every continuing iteration and starts below 2^d *)
Section LoopMeasure.
Context {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) (m : A -> Z).
Hypothesis Hstep : forall a, P a -> 0 <= m a /\
  ((exists r, body a = Some (inr r) /\ Q r) \/ (exists a', body a = Some (inl a') /\ P a' /\ m a' < m a)).

Lemma loop2_measure : forall d a, P a ->
  (exists r, loop2 d body a = Some (inr r) /\ Q r) \/
  (exists a', loop2 d body a = Some (inl a') /\ P a' /\ m a' + 2 ^ Z.of_nat d <= m a).
Proof.
  induction d as [|d IH]; intros a Ha; cbn [loop2].
  - destruct (Hstep a Ha) as [_ [[r [E HQ]]|[a' [E [HP Hm]]]]]; rewrite E.
    + left; eauto.
    + right; exists a'; split; [reflexivity|]; split; [exact HP|]. simpl. lia.
  - destruct (IH a Ha) as [[r [E HQ]]|[a' [E [HP Hm]]]]; rewrite E.
    + left; eauto.
    + destruct (IH a' HP) as [[r [E' HQ]]|[a'' [E' [HP' Hm']]]]; rewrite E'.
      * left; eauto.
      * right. exists a''. split; [reflexivity|]. split; [exact HP'|].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma loop_measure : forall d a, P a -> m a < 2 ^ Z.of_nat d -> exists r, loop d body a = Some r /\ Q r.
Proof.
  intros d a Ha Hm. unfold loop.
  destruct (loop2_measure d a Ha) as [[r [E HQ]]|[a' [E [HP Hm']]]]; rewrite E.
  - eauto.
  - destruct (Hstep a' HP) as [H0 _]. lia.
Qed.
End LoopMeasure.

(** ** Checked accesses *)
Lemma mb_rd_ok b i : 0 <= i < Zlength (mb_val b) -> Znth i (mb_def b) = true ->
  mb_rd b i = Some (Znth i (mb_val b)).
Proof.
  intros Hi Hd. unfold mb_rd, in_range. rewrite Hd.
  replace ((0 <=? i) && (i <? Zlength (mb_val b))) with true by (symmetry; apply andb_true_iff; lia).
  reflexivity.
Qed.

Lemma rd_ok l i : 0 <= i < Zlength l -> rd l i = Some (Znth i l).
Proof.
  intros Hi. unfold rd, in_range.
  replace ((0 <=? i) && (i <? Zlength l)) with true by (symmetry; apply andb_true_iff; lia). reflexivity.
Qed.

Lemma wr_ok l i v : 0 <= i < Zlength l -> wr l i v = Some (upd_Znth i l v).
Proof.
  intros Hi. unfold wr, in_range.
  replace ((0 <=? i) && (i <? Zlength l)) with true by (symmetry; apply andb_true_iff; lia). reflexivity.
Qed.

Lemma u32_id x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros; unfold u32; apply Z.mod_small; lia. Qed.

Lemma u16_id x : 0 <= x < 65536 -> u16 x = x.
Proof. intros; unfold u16; apply Z.mod_small; lia. Qed.

Lemma land_mask_range x k : 0 <= k -> 0 <= Z.land x (2 ^ k - 1) < 2 ^ k.
Proof.
  intros Hk. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma prm_w s : prm s ->
  512 <= d_w_size s <= 32768 /\ d_w_mask s = 2 ^ d_w_bits s - 1 /\ d_w_size s = 2 ^ d_w_bits s /\
  0 <= d_w_bits s.
Proof.
  intros (Hb & Hs & Hm & _). rewrite Hm, Hs. split; [split|split; [reflexivity|split; [reflexivity|lia]]].
  - change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia.
  - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.

Lemma prm_h s : prm s ->
  d_hash_size s = 2 ^ d_hash_bits s /\ d_hash_mask s = 2 ^ d_hash_bits s - 1 /\ 0 <= d_hash_bits s <= 16 /\
  0 <= d_hash_shift s < 32.
Proof.
  intros (_ & _ & _ & Hb & Hs & Hm & Hsh & _). rewrite Hm, Hs, Hsh.
  split; [reflexivity|split; [reflexivity|split; [lia|]]].
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.

(** ** Projections of the setters used here *)
Lemma d_status_set_head s x : d_status (set_d_head s x) = d_status s. Proof. reflexivity. Qed.
Lemma d_po_set_head s x : d_po (set_d_head s x) = d_po s. Proof. reflexivity. Qed.
Lemma d_wrap_set_head s x : d_wrap (set_d_head s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma d_gzhead_set_head s x : d_gzhead (set_d_head s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma d_gzindex_set_head s x : d_gzindex (set_d_head s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma d_method_set_head s x : d_method (set_d_head s x) = d_method s. Proof. reflexivity. Qed.
Lemma d_last_flush_set_head s x : d_last_flush (set_d_head s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma d_w_size_set_head s x : d_w_size (set_d_head s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma d_w_bits_set_head s x : d_w_bits (set_d_head s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma d_w_mask_set_head s x : d_w_mask (set_d_head s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma d_window_set_head s x : d_window (set_d_head s x) = d_window s. Proof. reflexivity. Qed.
Lemma d_window_size_set_head s x : d_window_size (set_d_head s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma d_prev_set_head s x : d_prev (set_d_head s x) = d_prev s. Proof. reflexivity. Qed.
Lemma d_head_set_head s x : d_head (set_d_head s x) = x. Proof. reflexivity. Qed.
Lemma d_ins_h_set_head s x : d_ins_h (set_d_head s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma d_hash_size_set_head s x : d_hash_size (set_d_head s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma d_hash_bits_set_head s x : d_hash_bits (set_d_head s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma d_hash_mask_set_head s x : d_hash_mask (set_d_head s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma d_hash_shift_set_head s x : d_hash_shift (set_d_head s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma d_block_start_set_head s x : d_block_start (set_d_head s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma d_match_length_set_head s x : d_match_length (set_d_head s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma d_prev_match_set_head s x : d_prev_match (set_d_head s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma d_match_available_set_head s x : d_match_available (set_d_head s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma d_strstart_set_head s x : d_strstart (set_d_head s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma d_match_start_set_head s x : d_match_start (set_d_head s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma d_lookahead_set_head s x : d_lookahead (set_d_head s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma d_prev_length_set_head s x : d_prev_length (set_d_head s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma d_max_chain_length_set_head s x : d_max_chain_length (set_d_head s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma d_max_lazy_match_set_head s x : d_max_lazy_match (set_d_head s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma d_good_match_set_head s x : d_good_match (set_d_head s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma d_nice_match_set_head s x : d_nice_match (set_d_head s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma d_insert_set_head s x : d_insert (set_d_head s x) = d_insert s. Proof. reflexivity. Qed.
Lemma d_high_water_set_head s x : d_high_water (set_d_head s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma d_slid_set_head s x : d_slid (set_d_head s x) = d_slid s. Proof. reflexivity. Qed.
Lemma d_pending_buf_size_set_head s x : d_pending_buf_size (set_d_head s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma d_tr_set_head s x : d_tr (set_d_head s x) = d_tr s. Proof. reflexivity. Qed.
Lemma d_pbm_set_head s x : d_pbm (set_d_head s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma d_status_set_prev s x : d_status (set_d_prev s x) = d_status s. Proof. reflexivity. Qed.
Lemma d_po_set_prev s x : d_po (set_d_prev s x) = d_po s. Proof. reflexivity. Qed.
Lemma d_wrap_set_prev s x : d_wrap (set_d_prev s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma d_gzhead_set_prev s x : d_gzhead (set_d_prev s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma d_gzindex_set_prev s x : d_gzindex (set_d_prev s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma d_method_set_prev s x : d_method (set_d_prev s x) = d_method s. Proof. reflexivity. Qed.
Lemma d_last_flush_set_prev s x : d_last_flush (set_d_prev s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma d_w_size_set_prev s x : d_w_size (set_d_prev s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma d_w_bits_set_prev s x : d_w_bits (set_d_prev s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma d_w_mask_set_prev s x : d_w_mask (set_d_prev s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma d_window_set_prev s x : d_window (set_d_prev s x) = d_window s. Proof. reflexivity. Qed.
Lemma d_window_size_set_prev s x : d_window_size (set_d_prev s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma d_prev_set_prev s x : d_prev (set_d_prev s x) = x. Proof. reflexivity. Qed.
Lemma d_head_set_prev s x : d_head (set_d_prev s x) = d_head s. Proof. reflexivity. Qed.
Lemma d_ins_h_set_prev s x : d_ins_h (set_d_prev s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma d_hash_size_set_prev s x : d_hash_size (set_d_prev s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma d_hash_bits_set_prev s x : d_hash_bits (set_d_prev s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma d_hash_mask_set_prev s x : d_hash_mask (set_d_prev s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma d_hash_shift_set_prev s x : d_hash_shift (set_d_prev s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma d_block_start_set_prev s x : d_block_start (set_d_prev s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma d_match_length_set_prev s x : d_match_length (set_d_prev s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma d_prev_match_set_prev s x : d_prev_match (set_d_prev s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma d_match_available_set_prev s x : d_match_available (set_d_prev s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma d_strstart_set_prev s x : d_strstart (set_d_prev s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma d_match_start_set_prev s x : d_match_start (set_d_prev s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma d_lookahead_set_prev s x : d_lookahead (set_d_prev s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma d_prev_length_set_prev s x : d_prev_length (set_d_prev s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma d_max_chain_length_set_prev s x : d_max_chain_length (set_d_prev s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma d_max_lazy_match_set_prev s x : d_max_lazy_match (set_d_prev s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma d_good_match_set_prev s x : d_good_match (set_d_prev s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma d_nice_match_set_prev s x : d_nice_match (set_d_prev s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma d_insert_set_prev s x : d_insert (set_d_prev s x) = d_insert s. Proof. reflexivity. Qed.
Lemma d_high_water_set_prev s x : d_high_water (set_d_prev s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma d_slid_set_prev s x : d_slid (set_d_prev s x) = d_slid s. Proof. reflexivity. Qed.
Lemma d_pending_buf_size_set_prev s x : d_pending_buf_size (set_d_prev s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma d_tr_set_prev s x : d_tr (set_d_prev s x) = d_tr s. Proof. reflexivity. Qed.
Lemma d_pbm_set_prev s x : d_pbm (set_d_prev s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma d_status_set_ins_h s x : d_status (set_d_ins_h s x) = d_status s. Proof. reflexivity. Qed.
Lemma d_po_set_ins_h s x : d_po (set_d_ins_h s x) = d_po s. Proof. reflexivity. Qed.
Lemma d_wrap_set_ins_h s x : d_wrap (set_d_ins_h s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma d_gzhead_set_ins_h s x : d_gzhead (set_d_ins_h s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma d_gzindex_set_ins_h s x : d_gzindex (set_d_ins_h s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma d_method_set_ins_h s x : d_method (set_d_ins_h s x) = d_method s. Proof. reflexivity. Qed.
Lemma d_last_flush_set_ins_h s x : d_last_flush (set_d_ins_h s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma d_w_size_set_ins_h s x : d_w_size (set_d_ins_h s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma d_w_bits_set_ins_h s x : d_w_bits (set_d_ins_h s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma d_w_mask_set_ins_h s x : d_w_mask (set_d_ins_h s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma d_window_set_ins_h s x : d_window (set_d_ins_h s x) = d_window s. Proof. reflexivity. Qed.
Lemma d_window_size_set_ins_h s x : d_window_size (set_d_ins_h s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma d_prev_set_ins_h s x : d_prev (set_d_ins_h s x) = d_prev s. Proof. reflexivity. Qed.
Lemma d_head_set_ins_h s x : d_head (set_d_ins_h s x) = d_head s. Proof. reflexivity. Qed.
Lemma d_ins_h_set_ins_h s x : d_ins_h (set_d_ins_h s x) = x. Proof. reflexivity. Qed.
Lemma d_hash_size_set_ins_h s x : d_hash_size (set_d_ins_h s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma d_hash_bits_set_ins_h s x : d_hash_bits (set_d_ins_h s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma d_hash_mask_set_ins_h s x : d_hash_mask (set_d_ins_h s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma d_hash_shift_set_ins_h s x : d_hash_shift (set_d_ins_h s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma d_block_start_set_ins_h s x : d_block_start (set_d_ins_h s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma d_match_length_set_ins_h s x : d_match_length (set_d_ins_h s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma d_prev_match_set_ins_h s x : d_prev_match (set_d_ins_h s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma d_match_available_set_ins_h s x : d_match_available (set_d_ins_h s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma d_strstart_set_ins_h s x : d_strstart (set_d_ins_h s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma d_match_start_set_ins_h s x : d_match_start (set_d_ins_h s x) = d_match_start s. Proof. reflexivity. Qed.
Lemma d_lookahead_set_ins_h s x : d_lookahead (set_d_ins_h s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma d_prev_length_set_ins_h s x : d_prev_length (set_d_ins_h s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma d_max_chain_length_set_ins_h s x : d_max_chain_length (set_d_ins_h s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma d_max_lazy_match_set_ins_h s x : d_max_lazy_match (set_d_ins_h s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma d_good_match_set_ins_h s x : d_good_match (set_d_ins_h s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma d_nice_match_set_ins_h s x : d_nice_match (set_d_ins_h s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma d_insert_set_ins_h s x : d_insert (set_d_ins_h s x) = d_insert s. Proof. reflexivity. Qed.
Lemma d_high_water_set_ins_h s x : d_high_water (set_d_ins_h s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma d_slid_set_ins_h s x : d_slid (set_d_ins_h s x) = d_slid s. Proof. reflexivity. Qed.
Lemma d_pending_buf_size_set_ins_h s x : d_pending_buf_size (set_d_ins_h s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma d_tr_set_ins_h s x : d_tr (set_d_ins_h s x) = d_tr s. Proof. reflexivity. Qed.
Lemma d_pbm_set_ins_h s x : d_pbm (set_d_ins_h s x) = d_pbm s. Proof. reflexivity. Qed.
Lemma d_status_set_match_start s x : d_status (set_d_match_start s x) = d_status s. Proof. reflexivity. Qed.
Lemma d_po_set_match_start s x : d_po (set_d_match_start s x) = d_po s. Proof. reflexivity. Qed.
Lemma d_wrap_set_match_start s x : d_wrap (set_d_match_start s x) = d_wrap s. Proof. reflexivity. Qed.
Lemma d_gzhead_set_match_start s x : d_gzhead (set_d_match_start s x) = d_gzhead s. Proof. reflexivity. Qed.
Lemma d_gzindex_set_match_start s x : d_gzindex (set_d_match_start s x) = d_gzindex s. Proof. reflexivity. Qed.
Lemma d_method_set_match_start s x : d_method (set_d_match_start s x) = d_method s. Proof. reflexivity. Qed.
Lemma d_last_flush_set_match_start s x : d_last_flush (set_d_match_start s x) = d_last_flush s. Proof. reflexivity. Qed.
Lemma d_w_size_set_match_start s x : d_w_size (set_d_match_start s x) = d_w_size s. Proof. reflexivity. Qed.
Lemma d_w_bits_set_match_start s x : d_w_bits (set_d_match_start s x) = d_w_bits s. Proof. reflexivity. Qed.
Lemma d_w_mask_set_match_start s x : d_w_mask (set_d_match_start s x) = d_w_mask s. Proof. reflexivity. Qed.
Lemma d_window_set_match_start s x : d_window (set_d_match_start s x) = d_window s. Proof. reflexivity. Qed.
Lemma d_window_size_set_match_start s x : d_window_size (set_d_match_start s x) = d_window_size s. Proof. reflexivity. Qed.
Lemma d_prev_set_match_start s x : d_prev (set_d_match_start s x) = d_prev s. Proof. reflexivity. Qed.
Lemma d_head_set_match_start s x : d_head (set_d_match_start s x) = d_head s. Proof. reflexivity. Qed.
Lemma d_ins_h_set_match_start s x : d_ins_h (set_d_match_start s x) = d_ins_h s. Proof. reflexivity. Qed.
Lemma d_hash_size_set_match_start s x : d_hash_size (set_d_match_start s x) = d_hash_size s. Proof. reflexivity. Qed.
Lemma d_hash_bits_set_match_start s x : d_hash_bits (set_d_match_start s x) = d_hash_bits s. Proof. reflexivity. Qed.
Lemma d_hash_mask_set_match_start s x : d_hash_mask (set_d_match_start s x) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma d_hash_shift_set_match_start s x : d_hash_shift (set_d_match_start s x) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma d_block_start_set_match_start s x : d_block_start (set_d_match_start s x) = d_block_start s. Proof. reflexivity. Qed.
Lemma d_match_length_set_match_start s x : d_match_length (set_d_match_start s x) = d_match_length s. Proof. reflexivity. Qed.
Lemma d_prev_match_set_match_start s x : d_prev_match (set_d_match_start s x) = d_prev_match s. Proof. reflexivity. Qed.
Lemma d_match_available_set_match_start s x : d_match_available (set_d_match_start s x) = d_match_available s. Proof. reflexivity. Qed.
Lemma d_strstart_set_match_start s x : d_strstart (set_d_match_start s x) = d_strstart s. Proof. reflexivity. Qed.
Lemma d_match_start_set_match_start s x : d_match_start (set_d_match_start s x) = x. Proof. reflexivity. Qed.
Lemma d_lookahead_set_match_start s x : d_lookahead (set_d_match_start s x) = d_lookahead s. Proof. reflexivity. Qed.
Lemma d_prev_length_set_match_start s x : d_prev_length (set_d_match_start s x) = d_prev_length s. Proof. reflexivity. Qed.
Lemma d_max_chain_length_set_match_start s x : d_max_chain_length (set_d_match_start s x) = d_max_chain_length s. Proof. reflexivity. Qed.
Lemma d_max_lazy_match_set_match_start s x : d_max_lazy_match (set_d_match_start s x) = d_max_lazy_match s. Proof. reflexivity. Qed.
Lemma d_good_match_set_match_start s x : d_good_match (set_d_match_start s x) = d_good_match s. Proof. reflexivity. Qed.
Lemma d_nice_match_set_match_start s x : d_nice_match (set_d_match_start s x) = d_nice_match s. Proof. reflexivity. Qed.
Lemma d_insert_set_match_start s x : d_insert (set_d_match_start s x) = d_insert s. Proof. reflexivity. Qed.
Lemma d_high_water_set_match_start s x : d_high_water (set_d_match_start s x) = d_high_water s. Proof. reflexivity. Qed.
Lemma d_slid_set_match_start s x : d_slid (set_d_match_start s x) = d_slid s. Proof. reflexivity. Qed.
Lemma d_pending_buf_size_set_match_start s x : d_pending_buf_size (set_d_match_start s x) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma d_tr_set_match_start s x : d_tr (set_d_match_start s x) = d_tr s. Proof. reflexivity. Qed.
Lemma d_pbm_set_match_start s x : d_pbm (set_d_match_start s x) = d_pbm s. Proof. reflexivity. Qed.
#[export] Hint Rewrite d_status_set_head d_po_set_head d_wrap_set_head d_gzhead_set_head d_gzindex_set_head d_method_set_head d_last_flush_set_head d_w_size_set_head d_w_bits_set_head d_w_mask_set_head d_window_set_head d_window_size_set_head d_prev_set_head d_head_set_head d_ins_h_set_head d_hash_size_set_head d_hash_bits_set_head d_hash_mask_set_head d_hash_shift_set_head d_block_start_set_head d_match_length_set_head d_prev_match_set_head d_match_available_set_head d_strstart_set_head d_match_start_set_head d_lookahead_set_head d_prev_length_set_head d_max_chain_length_set_head d_max_lazy_match_set_head d_good_match_set_head d_nice_match_set_head d_insert_set_head d_high_water_set_head d_slid_set_head d_pending_buf_size_set_head d_tr_set_head d_pbm_set_head d_status_set_prev d_po_set_prev d_wrap_set_prev d_gzhead_set_prev d_gzindex_set_prev d_method_set_prev d_last_flush_set_prev d_w_size_set_prev d_w_bits_set_prev d_w_mask_set_prev d_window_set_prev d_window_size_set_prev d_prev_set_prev d_head_set_prev d_ins_h_set_prev d_hash_size_set_prev d_hash_bits_set_prev d_hash_mask_set_prev d_hash_shift_set_prev d_block_start_set_prev d_match_length_set_prev d_prev_match_set_prev d_match_available_set_prev d_strstart_set_prev d_match_start_set_prev d_lookahead_set_prev d_prev_length_set_prev d_max_chain_length_set_prev d_max_lazy_match_set_prev d_good_match_set_prev d_nice_match_set_prev d_insert_set_prev d_high_water_set_prev d_slid_set_prev d_pending_buf_size_set_prev d_tr_set_prev d_pbm_set_prev d_status_set_ins_h d_po_set_ins_h d_wrap_set_ins_h d_gzhead_set_ins_h d_gzindex_set_ins_h d_method_set_ins_h d_last_flush_set_ins_h d_w_size_set_ins_h d_w_bits_set_ins_h d_w_mask_set_ins_h d_window_set_ins_h d_window_size_set_ins_h d_prev_set_ins_h d_head_set_ins_h d_ins_h_set_ins_h d_hash_size_set_ins_h d_hash_bits_set_ins_h d_hash_mask_set_ins_h d_hash_shift_set_ins_h d_block_start_set_ins_h d_match_length_set_ins_h d_prev_match_set_ins_h d_match_available_set_ins_h d_strstart_set_ins_h d_match_start_set_ins_h d_lookahead_set_ins_h d_prev_length_set_ins_h d_max_chain_length_set_ins_h d_max_lazy_match_set_ins_h d_good_match_set_ins_h d_nice_match_set_ins_h d_insert_set_ins_h d_high_water_set_ins_h d_slid_set_ins_h d_pending_buf_size_set_ins_h d_tr_set_ins_h d_pbm_set_ins_h d_status_set_match_start d_po_set_match_start d_wrap_set_match_start d_gzhead_set_match_start d_gzindex_set_match_start d_method_set_match_start d_last_flush_set_match_start d_w_size_set_match_start d_w_bits_set_match_start d_w_mask_set_match_start d_window_set_match_start d_window_size_set_match_start d_prev_set_match_start d_head_set_match_start d_ins_h_set_match_start d_hash_size_set_match_start d_hash_bits_set_match_start d_hash_mask_set_match_start d_hash_shift_set_match_start d_block_start_set_match_start d_match_length_set_match_start d_prev_match_set_match_start d_match_available_set_match_start d_strstart_set_match_start d_match_start_set_match_start d_lookahead_set_match_start d_prev_length_set_match_start d_max_chain_length_set_match_start d_max_lazy_match_set_match_start d_good_match_set_match_start d_nice_match_set_match_start d_insert_set_match_start d_high_water_set_match_start d_slid_set_match_start d_pending_buf_size_set_match_start d_tr_set_match_start d_pbm_set_match_start : dproj.
Lemma set_ms_ms s a b : set_d_match_start (set_d_match_start s a) b = set_d_match_start s b. Proof. reflexivity. Qed.

(** ** INSERT_STRING *)
Lemma ins_ok : ins_spec.
Proof.
  intros s p n l G Hprm Hws Hcw Hp Hlen Hdef Hn Hl.
  destruct (prm_w s Hprm) as (Hwr & Hwm & Hwsz & Hwb).
  destruct (prm_h s Hprm) as (Hhs & Hhm & Hhb & Hsh).
  destruct Hws as (Hwl & Hwok & Hwsize & Hpl & Hhl).
  destruct Hcw as (Hc1 & Hc2 & Hc3).
  set (hv := update_hash s (d_ins_h s) (Znth (p + 2) (mb_val (d_window s)))).
  assert (Hhv : 0 <= hv < d_hash_size s).
  { unfold hv, update_hash. rewrite Hhm, Hhs. pose proof (land_mask_range
      (Z.lxor (u32 (Z.shiftl (d_ins_h s) (d_hash_shift s))) (Znth (p + 2) (mb_val (d_window s))))
      (d_hash_bits s) (proj1 Hhb)).
    rewrite u32_id; [lia|]. split; [lia|]. assert (2 ^ d_hash_bits s <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia).
    lia. }
  set (pi := Z.land p (d_w_mask s)).
  assert (Hpi : 0 <= pi < d_w_size s) by (unfold pi; rewrite Hwm, Hwsz; apply land_mask_range; lia).
  set (h := Znth hv (d_head s)).
  exists (set_d_head (set_d_prev (set_d_ins_h s hv) (upd_Znth pi (d_prev s) h)) (upd_Znth hv (d_head s) (u16 p))), h.
  split.
  { unfold c_insert_string.
    replace (d_hash_shift s <? 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [guard bind].
    change (p + (MIN_MATCH - 1)) with (p + 2). rewrite u32_id by lia.
    rewrite mb_rd_ok by (first [exact Hdef | lia]). cbn [bind]. fold hv.
    change (d_ins_h (set_d_ins_h s hv)) with hv. change (d_head (set_d_ins_h s hv)) with (d_head s).
    rewrite rd_ok by lia. cbn [bind].
    change (d_prev (set_d_ins_h s hv)) with (d_prev s). change (d_w_mask (set_d_ins_h s hv)) with (d_w_mask s).
    fold pi. rewrite wr_ok by lia. cbn [bind]. fold h.
    change (d_head (set_d_prev (set_d_ins_h s hv) (upd_Znth pi (d_prev s) h))) with (d_head s).
    change (d_ins_h (set_d_prev (set_d_ins_h s hv) (upd_Znth pi (d_prev s) h))) with hv.
    rewrite wr_ok by lia. reflexivity. }
  rewrite u16_id by lia.
  split; [reflexivity|].
  split.
  { unfold wstruct; autorewrite with dproj.
    split; [exact Hwl|]. split; [exact Hwok|]. split; [exact Hwsize|].
    split; rewrite upd_Znth_Zlength; lia. }
  split; [apply Hc2; lia|].
  assert (Hprev' : forall q, Znth (Z.land q (d_w_mask s))
            (upd_Znth pi (d_prev s) h) = if Z.land q (d_w_mask s) =? pi then h
            else Znth (Z.land q (d_w_mask s)) (d_prev s)).
  { intros q. destruct (Z.eqb_spec (Z.land q (d_w_mask s)) pi) as [E|E].
    - rewrite E. apply upd_Znth_same. lia.
    - apply upd_Znth_diff; try lia. rewrite Hwm. pose proof (land_mask_range q (d_w_bits s) Hwb). lia. }
  split.
  - split; [|split].
    + intros v [Hv|Hv]; [destruct (Hc1 v Hv); lia|lia].
    + intros h' Hh'. autorewrite with dproj in *.
      destruct (Z.eq_dec h' hv) as [->|E].
      * rewrite upd_Znth_same by lia. right; reflexivity.
      * rewrite upd_Znth_diff by lia. left. apply Hc2. lia.
    + intros q Hq Hq0 Hql. autorewrite with dproj. rewrite Hprev'.
      destruct (Z.land q (d_w_mask s) =? pi) eqn:E.
      * left. apply Hc2. lia.
      * left. destruct Hq as [Hq|Hq].
        -- apply Hc3; auto.
        -- subst q. unfold pi in E. rewrite Z.eqb_refl in E. discriminate.
  - split; [exact Hc1|].
    intros q Hq Hq0 Hql. autorewrite with dproj. rewrite Hprev'.
    destruct (Z.land q (d_w_mask s) =? pi); [apply Hc2; lia|apply Hc3; auto].
Qed.

(** ** longest_match *)

(** The inner comparison loop: at most 256 steps, the reads in scan .. strstart + 258 and cur .. cur + 258. *)
Lemma cmp_ok s0 st cur :
  st + MAX_MATCH < Zlength (mb_val (d_window s0)) ->
  (forall i, 0 <= i <= st + MAX_MATCH -> Znth i (mb_def (d_window s0)) = true) ->
  0 <= cur < st ->
  exists sc, loop FUEL (lm_cmp_body s0 (st + MAX_MATCH)) (st + 2, cur + 2, 0) = Some sc /\
             st + 3 <= sc <= st + MAX_MATCH.
Proof.
  intros Hl Hd Hc.
  apply (loop_measure _
    (fun a => let '(scan, mt, k) := a in
       exists q, scan = st + 2 + 8 * q + k /\ mt = cur + 2 + 8 * q + k /\ 0 <= q <= 31 /\ 0 <= k <= 7)
    (fun sc => st + 3 <= sc <= st + MAX_MATCH)
    (fun a => let '(scan, mt, k) := a in st + MAX_MATCH - scan)).
  - intros [[scan mt] k] [q (-> & -> & Hq & Hk)]. unfold MAX_MATCH in *. split; [lia|].
    unfold lm_cmp_body.
    rewrite !mb_rd_ok by (try apply Hd; lia). cbn [bind].
    destruct (negb _) eqn:E1; [left; eexists; split; [reflexivity|lia]|].
    destruct (Z.eqb_spec k 7) as [->|Hk7].
    + destruct (Z.ltb_spec (st + 2 + 8 * q + 7 + 1) (st + 258)) as [Hlt|Hge].
      * right. eexists; split; [reflexivity|]. split; [exists (q + 1); lia|lia].
      * left. eexists; split; [reflexivity|lia].
    + right. eexists; split; [reflexivity|]. split; [exists q; lia|lia].
  - exists 0. lia.
  - unfold MAX_MATCH. change (2 ^ Z.of_nat FUEL) with (2 ^ 40). lia.
Qed.

(** lm_body with its local [next] named *)
Definition lm_next (limit : Z) (a : lm_st) : option (lm_st + (Z * dstate)) :=
  let s := lm_s a in
  let* cur' := rd (d_prev s) (Z.land (lm_cur a) (d_w_mask s)) in
  if cur' >? limit then
    let chain := u32 (lm_chain a - 1) in
    if chain =? 0 then Some (inr (lm_best a, s))
    else Some (inl (mkLM cur' chain (lm_best a) (lm_end1 a) (lm_end a) s))
  else Some (inr (lm_best a, s)).

Lemma lm_body_eq nice limit cur chain best e1 e s0 : lm_body nice limit (mkLM cur chain best e1 e s0) =
  let* m0 := mb_rd (d_window s0) (cur + best) in
  if negb (m0 =? e) then lm_next limit (mkLM cur chain best e1 e s0) else
  let* m1 := mb_rd (d_window s0) (cur + best - 1) in
  if negb (m1 =? e1) then lm_next limit (mkLM cur chain best e1 e s0) else
  let* m2 := mb_rd (d_window s0) cur in
  let* sc0 := mb_rd (d_window s0) (d_strstart s0) in
  if negb (m2 =? sc0) then lm_next limit (mkLM cur chain best e1 e s0) else
  let* m3 := mb_rd (d_window s0) (cur + 1) in
  let* sc1 := mb_rd (d_window s0) (d_strstart s0 + 1) in
  if negb (m3 =? sc1) then lm_next limit (mkLM cur chain best e1 e s0) else
  let* scan' := loop FUEL (lm_cmp_body s0 (d_strstart s0 + MAX_MATCH)) (d_strstart s0 + 2, cur + 2, 0) in
  if MAX_MATCH - (d_strstart s0 + MAX_MATCH - scan') >? best then
    if MAX_MATCH - (d_strstart s0 + MAX_MATCH - scan') >=? nice
    then Some (inr (MAX_MATCH - (d_strstart s0 + MAX_MATCH - scan'), set_d_match_start s0 cur)) else
    let* e1' := mb_rd (d_window (set_d_match_start s0 cur))
                  (d_strstart s0 + (MAX_MATCH - (d_strstart s0 + MAX_MATCH - scan')) - 1) in
    let* e' := mb_rd (d_window (set_d_match_start s0 cur))
                  (d_strstart s0 + (MAX_MATCH - (d_strstart s0 + MAX_MATCH - scan'))) in
    lm_next limit (mkLM cur chain (MAX_MATCH - (d_strstart s0 + MAX_MATCH - scan')) e1' e'
                     (set_d_match_start s0 cur))
  else lm_next limit (mkLM cur chain best e1 e s0).
Proof. reflexivity. Qed.

Section LM.
Variables (s : dstate) (n l : Z) (G : Z -> Prop).
Hypotheses (Hprm : prm s) (Hws : wstruct s) (Hcc : chain_closed s n l G) (Hn : n <= d_strstart s)
  (Hl : l <= lim s) (Hlen : d_strstart s + MAX_MATCH < Zlength (mb_val (d_window s)))
  (Hdef : forall i, 0 <= i <= d_strstart s + MAX_MATCH -> Znth i (mb_def (d_window s)) = true)
  (Hpl : 0 <= d_prev_length s <= MAX_MATCH).

Definition msok (ms : Z) : Prop := lim s <= ms /\ 0 < ms < d_strstart s.

Definition LP (a : lm_st) : Prop := exists ms,
  lm_s a = set_d_match_start s ms /\ (ms = d_match_start s \/ msok ms) /\
  (d_prev_length s < lm_best a -> msok ms) /\ d_prev_length s <= lm_best a <= MAX_MATCH /\
  G (lm_cur a) /\ 0 < lm_cur a /\ lim s <= lm_cur a.

Definition LQ (r : Z * dstate) : Prop := exists ms,
  snd r = set_d_match_start s ms /\ (ms = d_match_start s \/ msok ms) /\
  (d_prev_length s < fst r -> msok ms) /\ d_prev_length s <= fst r <= MAX_MATCH.

Definition lmm (a : lm_st) : Z :=
  if (0 <? lm_chain a) && (lm_chain a <? 4294967296) then lm_chain a else 4294967296.

Lemma lim_nonneg : 0 <= lim s.
Proof. unfold lim. destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); lia. Qed.

Lemma cur_lt cur : G cur -> 0 < cur -> cur < d_strstart s.
Proof. intros HG H0. destruct Hcc as [Hc1 _]. destruct (Hc1 cur HG); lia. Qed.

Lemma lmm_range a : 0 <= lmm a <= 4294967296.
Proof. unfold lmm. destruct ((0 <? lm_chain a) && (lm_chain a <? 4294967296)) eqn:E; [|lia].
  apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.ltb_lt in E1, E2. lia. Qed.

Lemma next_ok a : LP a ->
  lm_next (lim s) a = Some (inr (lm_best a, lm_s a)) \/
  exists a', lm_next (lim s) a = Some (inl a') /\ LP a' /\ lmm a' < lmm a.
Proof.
  destruct a as [cur chain best e1 e s0].
  intros (ms & Hs0 & Hms & Hbest & Hb & HG & Hc0 & Hcl). cbn [lm_s lm_cur lm_best lm_chain] in *. subst s0.
  destruct (prm_w s Hprm) as (Hwr & Hwm & Hwsz & Hwb).
  destruct Hws as (Hwl & Hwok & Hwsize & Hpl' & Hhl).
  pose proof lim_nonneg as Hlim0. pose proof (cur_lt cur HG Hc0) as Hcs.
  unfold lm_next. cbn [lm_s lm_cur lm_chain lm_best lm_end1 lm_end]. autorewrite with dproj.
  rewrite rd_ok by (rewrite Hpl', Hwm, Hwsz; apply land_mask_range; lia). cbn [bind].
  destruct (Z.gtb_spec (Znth (Z.land cur (d_w_mask s)) (d_prev s)) (lim s)) as [Hgt|Hle]; [|left; reflexivity].
  destruct (Z.eqb_spec (u32 (chain - 1)) 0) as [E|E]; [left; reflexivity|].
  right. eexists; split; [reflexivity|]. split.
  - exists ms. cbn [lm_s lm_cur lm_best]. split; [reflexivity|]. split; [exact Hms|]. split; [exact Hbest|].
    split; [exact Hb|]. destruct Hcc as [_ Hc2]. split; [apply Hc2; auto; lia|]. lia.
  - unfold lmm. cbn [lm_chain]. unfold u32 in *.
    pose proof (Z.mod_pos_bound (chain - 1) 4294967296 ltac:(lia)) as Hmb.
    replace ((0 <? (chain - 1) mod 4294967296) && ((chain - 1) mod 4294967296 <? 4294967296)) with true
      by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
    destruct ((0 <? chain) && (chain <? 4294967296)) eqn:Ec; [|lia].
    apply andb_true_iff in Ec. destruct Ec as [Ec1 Ec2]. apply Z.ltb_lt in Ec1, Ec2.
    rewrite Z.mod_small by lia. lia.
Qed.

Lemma step_ok nice a : LP a -> 0 <= lmm a /\
  ((exists r, lm_body nice (lim s) a = Some (inr r) /\ LQ r) \/
   (exists a', lm_body nice (lim s) a = Some (inl a') /\ LP a' /\ lmm a' < lmm a)).
Proof.
  intros HP. split; [pose proof (lmm_range a); lia|].
  assert (Hnext : forall a0, LP a0 -> lmm a0 = lmm a ->
    (exists r, lm_next (lim s) a0 = Some (inr r) /\ LQ r) \/
    (exists a', lm_next (lim s) a0 = Some (inl a') /\ LP a' /\ lmm a' < lmm a)).
  { intros a0 H0 Hm. destruct (next_ok a0 H0) as [E|(a' & E & H' & Hm')]; [left|right].
    - exists (lm_best a0, lm_s a0); split; [exact E|].
      destruct H0 as (ms & Hs0 & Hms & Hbest & Hb & _). exists ms. cbn [fst snd]. auto.
    - exists a'. split; [exact E|]. split; [exact H'|]. lia. }
  destruct a as [cur chain best e1 e s0].
  pose proof HP as (ms & Hs0 & Hms & Hbest & Hb & HG & Hc0 & Hcl). cbn [lm_s lm_cur lm_best lm_chain] in *.
  subst s0.
  pose proof lim_nonneg as Hlim0. pose proof (cur_lt cur HG Hc0) as Hcs.
  rewrite lm_body_eq. autorewrite with dproj.
  assert (Hrd : forall i, 0 <= i <= d_strstart s + MAX_MATCH ->
            mb_rd (d_window s) i = Some (Znth i (mb_val (d_window s))))
    by (intros i Hi; apply mb_rd_ok; [lia|apply Hdef; lia]).
  unfold MAX_MATCH in Hrd, Hb, Hpl.
  rewrite (Hrd (cur + best)) by lia. cbn [bind].
  destruct (negb _); [apply Hnext; auto|].
  rewrite (Hrd (cur + best - 1)) by lia. cbn [bind].
  destruct (negb _); [apply Hnext; auto|].
  rewrite (Hrd cur), (Hrd (d_strstart s)) by lia. cbn [bind].
  destruct (negb _); [apply Hnext; auto|].
  rewrite (Hrd (cur + 1)), (Hrd (d_strstart s + 1)) by lia. cbn [bind].
  destruct (negb _); [apply Hnext; auto|].
  destruct (cmp_ok (set_d_match_start s ms) (d_strstart s) cur) as (sc & Esc & Hsc).
  { autorewrite with dproj. exact Hlen. }
  { autorewrite with dproj. exact Hdef. }
  { lia. }
  autorewrite with dproj in Esc. rewrite Esc. cbn [bind]. unfold MAX_MATCH in Hsc |- *.
  destruct (Z.gtb_spec (258 - (d_strstart s + 258 - sc)) best) as [Hgt|Hle].
  - rewrite set_ms_ms.
    destruct (Z.geb_spec (258 - (d_strstart s + 258 - sc)) nice) as [Hge|Hlt].
    + left. eexists; split; [reflexivity|]. exists cur. cbn [fst snd].
      split; [reflexivity|]. unfold msok, MAX_MATCH. split; [right; lia|]. split; [intros; lia|lia].
    + autorewrite with dproj. rewrite !Hrd by lia. cbn [bind]. apply Hnext; [|reflexivity].
      exists cur. cbn [lm_s lm_cur lm_best]. unfold msok, MAX_MATCH.
      split; [reflexivity|]. split; [right; lia|]. split; [intros; lia|]. split; [lia|]. auto.
  - apply Hnext; auto.
Qed.

Lemma lm_loop_ok nice cur chain best e1 e :
  LP (mkLM cur chain best e1 e s) ->
  exists r, loop FUEL (lm_body nice (lim s)) (mkLM cur chain best e1 e s) = Some r /\ LQ r.
Proof.
  intros HP. apply (loop_measure _ LP LQ lmm (step_ok nice)); [exact HP|].
  pose proof (lmm_range (mkLM cur chain best e1 e s)). change (2 ^ Z.of_nat FUEL) with (2 ^ 40). lia.
Qed.
End LM.

Lemma lm_ok' : lm_spec.
Proof.
  intros s cur n l G Hprm Hws Hcc Hn Hl HG Hc0 Hcl Hpl Hla Hlaw Hlen Hdef.
  destruct (prm_w s Hprm) as (Hwr & Hwm & Hwsz & Hwb).
  pose proof Hws as (Hwl & Hwok & Hwsize & Hpl' & Hhl).
  pose proof (cur_lt s n l G Hcc Hn cur HG Hc0) as Hcs.
  unfold c_longest_match. cbv zeta.
  unfold MAX_MATCH, MIN_MATCH in Hpl, Hla, Hlen.
  replace (in_int (d_prev_length s)) with true
    by (symmetry; unfold in_int; apply andb_true_iff; split; apply Z.leb_le; lia).
  replace (in_int (d_lookahead s)) with true
    by (symmetry; unfold in_int; apply andb_true_iff; split; apply Z.leb_le; lia).
  replace (d_strstart s + MAX_MATCH <=? Zlength (mb_val (d_window s))) with true
    by (symmetry; apply Z.leb_le; unfold MAX_MATCH; lia).
  cbn [guard bind].
  replace (if d_strstart s >? u32 (d_w_size s - MIN_LOOKAHEAD)
           then u32 (d_strstart s - u32 (d_w_size s - MIN_LOOKAHEAD)) else NIL) with (lim s).
  2:{ unfold lim, MAX_DIST. change MIN_LOOKAHEAD with 262. rewrite (u32_id (d_w_size s - 262)) by lia.
      destruct (Z.gtb_spec (d_strstart s) (d_w_size s - 262)); [|reflexivity].
      rewrite u32_id by lia. reflexivity. }
  rewrite !mb_rd_ok by (try apply Hdef; unfold MAX_MATCH; lia). cbn [bind].
  match goal with |- context [loop FUEL (lm_body ?nc (lim s)) (mkLM cur ?ch ?b ?x ?y s)] =>
    destruct (lm_loop_ok s n l G Hprm Hws Hcc Hn Hl Hlen Hdef Hpl nc cur ch b x y) as (r & Er & HQ) end.
  { exists (d_match_start s). cbn [lm_s lm_cur lm_best].
    split; [destruct s; reflexivity|]. split; [left; reflexivity|]. split; [lia|].
    split; [unfold MAX_MATCH; lia|]. split; [exact HG|]. split; [exact Hc0|]. exact Hcl. }
  rewrite Er. cbn [bind]. destruct r as [best' s'].
  destruct HQ as (ms & Hs' & Hms & Hbest & Hb). cbn [fst snd] in *. subst s'.
  exists ms, (if best' <=? d_lookahead s then best' else d_lookahead s).
  split; [reflexivity|].
  unfold msok in *. unfold MAX_MATCH in *.
  destruct (Z.leb_spec best' (d_lookahead s));
    (split; [lia|]); (split; [lia|]); (split; [exact Hms|]); intros; apply Hbest; lia.
Qed.
