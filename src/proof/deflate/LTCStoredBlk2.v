(** * deflate_stored at level 0: the second-phase stored block
    Statement and design: LTCStoredKit.v and its header. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCStoredKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** W survives a change of the output part and of block_start (level 0, no symbols). *)
Lemma W_ob s s' :
  W s -> d_level s = 0 -> ob_keep s' = ob_keep s ->
  Zlength (o_buf (tr_out (d_tr s'))) = Zlength (o_buf (tr_out (d_tr s))) ->
  Zlength (d_pbm s') = Zlength (d_pbm s) ->
  d_block_start s <= d_block_start s' <= d_strstart s -> W s'.
Proof.
  intros HW Hl Hob E1 E2 Hbs.
  destruct s as [x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 tr pb], s' as [y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 y32 y33 y34 y35 tr' pb'], tr as [t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15], tr' as [u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15].
  cbn [ob_keep fp_keep set_d_block_start set_d_po set_d_pbm set_d_tr set_out d_tr d_pbm d_po d_block_start tr_out tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk tr_sym_next tr_sym_end tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type d_status d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size] in Hob.
  injection Hob; intros; subst. clear Hob.
  cbn [d_tr d_pbm d_po d_block_start tr_out tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk tr_sym_next tr_sym_end tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type d_status d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size d_level] in E1, E2, Hbs, Hl.
  destruct HW as (Hp & Hws & Hwp & Hww & Hwh & Hwm & Hl0 & syms & Ht).
  unfold W.
  split; [|split; [exact Hws|split; [|split; [exact Hww|split; [exact Hwh|split; [exact Hwm|split]]]]]].
  - unfold prm, d_L in Hp |- *. cbn [d_tr d_pbm d_po d_block_start tr_out tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk tr_sym_next tr_sym_end tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type d_status d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size d_level] in Hp |- *. rewrite E1, E2. exact Hp.
  - unfold wpos in Hwp |- *. cbn [d_tr d_pbm d_po d_block_start tr_out tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk tr_sym_next tr_sym_end tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type d_status d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size] in Hwp |- *.
    unfold d_level in Hl0; cbn [d_tr d_pbm d_po d_block_start tr_out tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk tr_sym_next tr_sym_end tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type d_status d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size] in Hl0. destruct (Hl0 Hl) as [Hla Hb0].
    destruct Hwp as (A1&A2&A3&A4&A5&A6&A7&A8&A9). repeat split; try lia.
  - unfold d_level in Hl0 |- *; cbn [d_tr d_pbm d_po d_block_start tr_out tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk tr_sym_next tr_sym_end tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type d_status d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size] in Hl0 |- *. intros _. destruct (Hl0 Hl). lia.
  - exists []. unfold wtrees, tree_ok, d_L, d_level in Ht |- *. cbn [d_tr d_pbm d_po d_block_start tr_out tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk tr_sym_next tr_sym_end tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type d_status d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size] in Ht |- *.
    destruct Ht as ((T1&T2&T3&T4&T5&T6&T7&T8&T9&T10) & Hs1 & Hs2 & Hs3 & Hs4).
    rewrite (Hs3 Hl) in *. clear Hs3.
    split; [|split; [|split; [constructor|split; [auto|intros N; congruence]]]].
    + rewrite E1, E2. refine (conj T1 (conj T2 (conj T3 (conj _ (conj _ (conj _ (conj T7 (conj T8 (conj T9 T10))))))))).
      * intros x [].
      * rewrite Zlength_nil, Z.mul_0_r, Z.add_0_r, sublist_nil. reflexivity.
      * rewrite Zlength_nil, Z.mul_0_r, Z.add_0_r, sublist_nil. reflexivity.
    + rewrite Zlength_nil in *. lia.
Qed.

Lemma mb_read_ok b lo len :
  mb_defined b lo (lo + len) -> 0 <= len -> mb_read b lo len = Some (sublist lo (lo + len) (mb_val b)).
Proof.
  intros (H1 & H2 & H3) Hl. unfold mb_read, mb_definedb.
  assert (F : forallb (fun i => Znth i (mb_def b))
                (map (fun k => lo + Z.of_nat k) (seq 0 (Z.to_nat (lo + len - lo)))) = true).
  { apply forallb_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (k & <- & Hk).
    apply in_seq in Hk. apply H3. lia. }
  rewrite F.
  replace (0 <=? len) with true by (symmetry; apply Z.leb_le; lia).
  replace (0 <=? lo) with true by (symmetry; apply Z.leb_le; lia).
  replace (lo + len <=? Zlength (mb_val b)) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma ob_keep_fp s s' : fp_keep s' = fp_keep s -> ob_keep s' = ob_keep s.
Proof. intros H. unfold ob_keep. rewrite H. reflexivity. Qed.

Lemma fp_fields s s' : fp_keep s' = fp_keep s ->
  d_block_start s' = d_block_start s /\ d_strstart s' = d_strstart s /\ d_lookahead s' = d_lookahead s.
Proof.
  intros H. split; [|split].
  - exact (f_equal d_block_start H).
  - exact (f_equal d_strstart H).
  - exact (f_equal d_lookahead H).
Qed.

(* The lemma of this block against the false LTCSpecs.fpend_spec is not kept: see LTCStoredBlk2b.blk2_ok2. *)
