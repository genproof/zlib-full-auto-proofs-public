(** * deflateSetDictionary, fragment S_clear (DictKit.v): CLEAR_HASH(s); strstart = block_start = insert = 0. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.DictKit.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** CLEAR_HASH: zero bytes written by memset are zero unsigned shorts *)

Lemma tuchar_zero_mapsto_zeros1 sh q :
  readable_share sh ->
  @data_at DCS.CS sh tuchar (Vint Int.zero) q |-- mapsto_zeros 1 sh q.
Proof.
  intros Hsh.
  unfold data_at, field_at, at_offset. simpl.
  Intros. destruct q; try (destruct H as [Hp _]; contradiction).
  rewrite data_at_rec_eq. simpl. unfold mapsto. simpl. rewrite if_true by auto.
  destruct H as (_ & _ & Hsz & _). red in Hsz. simpl in Hsz.
  rewrite Ptrofs.add_zero.
  unfold mapsto_zeros. apply orp_left.
  - normalize. rewrite prop_true_andp by rep_lia. simpl.
    change (predicates_sl.sepcon ?a predicates_sl.emp) with (a * emp)%logic. rewrite sepcon_emp.
    apply derives_refl.
  - normalize. discriminate.
Qed.

Lemma tuchar_zeros_mapsto_zeros sh b ofs :
  readable_share sh -> 0 <= ofs ->
  forall n, 0 <= n -> ofs + n < Ptrofs.modulus ->
  @data_at DCS.CS sh (tarray tuchar n) (Zrepeat (Vint Int.zero) n) (Vptr b (Ptrofs.repr ofs))
  |-- mapsto_zeros n sh (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros Hsh Ho n Hn. pattern n. revert n Hn. apply natlike_ind.
  - intros _. rewrite VST.floyd.aggregate_pred.mapsto_zeros_zero_Vptr. entailer!.
    rewrite data_at_zero_array_eq; auto.
  - intros x Hx IH Hm.
    assert_PROP (field_compatible (tarray tuchar (Z.succ x)) nil (Vptr b (Ptrofs.repr ofs))) by entailer!.
    replace (Zrepeat (Vint Int.zero) (Z.succ x)) with (Zrepeat (Vint Int.zero) x ++ [Vint Int.zero])
      by (unfold Zrepeat; rewrite Z2Nat.inj_succ by lia; rewrite <- repeat_cons; reflexivity).
    rewrite (split2_data_at_Tarray_app x (Z.succ x)) by (try rewrite Zlength_Zrepeat; list_solve).
    rewrite field_address0_offset by auto with field_compatible.
    replace (Z.succ x - x) with 1 by lia.
    rewrite (data_at_singleton_array_eq sh tuchar (Vint Int.zero)) by reflexivity.
    sep_apply IH; [lia|].
    sep_apply tuchar_zero_mapsto_zeros1.
    unfold Z.succ. rewrite VST.floyd.aggregate_pred.mapsto_zeros_split by lia.
    simpl offset_val. rewrite ptrofs_add_repr. cancel.
    replace (ofs + (0 + 1 * x)) with (ofs + x) by lia. apply derives_refl.
Qed.

(** head[hash_size-1] stored: the rest of head[] as the bytes memset clears, and the last entry. *)
Lemma head_split n (l : list val) p : 1 <= n -> n <= Int.max_unsigned -> Zlength l = n ->
  @data_at DCS.CS Ews (tarray tushort n) (upd_Znth (n - 1) l (Vint (Int.zero_ext 16 (Int.repr 0)))) p
  |-- @data_at_ DCS.CS Ews (tarray tuchar ((n - 1) * 2)) p *
      @data_at DCS.CS Ews (tarray tushort 1) [vi 0] (offset_val ((n - 1) * 2) p).
Proof.
  intros Hn Hm Hl.
  assert_PROP (field_compatible (tarray tushort n) nil p) as Hfc by entailer!.
  replace (upd_Znth (n - 1) l (Vint (Int.zero_ext 16 (Int.repr 0))))
    with (sublist 0 (n - 1) l ++ [vi 0]).
  2: { rewrite upd_Znth_unfold by lia. list_solve. }
  rewrite (split2_data_at_Tarray_app (n - 1) n) by (rewrite ?Zlength_sublist; list_solve).
  rewrite field_address0_offset by auto with field_compatible.
  replace (n - (n - 1)) with 1 by lia.
  simpl nested_field_offset. replace (0 + 2 * (n - 1)) with ((n - 1) * 2) by lia.
  apply sepcon_derives; [|apply derives_refl].
  sep_apply data_at_data_at_.
  rewrite data_at__memory_block. Intros.
  rewrite <- memory_block_data_at__tarray_tuchar_eq by (simpl in *; rep_lia).
  simpl sizeof. replace (2 * Z.max 0 (n - 1)) with ((n - 1) * 2) by lia. apply derives_refl.
Qed.

(** The zero bytes memset wrote and the last entry: head[] all zero. *)
Lemma head_join n p : 1 <= n -> field_compatible (tarray tushort n) nil p ->
  @data_at DCS.CS Ews (tarray tuchar ((n - 1) * 2)) (Zlib.proof.zutil.Libc.byte_vals (repeat (0 mod 256) (Z.to_nat ((n - 1) * 2)))) p *
  @data_at DCS.CS Ews (tarray tushort 1) [vi 0] (offset_val ((n - 1) * 2) p)
  |-- @data_at DCS.CS Ews (tarray tushort n) (map vi (repeat 0 (Z.to_nat n))) p.
Proof.
  intros Hn Hfc.
  pose proof Hfc as Hfc'. destruct Hfc' as (Hp & _ & Hsz & _).
  destruct p; try contradiction. red in Hsz. simpl sizeof in Hsz.
  pose proof (Ptrofs.unsigned_range i) as Hi.
  rewrite <- (Ptrofs.repr_unsigned i) in Hfc |- *. set (ofs := Ptrofs.unsigned i) in *.
  assert (Hr : ofs + (n - 1) * 2 < Ptrofs.modulus) by lia.
  replace (Zlib.proof.zutil.Libc.byte_vals (repeat (0 mod 256) (Z.to_nat ((n - 1) * 2)))) with (Zrepeat (Vint Int.zero) ((n - 1) * 2))
    by (unfold Zlib.proof.zutil.Libc.byte_vals; rewrite map_repeat; reflexivity).
  sep_apply (tuchar_zeros_mapsto_zeros Ews b ofs (writable_readable writable_Ews) (proj1 Hi)
               ((n - 1) * 2) ltac:(lia) Hr).
  replace ((n - 1) * 2) with (sizeof (tarray tushort (n - 1))) at 1 by (simpl; lia).
  sep_apply (mapsto_zero_data_at_zero (tarray tushort (n - 1)) Ews); auto.
  { apply field_compatible_array_smaller0 with n; auto; lia. }
  rewrite zero_val_tarray. replace (zero_val tushort) with (vi 0) by (symmetry; apply zero_val_Tint).
  replace (map vi (repeat 0 (Z.to_nat n))) with (Zrepeat (vi 0) (n - 1) ++ [vi 0]).
  2: { unfold Zrepeat. rewrite map_repeat. replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia.
       rewrite <- repeat_cons. reflexivity. }
  rewrite (split2_data_at_Tarray_app (n - 1) n) by (rewrite ?Zlength_Zrepeat; list_solve).
  rewrite field_address0_offset by auto with field_compatible.
  replace (n - (n - 1)) with 1 by lia.
  simpl nested_field_offset. replace (0 + 2 * (n - 1)) with ((n - 1) * 2) by lia. cancel.
Qed.

Lemma sd_clear : sd_clear_triple.
Proof.
  unfold sd_clear_triple. intros.
  unfold c_clear_hash in H.
  inv_bind H. inv_bind H. destruct x0. apply guard_inv in Ha0. inversion H; subst s1; clear H.
  unfold wr in Ha. destruct (in_range _ _) eqn:Hir in Ha; [|discriminate].
  inversion Ha; subst x; clear Ha.
  rewrite andb_true_iff, Z.leb_le, Z.eqb_eq in Ha0. destruct Ha0 as [Hhs Hzl].
  rewrite Zlength_upd_Znth in Hzl.
  set (s2 := sd_clear_post _).
  unfold dstate_at at 1, hash_at, match_at. Intros.
  rewrite Hzl.
  assert (Hhsu : d_hash_size s <= Int.max_unsigned) by (unfold dstate_ranges, u32_ok in H; tauto).
  freeze [0;1;2;4;6;7;8;9;12;13;14;16;17;18;21;22;23] FR.
  show_sd_stmt.
  assert_PROP (field_compatible (tarray tushort (d_hash_size s)) nil (p_head p)) as Hfc by entailer!.
  eapply semax_seq'.
  { apply semax_loop_nocontinue.
    forward. forward. forward.
    sep_apply (head_split (d_hash_size s) (map vi (d_head s)) (p_head p) Hhs Hhsu
                 ltac:(rewrite Zlength_map; exact Hzl)). Intros.
    forward. forward.
    forward_call (Ews, p_head p, (d_hash_size s - 1) * 2, 0).
    sep_apply (head_join (d_hash_size s) (p_head p) Hhs Hfc).
    forward. forward.
    apply andp_left2; apply derives_refl. }
  abbreviate_semax.
  forward. forward. forward.
  thaw FR.
  assert (Hzr : Zlength (repeat 0 (Z.to_nat (d_hash_size s))) = d_hash_size s)
    by (rewrite Zlength_correct, repeat_length; lia).
  assert (Hrng : dstate_ranges s2).
  { unfold dstate_ranges in H |- *. unfold s2, sd_clear_post. cbn [d_trm d_tr d_pbm d_status d_po d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_block_start d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size set_d_insert set_d_block_start set_d_strstart set_d_slid set_d_head].
    rewrite Hzr.
    unfold u32_ok, u64_ok, s32_ok, s64_ok in *. decompose [and] H.
    repeat (first [assumption | split]); try rep_lia.
    rewrite Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. }
  assert (Htrm : d_trm s2 = d_trm s) by reflexivity.
  assert (Hw : win_at s2 p = win_at s p) by reflexivity.
  assert (Hc : cfg_at s2 p = cfg_at s p) by reflexivity.
  assert (Hst : stat_at s2 p = stat_at s p) by reflexivity.
  unfold dstate_at. rewrite (prop_true_andp _ _ Hrng). rewrite Htrm, Hw, Hc, Hst.
  unfold hash_at, match_at.
  unfold s2, sd_clear_post. cbn [d_trm d_tr d_pbm d_status d_po d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_block_start d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size set_d_insert set_d_block_start set_d_strstart set_d_slid set_d_head].
  rewrite Hzr.
  entailer!.
Qed.
