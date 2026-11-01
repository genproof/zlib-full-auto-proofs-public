(** * The body of deflate.c's lm_init against its shared specification (DSpec.lm_init_spec): ob_lm_init. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.deflate.code.

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
Lemma head_split n p : 1 <= n -> n <= Int.max_unsigned ->
  @data_at DCS.CS Ews (tarray tushort n)
    (upd_Znth (n - 1) (default_val (tarray tushort n)) (Vint (Int.zero_ext 16 (Int.repr 0)))) p
  |-- @data_at_ DCS.CS Ews (tarray tuchar ((n - 1) * 2)) p *
      @data_at DCS.CS Ews (tarray tushort 1) [vi 0] (offset_val ((n - 1) * 2) p).
Proof.
  intros Hn Hm.
  assert_PROP (field_compatible (tarray tushort n) nil p) as Hfc by entailer!.
  replace (upd_Znth (n - 1) (default_val (tarray tushort n)) (Vint (Int.zero_ext 16 (Int.repr 0))))
    with (Zrepeat Vundef (n - 1) ++ [vi 0]).
  2: { unfold default_val. simpl. rewrite upd_Znth_unfold by (rewrite Zlength_Zrepeat; lia).
       rewrite Zlength_Zrepeat by lia. rewrite sublist_Zrepeat by lia. rewrite sublist_Zrepeat by lia.
       replace (n - (n - 1 + 1)) with 0 by lia. replace (n - 1 - 0) with (n - 1) by lia.
       reflexivity. }
  rewrite (split2_data_at_Tarray_app (n - 1) n) by (rewrite ?Zlength_Zrepeat; list_solve).
  rewrite field_address0_offset by auto with field_compatible.
  replace (n - (n - 1)) with 1 by lia.
  simpl nested_field_offset. replace (0 + 2 * (n - 1)) with ((n - 1) * 2) by lia.
  apply sepcon_derives; [|apply derives_refl].
  change (Zrepeat Vundef (n - 1)) with (default_val (tarray tushort (n - 1))).
  change (data_at Ews (tarray tushort (n - 1)) (default_val (tarray tushort (n - 1))) p)
    with (data_at_ Ews (tarray tushort (n - 1)) p).
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

Lemma config_bounds i g l n c f : 0 <= i < 10 -> Znth i config_table = (g, l, n, c, f) ->
  0 <= g <= 258 /\ 0 <= l <= 258 /\ 0 <= n <= 258 /\ 0 <= c <= 4096.
Proof.
  intros Hi Hz.
  assert (Hc : In (g, l, n, c, f) config_table)
    by (rewrite <- Hz; apply Znth_In; change (Zlength config_table) with 10; lia).
  simpl in Hc. repeat (destruct Hc as [Hc|Hc]; [inversion Hc; subst; lia|]). contradiction.
Qed.

Lemma Znth_any {A} (d1 d2 : Inhabitant A) i (l : list A) : 0 <= i < Zlength l -> @Znth A d1 i l = @Znth A d2 i l.
Proof.
  intros Hi. unfold Znth. rewrite !if_false by lia. apply nth_indep.
  rewrite Zlength_correct in Hi. lia.
Qed.

Ltac cfg_fwd Hcv :=
  forward;
  [ rewrite Hcv; cbv beta iota; go_lower; apply prop_right; apply tc_val_tushort_repr; rep_lia
  | rewrite Hcv; cbv beta iota ].

Lemma body_lm_init : ob_lm_init.
Proof.
  unfold ob_lm_init.
  start_function.
  unfold c_lm_init, c_clear_hash in H. cbn [d_head d_hash_size set_d_window_size] in H.
  inv_bind H. inv_bind H. destruct x0. apply guard_inv in Ha0.
  inv_bind Ha. inv_bind Ha. destruct x1. apply guard_inv in Ha2. inversion Ha; subst x; clear Ha.
  assert (Hlv : d_level (set_d_slid (set_d_head (set_d_window_size s (u64 (2 * d_w_size s)))
                  (repeat 0 (Z.to_nat (d_hash_size s)))) 0) = d_level s) by reflexivity.
  rewrite Hlv in Ha0, H; clear Hlv.
  destruct (Znth (d_level s) config_table) as [[[[g l] n] c] f] eqn:Hcfg.
  inversion H; subst r; clear H.
  unfold wr in Ha1. destruct (in_range _ _) eqn:Hir in Ha1; [|discriminate].
  inversion Ha1; subst x0; clear Ha1 Hir.
  rewrite andb_true_iff, Z.leb_le, Z.eqb_eq in Ha2. destruct Ha2 as [Hhs Hzl].
  rewrite Zlength_upd_Znth in Hzl.
  rewrite andb_true_iff, Z.leb_le, Z.ltb_lt in Ha0.
  unfold dstate_at_h0, hash_at_h0, win_at, match_at, cfg_at, trees_at, lvl_at, deflate_globals. Intros.
  rewrite Hzl.
  assert (Hhsu : d_hash_size s <= Int.max_unsigned) by (unfold dstate_ranges, u32_ok in H; tauto).
  assert (Hwsu : 0 <= d_w_size s <= Int.max_unsigned) by (unfold dstate_ranges, u32_ok in H; tauto).
  change (d_level s) with (tr_level (fst (d_trm s))) in Hcfg, Ha0.
  set (lv := tr_level (fst (d_trm s))) in *.
  assert (Hcv : Znth lv (config_vals gv) = (vi g, (vi l, (vi n, (vi c, cfg_func_ptr gv f))))).
  { unfold config_vals. rewrite Znth_map by (change (Zlength config_table) with 10; lia). rewrite Hcfg. reflexivity. }
  assert (Hcv' : forall d, @Znth _ d lv (config_vals gv) = (vi g, (vi l, (vi n, (vi c, cfg_func_ptr gv f))))).
  { intros d. rewrite <- Hcv. apply Znth_any. unfold config_vals. rewrite Zlength_map.
    change (Zlength config_table) with 10; lia. }
  clear Hcv; rename Hcv' into Hcv.
  freeze [0;1;2;3;4;5;6;7;8;10;11;12;15;16;17;18;19;23;24;25;26;30;33;42;43;44;46;47] FR.
  forward. forward.
  assert_PROP (field_compatible (tarray tushort (d_hash_size s)) nil (p_head p)) as Hfc by entailer!.
  eapply semax_seq'.
  { apply semax_loop_nocontinue.
    forward. forward. forward.
    sep_apply (head_split (d_hash_size s) (p_head p) Hhs Hhsu). Intros.
    forward. forward.
    forward_call (Ews, p_head p, (d_hash_size s - 1) * 2, 0).
    sep_apply (head_join (d_hash_size s) (p_head p) Hhs Hfc).
    forward. forward.
    apply andp_left2; apply derives_refl. }
  unfold MORE_COMMANDS, abbreviate. abbreviate_semax.
  pose proof (config_bounds _ _ _ _ _ _ Ha0 Hcfg) as Hcb.
  forward. cfg_fwd Hcv. forward.
  forward. cfg_fwd Hcv. forward.
  forward. cfg_fwd Hcv. forward.
  forward. cfg_fwd Hcv. forward.
  forward. forward. forward. forward.
  forward. forward. forward.
  forward. forward.
  thaw FR.
  match goal with |- context [dstate_at ?r p gv] => set (rr := r) end.
  assert (Htrm : d_trm rr = d_trm s) by reflexivity.
  assert (Hst : stat_at rr p = stat_at s p) by reflexivity.
  assert (Hu : u64 (2 * d_w_size s) = 2 * d_w_size s).
  { change (u64 (2 * d_w_size s)) with ((2 * d_w_size s) mod 18446744073709551616).
    apply Z.mod_small. rep_lia. }
  assert (Hzr : Zlength (repeat 0 (Z.to_nat (d_hash_size s))) = d_hash_size s)
    by (rewrite Zlength_correct, repeat_length; lia).
  assert (Hrng : dstate_ranges rr).
  { unfold dstate_ranges in H |- *. unfold rr. cbn [d_trm d_tr d_pbm d_status d_po d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_block_start d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size set_d_ins_h set_d_match_available set_d_prev_length set_d_match_length set_d_insert set_d_lookahead set_d_block_start set_d_strstart set_d_max_chain_length set_d_nice_match set_d_good_match set_d_max_lazy_match set_d_slid set_d_head set_d_window_size].
    rewrite Hu, Hzr. unfold MIN_MATCH.
    unfold u32_ok, u64_ok, s32_ok, s64_ok in *. decompose [and] H.
    repeat (first [assumption | split]); try rep_lia.
    rewrite Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. }
  unfold dstate_at, deflate_globals, trees_at, lvl_at, win_at, hash_at, match_at, cfg_at.
  rewrite (prop_true_andp _ _ Hrng). rewrite Htrm, Hst.
  unfold rr. cbn [d_trm d_tr d_pbm d_status d_po d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_block_start d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size set_d_ins_h set_d_match_available set_d_prev_length set_d_match_length set_d_insert set_d_lookahead set_d_block_start set_d_strstart set_d_max_chain_length set_d_nice_match set_d_good_match set_d_max_lazy_match set_d_slid set_d_head set_d_window_size].
  rewrite Hu, Hzr.
  rewrite Int.unsigned_repr by rep_lia.
  replace (Vlong (Int64.mul (Int64.repr 2) (Int64.repr (d_w_size s)))) with (vl (2 * d_w_size s))
    by (unfold vl, Int64.mul; rewrite !Int64.unsigned_repr by rep_lia; reflexivity).
  change (Vint (Int.sub (Int.repr 3) (Int.repr 1))) with (vi 2).
  change (Vint (Int.repr 0)) with (vi 0). change (Vlong (Int64.repr 0)) with (vl 0).
  unfold MIN_MATCH. change (3 - 1) with 2.
  forget (gv code._static_bl_desc) as a1. forget (gv code._static_d_desc) as a2.
  forget (gv code._static_l_desc) as a3.
  entailer!.
Qed.
