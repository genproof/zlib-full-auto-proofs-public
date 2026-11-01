(** * Shared lemmas for the bodies of deflate_fast, deflate_slow, deflate_rle, deflate_huff

    - loops: reading a [runs] of the model step by step ([runs_exit_eq], [runs_step_eq]);
    - the output space: [rest_after] along a call ([out_grow], [rest_after_trans]) and the models that only
      append to [z_out] (fill_window: nothing; flush_pending, FLUSH_BLOCK: appends);
    - folding the opened groups back into [dfull]. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.zutil.Libc Zlib.proof.zutil.Spec Zlib.proof.crc32.Spec.
Require Import Zlib.deflate.code.
Require Zlib.trees.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** Case on the first [if] of a hypothesis. *)
Ltac case_if H := match type of H with context [if ?b then _ else _] => destruct b eqn:? end.
Ltac case_if_as H E := match type of H with context [if ?b then _ else _] => destruct b eqn:E end.

(** ** Loops *)
Lemma runs_exit_eq {A B} (body : A -> option (A + B)) a r r' :
  runs body a r -> body a = Some (inr r') -> r = r'.
Proof. intros H E. inversion H; subst; congruence. Qed.

Lemma runs_step_eq {A B} (body : A -> option (A + B)) a a' r :
  runs body a r -> body a = Some (inl a') -> runs body a' r.
Proof. intros H E. inversion H; subst; congruence. Qed.

Lemma runs_some {A B} (body : A -> option (A + B)) a r : runs body a r -> exists o, body a = Some o.
Proof. intros H. inversion H; eauto. Qed.

(** ** The output space *)
Definition out_grow (z z' : strm) : Prop :=
  exists d, z_out z' = z_out z ++ d /\ z_avail_out z' = z_avail_out z - Zlength d.

Lemma out_grow_refl z : out_grow z z.
Proof. exists []. rewrite app_nil_r. split; auto. rewrite Zlength_nil. lia. Qed.

Lemma out_grow_same z z' : z_out z' = z_out z -> z_avail_out z' = z_avail_out z -> out_grow z z'.
Proof. intros E1 E2. exists []. rewrite app_nil_r, Zlength_nil. split; [auto | lia]. Qed.

Lemma out_grow_trans z1 z2 z3 : out_grow z1 z2 -> out_grow z2 z3 -> out_grow z1 z3.
Proof.
  intros [d1 [E1 F1]] [d2 [E2 F2]]. exists (d1 ++ d2). rewrite E2, E1, app_assoc, Zlength_app.
  split; [auto | lia].
Qed.

Lemma rest_after_refl z rest : Zlength rest = z_avail_out z -> rest_after z z rest = rest.
Proof. intros. unfold rest_after. rewrite Z.sub_diag, sublist_same; auto. Qed.

Lemma rest_after_trans z z' z2 rest :
  Zlength rest = z_avail_out z -> 0 <= z_avail_out z2 -> out_grow z z' -> out_grow z' z2 ->
  rest_after z' z2 (rest_after z z' rest) = rest_after z z2 rest.
Proof.
  intros Hr H2 [d1 [E1 F1]] [d2 [E2 F2]]. unfold rest_after.
  rewrite E2, E1, !Zlength_app.
  assert (0 <= Zlength d1) by apply Zlength_nonneg. assert (0 <= Zlength d2) by apply Zlength_nonneg.
  rewrite Zlength_sublist by lia.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma rest_after_same z z' rest : z_out z' = z_out z -> rest_after z z' rest = rest_after z z rest.
Proof. intros E. unfold rest_after. rewrite E. reflexivity. Qed.

(** ** Models that touch the output *)
Lemma c_read_buf_out s z n z' d : c_read_buf s z n = Some (z', d) ->
  z_out z' = z_out z /\ z_avail_out z' = z_avail_out z /\ z_total_out z' = z_total_out z.
Proof.
  unfold c_read_buf. intros H.
  case_if H; [inversion H; subst; auto|].
  inv_bind H. inversion H; subst. clear H.
  destruct (d_wrap s =? 1); [|destruct (d_wrap s =? 2)]; cbn; auto.
Qed.

Lemma fw_body_out a o : fw_body a = Some o ->
  match o with inl (_, z') | inr (_, z') =>
    z_out z' = z_out (snd a) /\ z_avail_out z' = z_avail_out (snd a) /\ z_total_out z' = z_total_out (snd a) end.
Proof.
  destruct a as [s z]. unfold fw_body. intros H.
  inv_bind H. destruct x as [s2 more].
  case_if H; [inversion H; subst; auto|].
  inv_bind H. destruct x as [z2 data]. apply c_read_buf_out in Ha0. destruct Ha0 as [E1 [E2 E3]].
  inv_bind H. inv_bind H.
  case_if H; inversion H; subst; cbn; auto.
Qed.

Lemma runs_fw_out a r : runs fw_body a r ->
  z_out (snd r) = z_out (snd a) /\ z_avail_out (snd r) = z_avail_out (snd a) /\ z_total_out (snd r) = z_total_out (snd a).
Proof.
  induction 1 as [a r H|a a' r H _ IH].
  - apply fw_body_out in H. destruct r; auto.
  - apply fw_body_out in H. destruct a' as [s' z']. cbn in *. destruct H as [? [? ?]], IH as [? [? ?]].
    split; [|split]; congruence.
Qed.

Lemma c_fill_window_out s z r : c_fill_window s z = Some r ->
  z_out (snd r) = z_out z /\ z_avail_out (snd r) = z_avail_out z /\ z_total_out (snd r) = z_total_out z.
Proof.
  unfold c_fill_window. intros H. inv_bind H. destruct x as [s2 z2].
  apply loop_runs in Ha. apply runs_fw_out in Ha.
  inv_bind H. inversion H; subst. auto.
Qed.

Lemma c_fill_window_grow s z r : c_fill_window s z = Some r -> out_grow z (snd r).
Proof. intros H. apply c_fill_window_out in H. destruct H as [? [? ?]]. apply out_grow_same; auto. Qed.

(** fill_window's call (v2: on [dfull_in]): frame the output side of [dfull], and fold it back. *)
Lemma dfull_split_in s z p pin pout ish rest msgv gv :
  dfull s z p pin pout ish rest msgv gv |--
  dfull_in s z p pin ish msgv gv * (strm_out_fields z (p_strm p) pout * out_space z pout rest).
Proof. unfold dfull, dfull_in. rewrite strm_at_split. Intros. entailer!. Qed.

Lemma dfull_join_in s z z' p pin pout ish rest msgv gv :
  z_out z' = z_out z -> z_avail_out z' = z_avail_out z -> z_total_out z' = z_total_out z ->
  dfull_in s z' p pin ish msgv gv * (strm_out_fields z (p_strm p) pout * out_space z pout rest) |--
  dfull s z' p pin pout ish rest msgv gv.
Proof.
  intros E1 E2 E3. unfold dfull, dfull_in, strm_out_fields, out_space. rewrite strm_at_split.
  unfold strm_out_fields. rewrite E1, E2, E3. Intros. entailer!.
Qed.

Lemma rest_after_out z z1 z2 rest : z_out z2 = z_out z1 -> rest_after z z2 rest = rest_after z z1 rest.
Proof. intros E. unfold rest_after. rewrite E. reflexivity. Qed.

Lemma mb_read_length b lo len l : mb_read b lo len = Some l -> Zlength l = len.
Proof.
  unfold mb_read, mb_definedb. intros H.
  case_if_as H E; [|discriminate]. inversion H; subst.
  repeat rewrite andb_true_iff in E. destruct E as [E1 [[E2 E3] E4]].
  apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.leb_le in E3.
  rewrite Zlength_sublist by lia. lia.
Qed.

Lemma c_flush_pending_grow s z r : c_flush_pending s z = Some r -> out_grow z (snd r).
Proof.
  unfold c_flush_pending. intros H. inv_bind H.
  case_if H; [inversion H; subst; apply out_grow_refl|].
  inv_bind H. inv_bind H. inversion H; subst; clear H. cbn.
  unfold out_put in Ha1. case_if Ha1; [|discriminate]. inversion Ha1; subst.
  apply mb_read_length in Ha0.
  exists x0. cbn. split; [auto | lia].
Qed.

Lemma c_flush_block_only_grow s z last r : c_flush_block_only s z last = Some r -> out_grow z (snd r).
Proof.
  unfold c_flush_block_only. intros H. inv_bind H. inv_bind H. inv_bind H. destruct x1 as [t k].
  eapply c_flush_pending_grow. exact H.
Qed.

Lemma c_flush_block_grow s z last r : c_flush_block s z last = Some r -> out_grow z (snd (fst r)).
Proof.
  unfold c_flush_block. intros H. inv_bind H. destruct x as [s2 z2].
  apply c_flush_block_only_grow in Ha.
  case_if H; inversion H; subst; exact Ha.
Qed.

(** ** Folding [dfull] *)
Lemma dfull_fold s z p pin pout ish rest msgv gv :
  strm_ranges z -> msg_ok (z_msg z) msgv -> readable_share ish -> dstate_ranges s ->
  trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * win_at s p * hash_at s p * match_at s p * cfg_at s p *
  stat_at s p * strm_at z (p_s p) (p_strm p) pin pout msgv gv * in_obj ish z pin * out_space z pout rest
  |-- dfull s z p pin pout ish rest msgv gv.
Proof. intros. unfold dfull, dstate_at. entailer!. Qed.

Lemma match_at_fold s p :
  @field_at DCS.CS Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p)
  |-- match_at s p.
Proof. unfold match_at. cancel. Qed.

(** ** Ranges *)

(** All the range facts of a [dstate_ranges] / [strm_ranges] hypothesis, as separate hypotheses. *)
Ltac open_dranges H :=
  let Hc := fresh "Hc" in pose proof H as Hc;
  unfold dstate_ranges, u32_ok, u64_ok, s32_ok, s64_ok in Hc; decompose [and] Hc; clear Hc.
Ltac open_zranges H :=
  let Hc := fresh "Hc" in pose proof H as Hc;
  unfold strm_ranges, u32_ok, u64_ok in Hc; decompose [and] Hc; clear Hc.

Lemma repr_eq_u32 a b : Int.repr a = Int.repr b -> 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned -> a = b.
Proof. intros E Ha Hb. apply repr_inj_unsigned in E; auto. Qed.

Lemma repr_neq_u32 a b : Int.repr a <> Int.repr b -> a <> b.
Proof. congruence. Qed.

(** A range goal closed from some [dstate_ranges] / [strm_ranges] hypothesis. *)
Ltac drange :=
  first [ rep_lia
        | match goal with H : dstate_ranges _ |- _ =>
            let Hc := fresh "Hc" in pose proof H as Hc;
            unfold dstate_ranges, u32_ok, u64_ok, s32_ok, s64_ok in Hc; decompose [and] Hc; rep_lia end
        | match goal with H : strm_ranges _ |- _ =>
            let Hc := fresh "Hc" in pose proof H as Hc;
            unfold strm_ranges, u32_ok, u64_ok in Hc; decompose [and] Hc; rep_lia end ].

(** [a = b] from a hypothesis [Int.repr a = Int.repr b] (unsigned ranges). *)
Ltac repr_eq :=
  match goal with H : Int.repr ?a = Int.repr ?b |- ?a = ?b => apply (repr_eq_u32 a b H); drange end.

(** ** Masked buffers in memory *)
Lemma mb_rd_vals b i c : mb_ok b -> mb_rd b i = Some c ->
  0 <= i < Zlength (mb_val b) /\ Znth i (mb_vals b) = vi c /\ 0 <= c < 256.
Proof.
  intros [Hl Hd] H. unfold mb_rd, in_range in H.
  case_if_as H E; [|discriminate]. inversion H; subst; clear H.
  rewrite !andb_true_iff in E. destruct E as [[E1 E2] E3].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  unfold mb_vals. rewrite Znth_pb_vals by lia. rewrite E3. split; [lia|]. split; auto.
Qed.

Lemma sublist_upd_shift {A} `{Inhabitant A} (V : list A) lb n j x :
  0 <= lb -> 0 <= j -> lb + j < n -> n <= Zlength V ->
  upd_Znth j (sublist lb n V) x = sublist lb n (upd_Znth (lb + j) V x).
Proof.
  intros. apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth, !Zlength_sublist; try rewrite Zlength_upd_Znth; lia.
  - intros k Hk. rewrite Zlength_upd_Znth, Zlength_sublist in Hk by lia.
    rewrite Znth_sublist by (try rewrite Zlength_upd_Znth; lia).
    destruct (Z.eq_dec k j) as [->|ne].
    + rewrite upd_Znth_same by (rewrite Zlength_sublist; lia).
      replace (j + lb) with (lb + j) by lia. rewrite upd_Znth_same by lia. reflexivity.
    + rewrite upd_Znth_diff by (try rewrite Zlength_sublist; lia).
      rewrite upd_Znth_diff by lia. rewrite Znth_sublist by lia. reflexivity.
Qed.

Lemma Zlength_mb_vals b : mb_ok b -> Zlength (mb_vals b) = Zlength (mb_val b).
Proof. intros [Hl _]. unfold mb_vals. apply Zlength_pb_vals. auto. Qed.

(** ** The tally macros *)
Definition put_sym_c (t : tstate) (m : list bool) (b : Z) : cstate :=
  let o := tr_out t in let i := tr_lit_bufsize t + tr_sym_next t in
  (set_sym_next (set_out t (mkOut (upd_Znth i (o_buf o) (u8 b)) (o_pending o) (o_bi_buf o) (o_bi_valid o)
                                  (o_bi_used o))) (tr_sym_next t + 1),
   upd_Znth i m true).

Lemma c_put_sym_inv cs b r : c_put_sym cs b = Some r ->
  0 <= tr_lit_bufsize (fst cs) + tr_sym_next (fst cs) < Zlength (o_buf (tr_out (fst cs))) /\
  r = put_sym_c (fst cs) (snd cs) b.
Proof.
  destruct cs as [t m]. unfold c_put_sym, wr, in_range, bind. cbn [fst snd]. intros H.
  case_if_as H E; [|discriminate]. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  inversion H. split; [lia | reflexivity].
Qed.

Definition incr_fc (t : tree) (i : Z) : tree := mkTree (upd_Znth i (fc t) (u16 (Znth i (fc t) + 1))) (dl t).

Lemma c_incr_lfreq_inv s i r : c_incr_lfreq s i = Some r ->
  0 <= i < Zlength (fc (tr_ltree s)) /\ r = set_ltree s (incr_fc (tr_ltree s) i).
Proof.
  unfold c_incr_lfreq, c_set_fc, rd, wr, in_range, bind. intros H.
  case_if_as H E; [|discriminate]. try rewrite E in H. inversion H; subst.
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. auto.
Qed.

Lemma c_incr_dfreq_inv s i r : c_incr_dfreq s i = Some r ->
  0 <= i < Zlength (fc (tr_dtree s)) /\ r = set_dtree s (incr_fc (tr_dtree s) i).
Proof.
  unfold c_incr_dfreq, c_set_fc, rd, wr, in_range, bind. intros H.
  case_if_as H E; [|discriminate]. try rewrite E in H. inversion H; subst.
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. auto.
Qed.

Lemma ct_canon_upd t i v : 0 <= i < Zlength (fc t) -> Zlength (dl t) = Zlength (fc t) ->
  upd_Znth i (ct_canon t) (ctv_of false false v (Znth i (dl t))) = ct_canon (mkTree (upd_Znth i (fc t) v) (dl t)).
Proof.
  intros Hi Hl. unfold ct_canon. apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth, !Zlength_ct_arr. cbn [fc]. rewrite Zlength_upd_Znth. auto.
  - intros k Hk. rewrite Zlength_upd_Znth, Zlength_ct_arr in Hk.
    rewrite (Znth_ct_arr _ _ (mkTree _ _)) by (cbn [fc]; rewrite Zlength_upd_Znth; lia). cbn [fc dl].
    destruct (Z.eq_dec k i) as [->|ne].
    + rewrite upd_Znth_same by (rewrite Zlength_ct_arr; lia). rewrite upd_Znth_same by lia. reflexivity.
    + rewrite upd_Znth_diff by (rewrite ?Zlength_ct_arr; lia). rewrite Znth_ct_arr by lia.
      rewrite upd_Znth_diff by lia. reflexivity.
Qed.

Lemma Znth_ct_canon t i : 0 <= i < Zlength (fc t) ->
  Znth i (ct_canon t) = (inl (vi (Znth i (fc t))), inl (vi (Znth i (dl t)))).
Proof. intros. unfold ct_canon. rewrite Znth_ct_arr by auto. reflexivity. Qed.

Lemma tree_ok_incr t n i : tree_ok t n -> tree_ok (incr_fc t i) n.
Proof.
  intros [H1 [H2 H3]]. split; [|split]; cbn [fc dl incr_fc].
  - rewrite Zlength_upd_Znth; auto.
  - auto.
  - intros j Hj. destruct (H3 j Hj). split; auto.
    destruct (zlt i 0); [rewrite upd_Znth_out_of_range by lia; auto|].
    destruct (zlt i (Zlength (fc t))); [|rewrite upd_Znth_out_of_range by lia; auto].
    destruct (zeq j i) as [->|ne].
    + rewrite upd_Znth_same by lia. unfold u16. apply Z.mod_pos_bound. lia.
    + rewrite upd_Znth_diff by lia. auto.
Qed.

(** ** pending_buf seen as two arrays: [0, lb) and the symbol buffer [lb, n) at sym_buf = pending_buf + lb *)
Lemma pb_split sh n lb (V : list val) pbp : 0 <= lb <= n -> Zlength V = n ->
  @data_at DCS.CS sh (tarray tuchar n) V pbp |--
  !! field_compatible (tarray tuchar n) nil pbp &&
  (@data_at DCS.CS sh (tarray tuchar lb) (sublist 0 lb V) pbp *
   @data_at DCS.CS sh (tarray tuchar (n - lb)) (sublist lb n V) (offset_val lb pbp))%logic.
Proof.
  intros Hl HV.
  assert_PROP (field_compatible (tarray tuchar n) nil pbp) as Hc by entailer!.
  apply andp_right; [apply prop_right; auto|].
  assert (field_compatible0 (tarray tuchar n) (ArraySubsc lb :: nil) pbp).
  { apply field_compatible0_cons. cbn. split; [lia|auto]. }
  rewrite (split2_data_at_Tarray_tuchar sh n lb) by auto.
  rewrite field_address0_offset by auto. cbn. rewrite Z.mul_1_l. cancel.
Qed.

Lemma pb_join sh n lb (V : list val) pbp : 0 <= lb <= n -> Zlength V = n ->
  field_compatible (tarray tuchar n) nil pbp ->
  @data_at DCS.CS sh (tarray tuchar lb) (sublist 0 lb V) pbp *
  @data_at DCS.CS sh (tarray tuchar (n - lb)) (sublist lb n V) (offset_val lb pbp)
  |-- @data_at DCS.CS sh (tarray tuchar n) V pbp.
Proof.
  intros Hl HV Hc.
  assert (field_compatible0 (tarray tuchar n) (ArraySubsc lb :: nil) pbp).
  { apply field_compatible0_cons. cbn. split; [lia|auto]. }
  rewrite (split2_data_at_Tarray_tuchar sh n lb) by auto.
  rewrite field_address0_offset by auto. cbn. rewrite Z.mul_1_l. cancel.
Qed.

Lemma sublist_lo_upd {A} `{Inhabitant A} (V : list A) lb k x :
  lb <= k -> sublist 0 lb (upd_Znth k V x) = sublist 0 lb V.
Proof.
  intros. destruct (zlt k 0); [rewrite upd_Znth_out_of_range by lia; auto|].
  destruct (zlt k (Zlength V)); [|rewrite upd_Znth_out_of_range by lia; auto].
  destruct (zlt lb 0).
  - rewrite !sublist_nil_gen by lia. auto.
  - rewrite upd_Znth_unfold by lia.
    destruct (zle lb (Zlength V)).
    + rewrite sublist_app1 by (rewrite ?Zlength_sublist; lia).
      rewrite sublist_sublist by lia. f_equal; lia.
    + lia.
Qed.

(** A store of a byte into the symbol buffer, folded into the masked pending_buf. *)
Lemma pb_store_hi lb n b m j v :
  0 <= lb -> 0 <= j -> lb + j < n -> Zlength b = n -> Zlength m = n ->
  upd_Znth j (sublist lb n (pb_vals b m)) (Vint (Int.repr (u8 v))) =
  sublist lb n (pb_vals (upd_Znth (lb + j) b (u8 v)) (upd_Znth (lb + j) m true)) /\
  sublist 0 lb (pb_vals b m) = sublist 0 lb (pb_vals (upd_Znth (lb + j) b (u8 v)) (upd_Znth (lb + j) m true)).
Proof.
  intros. rewrite pb_vals_upd by lia. split.
  - rewrite sublist_upd_shift; auto. rewrite Zlength_pb_vals; lia.
  - rewrite sublist_lo_upd by lia. auto.
Qed.

(** ** trees_at, opened at the groups the tally macros touch.  The rest stays folded: it mentions trees.c's
    static descriptors, which are not in deflate.c's type context (go_lower refuses them). *)
Definition trees_rest (t : tstate) (sp strmp : val) (gv : globals) : mpred :=
  (bltree_at (tr_bltree t) sp *
   ldesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) sp) (tr_lmax t) (gv Zlib.trees.code._static_l_desc) sp *
   ddesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) sp) (tr_dmax t) (gv Zlib.trees.code._static_d_desc) sp *
   bldesc_at (field_address t_ds (DOT Zlib.trees.code._bl_tree) sp) (tr_blmax t) (gv Zlib.trees.code._static_bl_desc) sp *
   work_at (tr_wk t) sp * lvl_at t sp)%logic.

Lemma trees_at_open cs sp pbp strmp gv :
  trees_at cs sp pbp strmp gv =
  (ltree_at (tr_ltree (fst cs)) sp * dtree_at (tr_dtree (fst cs)) sp * out_at (tr_out (fst cs)) (snd cs) sp pbp *
   sym_at (fst cs) sp pbp * dtype_at (fst cs) sp strmp * trees_rest (fst cs) sp strmp gv)%logic.
Proof. unfold trees_at, trees_rest. apply pred_ext; cancel. Qed.

(** ** strm_at, opened without its zalloc / zfree fields (zutil.c's globals, not in deflate.c's type context) *)
Definition ck_strm_zfuncs (strmp : val) (gv : globals) : mpred :=
  (@field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) strmp *
   @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) strmp)%logic.

Lemma ck_strm_at_open z sp strmp pin pout msgv gv :
  strm_at z sp strmp pin pout msgv gv =
  (@field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) pout) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_out) (vl (z_total_out z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _msg) msgv strmp *
   @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
   ck_strm_zfuncs strmp gv *
   @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp *
   @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) strmp *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp)%logic.
Proof. unfold strm_at, ck_strm_zfuncs. apply pred_ext; cancel. Qed.

(** ** Unsigned arithmetic *)
Lemma repr_u32 x : Int.repr (u32 x) = Int.repr x.
Proof.
  unfold u32. apply Int.eqm_samerepr. apply Int.eqm_sym. unfold Int.eqm.
  apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma repr_u64 x : Int64.repr (u64 x) = Int64.repr x.
Proof.
  unfold u64. apply Int64.eqm_samerepr. apply Int64.eqm_sym. unfold Int64.eqm.
  apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma u32_range x : 0 <= u32 x <= Int.max_unsigned.
Proof. unfold u32. pose proof (Z.mod_pos_bound x 4294967296). rep_lia. Qed.

Lemma u64_range x : 0 <= u64 x <= Int64.max_unsigned.
Proof. unfold u64. pose proof (Z.mod_pos_bound x 18446744073709551616). rep_lia. Qed.

Lemma unsigned_repr_u32 x : Int.unsigned (Int.repr (u32 x)) = u32 x.
Proof. apply Int.unsigned_repr. apply u32_range. Qed.

Lemma u32_small x : 0 <= x <= Int.max_unsigned -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. rep_lia. Qed.

Lemma u64_small x : 0 <= x <= Int64.max_unsigned -> u64 x = x.
Proof. intros. unfold u64. apply Z.mod_small. rep_lia. Qed.

(** ** A defined slice of the window, for _tr_flush_block's [buf] *)
Lemma mb_read_inv b lo len l : mb_read b lo len = Some l ->
  0 <= len /\ 0 <= lo /\ lo + len <= Zlength (mb_val b) /\ l = sublist lo (lo + len) (mb_val b) /\
  forall i, lo <= i < lo + len -> Znth i (mb_def b) = true.
Proof.
  unfold mb_read, mb_definedb. intros H.
  case_if_as H E; [|discriminate]. inversion H; subst; clear H.
  repeat rewrite andb_true_iff in E. destruct E as [E1 [[E2 E3] E4]].
  apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.leb_le in E3.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [auto|].
  intros i Hi. rewrite forallb_forall in E4. apply E4.
  apply in_map_iff. exists (Z.to_nat (i - lo)). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma mb_vals_slice b lo len l : mb_ok b -> mb_read b lo len = Some l ->
  sublist lo (lo + len) (mb_vals b) = map vi l.
Proof.
  intros Hok H. pose proof (Zlength_mb_vals _ Hok) as Hv.
  destruct (mb_read_inv _ _ _ _ H) as (H1 & H2 & H3 & -> & H5).
  destruct Hok as [Hl _]. apply Znth_eq_ext.
  - rewrite Zlength_map, !Zlength_sublist; lia.
  - intros i Hi. rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_sublist by lia. rewrite Znth_map by (rewrite Zlength_sublist; lia).
    rewrite Znth_sublist by lia. unfold mb_vals. rewrite Znth_pb_vals by lia.
    rewrite H5 by lia. reflexivity.
Qed.

Lemma win_slice_open sh w wp lo len l : mb_ok w -> mb_read w lo len = Some l ->
  @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val w))) (mb_vals w) wp |--
  !! field_compatible (tarray tuchar (Zlength (mb_val w))) nil wp &&
  (@data_at DCS.CS sh (tarray tuchar lo) (sublist 0 lo (mb_vals w)) wp *
   @data_at DCS.CS sh (tarray tuchar (Zlength l)) (map vi l) (offset_val lo wp) *
   @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val w) - (lo + len)))
     (sublist (lo + len) (Zlength (mb_val w)) (mb_vals w)) (offset_val (lo + len) wp))%logic.
Proof.
  intros Hok H. pose proof (mb_vals_slice _ _ _ _ Hok H) as Es.
  destruct (mb_read_inv _ _ _ _ H) as (H1 & H2 & H3 & El & _).
  assert (Hlen : Zlength l = len) by (rewrite El, Zlength_sublist; lia).
  pose proof (Zlength_mb_vals _ Hok) as Hv.
  assert_PROP (field_compatible (tarray tuchar (Zlength (mb_val w))) nil wp) as Hc by entailer!.
  apply andp_right; [apply prop_right; auto|].
  rewrite (split3_data_at_Tarray_tuchar sh (Zlength (mb_val w)) lo (lo + len)) by lia.
  rewrite !field_address0_offset.
  2, 3: apply field_compatible0_cons; cbn; split; [lia|auto].
  cbn. rewrite !Z.mul_1_l. rewrite Es. replace (lo + len - lo) with (Zlength l) by lia. cancel.
Qed.

Lemma win_slice_close sh w wp lo len l : mb_ok w -> mb_read w lo len = Some l ->
  field_compatible (tarray tuchar (Zlength (mb_val w))) nil wp ->
  @data_at DCS.CS sh (tarray tuchar lo) (sublist 0 lo (mb_vals w)) wp *
  @data_at DCS.CS sh (tarray tuchar (Zlength l)) (map vi l) (offset_val lo wp) *
  @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val w) - (lo + len)))
    (sublist (lo + len) (Zlength (mb_val w)) (mb_vals w)) (offset_val (lo + len) wp)
  |-- @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val w))) (mb_vals w) wp.
Proof.
  intros Hok H Hc. pose proof (mb_vals_slice _ _ _ _ Hok H) as Es.
  destruct (mb_read_inv _ _ _ _ H) as (H1 & H2 & H3 & El & _).
  assert (Hlen : Zlength l = len) by (rewrite El, Zlength_sublist; lia).
  pose proof (Zlength_mb_vals _ Hok) as Hv.
  rewrite (split3_data_at_Tarray_tuchar sh (Zlength (mb_val w)) lo (lo + len)) by lia.
  rewrite !field_address0_offset.
  2, 3: apply field_compatible0_cons; cbn; split; [lia|auto].
  cbn. rewrite !Z.mul_1_l. rewrite Es. replace (lo + len - lo) with (Zlength l) by lia. cancel.
Qed.

(** ** Simplification of the projections of updated states *)
Tactic Notation "dsimpl" :=
  cbn [set_d_status set_d_po set_d_wrap set_d_gzhead set_d_gzindex set_d_method set_d_last_flush set_d_w_size
       set_d_w_bits set_d_w_mask set_d_window set_d_window_size set_d_prev set_d_head set_d_ins_h set_d_hash_size
       set_d_hash_bits set_d_hash_mask set_d_hash_shift set_d_block_start set_d_match_length set_d_prev_match
       set_d_match_available set_d_strstart set_d_match_start set_d_lookahead set_d_prev_length
       set_d_max_chain_length set_d_max_lazy_match set_d_good_match set_d_nice_match set_d_insert set_d_high_water
       set_d_slid set_d_pending_buf_size set_d_tr set_d_pbm d_trm set_d_trm set_d_out d_out d_level d_strategy d_pending
       d_status d_po d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window
       d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_block_start
       d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length
       d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid
       d_pending_buf_size d_tr d_pbm
       o_buf o_pending o_bi_buf o_bi_valid o_bi_used tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk
       tr_out tr_sym_next tr_sym_end tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type
       set_ltree set_dtree set_bltree set_lmax set_dmax set_blmax set_wk set_out set_sym_next set_matches
       set_data_type fst snd fc dl incr_fc put_sym_c].
Tactic Notation "dsimpl" "in" hyp(H) :=
  cbn [set_d_status set_d_po set_d_wrap set_d_gzhead set_d_gzindex set_d_method set_d_last_flush set_d_w_size
       set_d_w_bits set_d_w_mask set_d_window set_d_window_size set_d_prev set_d_head set_d_ins_h set_d_hash_size
       set_d_hash_bits set_d_hash_mask set_d_hash_shift set_d_block_start set_d_match_length set_d_prev_match
       set_d_match_available set_d_strstart set_d_match_start set_d_lookahead set_d_prev_length
       set_d_max_chain_length set_d_max_lazy_match set_d_good_match set_d_nice_match set_d_insert set_d_high_water
       set_d_slid set_d_pending_buf_size set_d_tr set_d_pbm d_trm set_d_trm set_d_out d_out d_level d_strategy d_pending
       d_status d_po d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask d_window
       d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_block_start
       d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length
       d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid
       d_pending_buf_size d_tr d_pbm
       o_buf o_pending o_bi_buf o_bi_valid o_bi_used tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk
       tr_out tr_sym_next tr_sym_end tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type
       set_ltree set_dtree set_bltree set_lmax set_dmax set_blmax set_wk set_out set_sym_next set_matches
       set_data_type fst snd fc dl incr_fc put_sym_c] in H.

Lemma trees_rest_ext t t' sp strmp gv :
  tr_bltree t' = tr_bltree t -> tr_lmax t' = tr_lmax t -> tr_dmax t' = tr_dmax t -> tr_blmax t' = tr_blmax t ->
  tr_wk t' = tr_wk t -> tr_level t' = tr_level t -> tr_strategy t' = tr_strategy t ->
  trees_rest t' sp strmp gv = trees_rest t sp strmp gv.
Proof.
  intros E1 E2 E3 E4 E5 E6 E7. unfold trees_rest, lvl_at.
  rewrite E1, E2, E3, E4, E5, E6, E7. reflexivity.
Qed.

Lemma u8_u8 x : u8 (u8 x) = u8 x.
Proof. unfold u8. apply Zmod_mod. Qed.

Lemma ct_canon_incr t i : 0 <= i < Zlength (fc t) -> Zlength (dl t) = Zlength (fc t) ->
  upd_Znth i (ct_canon t)
    (inl (Vint (Int.zero_ext 16 (Int.add (Int.repr (Znth i (fc t))) (Int.repr 1)))),
     snd (Znth i (ct_canon t))) = ct_canon (incr_fc t i).
Proof.
  intros. rewrite Znth_ct_canon by auto. cbn [snd]. unfold incr_fc. rewrite <- ct_canon_upd by auto.
  f_equal. rewrite add_repr32, zext16_repr. reflexivity.
Qed.

(** After a C store into the symbol buffer (the upper part of pending_buf, see [pb_split]): the contents as the
    masked pending_buf of the model's [put_sym]. *)
Ltac sym_store_fold :=
  rewrite ?add_repr32;
  rewrite ?Int.zero_ext_idem by lia; rewrite ?byte_zext8;
  match goal with |- context [upd_Znth ?j (sublist ?lb ?n (pb_vals ?b ?m)) (Vint (Int.repr (u8 ?v)))] =>
    let E1 := fresh "E" in let E2 := fresh "E" in
    destruct (pb_store_hi lb n b m j v ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_upd_Znth in *; lia)
                ltac:(rewrite ?Zlength_upd_Znth; lia) ltac:(rewrite ?Zlength_upd_Znth; lia)) as [E1 E2];
    rewrite E1, E2; clear E1 E2
  end.

(** ** flush_pending changes only pending_out and the trees.c output part *)
Lemma set_d_out_out s o1 o2 : set_d_out (set_d_out s o1) o2 = set_d_out s o2.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]. destruct t. reflexivity. Qed.

Lemma set_d_out_po s o x : set_d_out (set_d_po s x) o = set_d_po (set_d_out s o) x.
Proof. reflexivity. Qed.

Lemma set_d_po_po s x y : set_d_po (set_d_po s x) y = set_d_po s y.
Proof. reflexivity. Qed.

Lemma c_flush_pending_shape s z r : c_flush_pending s z = Some r -> 0 <= d_po s -> 0 <= z_avail_out z ->
  exists o po, fst r = set_d_po (set_d_out s o) po /\ 0 <= po.
Proof.
  unfold c_flush_pending. intros H Hpo Hav. inv_bind H.
  match type of H with context [if (?l =? 0) then _ else _] => destruct (l =? 0) eqn:E0 end.
  { inversion H; subst; cbn. exists x, (d_po s). split; [destruct s; reflexivity | auto]. }
  inv_bind H. inv_bind H. inversion H; subst; clear H. cbn [fst].
  match goal with |- context [if ?b then _ else _] => destruct b end; eexists; eexists.
  - rewrite set_d_out_po, set_d_out_out. rewrite set_d_po_po. split; [reflexivity|lia].
  - rewrite set_d_out_po, set_d_out_out. split; [reflexivity|].
    cbn. match goal with |- context [if ?b then _ else _] => destruct b end; [lia|].
    pose proof (u32_range (d_pending (set_d_out s x))). lia.
Qed.


Lemma out_ok_upd buf p bb bv bu m i v : out_ok (mkOut buf p bb bv bu) m -> 0 <= i < Zlength buf ->
  out_ok (mkOut (upd_Znth i buf (u8 v)) p bb bv bu) (upd_Znth i m true).
Proof.
  intros [[Hm Hd] [Hb Hr]] Hi. cbn in *.
  split; [split|]; cbn.
  - rewrite !Zlength_upd_Znth. auto.
  - intros j Hj Hdj. rewrite Zlength_upd_Znth in Hj.
    destruct (Z.eq_dec j i) as [->|ne].
    + rewrite upd_Znth_same by lia. apply u8_range.
    + rewrite upd_Znth_diff in Hdj by lia. rewrite upd_Znth_diff by lia. auto.
  - rewrite Zlength_upd_Znth. auto.
Qed.

(** The ranges of a state whose fields were updated with values of the right C types. *)
Ltac dranges_tac H :=
  unfold dstate_ranges, u32_ok, u64_ok, s32_ok, s64_ok in *; dsimpl; decompose [and] H;
  repeat match goal with |- _ /\ _ => split end;
  try assumption; try apply u32_range; try apply u64_range; try rep_lia;
  try (match goal with |- context [u32 ?x] => pose proof (u32_range x) end; rep_lia).

(** ** FLUSH_BLOCK_ONLY *)
Lemma in_long_inv x : in_long x = true -> Int64.min_signed <= x <= Int64.max_signed.
Proof. unfold in_long. intros H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1, H2. rep_lia. Qed.

Lemma c_flush_block_only_inv s z last r : c_flush_block_only s z last = Some r ->
  exists bo t k,
    Int64.min_signed <= d_strstart s - d_block_start s <= Int64.max_signed /\
    (0 <= d_block_start s -> exists b, bo = Some b /\
       mb_read (d_window s) (d_block_start s) (u64 (d_strstart s - d_block_start s)) = Some b) /\
    (d_block_start s < 0 -> bo = None) /\
    c_tr_flush_block (d_trm s) bo (u64 (d_strstart s - d_block_start s)) last = Some (t, k) /\
    c_flush_pending (set_d_block_start (set_d_trm s t) (d_strstart s)) z = Some r.
Proof.
  unfold c_flush_block_only. intros H.
  inv_bind H. destruct x. apply guard_inv, in_long_inv in Ha.
  inv_bind H. rename x into bo. inv_bind H. destruct x as [t k].
  exists bo, t, k. split; [auto|]. split; [|split; [|split; auto]].
  - intros Hb. rewrite (proj2 (Z.geb_le _ _) Hb) in Ha0. inv_bind Ha0. inversion Ha0; subst. eauto.
  - intros Hb. destruct (d_block_start s >=? 0) eqn:E; [apply Z.geb_le in E; lia|]. inversion Ha0; auto.
Qed.

Lemma opt_buf_some sh b q : readable_share sh -> Forall (fun x => 0 <= x < 256) b ->
  @data_at DCS.CS sh (tarray tuchar (Zlength b)) (map vi b) q |-- opt_buf_at sh (Some b) q.
Proof. intros. unfold opt_buf_at. entailer!. Qed.

Lemma opt_buf_some_inv sh b q : opt_buf_at sh (Some b) q |-- @data_at DCS.CS sh (tarray tuchar (Zlength b)) (map vi b) q.
Proof. unfold opt_buf_at. entailer!. Qed.

Lemma opt_buf_none sh : emp |-- opt_buf_at sh None nullval.
Proof. unfold opt_buf_at. entailer!. Qed.

(** deflate_globals with trees.c's tables apart (for the call of _tr_flush_block). *)
Definition dglobals_rest (gv : globals) : mpred :=
  (errmsg_at gv * @data_at DCS.CS Ers (tarray t_config 10) (config_vals gv) (gv _configuration_table) *
   @data_at DCS.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0]) (gv _my_version) *
   crc_table_at Ers gv)%logic.

Lemma deflate_globals_open gv : deflate_globals gv = (trees_globals gv * dglobals_rest gv)%logic.
Proof. unfold deflate_globals, dglobals_rest. apply pred_ext; cancel. Qed.

(** ** Closing an opened stream back into [dfull]

    [trees_rest] in a normal form that depends only on the fields it shows (so that states that differ in other
    fields give syntactically equal terms after [dsimpl]). *)
Definition trees_rest' (bl : tree) (lmax dmax blmax : Z) (w : work) (lvl strat : Z) (sp : val) (gv : globals)
    : mpred :=
  (bltree_at bl sp *
   ldesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) sp) lmax (gv Zlib.trees.code._static_l_desc) sp *
   ddesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) sp) dmax (gv Zlib.trees.code._static_d_desc) sp *
   bldesc_at (field_address t_ds (DOT Zlib.trees.code._bl_tree) sp) blmax (gv Zlib.trees.code._static_bl_desc) sp *
   work_at w sp *
   (!! (Int.min_signed <= lvl <= Int.max_signed /\ Int.min_signed <= strat <= Int.max_signed) &&
    (@field_at DCS.CS Ews t_ds (DOT _level) (vi lvl) sp * @field_at DCS.CS Ews t_ds (DOT _strategy) (vi strat) sp)))%logic.

Lemma trees_rest_norm t sp strmp gv :
  trees_rest t sp strmp gv =
  trees_rest' (tr_bltree t) (tr_lmax t) (tr_dmax t) (tr_blmax t) (tr_wk t) (tr_level t) (tr_strategy t) sp gv.
Proof. reflexivity. Qed.

(** The entailment [opened pieces |-- dfull S Z ... * deflate_globals gv] (after [apply semax_pre]):
    unfold every group on both sides, normalise and cancel; leaves the pure side conditions entailer! cannot
    prove. *)
Ltac dfull_close_entail :=
  unfold dfull, dstate_at, in_obj;
  repeat rewrite trees_at_open; repeat rewrite ck_strm_at_open; repeat rewrite deflate_globals_open;
  repeat rewrite trees_rest_norm;
  unfold ltree_at, out_at, sym_at, dtype_at, match_at, win_at, hash_at, cfg_at, stat_at;
  dsimpl;
  rewrite ?sub_repr32, ?add_repr32, ?sub64_repr, ?add64_repr; unfold vi, vl;
  rewrite ?unsigned_repr_u32, ?repr_u32, ?repr_u64;
  entailer!.

(** Replace the precondition's SEP by [dfull S Z ...; deflate_globals gv] (keeping PROP and LOCAL). *)
Ltac pre_dfull S Z p pin pout ish R M gv :=
  match goal with |- semax ?D (PROPx ?P (LOCALx ?L _)) ?c ?Post =>
    apply semax_pre with (PROPx P (LOCALx L (SEPx [dfull S Z p pin pout ish R M gv; deflate_globals gv]))) end.

(** ** What flush_pending keeps, and the ranges of the stream after it *)

Lemma c_flush_pending_z s z r : c_flush_pending s z = Some r ->
  z_in (snd r) = z_in z /\ z_next_in (snd r) = z_next_in z /\ z_avail_in (snd r) = z_avail_in z /\
  z_total_in (snd r) = z_total_in z /\ z_adler (snd r) = z_adler z /\ z_msg (snd r) = z_msg z.
Proof.
  unfold c_flush_pending. intros H. inv_bind H.
  match type of H with context [if (?l =? 0) then _ else _] => destruct (l =? 0) eqn:E0 end.
  { inversion H; subst; cbn; repeat split. }
  inv_bind H. inv_bind H. inversion H; subst; clear H. cbn.
  unfold out_put in Ha1. case_if Ha1; [|discriminate]. inversion Ha1; subst. cbn. repeat split.
Qed.

Lemma mb_read_bytes b lo len l : mb_ok b -> mb_read b lo len = Some l -> Forall (fun x => 0 <= x < 256) l.
Proof.
  intros [Hl Hd] H. destruct (mb_read_inv _ _ _ _ H) as (H1 & H2 & H3 & -> & H5).
  apply Forall_forall. intros x Hx. apply In_Znth in Hx. destruct Hx as (i & Hi & <-).
  rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia.
  apply Hd; [lia|]. apply H5. lia.
Qed.

Lemma c_flush_pending_ranges s z r : c_flush_pending s z = Some r -> strm_ranges z ->
  mb_ok (mkMB (o_buf (tr_out (d_tr (fst r)))) (d_pbm (fst r))) -> strm_ranges (snd r).
Proof.
  unfold c_flush_pending. intros H Hz Hok. inv_bind H.
  match type of H with context [if (?l =? 0) then _ else _] => destruct (l =? 0) end;
    [inversion H; subst; cbn; auto|].
  inv_bind H. inv_bind H. inversion H; subst; clear H. cbn in Hok |- *.
  rename x into o, x0 into bytes, x1 into z'.
  unfold out_put in Ha1. case_if_as Ha1 E; [|discriminate]. inversion Ha1; subst; clear Ha1.
  apply Z.leb_le in E. pose proof (mb_read_length _ _ _ _ Ha0) as Hlen.
  match type of Hok with mb_ok ?b' => assert (Hb : Forall (fun x => 0 <= x < 256) bytes) end.
  { eapply mb_read_bytes; [|exact Ha0].
    match type of Hok with context [if ?c then _ else _] => destruct c end; exact Hok. }
  unfold strm_ranges, u32_ok, u64_ok in *. cbn in *.
  rewrite Zlength_app.
  destruct Hz as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
  pose proof (Zlength_nonneg bytes).
  repeat split; try assumption; try lia; try apply u64_range.
  apply Forall_app; auto.
Qed.
