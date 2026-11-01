(** * The bodies of trees.c's init_block, tr_static_init and _tr_init against TSpec.v *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.trees.CtModeS.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Lemma body_tr_static_init : semax_body Vprog Gprog_tr_static_init f_tr_static_init tr_static_init_spec.
Proof.
  start_function. forward. entailer!.
Qed.

(** ** The model of the zeroing loops *)
Lemma c_set_fc_inv t i v t' : c_set_fc t i v = Some t' ->
  0 <= i < Zlength (fc t) /\ t' = mkTree (upd_Znth i (fc t) v) (dl t).
Proof.
  unfold c_set_fc, wr, in_range, bind. intros H.
  destruct (andb (0 <=? i) (i <? Zlength (fc t))) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  inversion H. split; [lia | reflexivity].
Qed.

Lemma zero_fc_step f t n hi lt : n < hi -> c_zero_fc (S f) t n hi = Some lt ->
  0 <= n < Zlength (fc t) /\ c_zero_fc f (mkTree (upd_Znth n (fc t) 0) (dl t)) (n + 1) hi = Some lt.
Proof.
  intros Hn H. cbn [c_zero_fc] in H. rewrite (proj2 (Z.ltb_lt n hi) Hn) in H.
  inv_bind H. apply c_set_fc_inv in Ha. destruct Ha as [Hi ->]. auto.
Qed.

Lemma zero_fc_end t n hi lt : hi <= n -> c_zero_fc O t n hi = Some lt -> lt = t.
Proof.
  intros Hn H. cbn [c_zero_fc] in H. rewrite (proj2 (Z.ltb_ge n hi) Hn) in H. congruence.
Qed.

Lemma tree_ok_set_fc t n i v : tree_ok t n -> 0 <= v < 65536 -> tree_ok (mkTree (upd_Znth i (fc t) v) (dl t)) n.
Proof.
  intros [H1 [H2 H3]] Hv. split; [|split]; cbn [fc dl].
  - rewrite Zlength_upd_Znth; auto.
  - auto.
  - intros j Hj. destruct (H3 j Hj). split; auto.
    destruct (zlt i 0); [rewrite upd_Znth_out_of_range by lia; auto|].
    destruct (zlt i (Zlength (fc t))); [|rewrite upd_Znth_out_of_range by lia; auto].
    destruct (zeq j i) as [->|ne].
    + rewrite upd_Znth_same by lia. auto.
    + rewrite upd_Znth_diff by lia. auto.
Qed.

(** The canonical presentation after a store of [v] into entry [i]'s Freq. *)
Lemma ct_canon_set_fc t i v : 0 <= i < Zlength (fc t) -> Zlength (dl t) = Zlength (fc t) ->
  upd_Znth i (ct_canon t) (ctv_of false false v (Znth i (dl t))) = ct_canon (mkTree (upd_Znth i (fc t) v) (dl t)).
Proof.
  intros Hi Hl. unfold ct_canon. pose proof (ct_arr_set_fc ffalse ffalse t i false v Hi Hl) as E.
  change (ffalse i) with false in E. rewrite E.
  apply ct_arr_ext; cbn; auto. intros j. unfold fupd, ffalse. destruct (Z.eq_dec j i); auto.
Qed.

Lemma Znth_ct_canon_snd t i : 0 <= i < Zlength (fc t) ->
  snd (Znth i (ct_canon t)) = inl (vi (Znth i (dl t))).
Proof. intros. unfold ct_canon. rewrite Znth_ct_arr by auto. reflexivity. Qed.

Lemma to_nat_succ k i : i < k -> Z.to_nat (k - i) = S (Z.to_nat (k - (i + 1))).
Proof. intros. rewrite <- Z2Nat.inj_succ by lia. f_equal. lia. Qed.

(** One iteration of a zeroing loop: the model step and the new tree. *)
Ltac zero_step Hz Hok :=
  rewrite to_nat_succ in Hz by lia;
  let Hi := fresh "Hi" in
  apply zero_fc_step in Hz; [|lia]; destruct Hz as [Hi Hz];
  match type of Hz with c_zero_fc _ ?t' _ _ = _ =>
    Exists t';
    entailer!; [apply tree_ok_set_fc; auto; lia|];
    apply derives_refl'; f_equal;
    rewrite <- (ct_canon_set_fc _ _ 0 Hi ltac:(destruct Hok as [? [? ?]]; lia));
    f_equal; unfold ct_canon; rewrite Znth_ct_arr by lia; reflexivity
  end.

Ltac zero_step' :=
  match goal with Hz : c_zero_fc (Z.to_nat (_ - _)) ?tn _ _ = Some _, Hok : tree_ok ?tn _ |- _ =>
    zero_step Hz Hok end.

Lemma zero_fc_end' t k lt : c_zero_fc (Z.to_nat (k - k)) t k k = Some lt -> lt = t.
Proof. rewrite Z.sub_diag. apply zero_fc_end. lia. Qed.

Ltac zero_end :=
  match goal with H : c_zero_fc (Z.to_nat (?k - ?k)) ?tn ?k ?k = Some _ |- _ =>
    apply zero_fc_end' in H; subst tn end.

Lemma body_init_block : semax_body Vprog Gprog_init_block f_init_block init_block_spec.
Proof.
  start_function.
  unfold ltree_at, dtree_at, bltree_at. Intros.
  unfold c_init_block in H.
  inv_bind H. rename x into lt, Ha into Hlt.
  inv_bind H. rename x into dt, Ha into Hdt.
  inv_bind H. rename x into bt, Ha into Hbt.
  inv_bind H. rename x into lt2, Ha into Hlt2.
  injection H as <-.
  forward_for_simple_bound 286
    (EX i : Z, EX tn : tree,
      PROP (c_zero_fc (Z.to_nat (286 - i)) tn i 286 = Some lt; tree_ok tn HEAP_SIZE)
      LOCAL (temp _s sp)
      SEP (@field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon tn) sp;
           @field_at DCS.CS Ews t_ds (DOT _dyn_dtree) (ct_canon (tr_dtree ts)) sp;
           @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_canon (tr_bltree ts)) sp;
           work_at (tr_wk ts) sp; sym_at ts sp pbp)).
  { Exists (tr_ltree ts). entailer!. }
  { forward. zero_step'. }
  Intros tn. zero_end.
  cbn [tr_dtree tr_bltree tr_ltree set_ltree set_dtree set_bltree] in Hdt, Hbt, Hlt2.
  forward_for_simple_bound 30
    (EX i : Z, EX tn : tree,
      PROP (c_zero_fc (Z.to_nat (30 - i)) tn i 30 = Some dt; tree_ok tn (2 * D_CODES + 1))
      LOCAL (temp _s sp)
      SEP (@field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon lt) sp;
           @field_at DCS.CS Ews t_ds (DOT _dyn_dtree) (ct_canon tn) sp;
           @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_canon (tr_bltree ts)) sp;
           work_at (tr_wk ts) sp; sym_at ts sp pbp)).
  { Exists (tr_dtree ts). entailer!. }
  { forward. zero_step'. }
  Intros tn. zero_end.
  forward_for_simple_bound 19
    (EX i : Z, EX tn : tree,
      PROP (c_zero_fc (Z.to_nat (19 - i)) tn i 19 = Some bt; tree_ok tn (2 * BL_CODES + 1))
      LOCAL (temp _s sp)
      SEP (@field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon lt) sp;
           @field_at DCS.CS Ews t_ds (DOT _dyn_dtree) (ct_canon dt) sp;
           @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_canon tn) sp;
           work_at (tr_wk ts) sp; sym_at ts sp pbp)).
  { Exists (tr_bltree ts). entailer!. }
  { forward. zero_step'. }
  Intros tn. zero_end.
  forward.
  apply c_set_fc_inv in Hlt2. change END_BLOCK with 256 in Hlt2. destruct Hlt2 as [Hi ->].
  replace_SEP 0 (@field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon (mkTree (upd_Znth 256 (fc lt) 1) (dl lt))) sp).
  { entailer!. apply derives_refl'. f_equal.
    rewrite <- (ct_canon_set_fc _ _ 1 Hi ltac:(destruct H3 as [? [? ?]]; lia)).
    f_equal. unfold ct_canon. rewrite Znth_ct_arr by lia. reflexivity. }
  unfold work_at, sym_at. Intros.
  forward. forward. forward. forward. forward. forward.
  cbn [tr_ltree tr_dtree tr_bltree tr_wk tr_sym_next tr_sym_end tr_matches tr_lit_bufsize
       set_matches set_sym_next set_wk set_ltree set_dtree set_bltree w_set_static_len w_set_opt_len
       w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len].
  unfold ltree_at, dtree_at, bltree_at, work_at, sym_at.
  destruct H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
  entailer!.
  - split; [apply tree_ok_set_fc; auto; lia|].
    unfold work_ok.
    cbn [w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len tr_sym_next tr_matches
         w_set_static_len w_set_opt_len set_matches set_sym_next set_wk set_ltree set_dtree set_bltree].
    split; [|split; rep_lia]. do 8 (split; [assumption|]). split; rep_lia.
Qed.

Lemma c_init_block_fields s s' : c_init_block s = Some s' ->
  tr_lmax s' = tr_lmax s /\ tr_dmax s' = tr_dmax s /\ tr_blmax s' = tr_blmax s /\ tr_out s' = tr_out s /\
  tr_lit_bufsize s' = tr_lit_bufsize s.
Proof.
  unfold c_init_block. intros H.
  inv_bind H. inv_bind H. inv_bind H. inv_bind H. injection H as <-. cbn. auto.
Qed.

Lemma body_tr_init : semax_body Vprog Gprog_tr_init f__tr_init tr_init_spec.
Proof.
  start_function.
  destruct cs as [s m].
  unfold c_tr_init in H. inv_bind H. rename x into s', Ha into Hs'. injection H as <-.
  cbn [fst snd] in *.
  forward_call tt.
  unfold ldesc_at, ddesc_at, bldesc_at. Intros.
  forward. forward. forward. forward. forward. forward.
  destruct (tr_out s) as [buf p bb bv bu] eqn:Eo.
  unfold out_at. Intros. cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in *.
  forward. forward. forward.
  set (o := mkOut buf p 0 0 0) in *.
  pose proof (c_init_block_fields _ _ Hs') as (El & Ed & Ebl & Eout & Elb).
  cbn [tr_lmax tr_dmax tr_blmax tr_out tr_lit_bufsize set_out] in El, Ed, Ebl, Eout, Elb.
  sep_apply (out_at_fields buf p 0 0 0 m sp pbp (out_ok_set_bits _ _ _ _ _ _ 0 0 0 H2 ltac:(lia) ltac:(rep_lia) ltac:(rep_lia))).
  fold o.
  change (ltree_at (tr_ltree s) sp) with (ltree_at (tr_ltree (set_out s o)) sp).
  change (dtree_at (tr_dtree s) sp) with (dtree_at (tr_dtree (set_out s o)) sp).
  change (bltree_at (tr_bltree s) sp) with (bltree_at (tr_bltree (set_out s o)) sp).
  change (work_at (tr_wk s) sp) with (work_at (tr_wk (set_out s o)) sp).
  change (sym_at s sp pbp) with (sym_at (set_out s o) sp pbp).
  forward_call (sp, pbp, set_out s o, s').
  rewrite El, Ed, Ebl, Eout.
  unfold ldesc_at, ddesc_at, bldesc_at.
  entailer!.
  assert (field_compatible t_ds (DOT _dyn_ltree) sp)
    by (destruct H3 as [? [? [? [? [? ?]]]]]; repeat split; auto; cbv; repeat (first [left; reflexivity | right])).
  assert (field_compatible t_ds (DOT _dyn_dtree) sp)
    by (destruct H3 as [? [? [? [? [? ?]]]]]; repeat split; auto; cbv; repeat (first [left; reflexivity | right])).
  assert (field_compatible t_ds (DOT _bl_tree) sp)
    by (destruct H3 as [? [? [? [? [? ?]]]]]; repeat split; auto; cbv; repeat (first [left; reflexivity | right])).
  rewrite !field_address_offset by auto. simpl nested_field_offset. unfold td_val. cbn. cancel.
Qed.
