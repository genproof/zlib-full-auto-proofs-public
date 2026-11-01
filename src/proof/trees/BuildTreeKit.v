(** * Helpers for the body of build_tree (Body_build_tree.v): the static descriptor out of [trees_globals],
    inversion of the model run [c_build_tree], ranges of the work area and of trees after one store. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.trees.CtMode.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The static descriptor *)

Definition sd_stp (gv : globals) (sd : stat_desc) : val :=
  match sd_stree sd with
  | Some _ => if sd_elems sd =? L_CODES then gv _static_ltree else gv _static_dtree
  | None => nullval
  end.

Definition sd_rep (gv : globals) (sd : stat_desc) (ep : val) : reptype t_sd :=
  (sd_stp gv sd, (ep, (vi (sd_base sd), (vi (sd_elems sd), vi (sd_maxlen sd))))).

Lemma sdesc_facts gv sd statp : sdesc_ptr gv sd statp ->
  (sd_elems sd = L_CODES \/ sd_elems sd = D_CODES \/ sd_elems sd = BL_CODES) /\
  (sd_stree sd = None -> sd_stp gv sd = nullval).
Proof.
  intros [[-> ->]|[[-> ->]|[-> ->]]]; cbn; split; auto; try discriminate.
Qed.

Lemma wand_out (A D R : mpred) : (A |-- D * R) -> (D * R |-- A) -> A |-- D * (D -* A).
Proof.
  intros H1 H2. eapply derives_trans; [exact H1|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. exact H2.
Qed.

(** [A |-- D * ?R]: bring [D] to the front of [A] and take the rest. *)
Ltac pull_out :=
  match goal with |- ?A |-- ?D * ?R =>
    let G := fresh "G" in set (G := (D * R)%logic); rewrite <- ?sepcon_assoc; pull_left D; rewrite ?sepcon_assoc; subst G;
    apply derives_refl
  end.

Lemma tg_sdesc gv sd statp : sdesc_ptr gv sd statp ->
  trees_globals gv |-- EX ep : val,
    @data_at DCS.CS Ers t_sd (sd_rep gv sd ep) statp *
    (@data_at DCS.CS Ers t_sd (sd_rep gv sd ep) statp -* trees_globals gv).
Proof.
  intros [[-> ->]|[[-> ->]|[-> ->]]].
  - Exists (gv _extra_lbits).
    change (sd_rep gv static_l_desc (gv _extra_lbits)) with
      (gv _static_ltree, (gv _extra_lbits, (vi 257, (vi 286, vi 15)))).
    eapply wand_out; unfold trees_globals, trees_tables; [pull_out | cancel].
  - Exists (gv _extra_dbits).
    change (sd_rep gv static_d_desc (gv _extra_dbits)) with
      (gv _static_dtree, (gv _extra_dbits, (vi 0, (vi 30, vi 15)))).
    eapply wand_out; unfold trees_globals, trees_tables; [pull_out | cancel].
  - Exists (gv _extra_blbits).
    change (sd_rep gv static_bl_desc (gv _extra_blbits)) with
      (nullval, (gv _extra_blbits, (vi 0, (vi 19, vi 7)))).
    eapply wand_out; unfold trees_globals, trees_tables; [pull_out | cancel].
Qed.

Lemma tg_stp gv sd statp : sdesc_ptr gv sd statp ->
  trees_globals gv |-- !! is_pointer_or_null (sd_stp gv sd).
Proof.
  intros [[-> ->]|[[-> ->]|[-> ->]]].
  - change (sd_stp gv static_l_desc) with (gv _static_ltree).
    unfold trees_globals, static_trees, tree_arr. entailer!.
  - change (sd_stp gv static_d_desc) with (gv _static_dtree).
    unfold trees_globals, static_trees, tree_arr. entailer!.
  - change (sd_stp gv static_bl_desc) with nullval. apply prop_right. cbn; auto.
Qed.

Lemma tg_stp' gv sd statp : sdesc_ptr gv sd statp ->
  trees_globals gv |-- !! is_pointer_or_null (sd_stp gv sd) && trees_globals gv.
Proof. intros. apply andp_right; [apply (tg_stp gv sd statp H) | apply derives_refl]. Qed.

Lemma tg_stp2 gv sd statp : sdesc_ptr gv sd statp ->
  trees_globals gv |-- !! (match sd_stree sd with Some _ => isptr (sd_stp gv sd)
                          | None => sd_stp gv sd = nullval end) && trees_globals gv.
Proof.
  intros Hs. apply andp_right; [|apply derives_refl].
  destruct Hs as [[-> ->]|[[-> ->]|[-> ->]]].
  - change (sd_stp gv static_l_desc) with (gv _static_ltree). cbn [sd_stree static_l_desc].
    unfold trees_globals, static_trees, tree_arr. entailer!.
  - change (sd_stp gv static_d_desc) with (gv _static_dtree). cbn [sd_stree static_d_desc].
    unfold trees_globals, static_trees, tree_arr. entailer!.
  - apply prop_right. reflexivity.
Qed.

(** The test [if (stree)] is defined: the static tree pointer is valid or null. *)
Lemma tg_test_eq gv sd statp Q : sdesc_ptr gv sd statp ->
  trees_globals gv * Q |-- denote_tc_test_eq (sd_stp gv sd) (Vlong Int64.zero).
Proof.
  intros Hs. apply denote_tc_test_eq_split; [|apply valid_pointer_null].
  apply sepcon_valid_pointer1.
  destruct Hs as [[-> ->]|[[-> ->]|[-> ->]]].
  - change (sd_stp gv static_l_desc) with (gv _static_ltree).
    unfold trees_globals, static_trees, tree_arr. Intros.
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
    apply data_at_valid_ptr; [apply readable_nonidentity; auto | reflexivity].
  - change (sd_stp gv static_d_desc) with (gv _static_dtree).
    unfold trees_globals, static_trees, tree_arr. Intros.
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
    apply data_at_valid_ptr; [apply readable_nonidentity; auto | reflexivity].
  - apply valid_pointer_null.
Qed.

(** The static tree of a descriptor that has one, presented with its lengths (member Len). *)
Lemma tg_stree gv sd statp l : sdesc_ptr gv sd statp -> sd_stree sd = Some l ->
  trees_globals gv |-- EX st : tree, EX k : Z, !! (dl st = l /\ tree_ok st k) &&
    (@data_at DCS.CS Ers (tarray t_ct k) (ct_arr ffalse ftrue st) (sd_stp gv sd) *
     (@data_at DCS.CS Ers (tarray t_ct k) (ct_arr ffalse ftrue st) (sd_stp gv sd) -* trees_globals gv)).
Proof.
  intros [[-> ->]|[[-> ->]|[-> ->]]] E; cbn in E; inversion E; subst l.
  - change (sd_stp gv static_l_desc) with (gv _static_ltree).
    assert_PROP (tree_ok static_ltree_t (L_CODES + 2)) as Hok.
    { unfold trees_globals, static_trees, tree_arr. entailer!. }
    Exists static_ltree_t (L_CODES + 2). rewrite prop_true_andp by auto.
    rewrite <- (ct_canon_mode Ers (L_CODES + 2) ffalse ftrue).
    eapply wand_out; unfold trees_globals, static_trees, tree_arr;
      [rewrite prop_true_andp by auto; pull_out | entailer!].
  - change (sd_stp gv static_d_desc) with (gv _static_dtree).
    assert_PROP (tree_ok static_dtree_t D_CODES /\ tree_ok static_ltree_t (L_CODES + 2)) as Hok.
    { unfold trees_globals, static_trees, tree_arr. entailer!. }
    destruct Hok as [Hok Hok'].
    Exists static_dtree_t D_CODES. rewrite prop_true_andp by auto.
    rewrite <- (ct_canon_mode Ers D_CODES ffalse ftrue).
    eapply wand_out; unfold trees_globals, static_trees, tree_arr;
      [rewrite !prop_true_andp by auto; unfold ct_canon; pull_out | entailer!].
Qed.

(** ** The model: reads, writes, the run of build_tree *)

Lemma rd_inv l i x : rd l i = Some x -> 0 <= i < Zlength l /\ x = Znth i l.
Proof.
  unfold rd, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  intros H; inversion H. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. split; [lia|reflexivity].
Qed.

Lemma wr_inv l i v l' : wr l i v = Some l' -> 0 <= i < Zlength l /\ l' = upd_Znth i l v.
Proof.
  unfold wr, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  intros H; inversion H. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. split; [lia|reflexivity].
Qed.

Lemma c_set_fc_inv t i v t' : c_set_fc t i v = Some t' ->
  0 <= i < Zlength (fc t) /\ t' = mkTree (upd_Znth i (fc t) v) (dl t).
Proof.
  unfold c_set_fc. intros H. inv_bind H. apply wr_inv in Ha. destruct Ha as [? ->]. inversion H. auto.
Qed.

Lemma c_set_dl_inv t i v t' : c_set_dl t i v = Some t' ->
  0 <= i < Zlength (dl t) /\ t' = mkTree (fc t) (upd_Znth i (dl t) v).
Proof.
  unfold c_set_dl. intros H. inv_bind H. apply wr_inv in Ha. destruct Ha as [? ->]. inversion H. auto.
Qed.

Lemma c_build_tree_inv sd t w r : c_build_tree sd t w = Some r ->
  exists t1 w1 mc1 t2 w2 mc2 w3 t4 w4 nd top heap6 t7 w7 t8,
    c_bt_init (Z.to_nat (sd_elems sd)) (sd_elems sd) t
      (w_set_heap_max (w_set_heap_len w 0) HEAP_SIZE) (-1) 0 = Some (t1, w1, mc1) /\
    c_bt_force 2 sd t1 w1 mc1 = Some (t2, w2, mc2) /\
    c_bt_heapify (Z.to_nat (w_heap_len w2 / 2)) t2 w2 (w_heap_len w2 / 2) = Some w3 /\
    c_bt_merge (Z.to_nat (w_heap_len w3)) t2 w3 (sd_elems sd) = Some (t4, w4, nd) /\
    rd (w_heap w4) SMALLEST = Some top /\
    wr (w_heap w4) (w_heap_max w4 - 1) top = Some heap6 /\
    c_gen_bitlen sd mc2 t4 (w_set_heap (w_set_heap_max w4 (w_heap_max w4 - 1)) heap6) = Some (t7, w7) /\
    c_gen_codes t7 mc2 (w_bl_count w7) = Some t8 /\
    r = (t8, mc2, w7).
Proof.
  unfold c_build_tree. intros H.
  inv_bind H. destruct x as [[t1 w1] mc1].
  inv_bind H. destruct x as [[t2 w2] mc2].
  inv_bind H. rename x into w3.
  inv_bind H. destruct x as [[t4 w4] nd].
  inv_bind H. rename x into top. cbn [w_heap w_set_heap_max w_heap_max] in Ha3.
  inv_bind H. rename x into heap6. cbn [w_heap w_set_heap_max w_heap_max] in Ha4.
  inv_bind H. destruct x as [t7 w7].
  inv_bind H. rename x into t8. inversion H; subst r.
  exists t1, w1, mc1, t2, w2, mc2, w3, t4, w4, nd, top, heap6, t7, w7, t8.
  repeat split; auto.
Qed.

(** ** Ranges after one store *)

Lemma work_ok_heap_len w x : work_ok w -> Int.min_signed <= x <= Int.max_signed ->
  work_ok (w_set_heap_len w x).
Proof. unfold work_ok; cbn; tauto. Qed.

Lemma work_ok_heap_max w x : work_ok w -> Int.min_signed <= x <= Int.max_signed ->
  work_ok (w_set_heap_max w x).
Proof. unfold work_ok; cbn; tauto. Qed.

Lemma work_ok_heap w i v : work_ok w -> Int.min_signed <= v <= Int.max_signed ->
  work_ok (w_set_heap w (upd_Znth i (w_heap w) v)).
Proof.
  unfold work_ok; cbn. intros (H1 & H2 & H3 & H4 & H5) Hv.
  rewrite Zlength_upd_Znth. repeat split; try tauto.
  destruct (zlt i 0); [rewrite upd_Znth_out_of_range by lia; auto|].
  destruct (zlt i (Zlength (w_heap w))); [|rewrite upd_Znth_out_of_range by lia; auto].
  apply Forall_upd_Znth; auto; lia.
Qed.

Lemma work_ok_depth w i v : work_ok w -> 0 <= v < 256 ->
  work_ok (w_set_depth w (upd_Znth i (w_depth w) v)).
Proof.
  unfold work_ok; cbn. intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hv.
  rewrite Zlength_upd_Znth. repeat split; try tauto.
  destruct (zlt i 0); [rewrite upd_Znth_out_of_range by lia; auto|].
  destruct (zlt i (Zlength (w_depth w))); [|rewrite upd_Znth_out_of_range by lia; auto].
  apply Forall_upd_Znth; auto; lia.
Qed.

Lemma work_ok_opt_len w x : work_ok w -> work_ok (w_set_opt_len w (u64 x)).
Proof.
  unfold work_ok; cbn. intros. unfold u64. pose proof (Z.mod_pos_bound x 18446744073709551616 ltac:(lia)).
  change Int64.max_unsigned with 18446744073709551615. repeat split; tauto || lia.
Qed.

Lemma work_ok_static_len w x : work_ok w -> work_ok (w_set_static_len w (u64 x)).
Proof.
  unfold work_ok; cbn. intros. unfold u64. pose proof (Z.mod_pos_bound x 18446744073709551616 ltac:(lia)).
  change Int64.max_unsigned with 18446744073709551615. repeat split; tauto || lia.
Qed.

Lemma upd_range l i v j M : 0 <= v < M -> 0 <= j < Zlength l -> 0 <= Znth j l < M ->
  0 <= Znth j (upd_Znth i l v) < M.
Proof.
  intros Hv Hj Hl.
  destruct (zlt i 0); [rewrite upd_Znth_out_of_range by lia; auto|].
  destruct (zlt i (Zlength l)); [|rewrite upd_Znth_out_of_range by lia; auto].
  destruct (Z.eq_dec i j); [subst; rewrite upd_Znth_same by lia; auto|].
  rewrite upd_Znth_diff by lia. auto.
Qed.

Lemma tree_ok_fc t n i v : tree_ok t n -> 0 <= v < 65536 ->
  tree_ok (mkTree (upd_Znth i (fc t) v) (dl t)) n.
Proof.
  unfold tree_ok; cbn. intros (H1 & H2 & H3) Hv. rewrite Zlength_upd_Znth.
  split; [lia|split; [lia|]]. intros j Hj. split; [apply upd_range; [lia|lia|apply H3; auto] | apply H3; auto].
Qed.

Lemma tree_ok_dl t n i v : tree_ok t n -> 0 <= v < 65536 ->
  tree_ok (mkTree (fc t) (upd_Znth i (dl t) v)) n.
Proof.
  unfold tree_ok; cbn. intros (H1 & H2 & H3) Hv. rewrite Zlength_upd_Znth.
  split; [lia|split; [lia|]]. intros j Hj. split; [apply H3; auto | apply upd_range; [lia|lia|apply H3; auto]].
Qed.

(** ** heap_len stays below the size of the heap *)

Lemma c_pqdownheap_hl t w k r : c_pqdownheap t w k = Some r ->
  w_heap_len r = w_heap_len w /\ w_heap_max r = w_heap_max w.
Proof.
  unfold c_pqdownheap. intros H. inv_bind H. inv_bind H. destruct x0 as [heap k'].
  inv_bind H. inversion H. auto.
Qed.

Lemma c_bt_heapify_hl f t w k r : c_bt_heapify f t w k = Some r -> w_heap_len r = w_heap_len w.
Proof.
  revert w k. induction f as [|f IH]; intros w k H; cbn [c_bt_heapify] in H.
  - destruct (k >=? 1); inversion H; auto.
  - destruct (k >=? 1); [|inversion H; auto].
    inv_bind H. apply c_pqdownheap_hl in Ha. rewrite <- (proj1 Ha). apply (IH _ _ H).
Qed.

Lemma c_bt_init_hl f e t w mc i r : c_bt_init f e t w mc i = Some r ->
  Zlength (w_heap w) = 573 -> 0 <= w_heap_len w <= 572 ->
  Zlength (w_heap (snd (fst r))) = 573 /\ 0 <= w_heap_len (snd (fst r)) <= 572.
Proof.
  revert t w mc i. induction f as [|f IH]; intros t w mc i H Hl Hh; cbn [c_bt_init] in H.
  - destruct (i <? e); inversion H; auto.
  - destruct (i <? e); [|inversion H; auto].
    inv_bind H. destruct (negb (x =? 0)).
    + inv_bind H. apply wr_inv in Ha0. destruct Ha0 as [Hr ->]. cbn in Hr.
      inv_bind H. apply wr_inv in Ha0. destruct Ha0 as [_ ->].
      apply (IH _ _ _ _ H); cbn; rewrite ?Zlength_upd_Znth; lia.
    + inv_bind H. apply (IH _ _ _ _ H); auto.
Qed.

Lemma c_bt_force_hl f sd t w mc r : c_bt_force f sd t w mc = Some r ->
  Zlength (w_heap w) = 573 -> 0 <= w_heap_len w <= 572 ->
  Zlength (w_heap (snd (fst r))) = 573 /\ 0 <= w_heap_len (snd (fst r)) <= 572.
Proof.
  revert t w mc. induction f as [|f IH]; intros t w mc H Hl Hh; cbn [c_bt_force] in H.
  - destruct (w_heap_len w <? 2); inversion H; auto.
  - destruct (w_heap_len w <? 2); [|inversion H; auto].
    destruct (mc <? 2);
    (inv_bind H; apply wr_inv in Ha; destruct Ha as [Hr ->]; cbn in Hr;
     inv_bind H; inv_bind H; apply wr_inv in Ha0; destruct Ha0 as [_ ->];
     inv_bind H;
     assert (Zlength (w_heap x0) = 573 /\ 0 <= w_heap_len x0 <= 572) as [? ?]
       by (destruct (sd_stree sd); [inv_bind Ha0; inversion Ha0; subst; cbn; rewrite ?Zlength_upd_Znth; lia
                                   | inversion Ha0; subst; cbn; rewrite ?Zlength_upd_Znth; lia]);
     apply (IH _ _ _ H); auto).
Qed.
