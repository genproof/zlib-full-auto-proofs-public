(** * The body of trees.c's build_bl_tree against TSpec.v *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.trees.CtModeS.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** The trees of the state as stand-alone arrays at their field addresses. *)
Lemma ltree_at_arr t sp :
  ltree_at t sp = tree_arr Ews 573 t (field_address t_ds (DOT _dyn_ltree) sp).
Proof. unfold ltree_at, tree_arr. f_equal. apply (@field_at_data_at DCS.CS). Qed.

Lemma dtree_at_arr t sp :
  dtree_at t sp = tree_arr Ews 61 t (field_address t_ds (DOT _dyn_dtree) sp).
Proof. unfold dtree_at, tree_arr. f_equal. apply (@field_at_data_at DCS.CS). Qed.

Lemma bltree_at_arr t sp :
  bltree_at t sp = tree_arr Ews 39 t (field_address t_ds (DOT _bl_tree) sp).
Proof. unfold bltree_at, tree_arr. f_equal. apply (@field_at_data_at DCS.CS). Qed.

Lemma bldesc_at_td treep maxc statp sp :
  bldesc_at treep maxc statp sp = td_at Ews treep maxc statp (field_address t_ds (DOT _bl_desc) sp).
Proof. unfold bldesc_at, td_at. f_equal. apply (@field_at_data_at DCS.CS). Qed.

Lemma bltree_field_data v sp :
  @field_at DCS.CS Ews t_ds (DOT _bl_tree) v sp =
  @data_at DCS.CS Ews (tarray t_ct 39) v (field_address t_ds (DOT _bl_tree) sp).
Proof. apply (@field_at_data_at DCS.CS). Qed.

Lemma rd_inv l i x : rd l i = Some x -> 0 <= i < Zlength l /\ x = Znth i l.
Proof.
  unfold rd, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  intros Hx; injection Hx as <-. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. auto.
Qed.

Lemma bl_order_range i : 0 <= i < 19 -> 0 <= Znth i bl_order < 19.
Proof.
  intros Hi.
  assert (Hf : Forall (fun x => 0 <= x < 19) bl_order)
    by (unfold bl_order; repeat (apply Forall_cons; [lia|]); apply Forall_nil).
  rewrite Forall_Znth in Hf. apply Hf. exact Hi.
Qed.

Lemma c_find_lt3 f bl i : i < 3 -> c_find_max_blindex f bl i = Some i.
Proof.
  intros Hi. destruct f; cbn;
  (destruct (i >=? 3) eqn:E; [apply Z.geb_le in E; lia | reflexivity]).
Qed.

Lemma repr_u64 x : Int64.repr (u64 x) = Int64.repr x.
Proof.
  unfold u64. apply Int64.eqm_samerepr. apply Int64.eqm_sym. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma u64_range x : 0 <= u64 x <= Int64.max_unsigned.
Proof. unfold u64. pose proof (Z.mod_pos_bound x 18446744073709551616 ltac:(lia)). rep_lia. Qed.

Lemma body_build_bl_tree : semax_body Vprog Gprog_build_bl_tree f_build_bl_tree build_bl_tree_spec.
Proof.
  start_function.
  unfold c_build_bl_tree in H.
  inv_bind H. destruct x as [lt bl1].
  inv_bind H. destruct x as [dt bl2].
  inv_bind H. destruct x as [[bl3 blmax] w].
  inv_bind H. rename x into mb.
  injection H as <-.
  unfold ldesc_at, ddesc_at. Intros.
  unfold td_val. cbn [td_dyn_tree td_max_code td_stat_desc].
  forward.
  assert_PROP (field_compatible t_ds (DOT _dyn_ltree) sp /\ field_compatible t_ds (DOT _dyn_dtree) sp /\
               field_compatible t_ds (DOT _bl_tree) sp /\ field_compatible t_ds (DOT _bl_desc) sp) as Hfc
    by (unfold ltree_at, dtree_at, bltree_at, bldesc_at; Intros; entailer!).
  destruct Hfc as (Hfl & Hfd & Hfb & Hfbd).
  rewrite ltree_at_arr.
  forward_call (sp, field_address t_ds (DOT _dyn_ltree) sp, 573, tr_ltree ts, tr_lmax ts, tr_bltree ts, (lt, bl1)).
  cbn [fst snd].
  forward.
  rewrite dtree_at_arr.
  forward_call (sp, field_address t_ds (DOT _dyn_dtree) sp, 61, tr_dtree ts, tr_dmax ts, bl1, (dt, bl2)).
  cbn [fst snd].
  rewrite bltree_at_arr, bldesc_at_td.
  forward_call (sp, field_address t_ds (DOT _bl_desc) sp, field_address t_ds (DOT _bl_tree) sp, 39, bl2,
                tr_blmax ts, gv _static_bl_desc, static_bl_desc, tr_wk ts, (bl3, blmax, w), gv).
  { unfold sdesc_ptr; auto. }
  cbn [fst snd].
  unfold tree_arr at 1. Intros.
  unfold ct_canon. rewrite (ct_canon_mode Ews 39 ffalse ftrue bl3).
  rewrite <- bltree_field_data.
  unfold trees_globals, trees_tables. Intros.
  forward_loop
    (EX f : nat, EX i : Z,
      PROP (c_find_max_blindex f bl3 i = Some mb; 2 <= i <= 18)
      LOCAL (temp _max_blindex (Vint (Int.repr i)); gvars gv; temp _s sp)
      SEP (td_at Ews (field_address t_ds (DOT _bl_tree) sp) blmax (gv _static_bl_desc) (field_address t_ds (DOT _bl_desc) sp);
           @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ffalse ftrue bl3) sp;
           work_at w sp; static_trees gv;
           @data_at DCS.CS Ers (tarray tuchar 512) (map vi dist_code_tab) (gv __dist_code);
           @data_at DCS.CS Ers (tarray tuchar 256) (map vi length_code_tab) (gv __length_code);
           @data_at DCS.CS Ers (tarray tint 29) (map vi base_length_tab) (gv _base_length);
           @data_at DCS.CS Ers (tarray tint 30) (map vi base_dist_tab) (gv _base_dist);
           @data_at DCS.CS Ers (tarray tint 29) (map vi extra_lbits) (gv _extra_lbits);
           @data_at DCS.CS Ers (tarray tint 30) (map vi extra_dbits) (gv _extra_dbits);
           @data_at DCS.CS Ers (tarray tint 19) (map vi extra_blbits) (gv _extra_blbits);
           @data_at DCS.CS Ers (tarray tuchar 19) (map vi bl_order) (gv _bl_order);
           @data_at DCS.CS Ers t_sd (gv _static_ltree, (gv _extra_lbits, (vi 257, (vi 286, vi 15)))) (gv _static_l_desc);
           @data_at DCS.CS Ers t_sd (gv _static_dtree, (gv _extra_dbits, (vi 0, (vi 30, vi 15)))) (gv _static_d_desc);
           @data_at DCS.CS Ers t_sd (nullval, (gv _extra_blbits, (vi 0, (vi 19, vi 7)))) (gv _static_bl_desc);
           tree_arr Ews 61 dt (field_address t_ds (DOT _dyn_dtree) sp);
           tree_arr Ews 573 lt (field_address t_ds (DOT _dyn_ltree) sp);
           field_at Ews t_ds (DOT _l_desc)
             (field_address t_ds (DOT _dyn_ltree) sp, (Vint (Int.repr (tr_lmax ts)), gv _static_l_desc)) sp;
           field_at Ews t_ds (DOT _d_desc)
             (field_address t_ds (DOT _dyn_dtree) sp, (Vint (Int.repr (tr_dmax ts)), gv _static_d_desc)) sp))%assert
    continue:
    (EX f : nat, EX i : Z,
      PROP (c_find_max_blindex f bl3 (i - 1) = Some mb; 3 <= i <= 18)
      LOCAL (temp _max_blindex (Vint (Int.repr i)); gvars gv; temp _s sp)
      SEP (td_at Ews (field_address t_ds (DOT _bl_tree) sp) blmax (gv _static_bl_desc) (field_address t_ds (DOT _bl_desc) sp);
           @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ffalse ftrue bl3) sp;
           work_at w sp; static_trees gv;
           @data_at DCS.CS Ers (tarray tuchar 512) (map vi dist_code_tab) (gv __dist_code);
           @data_at DCS.CS Ers (tarray tuchar 256) (map vi length_code_tab) (gv __length_code);
           @data_at DCS.CS Ers (tarray tint 29) (map vi base_length_tab) (gv _base_length);
           @data_at DCS.CS Ers (tarray tint 30) (map vi base_dist_tab) (gv _base_dist);
           @data_at DCS.CS Ers (tarray tint 29) (map vi extra_lbits) (gv _extra_lbits);
           @data_at DCS.CS Ers (tarray tint 30) (map vi extra_dbits) (gv _extra_dbits);
           @data_at DCS.CS Ers (tarray tint 19) (map vi extra_blbits) (gv _extra_blbits);
           @data_at DCS.CS Ers (tarray tuchar 19) (map vi bl_order) (gv _bl_order);
           @data_at DCS.CS Ers t_sd (gv _static_ltree, (gv _extra_lbits, (vi 257, (vi 286, vi 15)))) (gv _static_l_desc);
           @data_at DCS.CS Ers t_sd (gv _static_dtree, (gv _extra_dbits, (vi 0, (vi 30, vi 15)))) (gv _static_d_desc);
           @data_at DCS.CS Ers t_sd (nullval, (gv _extra_blbits, (vi 0, (vi 19, vi 7)))) (gv _static_bl_desc);
           tree_arr Ews 61 dt (field_address t_ds (DOT _dyn_dtree) sp);
           tree_arr Ews 573 lt (field_address t_ds (DOT _dyn_ltree) sp);
           field_at Ews t_ds (DOT _l_desc)
             (field_address t_ds (DOT _dyn_ltree) sp, (Vint (Int.repr (tr_lmax ts)), gv _static_l_desc)) sp;
           field_at Ews t_ds (DOT _d_desc)
             (field_address t_ds (DOT _dyn_dtree) sp, (Vint (Int.repr (tr_dmax ts)), gv _static_d_desc)) sp))%assert
    break:
    (PROP (2 <= mb <= 18)
      LOCAL (temp _max_blindex (Vint (Int.repr mb)); gvars gv; temp _s sp)
      SEP (td_at Ews (field_address t_ds (DOT _bl_tree) sp) blmax (gv _static_bl_desc) (field_address t_ds (DOT _bl_desc) sp);
           @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ffalse ftrue bl3) sp;
           work_at w sp; static_trees gv;
           @data_at DCS.CS Ers (tarray tuchar 512) (map vi dist_code_tab) (gv __dist_code);
           @data_at DCS.CS Ers (tarray tuchar 256) (map vi length_code_tab) (gv __length_code);
           @data_at DCS.CS Ers (tarray tint 29) (map vi base_length_tab) (gv _base_length);
           @data_at DCS.CS Ers (tarray tint 30) (map vi base_dist_tab) (gv _base_dist);
           @data_at DCS.CS Ers (tarray tint 29) (map vi extra_lbits) (gv _extra_lbits);
           @data_at DCS.CS Ers (tarray tint 30) (map vi extra_dbits) (gv _extra_dbits);
           @data_at DCS.CS Ers (tarray tint 19) (map vi extra_blbits) (gv _extra_blbits);
           @data_at DCS.CS Ers (tarray tuchar 19) (map vi bl_order) (gv _bl_order);
           @data_at DCS.CS Ers t_sd (gv _static_ltree, (gv _extra_lbits, (vi 257, (vi 286, vi 15)))) (gv _static_l_desc);
           @data_at DCS.CS Ers t_sd (gv _static_dtree, (gv _extra_dbits, (vi 0, (vi 30, vi 15)))) (gv _static_d_desc);
           @data_at DCS.CS Ers t_sd (nullval, (gv _extra_blbits, (vi 0, (vi 19, vi 7)))) (gv _static_bl_desc);
           tree_arr Ews 61 dt (field_address t_ds (DOT _dyn_dtree) sp);
           tree_arr Ews 573 lt (field_address t_ds (DOT _dyn_ltree) sp);
           field_at Ews t_ds (DOT _l_desc)
             (field_address t_ds (DOT _dyn_ltree) sp, (Vint (Int.repr (tr_lmax ts)), gv _static_l_desc)) sp;
           field_at Ews t_ds (DOT _d_desc)
             (field_address t_ds (DOT _dyn_dtree) sp, (Vint (Int.repr (tr_dmax ts)), gv _static_d_desc)) sp)).
  - forward. Exists 20%nat 18. entailer!.
  - Intros f i.
    forward_if.
    2:{ forward. rewrite c_find_lt3 in H2 by lia. injection H2 as ->. entailer!. }
    destruct f as [|f].
    { cbn in H2. rewrite (proj2 (Z.geb_le i 3) ltac:(lia)) in H2. discriminate. }
    cbn [c_find_max_blindex] in H2. rewrite (proj2 (Z.geb_le i 3) ltac:(lia)) in H2.
    inv_bind H2. apply rd_inv in Ha3. destruct Ha3 as [Hi ->].
    inv_bind H2. apply rd_inv in Ha3. destruct Ha3 as [Hr ->].
    pose proof (bl_order_range i ltac:(lia)) as Hbo.
    destruct H1 as (Hfc3 & Hdl3 & Hr3).
    fwd.
    assert (Hlen : 0 <= Znth (Znth i bl_order) (dl bl3) < 65536) by (apply (Hr3 (Znth i bl_order)); lia).
    forward.
    { rewrite Znth_ct_arr by lia. cbn [ctv_of ffalse ftrue]. tc_side. }
    rewrite Znth_ct_arr by lia. cbn [ctv_of ffalse ftrue].
    forward_if.
    + forward.
      rewrite (proj2 (Z.eqb_neq _ _) H1) in H2. cbn in H2. injection H2 as ->.
      entailer!.
    + forward.
      rewrite H1 in H2. cbn in H2.
      Exists f i. entailer!.
  - Intros f i.
    forward.
    Exists f (i - 1). entailer!.
  - unfold work_at. Intros.
    forward. forward.
    forward.
    cbn [tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk set_wk set_blmax set_bltree set_dtree set_ltree].
    rewrite ltree_at_arr, dtree_at_arr, bldesc_at_td.
    unfold bltree_at, ldesc_at, ddesc_at, work_at, trees_globals, trees_tables, td_val, ct_canon.
    cbn [w_set_opt_len w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len td_dyn_tree td_max_code td_stat_desc].
    rewrite !bltree_field_data. rewrite <- (ct_canon_mode Ews 39 ffalse ftrue bl3).
    unfold vl. rewrite repr_u64.
    assert (Hw : work_ok (w_set_opt_len w (u64 (w_opt_len w + (3 * (mb + 1) + 5 + 5 + 4))))).
    { destruct H3 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10). unfold work_ok.
      cbn [w_set_opt_len w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len].
      pose proof (u64_range (w_opt_len w + (3 * (mb + 1) + 5 + 5 + 4))) as Hu.
      exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj Hu A10))))))))). }
    change (2 * BL_CODES + 1) with 39.
    rewrite !prop_true_andp by assumption.
    cancel.
Qed.
