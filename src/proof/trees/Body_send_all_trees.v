(** * The body of trees.c's send_all_trees against its shared specification (TSpec.send_all_trees_spec).

    The inlined send_bits / send_code macro blocks: [SendKit.sb_block] (see SendKit.v's header). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.SendKit2.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** Helpers *)

Lemma sat_ltree_at_arr t sp :
  ltree_at t sp = tree_arr Ews 573 t (field_address t_ds (DOT _dyn_ltree) sp).
Proof. unfold ltree_at, tree_arr. f_equal. apply (@field_at_data_at DCS.CS). Qed.

Lemma sat_dtree_at_arr t sp :
  dtree_at t sp = tree_arr Ews 61 t (field_address t_ds (DOT _dyn_dtree) sp).
Proof. unfold dtree_at, tree_arr. f_equal. apply (@field_at_data_at DCS.CS). Qed.

(** bl_tree in its Len member (the loop reads [s->bl_tree[bl_order[rank]].Len]). *)
Lemma sat_bltree_len t sp :
  bltree_at t sp =
  (!! tree_ok t 39 && @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ffalse ftrue t) sp)%logic.
Proof.
  unfold bltree_at, ct_canon. f_equal.
  rewrite !(@field_at_data_at DCS.CS). apply (sk_ct_arr_mode Ews 39 ffalse ffalse ffalse ftrue).
Qed.

Lemma sat_rd_inv l i x : rd l i = Some x -> 0 <= i < Zlength l /\ x = Znth i l.
Proof.
  unfold rd, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  intros Hx; injection Hx as <-. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. auto.
Qed.

Lemma sat_bl_order_range i : 0 <= i < 19 -> 0 <= Znth i bl_order < 19.
Proof.
  intros Hi.
  assert (Hf : Forall (fun x => 0 <= x < 19) bl_order)
    by (unfold bl_order; repeat (apply Forall_cons; [lia|]); apply Forall_nil).
  rewrite Forall_Znth in Hf. apply Hf. exact Hi.
Qed.

Lemma sat_bl_lens_done f bl om rank blcodes r :
  blcodes <= rank -> c_send_bl_lens f bl om rank blcodes = Some r -> r = om.
Proof.
  intros Hb. destruct f; cbn; rewrite (proj2 (Z.ltb_ge rank blcodes) ltac:(lia)); congruence.
Qed.

(** trees_tables without bl_order (kept folded in the loop). *)
Definition sat_tables_rest (gv : globals) : mpred :=
  (@data_at DCS.CS Ers (tarray tuchar 512) (map vi dist_code_tab) (gv __dist_code) *
   @data_at DCS.CS Ers (tarray tuchar 256) (map vi length_code_tab) (gv __length_code) *
   @data_at DCS.CS Ers (tarray tint 29) (map vi base_length_tab) (gv _base_length) *
   @data_at DCS.CS Ers (tarray tint 30) (map vi base_dist_tab) (gv _base_dist) *
   @data_at DCS.CS Ers (tarray tint 29) (map vi extra_lbits) (gv _extra_lbits) *
   @data_at DCS.CS Ers (tarray tint 30) (map vi extra_dbits) (gv _extra_dbits) *
   @data_at DCS.CS Ers (tarray tint 19) (map vi extra_blbits) (gv _extra_blbits) *
   @data_at DCS.CS Ers t_sd (gv _static_ltree, (gv _extra_lbits, (vi 257, (vi 286, vi 15)))) (gv _static_l_desc) *
   @data_at DCS.CS Ers t_sd (gv _static_dtree, (gv _extra_dbits, (vi 0, (vi 30, vi 15)))) (gv _static_d_desc) *
   @data_at DCS.CS Ers t_sd (nullval, (gv _extra_blbits, (vi 0, (vi 19, vi 7)))) (gv _static_bl_desc))%logic.

Lemma sat_tables_split gv :
  trees_tables gv =
  (@data_at DCS.CS Ers (tarray tuchar 19) (map vi bl_order) (gv _bl_order) * sat_tables_rest gv)%logic.
Proof.
  unfold trees_tables, sat_tables_rest.
  apply pred_ext; cancel.
Qed.

Lemma sat_fuel_succ rank : rank < 19 -> Z.to_nat (19 - rank) = S (Z.to_nat (19 - (rank + 1))).
Proof. intros. rewrite <- Z2Nat.inj_succ by lia. f_equal. lia. Qed.

Lemma sat_bl_order_len : Zlength bl_order = 19.
Proof. reflexivity. Qed.

Lemma body_send_all_trees : semax_body Vprog Gprog_send_all_trees f_send_all_trees send_all_trees_spec.
Proof.
  start_function.
  unfold c_send_all_trees in H2.
  inv_bind H2. destruct x. apply guard_inv in Ha. rewrite !andb_true_iff, !Z.leb_le in Ha.
  inv_bind H2. rename Ha0 into Hsb1.
  sb_block Hsb1 ltac:(idtac) ltac:(rewrite ?sub_repr32; sb_val_default).
  inv_bind H2. rename Ha0 into Hsb2.
  sb_block Hsb2 ltac:(idtac) ltac:(rewrite ?sub_repr32; sb_val_default).
  inv_bind H2. rename Ha0 into Hsb3.
  sb_block Hsb3 ltac:(idtac) ltac:(rewrite ?sub_repr32; sb_val_default).
  inv_bind H2. rename Ha0 into Hbl. destruct x as [ox mx].
  clear Hsb1 Hsb2 Hsb3 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
  rewrite sat_bltree_len, sat_tables_split. Intros.
  forward_loop
    (EX rank : Z, EX o1 : outbuf, EX m1 : list bool,
      PROP (0 <= rank <= 19; c_send_bl_lens (Z.to_nat (19 - rank)) bl (o1, m1) rank blcodes = Some (ox, mx))
      LOCAL (temp _rank (Vint (Int.repr rank)); gvars gv; temp _s sp; temp _lcodes (Vint (Int.repr lcodes));
             temp _dcodes (Vint (Int.repr dcodes)); temp _blcodes (Vint (Int.repr blcodes)))
      SEP (out_at o1 m1 sp pbp; ltree_at lt sp; dtree_at dt sp;
           @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ffalse ftrue bl) sp;
           @data_at DCS.CS Ers (tarray tuchar 19) (map vi bl_order) (gv _bl_order); sat_tables_rest gv))
    continue:
    (EX rank : Z, EX o1 : outbuf, EX m1 : list bool,
      PROP (0 <= rank < 19;
            c_send_bl_lens (Z.to_nat (19 - (rank + 1))) bl (o1, m1) (rank + 1) blcodes = Some (ox, mx))
      LOCAL (temp _rank (Vint (Int.repr rank)); gvars gv; temp _s sp; temp _lcodes (Vint (Int.repr lcodes));
             temp _dcodes (Vint (Int.repr dcodes)); temp _blcodes (Vint (Int.repr blcodes)))
      SEP (out_at o1 m1 sp pbp; ltree_at lt sp; dtree_at dt sp;
           @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ffalse ftrue bl) sp;
           @data_at DCS.CS Ers (tarray tuchar 19) (map vi bl_order) (gv _bl_order); sat_tables_rest gv))
    break:
    (PROP ()
      LOCAL (gvars gv; temp _s sp; temp _lcodes (Vint (Int.repr lcodes));
             temp _dcodes (Vint (Int.repr dcodes)); temp _blcodes (Vint (Int.repr blcodes)))
      SEP (out_at ox mx sp pbp; ltree_at lt sp; dtree_at dt sp;
           @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ffalse ftrue bl) sp;
           @data_at DCS.CS Ers (tarray tuchar 19) (map vi bl_order) (gv _bl_order); sat_tables_rest gv)).
  - forward. Exists 0 o m2. entailer!.
  - Intros rank o1 m3.
    forward_if.
    2:{ forward. apply sat_bl_lens_done in H5; [|lia]. injection H5 as -> ->. entailer!. }
    assert (Hr19 : rank < 19).
    { destruct (Z.eq_dec rank 19) as [->|]; [|lia]. cbn in H5.
      rewrite (proj2 (Z.ltb_lt 19 blcodes) ltac:(lia)) in H5. discriminate. }
    rewrite (sat_fuel_succ rank Hr19) in H5.
    cbn [c_send_bl_lens] in H5. rewrite (proj2 (Z.ltb_lt rank blcodes) ltac:(lia)) in H5.
    inv_bind H5. apply sat_rd_inv in Ha0. destruct Ha0 as [_ ->].
    inv_bind H5. apply sat_rd_inv in Ha0. destruct Ha0 as [Hr0 ->].
    inv_bind H5. rename Ha0 into Hsb.
    pose proof (sat_bl_order_range rank ltac:(lia)) as Hbr.
    pose proof H3 as (E1 & E2 & _).
    assert (Hbo : Znth rank (map vi bl_order) = Vint (Int.repr (Znth rank bl_order)))
      by (rewrite Znth_map by (rewrite sat_bl_order_len; lia); reflexivity).
    assert (Hlr : 0 <= Znth (Znth rank bl_order) (dl bl) < 65536)
      by (apply (sk_tree_rng_dl bl 39); auto; lia).
    assert (Hi1 : 0 <= rank < Zlength bl_order) by (rewrite sat_bl_order_len; lia).
    assert (Hi2 : 0 <= rank < Zlength (map vi bl_order)) by (rewrite Zlength_map, sat_bl_order_len; lia).
    assert (Hi3 : 0 <= Znth rank bl_order < Zlength (ct_arr ffalse ftrue bl)) by (rewrite Zlength_ct_arr; lia).
    sb_block Hsb ltac:(try (rewrite Znth_ct_arr by lia; cbn [ctv_of ffalse ftrue]); try unfold vi)
      ltac:(sb_val_default).
    lazymatch goal with Hn : c_send_bl_lens _ _ (?a, ?b) (rank + 1) _ = _ |- _ => Exists rank a b end.
    unfold vi. entailer!.
  - Intros rank o1 m3. forward. Exists (rank + 1) o1 m3. entailer!.
  - assert_PROP (field_compatible t_ds (DOT _dyn_ltree) sp /\ field_compatible t_ds (DOT _dyn_dtree) sp) as Hfc
      by (unfold ltree_at, dtree_at; Intros; entailer!).
    destruct Hfc as [Hfl Hfd].
    replace (@field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ffalse ftrue bl) sp) with (bltree_at bl sp)
      by (rewrite sat_bltree_len, prop_true_andp by exact H3; reflexivity).
    inv_bind H2. rename Ha0 into Hst1.
    rewrite sat_ltree_at_arr.
    forward_call (sp, pbp, ox, mx, field_address t_ds (DOT _dyn_ltree) sp, Ews, 573, lt, lcodes - 1, bl, x).
    destruct x as [ox2 mx2]. cbn [fst snd].
    rewrite sat_dtree_at_arr.
    forward_call (sp, pbp, ox2, mx2, field_address t_ds (DOT _dyn_dtree) sp, Ews, 61, dt, dcodes - 1, bl, r).
    rewrite <- sat_ltree_at_arr, <- sat_dtree_at_arr, sat_tables_split.
    entailer!.
Qed.
