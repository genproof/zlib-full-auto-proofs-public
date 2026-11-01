(** * fill_window, fragment S_read (FWKit.v) against its model step. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.FWKit.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Require Zlib.proof.adler32.Model Zlib.proof.crc32.Combine Zlib.trees.code Zlib.proof.crc32.Spec.

(** The model facts of a read. *)
Lemma c_read_buf_facts s z size z' data :
  strm_ranges z -> 0 <= size -> c_read_buf s z size = Some (z', data) ->
  strm_ranges z' /\ z_msg z' = z_msg z /\ z_in z' = z_in z /\
  Forall (fun x => 0 <= x < 256) data /\ Zlength data <= size.
Proof.
  intros Hr Hs H. unfold c_read_buf in H.
  pose proof Hr as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
  set (len := if z_avail_in z >? size then size else z_avail_in z) in H.
  assert (Hlen : 0 <= len <= size /\ len <= z_avail_in z).
  { unfold len. destruct (Z.gtb_spec (z_avail_in z) size); lia. }
  destruct (len =? 0) eqn:E0.
  { inversion H; subst. split; [exact Hr|]. repeat split; auto; rewrite ?Zlength_nil; lia. }
  unfold rds in H. cbn [z_in z_next_in set_z_avail_in] in H.
  rewrite (proj2 (andb_true_iff _ _)) in H.
  2: { split; [apply andb_true_iff; split|]; apply Z.leb_le; lia. }
  cbn [bind] in H.
  set (d := sublist (z_next_in z) (z_next_in z + len) (z_in z)) in H.
  assert (Hd : Forall (fun x => 0 <= x < 256) d).
  { unfold d. apply Forall_sublist. auto. }
  assert (Hdb : Zlib.proof.adler32.Bytes.is_bytes d).
  { unfold Zlib.proof.adler32.Bytes.is_bytes. eapply Forall_impl; [|exact Hd]. intros x Hx; cbn; rep_lia. }
  assert (Hdl : Zlength d = len) by (unfold d; rewrite Zlength_sublist; lia).
  match type of H with Some (?zz, _) = _ => set (zr := zz) in H end.
  assert (Ha : u64_ok (z_adler zr)).
  { unfold zr. destruct (d_wrap s =? 1); cbn.
    - pose proof (Zlib.proof.adler32.Model.adler32_z_val_range (z_adler z) d Hdb).
      unfold u64_ok. rep_lia.
    - destruct (d_wrap s =? 2); cbn; [|exact R10].
      pose proof (Zlib.proof.crc32.Combine.ref_crc32_range (z_adler z) d Hdb).
      unfold Zlib.proof.crc32.GF2.is32 in H0. unfold u64_ok. rep_lia. }
  assert (Hrest : z_in zr = z_in z /\ z_next_in zr = z_next_in z + len /\ z_avail_in zr = z_avail_in z - len /\
    z_total_in zr = u64 (z_total_in z + len) /\ z_out zr = z_out z /\ z_avail_out zr = z_avail_out z /\
    z_total_out zr = z_total_out z /\ z_msg zr = z_msg z).
  { unfold zr. destruct (d_wrap s =? 1); [|destruct (d_wrap s =? 2)]; cbn; repeat split; reflexivity. }
  inversion H; subst z' data. clear H.
  destruct Hrest as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  unfold strm_ranges. rewrite E1, E2, E3, E4, E5, E6, E7, E8.
  assert (0 <= u64 (z_total_in z + len) <= Int64.max_unsigned).
  { unfold u64. pose proof (Z.mod_pos_bound (z_total_in z + len) 18446744073709551616 ltac:(lia)). rep_lia. }
  unfold u32_ok, u64_ok in *. repeat split; auto; lia.
Qed.

(** trees_at without dtype_at (s->strm), kept folded. *)
Definition trees_rest (cs : tstate * list bool) (sp pbp : val) (gv : globals) : mpred :=
  (ltree_at (tr_ltree (fst cs)) sp * dtree_at (tr_dtree (fst cs)) sp * bltree_at (tr_bltree (fst cs)) sp *
   ldesc_at (field_address t_ds (DOT _dyn_ltree) sp) (tr_lmax (fst cs)) (gv Zlib.trees.code._static_l_desc) sp *
   ddesc_at (field_address t_ds (DOT _dyn_dtree) sp) (tr_dmax (fst cs)) (gv Zlib.trees.code._static_d_desc) sp *
   bldesc_at (field_address t_ds (DOT _bl_tree) sp) (tr_blmax (fst cs)) (gv Zlib.trees.code._static_bl_desc) sp *
   work_at (tr_wk (fst cs)) sp * out_at (tr_out (fst cs)) (snd cs) sp pbp * sym_at (fst cs) sp pbp *
   lvl_at (fst cs) sp)%logic.

Lemma trees_at_split cs sp pbp strmp gv :
  trees_at cs sp pbp strmp gv = (trees_rest cs sp pbp gv * dtype_at (fst cs) sp strmp)%logic.
Proof. reflexivity. Qed.

(** deflate_globals without crc_table_at, kept folded. *)
Definition dglobals_rest (gv : globals) : mpred :=
  (trees_globals gv * errmsg_at gv *
   @data_at DCS.CS Ers (tarray t_config 10) (config_vals gv) (gv _configuration_table) *
   @data_at DCS.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0]) (gv _my_version))%logic.

Lemma deflate_globals_split gv : deflate_globals gv = (dglobals_rest gv * Zlib.proof.crc32.Spec.crc_table_at Ers gv)%logic.
Proof. reflexivity. Qed.

Lemma dstate_ranges_read s win x :
  dstate_ranges s -> mb_ok win -> Zlength (mb_val win) = Zlength (mb_val (d_window s)) -> u32_ok x ->
  dstate_ranges (set_d_lookahead (set_d_window s win) x).
Proof.
  intros H Hm Hl Hx. unfold dstate_ranges in *.
  unfold set_d_lookahead, set_d_window; cbn -[u32_ok u64_ok s32_ok mb_ok Int.max_unsigned Int64.max_unsigned Zlength].
  rewrite Hl. tauto.
Qed.

Lemma repr_u32 x : Int.repr (u32 x) = Int.repr x.
Proof.
  unfold u32. change 4294967296 with Int.modulus. rewrite <- Int.unsigned_repr_eq. apply Int.repr_unsigned.
Qed.

Lemma app3_sublists {A} {d : Inhabitant A} (a b c : list A) :
  sublist 0 (Zlength a) (a ++ b ++ c) = a /\
  sublist (Zlength a) (Zlength a + Zlength b) (a ++ b ++ c) = b /\
  sublist (Zlength a + Zlength b) (Zlength a + Zlength b + Zlength c) (a ++ b ++ c) = c.
Proof. split; [|split]; list_solve. Qed.

Lemma fw_read : fw_read_triple.
Proof.
  unfold fw_read_triple; intros. show_fw_stmt. unfold dfull_in, dstate_at. Intros.
  destruct (c_read_buf_facts _ _ _ _ _ H2 (proj1 H) H0) as (Hz1 & Hz2 & Hz3 & Hz4 & Hz5).
  assert (Hmb : mb_ok (d_window s)) by (unfold dstate_ranges in H5; tauto).
  pose proof Hmb as [Hml _].
  destruct (mb_vals_write _ _ _ _ Hml H1) as (Hw1 & Hw2 & Hw3 & Hw4 & Hw5).
  assert (Hst : u32_ok (d_strstart s) /\ u32_ok (d_lookahead s)) by (unfold dstate_ranges in H5; tauto).
  rewrite trees_at_split. unfold dtype_at. Intros.
  unfold win_at, match_at. Intros.
  forward.
  forward.
  forward.
  forward.
  unfold stat_at. rewrite deflate_globals_split. Intros.
  set (L := Zlength (mb_val (d_window s))) in *.
  set (lo := d_strstart s + d_lookahead s) in *.
  assert (HL : Zlength (mb_vals (d_window s)) = L) by (apply Zlength_mb_vals; auto).
  pose proof (Zlength_nonneg data).
  assert_PROP (field_compatible (tarray tuchar L) [] (p_window p)) as Hfc by entailer!.
  rewrite (split3_data_at_Tarray_tuchar Ews L lo (lo + Zlength data)) by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  assert (Hnfo : forall i, nested_field_offset (Tarray tuchar L noattr) (SUB i) = i)
    by (intros; simpl; unfold Ctypes.sizeof; lia).
  rewrite !Hnfo. Intros.
  replace (lo + Zlength data - lo) with (Zlength data) by lia.
  sep_apply (data_at_data_at_ Ews (Tarray tuchar (Zlength data) noattr)
    (sublist lo (lo + Zlength data) (mb_vals (d_window s))) (offset_val lo (p_window p))).
  assert_PROP (isptr (p_strm p)) as Hps by entailer!.
  pose proof (field_compatible_isptr _ _ _ Hfc) as Hpw.
  forward_call (p_strm p, p_s p, pin, msgv, ish, z, s, more, offset_val lo (p_window p), (z', data), gv).
  { apply prop_right. destruct (p_window p) eqn:Epw; try contradiction.
    destruct (p_strm p); try contradiction. cbn.
    clear - Hst. destruct Hst as [Hs1 Hs2]. unfold u32_ok in *.
    rewrite Ptrofs.add_assoc, !(Ptrofs.mul_commut (Ptrofs.repr 1)), !Ptrofs.mul_one.
    unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite !Int.unsigned_repr by rep_lia.
    rewrite ptrofs_add_repr. reflexivity. }
  { clear - H5. unfold dstate_ranges in H5. tauto. }
  cbn [fst snd].
  forward.
  forward.
  forward.
  match goal with |- context [set_d_lookahead ?a ?b] => set (s2 := set_d_lookahead a b) end.
  assert (Hr2 : dstate_ranges s2).
  { apply dstate_ranges_read; auto.
    - eapply mb_ok_write; eauto.
    - unfold u32_ok, u32. pose proof (Z.mod_pos_bound (d_lookahead s + Zlength data) 4294967296 ltac:(lia)). rep_lia. }
  change (d_trm s2) with (d_trm s). change (hash_at s2 p) with (hash_at s p).
  change (cfg_at s2 p) with (cfg_at s p). change (stat_at s2 p) with (stat_at s p).
  change (d_window s2) with win.
  change (d_lookahead s2) with (u32 (d_lookahead s + Zlength data)).
  unfold s2; cbn [set_d_lookahead set_d_window d_window_size d_w_size d_w_bits d_w_mask d_high_water
    d_block_start d_match_length d_prev_match d_match_available d_strstart d_match_start d_prev_length
    d_insert d_slid].
  rewrite Hw2.
  rewrite (split3_data_at_Tarray_tuchar Ews L lo (lo + Zlength data) (mb_vals win)) by (try list_solve; lia).
  rewrite !field_address0_offset by auto with field_compatible. rewrite !Hnfo.
  replace (lo + Zlength data - lo) with (Zlength data) by lia.
  rewrite Hw1.
  pose proof (app3_sublists (sublist 0 lo (mb_vals (d_window s))) (map vi data)
    (sublist (lo + Zlength data) L (mb_vals (d_window s)))) as (E1 & E2 & E3).
  rewrite ?Zlength_map, ?Zlength_sublist in E1 by lia.
  rewrite ?Zlength_map, ?Zlength_sublist in E2 by lia.
  rewrite ?Zlength_map, ?Zlength_sublist in E3 by lia.
  replace (lo - 0) with lo in * by lia.
  replace (lo + Zlength data + (L - (lo + Zlength data))) with L in E3 by lia.
  rewrite E1, E2, E3. clear E1 E2 E3.
  rewrite trees_at_split, deflate_globals_split. unfold dtype_at, stat_at.
  replace (vi (u32 (d_lookahead s + Zlength data))) with
    (Vint (Int.add (Int.repr (d_lookahead s)) (Int.repr (Zlength data))))
    by (unfold vi; rewrite repr_u32, add_repr; reflexivity).
  entailer!.
Qed.
