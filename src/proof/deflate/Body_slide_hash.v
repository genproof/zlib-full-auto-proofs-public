(** * The body of deflate.c's slide_hash against its shared specification (DSpec.slide_hash_spec): ob_slide_hash. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.deflate.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** The array during the loop: entries [k, len) already slid. *)
Lemma slide_inv_step (f : Z -> Z) (l : list Z) k n :
  0 < k <= Zlength l -> n = Zlength l ->
  upd_Znth (k - 1) (map vi (sublist 0 k l ++ map f (sublist k n l))) (vi (f (Znth (k - 1) l))) =
  map vi (sublist 0 (k - 1) l ++ map f (sublist (k - 1) n l)).
Proof. intros. list_solve. Qed.

Lemma slide_inv_read (f : Z -> Z) (l : list Z) k n :
  0 < k <= Zlength l -> n = Zlength l ->
  Znth (k - 1) (sublist 0 k l ++ map f (sublist k n l)) = Znth (k - 1) l.
Proof. intros. list_solve. Qed.

Lemma slide_entry_range ws m : 0 <= ws -> 0 <= m < 65536 -> 0 <= slide_entry ws m < 65536.
Proof. intros. unfold slide_entry, NIL. destruct (m >=? ws) eqn:E; lia. Qed.

Lemma ranges_slide s : dstate_ranges s -> 0 <= d_w_size s ->
  dstate_ranges (set_d_slid (set_d_prev (set_d_head s (map (slide_entry (d_w_size s)) (d_head s)))
                                        (map (slide_entry (d_w_size s)) (d_prev s))) 1).
Proof.
  intros Hr Hw. unfold dstate_ranges in *. simpl.
  destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?&?&Hp&Hh&Hpl&Hhl&?).
  rewrite !Zlength_map.
  assert (Hm : forall l, Forall (fun x => 0 <= x < 65536) l ->
                         Forall (fun x => 0 <= x < 65536) (map (slide_entry (d_w_size s)) l)).
  { intros l Hl. apply Forall_map. eapply Forall_impl; [|exact Hl]. intros a Ha. cbv beta in Ha. change (0 <= slide_entry (d_w_size s) a < 65536).
    apply slide_entry_range; lia. }
  intuition. unfold s32_ok. rep_lia.
Qed.

(** Pointer arithmetic on [Pos *]. *)
Lemma add_ptr_ushort q n : 0 <= n <= Int.max_unsigned -> isptr q ->
  force_val (sem_add_ptr_int tushort Unsigned q (vi n)) = offset_val (2 * n) q.
Proof.
  intros Hn Hq. destruct q; try contradiction. unfold vi. simpl.
  f_equal. f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int.
  rewrite Int.unsigned_repr by lia. rewrite ptrofs_mul_repr. reflexivity.
Qed.

Lemma sub_ptr_ushort q : isptr q ->
  force_val (sem_binary_operation' Osub (tptr tushort) tint q (Vint (Int.repr 1))) = offset_val (-2) q.
Proof.
  intros Hq. destruct q; try contradiction. simpl.
  f_equal. rewrite Ptrofs.sub_add_opp. f_equal.
Qed.

(** The fields slide_hash does not touch, kept folded. *)
Definition sh_rest (s : dstate) (p : dptrs) (gv : globals) : mpred :=
  (trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv *
  @field_at DCS.CS Ews t_ds (DOT _window) (p_window p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _window_size) (vl (d_window_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_mask) (vi (d_w_mask s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _high_water) (vl (d_high_water s)) (p_s p) *
  @data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p) *
  @field_at DCS.CS Ews t_ds (DOT _ins_h) (vi (d_ins_h s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _hash_bits) (vi (d_hash_bits s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _hash_mask) (vi (d_hash_mask s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _hash_shift) (vi (d_hash_shift s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
  cfg_at s p * stat_at s p)%logic.

Lemma sh_rest_slide s h pr p gv :
  sh_rest (set_d_slid (set_d_prev (set_d_head s h) pr) 1) p gv = sh_rest s p gv.
Proof. reflexivity. Qed.

Lemma dstate_at_open s p gv :
  dstate_at s p gv =
  (!! dstate_ranges s &&
   (sh_rest s p gv *
    @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p) *
    @data_at DCS.CS Ews (tarray tushort (Zlength (d_head s))) (map vi (d_head s)) (p_head p) *
    @data_at DCS.CS Ews (tarray tushort (Zlength (d_prev s))) (map vi (d_prev s)) (p_prev p)))%logic.
Proof.
  unfold dstate_at, sh_rest, win_at, hash_at, match_at.
  f_equal. apply pred_ext; cancel.
Qed.

Lemma body_slide_hash : ob_slide_hash.
Proof.
  unfold ob_slide_hash.
  start_function.
  unfold c_slide_hash in H. inv_bind H. destruct x. apply guard_inv in Ha.
  rewrite !andb_true_iff, !Z.leb_le, !Z.eqb_eq in Ha. destruct Ha as [[[Hhs Hhl] Hws] Hpl].
  inversion H; subst r; clear H.
  rewrite dstate_at_open. Intros.
  pose proof H as Hr. unfold dstate_ranges, u32_ok in Hr.
  destruct Hr as (_&_&_&_&_&_&_&Hwsr&_&_&_&_&_&Hpr&Hhr&_&_&_&Hhsr&_).
  forward. forward. forward. forward.
  rewrite Hhl, Hpl.
  forward_loop
    (EX k : Z,
     PROP (0 < k <= d_hash_size s)
     LOCAL (temp _n (vi k); temp _p (offset_val (2 * k) (p_head p)); temp _wsize (vi (d_w_size s));
            gvars gv; temp _s (p_s p))
     SEP (sh_rest s p gv;
          @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p);
          @data_at DCS.CS Ews (tarray tushort (d_hash_size s))
            (map vi (sublist 0 k (d_head s) ++ map (slide_entry (d_w_size s)) (sublist k (d_hash_size s) (d_head s))))
            (p_head p);
          @data_at DCS.CS Ews (tarray tushort (d_w_size s)) (map vi (d_prev s)) (p_prev p)))
  continue:
    (EX k : Z,
     PROP (0 <= k < d_hash_size s)
     LOCAL (temp _n (vi (k + 1)); temp _p (offset_val (2 * k) (p_head p)); temp _wsize (vi (d_w_size s));
            gvars gv; temp _s (p_s p))
     SEP (sh_rest s p gv;
          @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p);
          @data_at DCS.CS Ews (tarray tushort (d_hash_size s))
            (map vi (sublist 0 k (d_head s) ++ map (slide_entry (d_w_size s)) (sublist k (d_hash_size s) (d_head s))))
            (p_head p);
          @data_at DCS.CS Ews (tarray tushort (d_w_size s)) (map vi (d_prev s)) (p_prev p)))
  break:
    (PROP ()
     LOCAL (temp _wsize (vi (d_w_size s)); gvars gv; temp _s (p_s p))
     SEP (sh_rest s p gv;
          @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p);
          @data_at DCS.CS Ews (tarray tushort (d_hash_size s)) (map vi (map (slide_entry (d_w_size s)) (d_head s))) (p_head p);
          @data_at DCS.CS Ews (tarray tushort (d_w_size s)) (map vi (d_prev s)) (p_prev p))).
  { Exists (d_hash_size s). entailer!.
    all: try (rewrite add_ptr_ushort by auto; reflexivity).
    rewrite sublist_same by lia. rewrite sublist_nil, map_nil, app_nil_r. apply derives_refl. }
  { Intros k. assert_PROP (isptr (p_head p)) as Hhp by entailer!.
    forward. rewrite sub_ptr_ushort by auto. rewrite offset_offset_val.
    replace (2 * k + -2) with (2 * (k - 1)) by lia.
    forward.
    assert (Hm : 0 <= Znth (k - 1) (d_head s) < 65536) by (apply (proj1 (Forall_Znth _ _) Hhr); lia).
    assert_PROP (offset_val (2 * (k - 1)) (p_head p) =
                 field_address (tarray tushort (d_hash_size s)) [ArraySubsc (k - 1)] (p_head p)) as Ha.
    { entailer!. rewrite field_address_offset by auto with field_compatible. simpl. f_equal. }
    forward.
    { rewrite slide_inv_read by lia. go_lower. apply prop_right. apply tc_val_tushort_repr. rep_lia. }
    rewrite slide_inv_read by lia.
    forward_if
      (PROP ()
       LOCAL (temp _t'3 (vi (slide_entry (d_w_size s) (Znth (k - 1) (d_head s))));
              temp _p (offset_val (2 * (k - 1)) (p_head p)); temp _n (vi k); temp _wsize (vi (d_w_size s));
              gvars gv; temp _s (p_s p))
       SEP (sh_rest s p gv;
          @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p);
          @data_at DCS.CS Ews (tarray tushort (d_hash_size s))
            (map vi (sublist 0 k (d_head s) ++ map (slide_entry (d_w_size s)) (sublist k (d_hash_size s) (d_head s))))
            (p_head p);
          @data_at DCS.CS Ews (tarray tushort (d_w_size s)) (map vi (d_prev s)) (p_prev p))).
    { forward. entailer!. unfold slide_entry. rewrite Z.geb_leb, (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    { forward. entailer!. unfold slide_entry. rewrite Z.geb_leb, (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
    assert (He := slide_entry_range (d_w_size s) _ ltac:(lia) Hm).
    forward.
    Exists (k - 1). entailer!.
    { f_equal. lia. }
    rewrite zext16_repr, Z.mod_small by lia. rewrite zext16_repr, Z.mod_small by lia.
    fold (vi (slide_entry (d_w_size s) (Znth (k - 1) (d_head s)))).
    rewrite slide_inv_step by lia. unfold data_at. apply derives_refl. }
  { Intros k. forward. forward. forward_if.
    { forward. Exists k. entailer!. replace (k + 1 - 1) with k in * by lia.
      split; [|reflexivity]. assert (k <> 0) by (intro; subst; apply H1; reflexivity). lia. }
    { forward. rewrite sub_repr in H1. replace (k + 1 - 1) with k in H1 by lia.
      assert (k = 0) by (apply repr_inj_unsigned in H1; rep_lia). subst k.
      entailer!. rewrite sublist_nil, sublist_same by lia. apply derives_refl. }
  }
  forward. forward. forward.
  forward_loop
    (EX k : Z,
     PROP (0 < k <= d_w_size s)
     LOCAL (temp _n (vi k); temp _p (offset_val (2 * k) (p_prev p)); temp _wsize (vi (d_w_size s));
            gvars gv; temp _s (p_s p))
     SEP (sh_rest s p gv;
          @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p);
          @data_at DCS.CS Ews (tarray tushort (d_hash_size s)) (map vi (map (slide_entry (d_w_size s)) (d_head s))) (p_head p);
          @data_at DCS.CS Ews (tarray tushort (d_w_size s))
            (map vi (sublist 0 k (d_prev s) ++ map (slide_entry (d_w_size s)) (sublist k (d_w_size s) (d_prev s))))
            (p_prev p)))
  continue:
    (EX k : Z,
     PROP (0 <= k < d_w_size s)
     LOCAL (temp _n (vi (k + 1)); temp _p (offset_val (2 * k) (p_prev p)); temp _wsize (vi (d_w_size s));
            gvars gv; temp _s (p_s p))
     SEP (sh_rest s p gv;
          @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p);
          @data_at DCS.CS Ews (tarray tushort (d_hash_size s)) (map vi (map (slide_entry (d_w_size s)) (d_head s))) (p_head p);
          @data_at DCS.CS Ews (tarray tushort (d_w_size s))
            (map vi (sublist 0 k (d_prev s) ++ map (slide_entry (d_w_size s)) (sublist k (d_w_size s) (d_prev s))))
            (p_prev p)))
  break:
    (PROP ()
     LOCAL (temp _wsize (vi (d_w_size s)); gvars gv; temp _s (p_s p))
     SEP (sh_rest s p gv;
          @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p);
          @data_at DCS.CS Ews (tarray tushort (d_hash_size s)) (map vi (map (slide_entry (d_w_size s)) (d_head s))) (p_head p);
          @data_at DCS.CS Ews (tarray tushort (d_w_size s)) (map vi (map (slide_entry (d_w_size s)) (d_prev s))) (p_prev p))).
  { Exists (d_w_size s). entailer!.
    all: try (rewrite add_ptr_ushort by auto; reflexivity).
    rewrite sublist_same by lia. rewrite sublist_nil, map_nil, app_nil_r. apply derives_refl. }
  { Intros k. assert_PROP (isptr (p_prev p)) as Hhp by entailer!.
    forward. rewrite sub_ptr_ushort by auto. rewrite offset_offset_val.
    replace (2 * k + -2) with (2 * (k - 1)) by lia.
    forward.
    assert (Hm : 0 <= Znth (k - 1) (d_prev s) < 65536) by (apply (proj1 (Forall_Znth _ _) Hpr); lia).
    assert_PROP (offset_val (2 * (k - 1)) (p_prev p) =
                 field_address (tarray tushort (d_w_size s)) [ArraySubsc (k - 1)] (p_prev p)) as Ha.
    { entailer!. rewrite field_address_offset by auto with field_compatible. simpl. f_equal. }
    forward.
    { rewrite slide_inv_read by lia. go_lower. apply prop_right. apply tc_val_tushort_repr. rep_lia. }
    rewrite slide_inv_read by lia.
    forward_if
      (PROP ()
       LOCAL (temp _t'6 (vi (slide_entry (d_w_size s) (Znth (k - 1) (d_prev s))));
              temp _p (offset_val (2 * (k - 1)) (p_prev p)); temp _n (vi k); temp _wsize (vi (d_w_size s));
              gvars gv; temp _s (p_s p))
       SEP (sh_rest s p gv;
          @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p);
          @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p);
          @data_at DCS.CS Ews (tarray tushort (d_hash_size s)) (map vi (map (slide_entry (d_w_size s)) (d_head s))) (p_head p);
          @data_at DCS.CS Ews (tarray tushort (d_w_size s))
            (map vi (sublist 0 k (d_prev s) ++ map (slide_entry (d_w_size s)) (sublist k (d_w_size s) (d_prev s))))
            (p_prev p))).
    { forward. entailer!. unfold slide_entry. rewrite Z.geb_leb, (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    { forward. entailer!. unfold slide_entry. rewrite Z.geb_leb, (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
    assert (He := slide_entry_range (d_w_size s) _ ltac:(lia) Hm).
    forward.
    Exists (k - 1). entailer!.
    { f_equal. lia. }
    rewrite zext16_repr, Z.mod_small by lia. rewrite zext16_repr, Z.mod_small by lia.
    fold (vi (slide_entry (d_w_size s) (Znth (k - 1) (d_prev s)))).
    rewrite slide_inv_step by lia. unfold data_at. apply derives_refl. }
  { Intros k. forward. forward. forward_if.
    { forward. Exists k. entailer!. replace (k + 1 - 1) with k in * by lia.
      split; [|reflexivity]. assert (k <> 0) by (intro; subst; apply H1; reflexivity). lia. }
    { forward. rewrite sub_repr in H1. replace (k + 1 - 1) with k in H1 by lia.
      assert (k = 0) by (apply repr_inj_unsigned in H1; rep_lia). subst k.
      entailer!. rewrite sublist_nil, sublist_same by lia. apply derives_refl. }
  }
  forward.
  rewrite dstate_at_open, sh_rest_slide.
  cbn [d_w_size d_hash_size d_head d_prev d_slid set_d_slid set_d_prev set_d_head].
  rewrite !Zlength_map, Hhl, Hpl.
  entailer!.
  apply ranges_slide; auto; lia.
Qed.
