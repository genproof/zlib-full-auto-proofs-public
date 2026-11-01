(** * fill_window, fragment S_high (FWKit.v) against its model step. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.FWKit.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** Opening the window for memset of [n] bytes at [lo]: the slice, and the way back to the written window. *)
Lemma win_zero_open (b b' : mbuf) (lo n : Z) (pw : val) :
  mb_ok b -> 0 <= n -> mb_write b lo (repeat 0 (Z.to_nat n)) = Some b' ->
  @data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val b))) (mb_vals b) pw |--
  @data_at_ DCS.CS Ews (tarray tuchar n) (offset_val lo pw) *
  (@data_at DCS.CS Ews (tarray tuchar n) (Libc.byte_vals (repeat (0 mod 256) (Z.to_nat n))) (offset_val lo pw) -*
   @data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val b'))) (mb_vals b') pw).
Proof.
  intros [Hl Hd] Hn Hw.
  destruct (mb_vals_write _ _ _ _ Hl Hw) as (Hv & Hlen & _ & Hlo & Hhi).
  rewrite Zlength_repeat in Hhi, Hv by lia.
  pose proof (Zlength_mb_vals b Hl) as HL.
  set (L := Zlength (mb_val b)) in *.
  sep_apply (data_at_local_facts Ews (tarray tuchar L) (mb_vals b) pw). Intros.
  rewrite (split3_data_at_Tarray_tuchar Ews L lo (lo + n) (mb_vals b) pw) by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  replace (nested_field_offset (Tarray tuchar L noattr) (SUB lo)) with lo
    by (cbv [nested_field_offset nested_field_rec]; simpl; lia).
  replace (nested_field_offset (Tarray tuchar L noattr) (SUB (lo + n))) with (lo + n)
    by (cbv [nested_field_offset nested_field_rec]; simpl; lia).
  replace (lo + n - lo) with n by lia.
  sep_apply (data_at_data_at_ Ews (tarray tuchar n) (sublist lo (lo + n) (mb_vals b)) (offset_val lo pw)).
  cancel. apply (proj1 (wand_sepcon_adjoint _ _ _)).
  rewrite Hlen, Hv.
  rewrite (split3_data_at_Tarray_tuchar Ews L lo (lo + n)
     (sublist 0 lo (mb_vals b) ++ map vi (repeat 0 (Z.to_nat n)) ++ sublist (lo + n) L (mb_vals b)) pw).
  2: lia. 2: lia.
  2: { rewrite !Zlength_app, Zlength_map, Zlength_repeat, !Zlength_sublist by lia. lia. }
  rewrite !field_address0_offset by auto with field_compatible.
  replace (nested_field_offset (Tarray tuchar L noattr) (SUB lo)) with lo
    by (cbv [nested_field_offset nested_field_rec]; simpl; lia).
  replace (nested_field_offset (Tarray tuchar L noattr) (SUB (lo + n))) with (lo + n)
    by (cbv [nested_field_offset nested_field_rec]; simpl; lia).
  replace (lo + n - lo) with n by lia.
  autorewrite with sublist.
  replace (L - lo - n + (lo + n)) with L by lia.
  unfold Libc.byte_vals. rewrite map_repeat. change (0 mod 256) with 0.
  cancel.
Qed.

Lemma ltu64_repr a b : 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt a b); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma repr_u64 x : Int64.repr (u64 x) = Int64.repr x.
Proof.
  unfold u64. change 18446744073709551616 with Int64.modulus.
  rewrite <- Int64.unsigned_repr_eq. apply Int64.repr_unsigned.
Qed.

Lemma u64_range x : 0 <= u64 x <= Int64.max_unsigned.
Proof. unfold u64. pose proof (Z.mod_pos_bound x 18446744073709551616). rep_lia. Qed.

Lemma ranges_high s win hw :
  dstate_ranges s -> mb_ok win -> Zlength (mb_val win) = Zlength (mb_val (d_window s)) ->
  0 <= hw <= Int64.max_unsigned -> dstate_ranges (set_d_high_water (set_d_window s win) hw).
Proof.
  intros R W L H. unfold dstate_ranges in *. cbn. rewrite L. unfold u64_ok. tauto.
Qed.

Lemma win_zero_ok b lo n b' :
  mb_ok b -> 0 <= n -> mb_write b lo (repeat 0 (Z.to_nat n)) = Some b' ->
  mb_ok b' /\ Zlength (mb_val b') = Zlength (mb_val b) /\ 0 <= lo /\ lo + n <= Zlength (mb_val b).
Proof.
  intros Hok Hn Hw. split.
  - eapply mb_ok_write; [exact Hok| |exact Hw]. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
  - destruct Hok as [Hl _]. destruct (mb_vals_write _ _ _ _ Hl Hw) as (_ & Hlen & _ & Hlo & Hhi).
    rewrite Zlength_repeat in Hhi by lia. auto.
Qed.

(** The final entailment: the window written and high_water set. *)
Ltac close_high s win hw :=
  let s' := fresh "s'" in
  set (s' := set_d_high_water (set_d_window s win) hw);
  change (hash_at s' ?p) with (hash_at s p);
  change (cfg_at s' ?p) with (cfg_at s p);
  change (stat_at s' ?p) with (stat_at s p);
  change (d_trm s') with (d_trm s);
  unfold s'; cbn [set_d_high_water set_d_window d_window_size d_w_size d_w_bits d_w_mask d_high_water d_window
    d_block_start d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead
    d_prev_length d_insert d_slid].

Ltac drop_init L :=
  match L with
  | temp _init _ :: ?L' => constr:(L')
  | ?x :: ?L' => let r := drop_init L' in constr:(x :: r)
  end.

(** [forward_if] over [if (..) init = ..;] with the join point [init = v]. *)
Ltac forward_if_init v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    let L' := drop_init L in forward_if (PROPx P (LOCALx (temp _init (vl v) :: L') (SEPx S))) end.

Lemma fw_high : fw_high_triple.
Proof.
  unfold fw_high_triple; intros. show_fw_stmt. unfold dfull_in, dstate_at, win_at, match_at. Intros.
  pose proof H3 as HR. unfold dstate_ranges in HR.
  destruct HR as (_&_&_&_&_&_&_&_&_&_&Hwin&HwinL&Hws&_&_&_&_&_&_&_&_&_&_&_&_&_&Hss&_&Hla&_&_&_&_&_&_&Hhw&_).
  unfold u32_ok, u64_ok in *.
  forward. forward.
  forward_if.
  - try (rewrite ltu64_repr in H4 by rep_lia; apply Z.ltb_lt in H4).
    unfold c_fw_high_water in H. rewrite (proj2 (Z.ltb_lt _ _) H4) in H. cbv zeta in H.
    forward. forward. forward.
    set (curr := d_strstart s + d_lookahead s) in *.
    assert (Ecurr : Vlong (Int64.add (Int64.repr (Int.unsigned (Int.repr (d_strstart s))))
                      (Int64.repr (Int.unsigned (Int.repr (d_lookahead s))))) = vl curr).
    { rewrite !Int.unsigned_repr by rep_lia. unfold vl. rewrite add64_repr. reflexivity. }
    rewrite Ecurr; clear Ecurr.
    forward.
    forward_if.
    + try (rewrite ltu64_repr in H5 by rep_lia; apply Z.ltb_lt in H5).
      rewrite (proj2 (Z.ltb_lt _ _) H5) in H.
      assert (Hcu : 0 <= curr <= 2 * Int.max_unsigned) by (unfold curr; lia).
      forward. forward.
      set (init0 := u64 (d_window_size s - curr)) in *.
      set (init := if init0 >? WIN_INIT then WIN_INIT else init0) in *.
      assert (Hi0 : 0 <= init0 <= Int64.max_unsigned) by apply u64_range.
      assert (Hi : 0 <= init <= 258) by (subst init; destruct (init0 >? WIN_INIT) eqn:E;
        [cbv [WIN_INIT MAX_MATCH]; lia | rewrite Z.gtb_ltb in E; apply Z.ltb_ge in E; cbv [WIN_INIT MAX_MATCH] in E; lia]).
      destruct (mb_write (d_window s) curr (repeat 0 (Z.to_nat init))) as [win|] eqn:Hwr; [|discriminate].
      cbn in H. inversion H; subst s'; clear H.
      rewrite sub64_repr, <- repr_u64. fold init0.
      match goal with |- semax _ (PROPx ?P (LOCALx (temp _init _ :: ?L) (SEPx ?S))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _init (vl init) :: L) (SEPx S))) end.
      { rewrite !Int64.unsigned_repr in H by rep_lia. forward. entailer!.
        unfold init. rewrite Z.gtb_ltb. cbv [WIN_INIT MAX_MATCH]. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
        reflexivity. }
      { rewrite !Int64.unsigned_repr in H by rep_lia. forward. entailer!.
        unfold init. rewrite Z.gtb_ltb. cbv [WIN_INIT MAX_MATCH]. rewrite (proj2 (Z.ltb_ge _ _)) by lia.
        reflexivity. }
      destruct (win_zero_ok _ _ _ _ Hwin (proj1 Hi) Hwr) as (Hwok & Hwlen & _ & Hhi).
      forward.
      sep_apply (win_zero_open (d_window s) win curr init (p_window p) Hwin (proj1 Hi) Hwr). Intros.
      assert_PROP (isptr (p_window p)) as Hpw by entailer!.
      forward_call (Ews, offset_val curr (p_window p), init, 0).
      1: entailer!.
      1: { destruct (p_window p); try contradiction. unfold vl. cbn. f_equal. f_equal.
           rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
           rewrite Int64.unsigned_repr by rep_lia. reflexivity.
           f_equal. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
           rewrite Int.unsigned_repr by rep_lia. reflexivity. }
      sep_apply modus_ponens_wand.
      forward.
      rewrite add64_repr. fold (vl (curr + init)).
      assert (Hr' : dstate_ranges (set_d_high_water (set_d_window s win) (curr + init)))
        by (apply ranges_high; auto; rep_lia).
      close_high s win (curr + init).
      entailer!.
    + rewrite (proj2 (Z.ltb_ge _ _)) in H by lia.
      assert (Hcu : 0 <= curr <= 2 * Int.max_unsigned) by (unfold curr; lia).
      cbv [WIN_INIT MAX_MATCH] in H.
      forward.
      forward_if.
      * rewrite add64_repr, !Int64.unsigned_repr in H6 by rep_lia.
        rewrite (proj2 (Z.ltb_lt _ _)) in H by lia.
        forward. forward.
        change (Int.signed (Int.repr 258)) with 258.
        rewrite add64_repr, sub64_repr, <- repr_u64.
        set (a := u64 (curr + 258 - d_high_water s)) in *.
        set (b := u64 (d_window_size s - d_high_water s)) in *.
        assert (Ea : a = curr + 258 - d_high_water s) by (unfold a, u64; apply Z.mod_small; rep_lia).
        assert (Eb : b = d_window_size s - d_high_water s) by (unfold b, u64; apply Z.mod_small; rep_lia).
        set (init := if a >? b then b else a) in *.
        assert (Hi : 0 < init <= 258) by (unfold init; destruct (a >? b) eqn:E;
          [rewrite Z.gtb_ltb in E; apply Z.ltb_lt in E | rewrite Z.gtb_ltb in E; apply Z.ltb_ge in E]; lia).
        replace (u32 init) with init in H by (unfold u32; rewrite Z.mod_small; rep_lia).
        replace (u64 (d_high_water s + init)) with (d_high_water s + init) in H
          by (unfold u64; rewrite Z.mod_small; rep_lia).
        destruct (mb_write (d_window s) (d_high_water s) (repeat 0 (Z.to_nat init))) as [win|] eqn:Hwr;
          [|discriminate].
        cbn in H. inversion H; subst s'; clear H.
        forward. forward.
        forward_if_init init.
        { rewrite sub64_repr, ltu64_repr in H by rep_lia. apply Z.ltb_lt in H.
          forward. forward. forward. entailer!.
          unfold init. rewrite Z.gtb_ltb, (proj2 (Z.ltb_lt _ _)) by lia. rewrite Eb. reflexivity. }
        { rewrite sub64_repr, ltu64_repr in H by rep_lia. apply Z.ltb_ge in H.
          forward. entailer!.
          unfold init. rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
        destruct (win_zero_ok (d_window s) (d_high_water s) init win Hwin ltac:(lia) Hwr) as (Hwok & Hwlen & _ & Hhi).
        forward. forward.
        sep_apply (win_zero_open (d_window s) win (d_high_water s) init (p_window p) Hwin ltac:(lia) Hwr). Intros.
        assert_PROP (isptr (p_window p)) as Hpw by entailer!.
        forward_call (Ews, offset_val (d_high_water s) (p_window p), init, 0).
        1: entailer!.
        1: { destruct (p_window p); try contradiction. unfold vl. cbn. f_equal. f_equal.
             rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
             rewrite Int64.unsigned_repr by rep_lia. reflexivity.
             f_equal. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
             rewrite Int.unsigned_repr by rep_lia. reflexivity. }
        sep_apply modus_ponens_wand.
        forward. forward.
        rewrite add64_repr. fold (vl (d_high_water s + init)).
        assert (Hr' : dstate_ranges (set_d_high_water (set_d_window s win) (d_high_water s + init)))
          by (apply ranges_high; auto; rep_lia).
        close_high s win (d_high_water s + init).
        entailer!.
      * rewrite add64_repr, !Int64.unsigned_repr in H6 by rep_lia.
        rewrite (proj2 (Z.ltb_ge _ _)) in H by lia.
        inversion H; subst s'; clear H.
        forward. entailer!.
  - unfold c_fw_high_water in H. rewrite (proj2 (Z.ltb_ge _ _)) in H by lia.
    inversion H; subst s'; clear H.
    forward. entailer!.
Qed.
