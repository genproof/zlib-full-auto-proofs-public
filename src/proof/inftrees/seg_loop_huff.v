(* Part sl_huff of the main loop of inflate_table (seg_loop_defs.v). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Import Zlib.proof.inftrees.seg_loop_defs.

#[local] Existing Instance Inftrees.CS.

Lemma sl_huff_shl L : 1 <= L <= 15 ->
  Int.shl (Int.repr 1) (Int.sub (Int.repr L) (Int.repr 1)) = Int.repr (Z.shiftl 1 (L - 1)).
Proof.
intros. unfold Int.shl, Int.sub. rewrite !(Int.unsigned_repr 1) by rep_lia.
rewrite (Int.unsigned_repr L) by rep_lia. rewrite (Int.unsigned_repr (L - 1)) by rep_lia. reflexivity.
Qed.

Lemma sl_huff_i0 L : 1 <= L <= 15 -> Z.shiftl 1 (L - 1) = 2 ^ (L - 1).
Proof. intros. rewrite Z.shiftl_1_l. reflexivity. Qed.

Lemma sl_huff_x_range L j : 1 <= L <= 15 -> 0 <= j -> 0 <= Z.shiftr (Z.shiftl 1 (L - 1)) j < 2 ^ 15.
Proof.
intros. rewrite sl_huff_i0 by lia. rewrite Z.shiftr_div_pow2 by lia.
assert (0 < 2 ^ (L - 1)) by (apply Z.pow_pos_nonneg; lia).
assert (2 ^ (L - 1) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia).
assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
split. apply Z.div_pos; lia.
apply Z.le_lt_trans with (2 ^ (L - 1)). apply Z.div_le_upper_bound; nia. lia.
Qed.

Lemma sl_huff_x_zero L j : 1 <= L <= 15 -> L <= j -> Z.shiftr (Z.shiftl 1 (L - 1)) j = 0.
Proof.
intros. rewrite sl_huff_i0 by lia. rewrite Z.shiftr_div_pow2 by lia.
apply Z.div_small. split. apply Z.pow_nonneg; lia. apply Z.pow_lt_mono_r; lia.
Qed.

Lemma sl_huff_and a b : 0 <= a < 2 ^ 15 -> 0 <= b < 2 ^ 15 ->
  Int.and (Int.repr a) (Int.repr b) = Int.repr (Z.land a b).
Proof. intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma sl_huff_land_range a b : 0 <= a < 2 ^ 15 -> 0 <= b -> 0 <= Z.land a b < 2 ^ 15.
Proof.
intros. assert (0 <= Z.land a b) by (apply Z.land_nonneg; lia). split; auto.
destruct (Z.eq_dec (Z.land a b) 0) as [E | E]; [rewrite E; cbn; lia | ].
apply (proj2 (Z.log2_lt_pow2 (Z.land a b) 15 ltac:(lia))).
pose proof (Z.log2_land a b ltac:(lia) ltac:(lia)).
destruct (Z.eq_dec a 0) as [-> | ]; [rewrite Z.land_0_l in E; congruence | ].
assert (Z.log2 a < 15) by (apply (proj1 (Z.log2_lt_pow2 a 15 ltac:(lia))); lia).
lia.
Qed.

Lemma sl_huff_shru1 x : 0 <= x < 2 ^ 15 ->
  Int.shru (Int.repr x) (Int.repr 1) = Int.repr (Z.shiftr x 1).
Proof. intros. unfold Int.shru. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma sl_huff_step h L j : 1 <= L <= 15 -> 0 <= j <= L ->
  Z.land h (Z.shiftr (Z.shiftl 1 (L - 1)) j) <> 0 ->
  j + 1 <= L /\
  bincr_loop (Z.to_nat (16 - j)) h (Z.shiftr (Z.shiftl 1 (L - 1)) j) =
  bincr_loop (Z.to_nat (16 - (j + 1))) h (Z.shiftr (Z.shiftl 1 (L - 1)) (j + 1)).
Proof.
intros HL HJ HA.
assert (j + 1 <= L).
{ destruct (Z.eq_dec j L); [ | lia]. subst. rewrite sl_huff_x_zero in HA by lia.
  rewrite Z.land_0_r in HA. congruence. }
split; auto.
replace (Z.to_nat (16 - j)) with (S (Z.to_nat (16 - (j + 1)))) by lia.
cbn [bincr_loop]. rewrite (proj2 (Z.eqb_neq _ _) HA).
rewrite Z.shiftr_shiftr by lia. reflexivity.
Qed.

Lemma sl_huff_exit h x n : (0 < n)%nat -> Z.land h x = 0 -> bincr_loop n h x = x.
Proof. intros. destruct n; [lia | ]. cbn [bincr_loop]. rewrite H0. reflexivity. Qed.

Lemma sl_huff_final h x : 0 <= h < 2 ^ 15 -> 0 < x < 2 ^ 15 ->
  Int.add (Int.and (Int.repr h) (Int.sub (Int.repr x) (Int.repr 1))) (Int.repr x) =
  Int.repr (Z.land h (x - 1) + x).
Proof.
intros. rewrite Int.sub_signed. rewrite !Int.signed_repr by rep_lia.
rewrite sl_huff_and by lia. apply add_repr.
Qed.

Lemma sl_huff_ok : loop_facts -> sl_huff_stmt.
Proof.
intros LF Espec X s WF.
destruct LF as (SSO & ROO & RKO & _).
pose proof WF as WF'. unfold it_wf in WF'.
destruct WF' as (SHg & SHl & SH & IN & OLD & CAP).
unfold SL_rep, SL_huff, sl_props, sl_locs, sl_K, sl_sep, params_locs.
unfold Delta_it. simplify_func_tycontext.
unfold sl_huff.
abbreviate_semax.
Intros.
assert (AO: acc_ok (c_type X) (c_lens X) (c_req X) (Zlength (c_old X))) by (unfold acc_ok; auto).
destruct (RKO _ _ _ _ _ _ AO H2) as (IT & SK).
destruct IT as (IS & IL & ID & IC & IH & _).
assert (HH: 0 <= s_huff s < 2 ^ 15).
{ rewrite Z.shiftl_1_l in IH. assert (2 ^ s_len s <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). lia. }
set (i0 := Z.shiftl 1 (s_len s - 1)).
forward.
{ entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
rewrite sl_huff_shl by lia. fold i0.
match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
forward_while (EX j: Z,
  PROPx [0 <= j <= s_len s;
        bincr_loop 16 (s_huff s) i0 = bincr_loop (Z.to_nat (16 - j)) (s_huff s) (Z.shiftr i0 j)]
  (LOCALx (temp _incr (Vint (Int.repr (Z.shiftr i0 j))) :: Q) (SEPx R)))
end.
- Exists 0. entailer!.
- entailer!.
- assert (XR: 0 <= Z.shiftr i0 j < 2 ^ 15) by (apply sl_huff_x_range; lia).
  rewrite !Int.unsigned_repr in HRE' by rep_lia.
  destruct (sl_huff_step (s_huff s) (s_len s) j IL H3 HRE') as (J1 & ST).
  fold i0 in ST.
  forward.
  Exists (j + 1). entailer!.
  rewrite sl_huff_shru1 by lia. rewrite Z.shiftr_shiftr by lia. reflexivity.
- assert (XR: 0 <= Z.shiftr i0 j < 2 ^ 15) by (apply sl_huff_x_range; lia).
  assert (LR: 0 <= Z.land (s_huff s) (Z.shiftr i0 j) < 2 ^ 15) by (apply sl_huff_land_range; lia).
  apply (f_equal Int.unsigned) in HRE. rewrite Int.unsigned_repr in HRE by rep_lia.
  change (Int.unsigned Int.zero) with 0 in HRE.
  assert (NH: st_huff' s = if Z.shiftr i0 j =? 0 then 0
                           else Z.land (s_huff s) (Z.shiftr i0 j - 1) + Z.shiftr i0 j).
  { unfold st_huff', next_huff. fold i0. rewrite H4. rewrite sl_huff_exit by (auto; lia). reflexivity. }
  match goal with |- semax _ (PROPx _ (LOCALx (?a :: ?b :: _ :: ?Q) (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (a :: b :: temp _huff (Vint (Int.repr (st_huff' s))) :: Q) (SEPx R)))
  end.
  + assert (XN: Z.shiftr i0 j <> 0) by (intro E; rewrite E in H5; contradiction).
    forward. forward.
    entailer!.
    rewrite NH, (proj2 (Z.eqb_neq _ _) XN).
    first [reflexivity | rewrite sl_huff_final by lia; reflexivity].
  + forward.
    entailer!.
    rewrite NH, H5. reflexivity.
  + forward.
    destruct (sl_R _) as [rn rb rc rr]; cbv iota beta; cbn [RA_normal].
    entailer!.
Qed.
