(* Body proofs of harness/deflate_ref.h helpers: see DRefSpec.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.

(* ---------------------------------------------------------------------------------------------- *)
(* Pure facts on pack                                                                             *)

Lemma sublist_clamp {A} lo hi (l: list A) :
  0 <= lo -> Zlength l <= hi -> sublist lo hi l = sublist lo (Zlength l) l.
Proof.
  intros Hlo Hhi. unfold sublist.
  rewrite (firstn_all2 (n := Z.to_nat hi)), (firstn_all2 (n := Z.to_nat (Zlength l))); auto;
    rewrite Zlength_correct in *; lia.
Qed.

Lemma div8_eq a q : 8 * q <= a < 8 * q + 8 -> a / 8 = q.
Proof. intros. symmetry. apply Z.div_unique with (a - 8 * q); lia. Qed.

Lemma Zlength_sublist_le {A} lo hi (l: list A) :
  0 <= lo <= hi -> Zlength (sublist lo hi l) <= hi - lo.
Proof.
  intros H. destruct (zle hi (Zlength l)).
  - rewrite Zlength_sublist by lia. lia.
  - rewrite sublist_clamp by lia. destruct (zle lo (Zlength l)).
    + rewrite Zlength_sublist by lia. lia.
    + rewrite sublist_over by lia. rewrite Zlength_nil. lia.
Qed.

Lemma bval_app l1 l2 : bval (l1 ++ l2) = bval l1 + 2 ^ Zlength l1 * bval l2.
Proof.
  induction l1 as [|b r IH]; simpl.
  - rewrite ?Zlength_nil. simpl. lia.
  - rewrite IH, Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg r); lia). lia.
Qed.

Lemma bval_range l : 0 <= bval l < 2 ^ Zlength l.
Proof.
  induction l as [|b r IH]; simpl.
  - rewrite ?Zlength_nil. simpl. lia.
  - rewrite Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg r); lia).
    destruct b; simpl; lia.
Qed.

Lemma bval_zeros p : bval (zeros p) = 0.
Proof. unfold zeros. induction (Z.to_nat p); simpl; auto. rewrite IHn. lia. Qed.

Lemma Zlength_zeros p : 0 <= p -> Zlength (zeros p) = p.
Proof. intros. unfold zeros. rewrite Zlength_correct, repeat_length. lia. Qed.

Lemma Zlength_pack bs : Zlength (pack bs) = (Zlength bs + 7) / 8.
Proof.
  unfold pack. rewrite Zlength_map, Zlength_correct, seq_length.
  pose proof (Zlength_nonneg bs). rewrite Z2Nat.id; auto. apply Z.div_pos; lia.
Qed.

Lemma Znth_pack bs k : 0 <= k < (Zlength bs + 7) / 8 ->
  Znth k (pack bs) = bval (sublist (8 * k) (8 * k + 8) bs).
Proof.
  intros Hk. unfold pack.
  rewrite Znth_map by (rewrite Zlength_correct, seq_length; lia).
  f_equal. rewrite <- nth_Znth by (rewrite Zlength_correct, seq_length; lia).
  rewrite seq_nth by lia. simpl. rewrite Z2Nat.id by lia. auto.
Qed.

Lemma bits_le_length v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof. intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma pack_bytes bs : Forall (fun x => 0 <= x < 256) (pack bs).
Proof.
  apply Forall_Znth. intros k Hk. rewrite Zlength_pack in Hk. rewrite Znth_pack by auto.
  pose proof (bval_range (sublist (8 * k) (8 * k + 8) bs)).
  assert (Zlength (sublist (8 * k) (8 * k + 8) bs) <= 8).
  { pose proof (Zlength_sublist_le (8 * k) (8 * k + 8) bs). lia. }
  assert (2 ^ Zlength (sublist (8 * k) (8 * k + 8) bs) <= 2 ^ 8) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 8) with 256 in *. lia.
Qed.

(* appending one bit *)
Lemma pack_snoc_new B b : Zlength B mod 8 = 0 -> pack (B ++ [b]) = pack B ++ [Z.b2z b].
Proof.
  intros Hm. pose proof (Zlength_nonneg B) as HB.
  pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)) as Hdm.
  assert (Hl: (Zlength B + 7) / 8 = Zlength B / 8) by (apply div8_eq; lia).
  assert (Hl': (Zlength (B ++ [b]) + 7) / 8 = Zlength B / 8 + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. apply div8_eq; lia. }
  apply Znth_eq_ext.
  - rewrite Zlength_app, !Zlength_pack, Hl, Hl', Zlength_cons, Zlength_nil. reflexivity.
  - intros k Hk. rewrite Zlength_pack, Hl' in Hk.
    rewrite Znth_pack by (rewrite Hl'; auto).
    destruct (zlt k (Zlength B / 8)).
    + rewrite app_Znth1 by (rewrite Zlength_pack, Hl; lia).
      rewrite Znth_pack by (rewrite Hl; lia).
      rewrite sublist_app1; auto; lia.
    + rewrite app_Znth2 by (rewrite Zlength_pack, Hl; lia).
      rewrite Zlength_pack, Hl. replace (k - Zlength B / 8) with 0 by lia. rewrite Znth_0_cons.
      assert (8 * k = Zlength B) by lia.
      rewrite sublist_clamp by (rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia).
      rewrite H, Zlength_app, sublist_app2 by lia. rewrite Z.sub_diag.
      replace (Zlength B + Zlength [b] - Zlength B) with 1 by (rewrite Zlength_cons, Zlength_nil; lia).
      rewrite sublist_one by (rewrite ?Zlength_cons, ?Zlength_nil; lia). rewrite Znth_0_cons. simpl. lia.
Qed.

Lemma pending_byte B : Zlength B mod 8 <> 0 ->
  Zlength (pack B) = Zlength B / 8 + 1 /\
  Znth (Zlength B / 8) (pack B) = bval (sublist (8 * (Zlength B / 8)) (Zlength B) B) /\
  Zlength (sublist (8 * (Zlength B / 8)) (Zlength B) B) = Zlength B mod 8.
Proof.
  intros Hm. pose proof (Zlength_nonneg B) as HB.
  pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (Zlength B) 8 ltac:(lia)) as Hmb.
  assert (Hl: (Zlength B + 7) / 8 = Zlength B / 8 + 1) by (apply div8_eq; lia).
  split; [|split].
  - rewrite Zlength_pack. auto.
  - rewrite Znth_pack by lia. f_equal. apply sublist_clamp; lia.
  - rewrite Zlength_sublist by lia. lia.
Qed.

Lemma pack_snoc B b :
  pack (B ++ [b]) = sublist 0 (Zlength B / 8) (pack B) ++
    [(if Zlength B mod 8 =? 0 then 0 else Znth (Zlength B / 8) (pack B)) + Z.b2z b * 2 ^ (Zlength B mod 8)].
Proof.
  pose proof (Zlength_nonneg B) as HB.
  pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (Zlength B) 8 ltac:(lia)) as Hmb.
  destruct (Z.eqb_spec (Zlength B mod 8) 0) as [Hm|Hm].
  - rewrite pack_snoc_new by auto. rewrite Hm. change (2 ^ 0) with 1.
    rewrite sublist_same; [f_equal; f_equal; lia | lia |].
    rewrite Zlength_pack. symmetry. apply div8_eq; lia.
  - destruct (pending_byte B Hm) as (Hlp & Hq & Hlq).
    assert (Hl': (Zlength (B ++ [b]) + 7) / 8 = Zlength B / 8 + 1).
    { rewrite Zlength_app, Zlength_cons, Zlength_nil. apply div8_eq; lia. }
    apply Znth_eq_ext.
    + rewrite Zlength_app, Zlength_pack, Hl', Zlength_sublist by lia.
      rewrite Zlength_cons, Zlength_nil. lia.
    + intros k Hk. rewrite Zlength_pack, Hl' in Hk.
      rewrite Znth_pack by (rewrite Hl'; auto).
      destruct (zlt k (Zlength B / 8)).
      * rewrite app_Znth1 by (rewrite Zlength_sublist; lia).
        rewrite Znth_sublist by lia. rewrite Z.add_0_r.
        rewrite Znth_pack by (rewrite <- Zlength_pack, Hlp; lia). rewrite sublist_app1; auto; lia.
      * rewrite app_Znth2 by (rewrite Zlength_sublist; lia).
        rewrite Zlength_sublist by lia. replace (k - (Zlength B / 8 - 0)) with 0 by lia.
        rewrite Znth_0_cons. replace k with (Zlength B / 8) by lia. rewrite Hq.
        rewrite sublist_clamp by (rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia).
        rewrite sublist_app by (rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia).
        rewrite Zlength_app, Zlength_cons, Zlength_nil.
        rewrite Z.min_l by lia. rewrite Z.min_r by lia. rewrite Z.max_r by lia.
        replace (Zlength B + Z.succ 0 - Zlength B) with 1 by lia.
        replace (Z.max 1 0) with 1 by lia.
        rewrite (sublist_same 0 1) by reflexivity.
        rewrite bval_app, Hlq. simpl. lia.
Qed.

Lemma pending_range B : 0 <= (if Zlength B mod 8 =? 0 then 0 else Znth (Zlength B / 8) (pack B))
  < 2 ^ (Zlength B mod 8).
Proof.
  destruct (Z.eqb_spec (Zlength B mod 8) 0) as [Hm|Hm].
  - rewrite Hm. simpl. lia.
  - destruct (pending_byte B Hm) as (Hlp & Hq & Hlq). rewrite Hq, <- Hlq. apply bval_range.
Qed.

Lemma lor_pow2 x r : 0 <= r -> 0 <= x < 2 ^ r -> Z.lor x (2 ^ r) = x + 2 ^ r.
Proof.
  intros Hr Hx.
  assert (Hl: Z.land x (2 ^ r) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb_spec r n); [subst|apply andb_false_r].
    rewrite <- (Z.mod_small x (2 ^ n)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by auto. reflexivity.
Qed.

Lemma or_bit x b r : 0 <= r < 8 -> 0 <= x < 2 ^ r -> 0 <= b <= Int.max_unsigned ->
  Int.zero_ext 8 (Int.or (Int.repr x) (Int.shl (Int.and (Int.repr b) (Int.repr 1)) (Int.repr r))) =
  Int.repr (x + Z.b2z (Z.odd b) * 2 ^ r).
Proof.
  intros Hr Hx Hb.
  assert (H2r: 2 ^ r <= 128) by (change 128 with (2 ^ 7); apply Z.pow_le_mono_r; lia).
  assert (Hand: Int.and (Int.repr b) (Int.repr 1) = Int.repr (Z.b2z (Z.odd b))).
  { change (Int.repr 1) with (Int.sub (Int.repr 2) Int.one).
    rewrite <- (Int.modu_and _ _ (Int.repr 1)) by reflexivity.
    unfold Int.modu. rewrite (Int.unsigned_repr 2) by rep_lia.
    f_equal. rewrite Zmod_odd, Int.unsigned_repr by lia. destruct (Z.odd b); reflexivity. }
  rewrite Hand, Int.shl_mul_two_p. unfold Int.mul, Int.or.
  rewrite (Int.unsigned_repr r), two_p_equiv by rep_lia.
  assert (Hc: 0 <= Z.b2z (Z.odd b) <= 1) by (destruct (Z.odd b); simpl; lia).
  rewrite (Int.unsigned_repr (Z.b2z _)), (Int.unsigned_repr (2 ^ r)) by rep_lia.
  rewrite (Int.unsigned_repr (_ * _)) by (split; [lia|]; assert (Z.b2z (Z.odd b) * 2 ^ r <= 128) by nia; rep_lia).
  rewrite (Int.unsigned_repr x) by rep_lia.
  assert (Hlor: Z.lor x (Z.b2z (Z.odd b) * 2 ^ r) = x + Z.b2z (Z.odd b) * 2 ^ r).
  { destruct (Z.odd b); simpl.
    - rewrite Z.mul_1_l. apply lor_pow2; lia.
    - rewrite Z.lor_0_r. lia. }
  rewrite Hlor.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)). rewrite Int.zero_ext_mod by (cbn; lia).
  assert (x + Z.b2z (Z.odd b) * 2 ^ r < 256) by nia.
  rewrite Int.unsigned_repr by rep_lia. rewrite two_p_equiv, Z.mod_small by (cbn; lia). reflexivity.
Qed.

Lemma bytes_ok_upd P y q cap (contents: list val) :
  Zlength contents = cap -> 0 <= q < cap -> Zlength P = q -> sublist 0 q contents = Bytes.bytes_rep P ->
  sublist 0 (Zlength (P ++ [y])) (upd_Znth q contents (Vint (Int.repr y))) = Bytes.bytes_rep (P ++ [y]).
Proof.
  intros Hl Hq HP Hs. unfold Bytes.bytes_rep in *. rewrite map_app. simpl.
  rewrite <- Hs. list_solve.
Qed.

Lemma pack_nil : pack [] = [].
Proof. reflexivity. Qed.

Lemma pack_app_aligned B C : Zlength B mod 8 = 0 -> pack (B ++ C) = pack B ++ pack C.
Proof.
  intros Hm. pose proof (Zlength_nonneg B) as HB.
  pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)) as Hdm.
  assert (HpB: Zlength (pack B) = Zlength B / 8) by (rewrite Zlength_pack; apply div8_eq; lia).
  induction C as [|c C IH] using rev_ind.
  - rewrite app_nil_r, pack_nil, app_nil_r. reflexivity.
  - pose proof (Zlength_nonneg C) as HC.
    pose proof (Z.div_mod (Zlength C) 8 ltac:(lia)) as Hdc.
    pose proof (Z.mod_pos_bound (Zlength C) 8 ltac:(lia)) as Hmc.
    assert (HpC: Zlength C / 8 <= Zlength (pack C)) by (rewrite Zlength_pack; apply Z.div_le_mono; lia).
    rewrite app_assoc, !pack_snoc, IH.
    assert (Hd: Zlength (B ++ C) / 8 = Zlength B / 8 + Zlength C / 8)
      by (rewrite Zlength_app; apply div8_eq; lia).
    assert (Hr: Zlength (B ++ C) mod 8 = Zlength C mod 8).
    { rewrite Zlength_app, Hdm, Hm, Z.add_0_r, Z.mul_comm, <- Z.add_comm, Z.mod_add by lia. reflexivity. }
    rewrite Hd, Hr, app_assoc. f_equal.
    + rewrite <- HpB. list_solve.
    + destruct (Zlength C mod 8 =? 0); auto.
      rewrite app_Znth2 by lia. rewrite HpB.
      replace (Zlength B / 8 + Zlength C / 8 - Zlength B / 8) with (Zlength C / 8) by lia. reflexivity.
Qed.

Lemma bval_bits8_check :
  forallb (fun b => bval (bits_le b 8) =? b) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bval_bits8 b : 0 <= b < 256 -> bval (bits_le b 8) = b.
Proof.
  intros Hb. pose proof bval_bits8_check as H. rewrite forallb_forall in H.
  apply Z.eqb_eq, H. rewrite in_map_iff. exists (Z.to_nat b). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma pack_bits8 b : 0 <= b < 256 -> pack (bits_le b 8) = [b].
Proof.
  intros Hb. apply Znth_eq_ext.
  - rewrite Zlength_pack, bits_le_length by lia. reflexivity.
  - intros k Hk. rewrite Zlength_pack, bits_le_length in Hk by lia. change ((8 + 7) / 8) with 1 in Hk.
    replace k with 0 by lia. rewrite Znth_pack by (rewrite bits_le_length by lia; cbn; lia).
    rewrite sublist_same by (rewrite ?bits_le_length; lia). rewrite bval_bits8 by auto. reflexivity.
Qed.

Lemma pack_snoc_false B : Zlength B mod 8 <> 0 -> pack (B ++ [false]) = pack B.
Proof.
  intros Hm. rewrite pack_snoc. destruct (pending_byte B Hm) as (Hlp & _ & _).
  rewrite (proj2 (Z.eqb_neq _ _) Hm). simpl Z.b2z. rewrite Z.mul_0_l, Z.add_0_r.
  pose proof (Zlength_nonneg B).
  assert (0 <= Zlength B / 8) by (apply Z.div_pos; lia).
  rewrite <- (sublist_same 0 (Zlength (pack B)) (pack B)) at 3 by lia.
  rewrite (sublist_split 0 (Zlength B / 8) (Zlength (pack B))) by lia.
  rewrite Hlp, sublist_len_1 by lia. reflexivity.
Qed.

Lemma zeros_snoc j : 0 <= j -> zeros (j + 1) = zeros j ++ [false].
Proof.
  intros. unfold zeros. rewrite Z2Nat.inj_add by lia. rewrite repeat_app. reflexivity.
Qed.

Lemma pack_zeros_pad B : pack (B ++ zeros (pad8 (Zlength B))) = pack B.
Proof.
  pose proof (Zlength_nonneg B) as HB.
  pose proof (Z.mod_pos_bound (Zlength B) 8 ltac:(lia)) as Hmb.
  unfold pad8.
  destruct (Z.eqb_spec (Zlength B mod 8) 0) as [Hm|Hm].
  - rewrite Hm. simpl. rewrite app_nil_r. reflexivity.
  - rewrite Z.mod_small by lia.
    pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)) as Hdm.
    assert (H: forall n: nat, (Z.of_nat n <= 8 - Zlength B mod 8) -> pack (B ++ zeros (Z.of_nat n)) = pack B).
    { induction n as [|n IH]; intros Hn.
      - simpl. rewrite app_nil_r. reflexivity.
      - rewrite Nat2Z.inj_succ, <- Z.add_1_r, zeros_snoc, app_assoc by lia.
        rewrite pack_snoc_false.
        + apply IH. lia.
        + rewrite Zlength_app, Zlength_zeros by lia.
          replace (Zlength B + Z.of_nat n) with ((Zlength B mod 8 + Z.of_nat n) + (Zlength B / 8) * 8) by lia.
          rewrite Z.mod_add, Z.mod_small by lia. lia. }
    rewrite <- (Z2Nat.id (8 - Zlength B mod 8)) by lia. apply H. lia.
Qed.

Lemma bits_le_snoc v i : 0 <= i -> bits_le v (i + 1) = bits_le v i ++ [Z.testbit v i].
Proof.
  intros Hi. unfold bits_le. rewrite Z2Nat.inj_add by lia. rewrite seq_app, map_app. simpl.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma Znth_bits_le c n k : 0 <= k < n -> Znth k (bits_le c n) = Z.testbit c k.
Proof.
  intros Hk. unfold bits_le.
  rewrite Znth_map by (rewrite Zlength_correct, seq_length; lia).
  rewrite <- nth_Znth by (rewrite Zlength_correct, seq_length; lia).
  rewrite seq_nth by lia. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma odd_shiftr v i : 0 <= i -> Z.odd (Z.shiftr v i) = Z.testbit v i.
Proof. intros. rewrite <- Z.bit0_odd, Z.shiftr_spec by lia. reflexivity. Qed.

Lemma shiftr_range v i : 0 <= i -> 0 <= v <= Int.max_unsigned -> 0 <= Z.shiftr v i <= Int.max_unsigned.
Proof.
  intros Hi Hv. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 i ltac:(lia) Hi).
  split; [apply Z.div_pos; lia|].
  assert (v / 2 ^ i <= v) by (apply Z.div_le_upper_bound; nia). lia.
Qed.

Lemma shru_repr v i : 0 <= v <= Int.max_unsigned -> 0 <= i <= Int.max_unsigned ->
  Int.shru (Int.repr v) (Int.repr i) = Int.repr (Z.shiftr v i).
Proof. intros. unfold Int.shru. rewrite !Int.unsigned_repr by lia. reflexivity. Qed.

Lemma room_step B X cap n : bw_room B cap n -> Zlength X < n -> bw_room (B ++ X) cap 1.
Proof.
  intros (Hn & Hc & Hm) HX. pose proof (Zlength_nonneg X). pose proof (Zlength_nonneg B).
  split; [lia|split; [|lia]]. rewrite Zlength_app.
  assert ((Zlength B + Zlength X + 1 + 7) / 8 <= (Zlength B + n + 7) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

#[local] Existing Instance Zlib.contracts.x_inflate_decode.Harness.CS.

Lemma body_bw_bit : semax_body Vprog_dref Gprog_bw_bit HD.f_bw_bit bw_bit_spec.
Proof.
  start_function. unfold bw_at, bw_rep. Intros contents.
  destruct H as (Hk & Hcap & Hmax). destruct H1 as (Hlc & Hpc & Hsub).
  pose proof (Zlength_nonneg B) as HB.
  pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (Zlength B) 8 ltac:(lia)) as Hmb.
  assert (Hc1: Zlength B / 8 + 1 <= cap).
  { replace (Zlength B + 1 + 7) with (Zlength B / 8 * 8 + (Zlength B mod 8 + 8)) in Hcap by lia.
    rewrite Z.div_add_l in Hcap by lia.
    assert ((Zlength B mod 8 + 8) / 8 = 1) by (apply div8_eq; lia). lia. }
  assert (HLq: Zlength B / 8 <= Zlength (pack B)).
  { rewrite Zlength_pack. apply Z.div_le_mono; lia. }
  assert (Hsubq: sublist 0 (Zlength B / 8) contents = Bytes.bytes_rep (sublist 0 (Zlength B / 8) (pack B))).
  { rewrite <- (sublist_sublist00 (Zlength B / 8) (Zlength (pack B))) by lia.
    rewrite Hsub, Bytes.sublist_bytes_rep. reflexivity. }
  assert (Hx0: Zlength B mod 8 <> 0 -> Znth (Zlength B / 8) contents = Vint (Int.repr (Znth (Zlength B / 8) (pack B)))).
  { intros Hm. destruct (pending_byte B Hm) as (Hlp & _ & _).
    replace (Znth (Zlength B / 8) contents) with (Znth (Zlength B / 8) (sublist 0 (Zlength (pack B)) contents))
      by (rewrite Znth_sublist by lia; f_equal; lia).
    rewrite Hsub, Bytes.Znth_bytes_rep by lia. reflexivity. }
  pose proof (pack_snoc B (Z.odd b)) as Hps.
  pose proof (pending_range B) as Hxr.
  assert (Hm1: Zlength (B ++ [Z.odd b]) = Zlength B + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  set (x := if Zlength B mod 8 =? 0 then 0 else Znth (Zlength B / 8) (pack B)) in *.
  assert (Hx1: Zlength B mod 8 <> 0 -> Znth (Zlength B / 8) contents = Vint (Int.repr x)).
  { intros Hm. rewrite Hx0 by auto. subst x. rewrite (proj2 (Z.eqb_neq _ _) Hm). reflexivity. }
  assert (Hx2: Zlength B mod 8 = 0 -> x = 0).
  { intros Hm. subst x. rewrite Hm. reflexivity. }
  clearbody x. clear Hx0.
  set (q := Zlength B / 8) in *. set (r := Zlength B mod 8) in *.
  set (P := sublist 0 q (pack B)) in *.
  assert (HP: Zlength P = q) by (subst P; rewrite Zlength_sublist; lia).
  clearbody P q r.
  assert (H2r: 2 ^ r <= 128) by (change 128 with (2 ^ 7); apply Z.pow_le_mono_r; lia).
  forward.
  forward_if (PROP () LOCAL (temp HD._w w; temp HD._b (Vint (Int.repr b)))
    SEP (data_at sh t_bw (buf, (Vint (Int.repr q), Vint (Int.repr r))) w;
         data_at bsh (tarray tuchar cap) (upd_Znth q contents (Vint (Int.repr x))) buf)).
  - assert (x = 0) by auto. subst x.
    forward. forward. forward. entailer!.
  - forward. entailer!. rewrite upd_Znth_triv; auto. lia.
  - forward. forward. forward. forward. forward.
    { entailer!. rewrite upd_Znth_same by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite upd_Znth_same by lia.
    forward.
    forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32; lia. }
    rewrite Int.zero_ext_idem, or_bit, upd_Znth_twice by (try lia; rep_lia).
    forward. forward. forward.
    forward_if (PROP () LOCAL () SEP (bw_at sh bsh (B ++ [Z.odd b]) cap buf w)).
    + assert (r = 7).
      { rewrite add_repr in H. apply repr_inj_unsigned in H; rep_lia. }
      subst r. forward. forward. forward.
      unfold bw_at, bw_rep.
      Exists (upd_Znth q contents (Vint (Int.repr (x + Z.b2z (Z.odd b) * 2 ^ 7)))).
      assert (Hq1: Zlength (B ++ [Z.odd b]) / 8 = q + 1) by (rewrite Hm1; apply div8_eq; lia).
      assert (Hr1: Zlength (B ++ [Z.odd b]) mod 8 = 0).
      { rewrite Hm1, Hdm. replace (8 * q + 7 + 1) with ((q + 1) * 8) by lia. apply Z.mod_mul. lia. }
      rewrite Hq1, Hr1. entailer!.
      split; [|split].
      * list_solve.
      * rewrite Hps, Zlength_app, Zlength_cons, Zlength_nil. lia.
      * rewrite Hps. apply (bytes_ok_upd _ _ _ (Zlength contents)); auto. lia.
    + forward. unfold bw_at, bw_rep.
      Exists (upd_Znth q contents (Vint (Int.repr (x + Z.b2z (Z.odd b) * 2 ^ r)))).
      assert (r <> 7) by (intro; subst r; contradiction).
      assert (Hq1: Zlength (B ++ [Z.odd b]) / 8 = q) by (rewrite Hm1; apply div8_eq; lia).
      assert (Hr1: Zlength (B ++ [Z.odd b]) mod 8 = r + 1).
      { rewrite Hm1, Hdm. replace (8 * q + r + 1) with ((r + 1) + q * 8) by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      rewrite Hq1, Hr1. entailer!.
      split; [|split].
      * list_solve.
      * rewrite Hps, Zlength_app, Zlength_cons, Zlength_nil. lia.
      * rewrite Hps. apply (bytes_ok_upd _ _ _ (Zlength contents)); auto. lia.
Qed.


Lemma body_bw_byte : semax_body Vprog_dref Gprog_bw_byte HD.f_bw_byte bw_byte_spec.
Proof.
  start_function. unfold bw_at, bw_rep. Intros contents.
  rename H into H1'. destruct H0 as (Hk & Hcap & Hmax). destruct H2 as (Hlc & Hpc & Hsub).
  pose proof (Zlength_nonneg B) as HB.
  pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)) as Hdm.
  rewrite H1', Z.add_0_r in Hdm.
  assert (HpB: Zlength (pack B) = Zlength B / 8) by (rewrite Zlength_pack; apply div8_eq; lia).
  assert (Hc1: Zlength B / 8 + 1 <= cap).
  { assert ((Zlength B + 8 + 7) / 8 = Zlength B / 8 + 1) by (apply div8_eq; lia). lia. }
  assert (Hm8: Zlength (B ++ bits_le b 8) = Zlength B + 8) by (rewrite Zlength_app, bits_le_length; lia).
  assert (Hq1: Zlength (B ++ bits_le b 8) / 8 = Zlength B / 8 + 1) by (rewrite Hm8; apply div8_eq; lia).
  assert (Hr1: Zlength (B ++ bits_le b 8) mod 8 = 0).
  { rewrite Hm8. replace (Zlength B + 8) with ((Zlength B / 8 + 1) * 8) by lia. apply Z.mod_mul. lia. }
  assert (Hps: pack (B ++ bits_le b 8) = pack B ++ [b]).
  { rewrite pack_app_aligned, pack_bits8 by lia. reflexivity. }
  assert (Hzx: Int.zero_ext 8 (Int.repr b) = Int.repr b).
  { rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)). rewrite Int.zero_ext_mod by (cbn; lia).
    rewrite Int.unsigned_repr by rep_lia. rewrite two_p_equiv, Z.mod_small by (cbn; lia). reflexivity. }
  forward. forward. forward. forward. forward.
  unfold bw_at, bw_rep. Exists (upd_Znth (Zlength B / 8) contents (Vint (Int.repr b))).
  rewrite Hq1, Hr1, Hzx. entailer!.
  split; [|split].
  - list_solve.
  - rewrite Hps, Zlength_app, Zlength_cons, Zlength_nil. lia.
  - rewrite Hps. apply (bytes_ok_upd _ _ _ (Zlength contents)); auto. lia.
    rewrite <- HpB. auto.
  - rewrite H1'. change (let (q, _) := Z.div_eucl (Zlength B) 8 in q) with (Zlength B / 8). cancel.
Qed.

Lemma body_bw_align : semax_body Vprog_dref Gprog_bw_align HD.f_bw_align bw_align_spec.
Proof.
  start_function. unfold bw_at, bw_rep. Intros contents.
  destruct H as (Hk & Hcap & Hmax). destruct H0 as (Hlc & Hpc & Hsub).
  pose proof (Zlength_nonneg B) as HB.
  pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (Zlength B) 8 ltac:(lia)) as Hmb.
  pose proof (pack_zeros_pad B) as Hps.
  assert (Hc1: Zlength B / 8 <= cap).
  { assert (Zlength B / 8 <= (Zlength B + 0 + 7) / 8) by (apply Z.div_le_mono; lia). lia. }
  forward.
  forward_if (PROP () LOCAL () SEP (bw_at sh bsh (B ++ zeros (pad8 (Zlength B))) cap buf w)).
  - forward. forward. forward.
    unfold bw_at, bw_rep. Exists contents.
    assert (Hp: pad8 (Zlength B) = 8 - Zlength B mod 8).
    { unfold pad8. apply Z.mod_small. lia. }
    assert (Hm8: Zlength (B ++ zeros (pad8 (Zlength B))) = 8 * (Zlength B / 8 + 1)).
    { rewrite Zlength_app, Zlength_zeros by (unfold pad8; apply Z.mod_pos_bound; lia). lia. }
    rewrite Hm8, Z.mul_comm, Z.div_mul, Z.mod_mul by lia.
    entailer!. unfold bw_bytes_ok. rewrite Hps. split; auto.
  - forward. unfold bw_at, bw_rep. Exists contents.
    assert (Hp: pad8 (Zlength B) = 0).
    { unfold pad8. rewrite H. reflexivity. }
    rewrite Hp. change (zeros 0) with (@nil bool). rewrite app_nil_r, H.
    entailer!. split; auto.
Qed.

Lemma body_bw_bits : semax_body Vprog_dref Gprog_bw_bits HD.f_bw_bits bw_bits_spec.
Proof.
  start_function.
  forward_for_simple_bound n (EX i: Z, PROP ()
    LOCAL (temp HD._w w; temp HD._v (Vint (Int.repr v)); temp HD._n (Vint (Int.repr n)))
    SEP (bw_at sh bsh (B ++ bits_le v i) cap buf w)).
  - entailer!. unfold bits_le. simpl. rewrite app_nil_r. auto.
  - forward_call (sh, bsh, B ++ bits_le v i, cap, buf, w, Z.shiftr v i).
    + change (Int.unsigned Int.iwordsize) with 32; lia.
    + entailer!. simpl. rewrite shru_repr by rep_lia. reflexivity.
    + split; [apply (room_step B _ cap n); auto; rewrite bits_le_length; lia|]. apply shiftr_range; lia.
    + entailer!. rewrite bits_le_snoc, app_assoc, odd_shiftr by lia. auto.
  - entailer!.
Qed.

Lemma rev_sublist_step {A} {d: Inhabitant A} (L: list A) i n :
  1 <= i <= n -> n = Zlength L ->
  rev (sublist (i - 1) n L) = rev (sublist i n L) ++ [Znth (i - 1) L].
Proof.
  intros Hi Hn. rewrite (sublist_split (i - 1) i n) by lia.
  assert (H1: sublist (i - 1) i L = [Znth (i - 1) L]).
  { replace i with (i - 1 + 1) at 2 by lia. apply sublist_len_1. lia. }
  rewrite H1, rev_app_distr. reflexivity.
Qed.

Lemma body_bw_code : semax_body Vprog_dref Gprog_bw_code HD.f_bw_code bw_code_spec.
Proof.
  start_function.
  assert (HL: Zlength (bits_le c n) = n) by (apply bits_le_length; lia).
  forward_loop (EX i: Z, PROP (0 <= i <= n)
    LOCAL (temp HD._i (Vint (Int.repr i)); temp HD._w w; temp HD._c (Vint (Int.repr c));
           temp HD._n (Vint (Int.repr n)))
    SEP (bw_at sh bsh (B ++ rev (sublist i n (bits_le c n))) cap buf w))
  continue: (EX i: Z, PROP (1 <= i <= n)
    LOCAL (temp HD._i (Vint (Int.repr i)); temp HD._w w; temp HD._c (Vint (Int.repr c));
           temp HD._n (Vint (Int.repr n)))
    SEP (bw_at sh bsh (B ++ rev (sublist (i - 1) n (bits_le c n))) cap buf w))
  break: (PROP () LOCAL () SEP (bw_at sh bsh (B ++ bits_msb c n) cap buf w)).
  - forward. Exists n. entailer!. rewrite sublist_nil. simpl. rewrite app_nil_r. auto.
  - Intros i. forward_if.
    + forward_call (sh, bsh, B ++ rev (sublist i n (bits_le c n)), cap, buf, w, Z.shiftr c (i - 1)).
      * change (Int.unsigned Int.iwordsize) with 32; lia.
      * entailer!. simpl. rewrite shru_repr by rep_lia. reflexivity.
      * split; [apply (room_step B _ cap n); auto|apply shiftr_range; lia].
        rewrite Zlength_rev, Zlength_sublist; lia.
      * Exists i. entailer!.
        rewrite (rev_sublist_step _ i n), app_assoc, Znth_bits_le, odd_shiftr by lia. auto.
    + forward. entailer!.
      replace i with 0 by lia. rewrite sublist_same by lia. unfold bits_msb. auto.
  - Intros i. forward. Exists (i - 1). entailer!.
  - unfold abbreviate in POSTCONDITION; subst POSTCONDITION. simpl. intro rho. apply andp_left2.
    unfold stackframe_of. simpl. rewrite sepcon_emp. apply derives_refl.
Qed.

Lemma dref_bw_bodies_proof : dref_bw_bodies.
Proof.
  split; [exact body_bw_bit|]. split; [exact body_bw_bits|]. split; [exact body_bw_code|].
  split; [exact body_bw_byte|exact body_bw_align].
Qed.
