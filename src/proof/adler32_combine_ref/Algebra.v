(* The algebra of adler32_combine for harness/adler32_combine_ref.c: the code's exact result
   (Spec.adler32_combine_impl) is RFC 1950's combination (Model.adler32_combine_val) for valid checksums and
   len2 >= 0, and that combination of the checksums of A and B is the checksum of A ++ B. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.adler32.Spec Zlib.proof.adler32.Facts.

Lemma mod_cong_k a b k: a = b + k * ADLER_BASE -> a mod ADLER_BASE = b mod ADLER_BASE.
Proof. intros ->. apply Z.mod_add. unfold ADLER_BASE; lia. Qed.

Lemma lor_pack s1 s2: 0 <= s1 < 65536 -> 0 <= s2 -> Z.lor s1 (s2 * 65536) = s2 * 65536 + s1.
Proof.
  intros. replace (s2 * 65536) with (Z.shiftl s2 16) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  assert (L: Z.land s1 (Z.shiftl s2 16) = 0).
  { apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases j 16).
    + rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    + rewrite (Z.bits_above_log2 s1 j); [reflexivity | lia | ].
      destruct (Z.eq_dec s1 0) as [E|E]; [subst; simpl; lia | ].
      apply (Z.lt_le_trans _ 16); [apply Z.log2_lt_pow2; lia | lia]. }
  rewrite <- Z.lxor_lor by auto. rewrite <- Z.add_nocarry_lxor by auto.
  rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Lemma adler32_combine_impl_val x y z: adler_valid x -> adler_valid y -> 0 <= z ->
  adler32_combine_impl x y z = adler32_combine_val x y z.
Proof.
  intros (_ & Hx1 & Hx2) (_ & Hy1 & Hy2) Hz.
  pose proof (adler_lo_range x). pose proof (adler_hi_range x).
  pose proof (adler_lo_range y). pose proof (adler_hi_range y).
  unfold adler32_combine_impl, adler32_combine_val. cbv zeta.
  set (x1 := adler_lo x) in *. set (x2 := adler_hi x) in *.
  set (y1 := adler_lo y) in *. set (y2 := adler_hi y) in *.
  set (r := z mod ADLER_BASE).
  assert (Hr: 0 <= r < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
  set (m := (r * x1) mod ADLER_BASE).
  assert (Hm: 0 <= m < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
  (* the low half *)
  assert (S1: forall t, 0 <= t < 3 * ADLER_BASE ->
     (let u := if t <? ADLER_BASE then t else t - ADLER_BASE in if u <? ADLER_BASE then u else u - ADLER_BASE)
       = t mod ADLER_BASE).
  { intros t Ht. cbv zeta. unfold ADLER_BASE in *.
    destruct (Z.ltb_spec t 65521).
    - rewrite Z.mod_small by lia. destruct (Z.ltb_spec t 65521); lia.
    - destruct (Z.ltb_spec (t - 65521) 65521).
      + apply Z.mod_unique with 1; lia.
      + apply Z.mod_unique with 2; lia. }
  assert (S2: forall t, 0 <= t < 4 * ADLER_BASE ->
     (let u := if t <? 2 * ADLER_BASE then t else t - 2 * ADLER_BASE in
      if u <? ADLER_BASE then u else u - ADLER_BASE) = t mod ADLER_BASE).
  { intros t Ht. cbv zeta. unfold ADLER_BASE in *.
    destruct (Z.ltb_spec t (2 * 65521)).
    - destruct (Z.ltb_spec t 65521).
      + rewrite Z.mod_small by lia. reflexivity.
      + apply Z.mod_unique with 1; lia.
    - destruct (Z.ltb_spec (t - 2 * 65521) 65521).
      + apply Z.mod_unique with 2; lia.
      + apply Z.mod_unique with 3; lia. }
  cbv zeta in S1, S2.
  rewrite (S1 (x1 + y1 + ADLER_BASE - 1)) by (unfold ADLER_BASE in *; lia).
  rewrite (S2 (m + x2 + y2 + ADLER_BASE - r)) by (unfold ADLER_BASE in *; lia).
  assert (0 <= (x1 + y1 + ADLER_BASE - 1) mod ADLER_BASE < ADLER_BASE)
    by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
  assert (0 <= (m + x2 + y2 + ADLER_BASE - r) mod ADLER_BASE < ADLER_BASE)
    by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
  rewrite lor_pack by (unfold ADLER_BASE in *; lia).
  f_equal. f_equal.
  (* the high half: m + x2 + y2 + B - r = x2 + y2 + r * ((x1 + B - 1) mod B)  (mod B) *)
  unfold m. rewrite (Z.mod_eq (r * x1)) by (unfold ADLER_BASE; lia).
  rewrite (Z.mod_eq (x1 + ADLER_BASE - 1)) by (unfold ADLER_BASE; lia).
  apply mod_cong_k with (k := 1 - (r * x1) / ADLER_BASE - r + r * ((x1 + ADLER_BASE - 1) / ADLER_BASE)).
  ring.
Qed.

(* The sums from (a, b) in terms of the sums from (0, 0). *)
Lemma adler_sums_shift: forall l a b,
  adler_sums (a, b) l =
    (fst (adler_sums (0, 0) l) + a, snd (adler_sums (0, 0) l) + Zlength l * a + b).
Proof.
  unfold adler_sums. induction l as [|c l IH]; intros a b.
  - simpl. rewrite ?Zlength_nil. f_equal; lia.
  - simpl fold_left.
    change (adler_sum_step (a, b) c) with (a + c, b + (a + c)).
    change (adler_sum_step (0, 0) c) with (0 + c, 0 + (0 + c)).
    rewrite (IH (a + c)), (IH (0 + c)). cbn [fst snd]. rewrite Zlength_cons. f_equal; lia.
Qed.

Lemma ref_adler32_shift a l: adler_valid a ->
  adler_lo (ref_adler32 a l) = (fst (adler_sums (0, 0) l) + adler_lo a) mod ADLER_BASE /\
  adler_hi (ref_adler32 a l) = (snd (adler_sums (0, 0) l) + Zlength l * adler_lo a + adler_hi a) mod ADLER_BASE.
Proof.
  intros (_ & Hlo & Hhi).
  pose proof (adler_lo_range a). pose proof (adler_hi_range a).
  unfold ref_adler32.
  rewrite (adler_ref_sums l (adler_lo a, adler_hi a) (adler_lo a, adler_hi a)) by
    (simpl; try rewrite Z.mod_small; unfold ADLER_BASE in *; lia).
  rewrite adler_sums_shift. unfold adler_pack. simpl fst; simpl snd.
  assert (0 <= (fst (adler_sums (0, 0) l) + adler_lo a) mod ADLER_BASE < ADLER_BASE)
    by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
  assert (0 <= (snd (adler_sums (0, 0) l) + Zlength l * adler_lo a + adler_hi a) mod ADLER_BASE < ADLER_BASE)
    by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
  unfold ADLER_BASE in *. rewrite adler_lo_pack, adler_hi_pack by lia. auto.
Qed.

Lemma adler_valid_1: adler_valid 1.
Proof. unfold adler_valid, adler_lo, adler_hi, ADLER_BASE. vm_compute. repeat split; congruence. Qed.

Lemma adler32_combine_val_ref x l: adler_valid x ->
  adler32_combine_val x (ref_adler32 1 l) (Zlength l) = ref_adler32 x l.
Proof.
  intros Vx.
  assert (Vr := ref_adler32_valid x l Vx). assert (Vy := ref_adler32_valid 1 l adler_valid_1).
  destruct (ref_adler32_shift x l Vx) as [L1 H1].
  destruct (ref_adler32_shift 1 l adler_valid_1) as [L2 H2].
  change (adler_lo 1) with 1 in L2, H2. change (adler_hi 1) with 0 in H2.
  destruct Vr as (Rr & Rlo & Rhi).
  pose proof (adler_lo_range (ref_adler32 x l)). pose proof (adler_hi_range (ref_adler32 x l)).
  assert (E: ref_adler32 x l = adler_hi (ref_adler32 x l) * 65536 + adler_lo (ref_adler32 x l)).
  { unfold adler_lo, adler_hi. rewrite (Z.mod_small (ref_adler32 x l / 65536)).
    - rewrite Z.mul_comm. apply Z.div_mod. lia.
    - split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite E. unfold adler32_combine_val. cbv zeta.
  rewrite L1, H1, L2, H2.
  set (P := fst (adler_sums (0, 0) l)). set (Q := snd (adler_sums (0, 0) l)). set (n := Zlength l).
  set (x1 := adler_lo x). set (x2 := adler_hi x).
  f_equal; [f_equal | ].
  - rewrite (Z.mod_eq (Q + n * 1 + 0)) by (unfold ADLER_BASE; lia).
    rewrite (Z.mod_eq n) by (unfold ADLER_BASE; lia).
    rewrite (Z.mod_eq (x1 + ADLER_BASE - 1)) by (unfold ADLER_BASE; lia).
    apply mod_cong_k with
      (k := - ((Q + n * 1 + 0) / ADLER_BASE) + n * (1 - (x1 + ADLER_BASE - 1) / ADLER_BASE)
            - n / ADLER_BASE * (x1 + ADLER_BASE - 1 - ADLER_BASE * ((x1 + ADLER_BASE - 1) / ADLER_BASE))).
    ring.
  - rewrite (Z.mod_eq (P + 1)) by (unfold ADLER_BASE; lia).
    apply mod_cong_k with (k := 1 - (P + 1) / ADLER_BASE). ring.
Qed.

(* The harness's first check. *)
Lemma adler32_combine_app a0 A B: adler_valid a0 ->
  adler32_combine_result (ref_adler32 a0 A) (ref_adler32 1 B) (Zlength B) = ref_adler32 a0 (A ++ B).
Proof.
  intros V. unfold adler32_combine_result.
  destruct (Z.ltb_spec (Zlength B) 0); [pose proof (Zlength_nonneg B); lia | ].
  rewrite adler32_combine_impl_val; auto using ref_adler32_valid, adler_valid_1.
  rewrite adler32_combine_val_ref by (apply ref_adler32_valid; auto).
  apply ref_adler32_app; auto.
Qed.
