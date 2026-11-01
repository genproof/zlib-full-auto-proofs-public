(* Machine-integer facts for multmodp and x2nmodp. *)
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.crc32.X2n.


Lemma pow2_ge_1 j: 0 <= j -> 1 <= 2 ^ j.
Proof. intros. assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia. Qed.

Lemma shiftr_2_31_range j: 0 <= j -> 0 <= Z.shiftr (2 ^ 31) j <= 2 ^ 31.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | ].
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia | ]. pose proof (pow2_ge_1 j H). nia.
Qed.

Lemma shiftr_2_31_low j: 0 <= j <= 31 -> Z.shiftr (2 ^ 31) j = 2 ^ (31 - j).
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. rewrite <- Z.pow_sub_r by lia. auto. Qed.

Lemma shiftr_2_31_high j: 32 <= j -> Z.shiftr (2 ^ 31) j = 0.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. split; [lia | ].
  apply (Z.lt_le_trans _ (2 ^ 32)); [lia | apply Z.pow_le_mono_r; lia].
Qed.

(* a & m, m = 2^(31-j) (0 when j > 31). *)
Lemma and_m_int a j: 0 <= a <= Int64.max_unsigned -> 0 <= j ->
  Int64.and (Int64.repr a) (Int64.repr (Z.shiftr (2 ^ 31) j)) =
  if ((j <=? 31) && Z.testbit a (31 - j))%bool then Int64.repr (Z.shiftr (2 ^ 31) j) else Int64.zero.
Proof.
  intros Ha Hj. pose proof (shiftr_2_31_range j Hj).
  unfold Int64.and. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (Z.leb_spec j 31).
  - rewrite shiftr_2_31_low by lia. simpl andb.
    destruct (Z.testbit a (31 - j)) eqn:B.
    + f_equal. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
      destruct (Z.eq_dec i (31 - j)); [subst; rewrite B, Z.pow2_bits_true by lia; auto | ].
      rewrite Z.pow2_bits_false by lia. apply andb_false_r.
    + change Int64.zero with (Int64.repr 0). f_equal. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.eq_dec i (31 - j)); [subst; rewrite B; auto | ].
      rewrite Z.pow2_bits_false by lia. apply andb_false_r.
  - rewrite shiftr_2_31_high by lia. simpl andb. rewrite Z.land_0_r. reflexivity.
Qed.

(* a & (m - 1) == 0, m = 2^(31-j), j <= 31: the bits of a below 31 - j are zero. *)
Lemma and_m1_int a j: 0 <= a <= Int64.max_unsigned -> 0 <= j <= 31 ->
  Int64.and (Int64.repr a) (Int64.sub (Int64.repr (Z.shiftr (2 ^ 31) j)) (Int64.repr (Int.signed (Int.repr 1)))) =
  Int64.repr (a mod 2 ^ (31 - j)).
Proof.
  intros Ha Hj. rewrite shiftr_2_31_low by lia. change (Int.signed (Int.repr 1)) with 1.
  rewrite sub64_repr. unfold Int64.and.
  assert (1 <= 2 ^ (31 - j) <= 2 ^ 31) by (split; [apply pow2_ge_1; lia | apply Z.pow_le_mono_r; lia]).
  rewrite !Int64.unsigned_repr by rep_lia.
  replace (2 ^ (31 - j) - 1) with (Z.ones (31 - j)) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma lowbits_zero a j i: 0 <= j <= 31 -> a mod 2 ^ (31 - j) = 0 -> 0 <= i < 31 - j -> Z.testbit a i = false.
Proof.
  intros Hj Hm Hi. rewrite <- (Z.mod_pow2_bits_low a (31 - j) i) by lia. rewrite Hm. apply Z.bits_0.
Qed.

Lemma m_shift_int j: 0 <= j ->
  Int64.shru (Int64.repr (Z.shiftr (2 ^ 31) j)) (Int64.repr (Int.unsigned (Int.repr 1))) =
  Int64.repr (Z.shiftr (2 ^ 31) (j + 1)).
Proof.
  intros. pose proof (shiftr_2_31_range j H). change (Int.unsigned (Int.repr 1)) with 1.
  unfold Int64.shru. rewrite !Int64.unsigned_repr by rep_lia. rewrite Z.shiftr_shiftr by lia. auto.
Qed.

Lemma b_odd_int x: 0 <= x < 2 ^ 32 ->
  Int64.and (Int64.repr x) (Int64.repr 1) = if Z.odd x then Int64.repr 1 else Int64.zero.
Proof.
  intros. unfold Int64.and.
  rewrite !Int64.unsigned_repr by rep_lia.
  change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite Zmod_odd. destruct (Z.odd x); reflexivity.
Qed.

Lemma b_step_odd_int x: 0 <= x < 2 ^ 32 -> Z.odd x = true ->
  Int64.xor (Int64.shru (Int64.repr x) (Int64.repr (Int.unsigned (Int.repr 1))))
    (Int64.repr (Int.unsigned (Int.repr (-306674912)))) = Int64.repr (crc_step x).
Proof.
  intros Hx O. change (Int.unsigned (Int.repr 1)) with 1.
  change (Int.unsigned (Int.repr (-306674912))) with CRC_POLY.
  unfold crc_step. rewrite O. unfold Int64.xor, Int64.shru.
  rewrite (Int64.unsigned_repr x), (Int64.unsigned_repr 1) by rep_lia.
  assert (0 <= Z.shiftr x 1 < 2 ^ 32).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite !Int64.unsigned_repr by (unfold CRC_POLY; rep_lia). reflexivity.
Qed.

Lemma b_step_even_int x: 0 <= x < 2 ^ 32 -> Z.odd x = false ->
  Int64.shru (Int64.repr x) (Int64.repr (Int.unsigned (Int.repr 1))) = Int64.repr (crc_step x).
Proof.
  intros Hx O. change (Int.unsigned (Int.repr 1)) with 1.
  unfold crc_step. rewrite O. unfold Int64.shru.
  rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

(* The partial sums of multmodp. *)
Lemma xsum_succ_term a b j: 0 <= j <= 31 ->
  xsum (Z.to_nat (Z.min (j + 1) 32)) (gf_term a b) =
  Z.lxor (xsum (Z.to_nat (Z.min j 32)) (gf_term a b)) (gf_term a b (Z.to_nat j)).
Proof.
  intros. rewrite !Z.min_l by lia. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. reflexivity.
Qed.

Lemma xsum_high a b j: 32 <= j ->
  xsum (Z.to_nat (Z.min (j + 1) 32)) (gf_term a b) = xsum (Z.to_nat (Z.min j 32)) (gf_term a b).
Proof. intros. rewrite !Z.min_r by lia. auto. Qed.

Lemma gf_term_set a b j: 0 <= j <= 31 -> Z.testbit a (31 - j) = true ->
  gf_term a b (Z.to_nat j) = Nat.iter (Z.to_nat j) crc_step b.
Proof. intros. unfold gf_term. rewrite Z2Nat.id by lia. rewrite H0. auto. Qed.

Lemma gf_term_unset a b j: 0 <= j <= 31 -> Z.testbit a (31 - j) = false -> gf_term a b (Z.to_nat j) = 0.
Proof. intros. unfold gf_term. rewrite Z2Nat.id by lia. rewrite H0. auto. Qed.

(* The break of multmodp: no bit of a below 31 - j. *)
Lemma gf_mul_break a b j: 0 <= j <= 31 -> a mod 2 ^ (31 - j) = 0 ->
  gf_mul a b = xsum (Z.to_nat (Z.min (j + 1) 32)) (gf_term a b).
Proof.
  intros Hj Hm. unfold gf_mul. rewrite Z.min_l by lia.
  apply xsum_tail_zero; [lia | ]. intros t Ht. unfold gf_term.
  rewrite (lowbits_zero a j) by (auto; lia). auto.
Qed.

Lemma xor64_repr32 x y: is32 x -> is32 y -> Int64.xor (Int64.repr x) (Int64.repr y) = Int64.repr (Z.lxor x y).
Proof. unfold is32. intros. unfold Int64.xor. rewrite !Int64.unsigned_repr by rep_lia. auto. Qed.

Lemma odd_int64 x: 0 <= x <= Int64.max_unsigned ->
  Int64.and (Int64.repr x) (Int64.repr 1) = if Z.odd x then Int64.repr 1 else Int64.zero.
Proof.
  intros. unfold Int64.and.
  rewrite !Int64.unsigned_repr by rep_lia.
  change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite Zmod_odd. destruct (Z.odd x); reflexivity.
Qed.

Lemma k31_int k: 0 <= k ->
  Int.and (Int.repr k) (Int.repr 31) = Int.repr (k mod 32).
Proof.
  intros. apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_and by auto. rewrite !Int.testbit_repr by auto.
  replace (k mod 32) with (Z.land k (Z.ones 5)) by (rewrite Z.land_ones by lia; reflexivity).
  rewrite Z.land_spec. reflexivity.
Qed.

Lemma shr1_int64 x: 0 <= x <= Int64.max_signed ->
  Int64.shr (Int64.repr x) (Int64.repr (Int.unsigned (Int.repr 1))) = Int64.repr (x / 2).
Proof.
  intros. change (Int.unsigned (Int.repr 1)) with 1. unfold Int64.shr.
  rewrite Int64.signed_repr by rep_lia. rewrite (Int64.unsigned_repr 1) by rep_lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma mask32_int64 x: 0 <= x <= Int64.max_unsigned ->
  Int64.and (Int64.repr x) (Int64.repr (Int.unsigned (Int.repr (-1)))) = Int64.repr (x mod 2 ^ 32).
Proof.
  intros. change (Int.unsigned (Int.repr (-1))) with (Z.ones 32). unfold Int64.and.
  rewrite !Int64.unsigned_repr by (try rewrite Z.ones_equiv; rep_lia).
  rewrite Z.land_ones by lia. reflexivity.
Qed.
