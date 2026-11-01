(* The input as a bit stream: the bits of `sbits` one by one, and the facts the bit buffer needs
   (a prefix of the bits, the bits after a shift, two runs of bits side by side, a byte). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the bit at position p of the input (bytes past the end read as 0) *)
Definition sbit (src: list Z) (p: Z) : bool := Z.testbit (Znth (p / 8) src) (p mod 8).

Lemma sik_byte_range src k : bytes_ok src -> 0 <= Znth k src < 256.
Proof.
  intros B. destruct (Z_lt_dec k 0).
  { rewrite Znth_underflow by lia. cbv. split; congruence. }
  destruct (Z_lt_dec k (Zlength src)).
  { unfold bytes_ok in B. rewrite Forall_Znth in B. specialize (B k ltac:(lia)). simpl in B. rep_lia. }
  rewrite Znth_overflow by lia. cbv. split; congruence.
Qed.

Lemma sik_le_val_bit src : bytes_ok src -> forall len k j, 0 <= j < 8 * Z.of_nat len ->
  Z.testbit (le_val src k len) j = Z.testbit (Znth (k + j / 8) src) (j mod 8).
Proof.
  intros B. induction len as [|len IH]; intros k j Hj; [lia|].
  cbn [le_val]. pose proof (sik_byte_range src k B) as R.
  assert (E: Znth k src + 256 * le_val src (k + 1) len = Znth k src + le_val src (k + 1) len * 2 ^ 8)
    by (change (2 ^ 8) with 256; ring).
  rewrite E. destruct (Z_lt_dec j 8).
  - rewrite Z.div_small, Z.mod_small by lia. rewrite Z.add_0_r.
    rewrite <- (Z.mod_pow2_bits_low _ 8 j) by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by (change (2 ^ 8) with 256; lia). reflexivity.
  - assert (H8: 0 <= j - 8) by lia.
    replace j with (j - 8 + 8) at 1 by lia.
    rewrite <- Z.shiftr_spec by lia. rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.div_add by (change (2 ^ 8) with 256; lia).
    rewrite Z.div_small by (change (2 ^ 8) with 256; lia). rewrite Z.add_0_l.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hj; lia).
    replace (k + 1 + (j - 8) / 8) with (k + j / 8).
    + replace ((j - 8) mod 8) with (j mod 8); [reflexivity|].
      replace j with ((j - 8) + 1 * 8) at 1 by lia. rewrite Z_mod_plus_full. reflexivity.
    + assert (D: j / 8 = (j - 8) / 8 + 1).
      { replace j with ((j - 8) + 1 * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
      lia.
Qed.

(* the i-th bit of sbits src q n is the bit q + i of the input *)
Lemma sik_sbits_bit src q n i : bytes_ok src -> 0 <= q -> 0 <= n -> 0 <= i ->
  Z.testbit (sbits src q n) i = andb (i <? n) (sbit src (q + i)).
Proof.
  intros B Q N I. unfold sbits.
  destruct (Z_lt_dec i n).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia.
    pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (q mod 8 + n + 7) 8 ltac:(lia)).
    pose proof (Z_div_mod_eq_full (q mod 8 + n + 7) 8).
    assert (0 <= (q mod 8 + n + 7) / 8) by (apply Z.div_pos; lia).
    rewrite sik_le_val_bit by (auto; rewrite Z2Nat.id by lia; lia).
    replace (Z.ltb i n) with true by (symmetry; apply Z.ltb_lt; lia). rewrite andb_true_l. unfold sbit.
    pose proof (Z_div_mod_eq_full q 8).
    replace (q + i) with ((i + q mod 8) + (q / 8) * 8) by lia.
    rewrite Z.div_add, Z_mod_plus_full by lia. f_equal. f_equal. lia.
  - rewrite Z.mod_pow2_bits_high by lia.
    replace (Z.ltb i n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma sik_sbits_bit_neg src q n i : i < 0 -> Z.testbit (sbits src q n) i = false.
Proof. intros. apply Z.testbit_neg_r. lia. Qed.

(* a prefix of the bits *)
Lemma sik_sbits_mod src q n k : bytes_ok src -> 0 <= q -> 0 <= k <= n ->
  sbits src q n mod 2 ^ k = sbits src q k.
Proof.
  intros B Q K. apply Z.bits_inj'. intros i I.
  destruct (Z_lt_dec i k).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite !sik_sbits_bit by (try exact B; lia).
    replace (i <? n) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (i <? k) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite sik_sbits_bit by (try exact B; lia).
    replace (i <? k) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* the bits after a shift *)
Lemma sik_sbits_shiftr src q n k : bytes_ok src -> 0 <= q -> 0 <= k <= n ->
  Z.shiftr (sbits src q n) k = sbits src (q + k) (n - k).
Proof.
  intros B Q K. apply Z.bits_inj'. intros i I.
  rewrite Z.shiftr_spec by lia. rewrite !sik_sbits_bit by (try exact B; lia).
  replace (q + (i + k)) with (q + k + i) by lia.
  f_equal. destruct (Z.ltb_spec (i + k) n), (Z.ltb_spec i (n - k)); auto; lia.
Qed.

Lemma sik_sbits_range src q n : 0 <= n -> 0 <= sbits src q n < 2 ^ n.
Proof. intros. unfold sbits. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

(* a byte at a byte boundary *)
Lemma sik_sbits_byte src q : bytes_ok src -> 0 <= q -> q mod 8 = 0 -> sbits src q 8 = sbyte src q.
Proof.
  intros B Q M. apply Z.bits_inj'. intros i I.
  rewrite sik_sbits_bit by (try exact B; lia). unfold sbyte, sbit.
  pose proof (sik_byte_range src (q / 8) B) as R.
  pose proof (Z_div_mod_eq_full q 8).
  destruct (Z_lt_dec i 8).
  - replace (i <? 8) with true by (symmetry; apply Z.ltb_lt; lia). rewrite andb_true_l.
    replace (q + i) with (i + (q / 8) * 8) by lia.
    rewrite Z.div_add, Z_mod_plus_full by lia. rewrite Z.div_small, Z.mod_small by lia.
    rewrite Z.add_0_l. reflexivity.
  - replace (i <? 8) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_l.
    rewrite <- (Z.mod_small (Znth (q / 8) src) (2 ^ 8)) by (change (2 ^ 8) with 256; lia).
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* two runs of bits side by side *)
Lemma sik_sbits_app src q n k : bytes_ok src -> 0 <= q -> 0 <= n -> 0 <= k ->
  sbits src q (n + k) = sbits src q n + 2 ^ n * sbits src (q + n) k.
Proof.
  intros B Q N K.
  rewrite <- (sik_sbits_mod src q (n + k) n) by (try exact B; lia).
  replace k with (n + k - n) at 3 by lia.
  rewrite <- (sik_sbits_shiftr src q (n + k) n) by (try exact B; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z_div_mod_eq_full (sbits src q (n + k)) (2 ^ n)). lia.
Qed.

Lemma sik_sbits_0 src q : sbits src q 0 = 0.
Proof. unfold sbits. rewrite Z.pow_0_r. apply Z.mod_1_r. Qed.

(* the n low bits of sbits src q b, b <= n: the b bits themselves *)
Lemma sik_sbits_mod_big src q b n : 0 <= b <= n -> sbits src q b mod 2 ^ n = sbits src q b.
Proof.
  intros. apply Z.mod_small. pose proof (sik_sbits_range src q b ltac:(lia)).
  pose proof (Z.pow_le_mono_r 2 b n ltac:(lia) ltac:(lia)). lia.
Qed.

(* the low n bits of b bits at q: the min(b, n) bits at q *)
Lemma sik_sbits_mod_min src q b n : bytes_ok src -> 0 <= q -> 0 <= b -> 0 <= n ->
  sbits src q b mod 2 ^ n = sbits src q (Z.min b n).
Proof.
  intros B Q Hb Hn. destruct (Z.le_ge_cases b n).
  - rewrite Z.min_l by lia. apply sik_sbits_mod_big; lia.
  - rewrite Z.min_r by lia. apply sik_sbits_mod; auto; lia.
Qed.

(* two bit strings that agree on their min(a, b) first bits *)
Lemma sik_sbits_agree src q a b k : bytes_ok src -> 0 <= q -> 0 <= k -> k <= a -> k <= b ->
  sbits src q a mod 2 ^ k = sbits src q b mod 2 ^ k.
Proof. intros B **. rewrite !sik_sbits_mod by (try exact B; lia). reflexivity. Qed.
