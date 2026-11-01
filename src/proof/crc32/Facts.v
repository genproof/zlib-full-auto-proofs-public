(* Facts about the CRC-32 reference: the register update is linear over GF(2) (xor), and one table step
   of crc32_z, (c >> 8) ^ crc_table[(c ^ b) & 0xff], is the bitwise update of one byte. *)
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.crc32.Model.
Require Import Coq.btauto.Btauto.

Lemma lxor_nonneg' a b: 0 <= a -> 0 <= b -> 0 <= Z.lxor a b.
Proof. intros. apply Z.lxor_nonneg. split; intros; auto. Qed.

Lemma odd_lxor x y: Z.odd (Z.lxor x y) = xorb (Z.odd x) (Z.odd y).
Proof. rewrite <- !Z.bit0_odd. apply Z.lxor_spec. Qed.

Lemma crc_step_lxor x y: crc_step (Z.lxor x y) = Z.lxor (crc_step x) (crc_step y).
Proof.
  unfold crc_step. rewrite odd_lxor, Z.shiftr_lxor.
  destruct (Z.odd x), (Z.odd y); simpl; try reflexivity;
    apply Z.bits_inj'; intros i Hi; rewrite !Z.lxor_spec; btauto.
Qed.

Lemma crc_step_0: crc_step 0 = 0.
Proof. reflexivity. Qed.

Lemma iter_crc_step_lxor k x y:
  Nat.iter k crc_step (Z.lxor x y) = Z.lxor (Nat.iter k crc_step x) (Nat.iter k crc_step y).
Proof.
  induction k; simpl; auto. rewrite IHk. apply crc_step_lxor.
Qed.

Lemma iter_crc_step_0 k: Nat.iter k crc_step 0 = 0.
Proof. induction k; simpl; auto. rewrite IHk. reflexivity. Qed.

Lemma crc_step_nonneg x: 0 <= x -> 0 <= crc_step x.
Proof.
  intros. unfold crc_step. destruct (Z.odd x).
  - apply lxor_nonneg'; [apply Z.shiftr_nonneg; auto | unfold CRC_POLY; lia].
  - apply Z.shiftr_nonneg. auto.
Qed.

(* The 32-bit range is kept. *)
Lemma crc_step_range x: 0 <= x < 2 ^ 32 -> 0 <= crc_step x < 2 ^ 32.
Proof.
  intros H. split; [apply crc_step_nonneg; lia | ].
  assert (S: 0 <= Z.shiftr x 1 < 2 ^ 32).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | ].
    apply Z.div_lt_upper_bound; lia. }
  unfold crc_step. destruct (Z.odd x); [ | lia].
  apply (Z.lt_le_trans _ (2 ^ 32)); [ | lia].
  destruct (Z.eq_dec (Z.lxor (Z.shiftr x 1) CRC_POLY) 0) as [E|E]; [rewrite E; lia | ].
  apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia.
  eapply Z.le_lt_trans; [apply Z.log2_lxor; [lia | unfold CRC_POLY; lia] | ].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec (Z.shiftr x 1) 0) as [E0|E0]; [rewrite E0; simpl; lia | ].
    apply Z.log2_lt_pow2; lia.
  - unfold CRC_POLY. simpl. lia.
Qed.

Lemma iter_crc_step_range k x: 0 <= x < 2 ^ 32 -> 0 <= Nat.iter k crc_step x < 2 ^ 32.
Proof. induction k; simpl; auto. intros. apply crc_step_range. auto. Qed.

(* An even value just shifts. *)
Lemma crc_step_even x: Z.odd x = false -> crc_step x = Z.shiftr x 1.
Proof. unfold crc_step. intros ->. reflexivity. Qed.

Lemma iter_succ_r {A} (f: A -> A) k x: Nat.iter (S k) f x = Nat.iter k f (f x).
Proof. induction k; simpl; auto. simpl in IHk. rewrite IHk. reflexivity. Qed.

Lemma iter_crc_step_shiftl k y: 0 <= y -> Nat.iter k crc_step (Z.shiftl y (Z.of_nat k)) = y.
Proof.
  revert y. induction k; intros y Hy.
  - change (Z.of_nat 0) with 0. rewrite Z.shiftl_0_r. reflexivity.
  - rewrite iter_succ_r. rewrite crc_step_even.
    + replace (Z.shiftr (Z.shiftl y (Z.of_nat (S k))) 1) with (Z.shiftl y (Z.of_nat k)).
      * apply IHk; auto.
      * rewrite Z.shiftr_shiftl_l by lia. f_equal. lia.
    + rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.odd_mul. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite Z.odd_mul. simpl. rewrite !andb_false_r. reflexivity.
Qed.

(* Eight steps of x: the high part of x shifted, xor eight steps of its low byte. *)
Lemma iter8_split x: 0 <= x ->
  Nat.iter 8 crc_step x = Z.lxor (Z.shiftr x 8) (Nat.iter 8 crc_step (Z.land x 255)).
Proof.
  intros Hx.
  assert (D: x = Z.lxor (Z.shiftl (Z.shiftr x 8) 8) (Z.land x 255)).
  { apply Z.bits_inj'. intros i Hi.
    rewrite Z.lxor_spec, Z.land_spec.
    change 255 with (Z.ones 8).
    destruct (Z.lt_ge_cases i 8).
    - rewrite Z.shiftl_spec_low by lia. rewrite Z.ones_spec_low by lia.
      rewrite andb_true_r. reflexivity.
    - rewrite Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia.
      rewrite Z.ones_spec_high by lia. rewrite andb_false_r, xorb_false_r. f_equal. lia. }
  rewrite D at 1. rewrite iter_crc_step_lxor.
  change 8%Z with (Z.of_nat 8). rewrite iter_crc_step_shiftl by (apply Z.shiftr_nonneg; auto).
  reflexivity.
Qed.

Lemma ref_crc_byte_0 i: ref_crc_byte 0 i = Nat.iter 8 crc_step i.
Proof. unfold ref_crc_byte. rewrite Z.lxor_0_l. reflexivity. Qed.

(* One table step of crc32_z is the bitwise update of one byte. *)
Lemma crc_table_step c b: 0 <= c -> 0 <= b < 256 ->
  Z.lxor (Z.shiftr c 8) (ref_crc_byte 0 (Z.land (Z.lxor c b) 255)) = ref_crc_byte c b.
Proof.
  intros Hc Hb. rewrite ref_crc_byte_0. unfold ref_crc_byte.
  rewrite (iter8_split (Z.lxor c b)) by (apply lxor_nonneg'; lia).
  f_equal. rewrite Z.shiftr_lxor.
  replace (Z.shiftr b 8) with 0. { rewrite Z.lxor_0_r. reflexivity. }
  symmetry. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. simpl. lia.
Qed.

Lemma ref_crc_byte_range c b: 0 <= c < 2 ^ 32 -> 0 <= b < 256 -> 0 <= ref_crc_byte c b < 2 ^ 32.
Proof.
  intros Hc Hb. unfold ref_crc_byte. apply iter_crc_step_range.
  split; [apply lxor_nonneg'; lia | ].
  destruct (Z.eq_dec (Z.lxor c b) 0) as [E|E]; [rewrite E; lia | ].
  apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia.
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia | ].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec c 0) as [E0|E0]; [rewrite E0; simpl; lia | ]. apply Z.log2_lt_pow2; lia.
  - destruct (Z.eq_dec b 0) as [E0|E0]; [rewrite E0; simpl; lia | ].
    apply (Z.le_lt_trans _ (Z.log2 255)); [apply Z.log2_le_mono; lia | simpl; lia].
Qed.

Lemma crc_fold_range data c: is_bytes data -> 0 <= c < 2 ^ 32 ->
  0 <= fold_left ref_crc_byte data c < 2 ^ 32.
Proof.
  revert c. induction data as [|b data IH]; intros c HB Hc; simpl; auto.
  inv HB. apply IH; auto. apply ref_crc_byte_range; auto. rep_lia.
Qed.

Lemma Znth_crc_table_vals i: 0 <= i < 256 -> Znth i crc_table_vals = ref_crc_byte 0 i.
Proof.
  intros. unfold crc_table_vals. rewrite Znth_map by (rewrite Zlength_upto; simpl; lia).
  rewrite Znth_upto by (simpl; lia). reflexivity.
Qed.

Lemma Zlength_crc_table_vals: Zlength crc_table_vals = 256.
Proof. reflexivity. Qed.
