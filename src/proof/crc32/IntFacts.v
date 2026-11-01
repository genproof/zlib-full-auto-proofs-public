(* Machine-integer facts for the body proofs of crc32.c: the operations of crc32_z on unsigned long
   values as operations on Z. *)
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.crc32.Facts.
Require Import Coq.btauto.Btauto.

Lemma Z_land_255_range x: 0 <= Z.land x 255 < 256.
Proof.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma lxor_lt_pow2 x y k: 0 < k -> 0 <= x < 2 ^ k -> 0 <= y < 2 ^ k -> 0 <= Z.lxor x y < 2 ^ k.
Proof.
  intros Hk Hx Hy. split; [apply lxor_nonneg'; lia | ].
  destruct (Z.eq_dec (Z.lxor x y) 0) as [E|E]; [rewrite E; lia | ].
  apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia.
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia | ].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec x 0) as [E0|E0]; [rewrite E0; simpl; lia | ]. apply Z.log2_lt_pow2; lia.
  - destruct (Z.eq_dec y 0) as [E0|E0]; [rewrite E0; simpl; lia | ]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma crc_mask_range: 0 <= crc_mask < 2 ^ 32.
Proof. unfold crc_mask. lia. Qed.

(* crc = (~crc) & 0xffffffff on any 64-bit crc. *)
Lemma crc_pre_int crc: 0 <= crc <= Int64.max_unsigned ->
  Int64.and (Int64.not (Int64.repr crc)) (Int64.repr (Int.unsigned (Int.repr (-1)))) =
  Int64.repr (Z.lxor (crc mod 2 ^ 32) crc_mask).
Proof.
  intros H. apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_and, Int64.bits_not by auto.
  change (Int.unsigned (Int.repr (-1))) with crc_mask.
  rewrite !Int64.testbit_repr by auto.
  rewrite Z.lxor_spec. unfold crc_mask. change 4294967295 with (Z.ones 32).
  change Int64.zwordsize with 64 in Hi.
  destruct (Z.lt_ge_cases i 32).
  - rewrite Z.ones_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia. btauto.
  - rewrite Z.ones_spec_high by lia. rewrite Z.mod_pow2_bits_high by lia. btauto.
Qed.

(* The table index (crc ^ b) & 0xff. *)
Lemma crc_idx_int c b: 0 <= c < 2 ^ 32 -> 0 <= b <= Byte.max_unsigned ->
  Ptrofs.unsigned (Ptrofs.of_int64 (Int64.and (Int64.xor (Int64.repr c) (Int64.repr b)) (Int64.repr 255))) =
  Z.land (Z.lxor c b) 255.
Proof.
  intros Hc Hb. unfold Int64.and, Int64.xor.
  pose proof (lxor_lt_pow2 c b 32 ltac:(lia) Hc ltac:(rep_lia)).
  pose proof (Z_land_255_range (Z.lxor c b)).
  rewrite (Int64.unsigned_repr c), (Int64.unsigned_repr b), (Int64.unsigned_repr 255) by rep_lia.
  rewrite (Int64.unsigned_repr (Z.lxor c b)) by rep_lia.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia.
  apply Ptrofs.unsigned_repr. rep_lia.
Qed.

Lemma crc_table_load {d: Inhabitant val} c b: 0 <= c < 2 ^ 32 -> 0 <= b <= Byte.max_unsigned ->
  @Znth val d (Ptrofs.unsigned (Ptrofs.of_int64 (Int64.and (Int64.xor (Int64.repr c) (Int64.repr b))
                                                  (Int64.repr 255)))) crc_table_rep =
  Vint (Int.repr (ref_crc_byte 0 (Z.land (Z.lxor c b) 255))).
Proof.
  intros Hc Hb. rewrite crc_idx_int by auto.
  pose proof (Z_land_255_range (Z.lxor c b)).
  unfold crc_table_rep. rewrite Znth_map by (rewrite Zlength_crc_table_vals; lia).
  rewrite Znth_crc_table_vals by lia. reflexivity.
Qed.

(* crc = (crc >> 8) ^ crc_table[..]: one byte. *)
Lemma crc_update_int c b: 0 <= c < 2 ^ 32 -> 0 <= b <= Byte.max_unsigned ->
  Int64.xor (Int64.shru (Int64.repr c) (Int64.repr (Int.unsigned (Int.repr 8))))
    (Int64.repr (Int.unsigned (Int.repr (ref_crc_byte 0 (Z.land (Z.lxor c b) 255))))) =
  Int64.repr (ref_crc_byte c b).
Proof.
  intros Hc Hb.
  pose proof (Z_land_255_range (Z.lxor c b)).
  assert (R0: 0 <= ref_crc_byte 0 (Z.land (Z.lxor c b) 255) < 2 ^ 32) by (apply ref_crc_byte_range; lia).
  unfold Int64.xor, Int64.shru.
  rewrite (Int.unsigned_repr 8) by rep_lia.
  rewrite (Int.unsigned_repr (ref_crc_byte _ _)) by rep_lia.
  rewrite (Int64.unsigned_repr c), (Int64.unsigned_repr 8), (Int64.unsigned_repr (ref_crc_byte _ _)) by rep_lia.
  rewrite Int64.unsigned_repr.
  2: { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | ].
       apply (Z.le_trans _ c); [apply Z.div_le_upper_bound; lia | rep_lia]. }
  f_equal. apply crc_table_step; rep_lia.
Qed.

(* return crc ^ 0xffffffff *)
Lemma crc_post_int r: 0 <= r < 2 ^ 32 ->
  Int64.xor (Int64.repr r) (Int64.repr (Int.unsigned (Int.repr (-1)))) = Int64.repr (Z.lxor r crc_mask).
Proof.
  intros H. unfold Int64.xor. change (Int.unsigned (Int.repr (-1))) with crc_mask.
  rewrite !Int64.unsigned_repr by (unfold crc_mask; rep_lia). reflexivity.
Qed.

(* The register after i bytes. *)
Definition crc_reg (c0: Z) (data: list Z) (i: Z) : Z := fold_left ref_crc_byte (sublist 0 i data) c0.

Lemma crc_reg_range c0 data i: 0 <= c0 < 2 ^ 32 -> is_bytes data -> 0 <= crc_reg c0 data i < 2 ^ 32.
Proof. intros. apply crc_fold_range; auto. apply is_bytes_sublist; auto. Qed.

Lemma crc_reg_succ c0 data i: 0 <= i < Zlength data ->
  ref_crc_byte (crc_reg c0 data i) (Znth i data) = crc_reg c0 data (i + 1).
Proof.
  intros. unfold crc_reg. rewrite (sublist_split 0 i (i + 1)) by lia.
  rewrite fold_left_app. rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma crc_reg_0 c0 data: crc_reg c0 data 0 = c0.
Proof. unfold crc_reg. rewrite sublist_nil. reflexivity. Qed.

Lemma crc_reg_full c0 data: crc_reg c0 data (Zlength data) = fold_left ref_crc_byte data c0.
Proof. unfold crc_reg. rewrite sublist_same by lia. reflexivity. Qed.
