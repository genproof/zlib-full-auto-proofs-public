(* What crc32_combine computes, in terms of the reference: the CRC-32 of a concatenation
   (crc32_combine_val_app), and the register advanced over zero bytes (crc32_combine_val_zeros). *)
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.crc32.X2n.
Require Import Coq.btauto.Btauto.

(* The register update is linear: from r over D, it is r advanced over |D| zero bytes xor the update
   from 0. *)
Lemma crc_fold_linear: forall D r,
  fold_left ref_crc_byte D r = Z.lxor (Nat.iter (8 * length D) crc_step r) (fold_left ref_crc_byte D 0).
Proof.
  induction D as [|b D IH]; intros r; cbn [fold_left length].
  - rewrite Z.lxor_0_r. reflexivity.
  - rewrite (IH (ref_crc_byte r b)), (IH (ref_crc_byte 0 b)).
    replace (8 * S (length D))%nat with (8 * length D + 8)%nat by lia.
    rewrite Nat.iter_add.
    unfold ref_crc_byte. rewrite Z.lxor_0_l, iter_crc_step_lxor, iter_crc_step_lxor.
    apply Z.bits_inj'. intros i Hi. rewrite !Z.lxor_spec. btauto.
Qed.

Lemma ref_crc32_range c D: is_bytes D -> is32 (ref_crc32 c D).
Proof.
  intros. unfold ref_crc32. apply lxor_lt_pow2; [lia | | apply crc_mask_range].
  apply crc_fold_range; auto. apply lxor_lt_pow2; [lia | apply is32_mod | apply crc_mask_range].
Qed.

Lemma is32_mod_id x: is32 x -> x mod 2 ^ 32 = x.
Proof. unfold is32. intros. apply Z.mod_small. auto. Qed.

(* crc32_combine(crc32(c0, A), crc32(0, B), |B|) = crc32(c0, A B). *)
Lemma crc32_combine_val_app c0 A B: is_bytes A -> is_bytes B -> Zlength B < 2 ^ 63 ->
  crc32_combine_val (ref_crc32 c0 A) (ref_crc32 0 B) (Zlength B) = ref_crc32 c0 (A ++ B).
Proof.
  intros HA HB HL. pose proof (Zlength_nonneg B).
  rewrite crc32_combine_val_shift by lia.
  rewrite !is32_mod_id by (apply ref_crc32_range; auto).
  rewrite Zlength_correct, Nat2Z.id.
  unfold ref_crc32. rewrite fold_left_app.
  rewrite (crc_fold_linear B (fold_left ref_crc_byte A _)).
  rewrite (crc_fold_linear B (Z.lxor (0 mod 2 ^ 32) crc_mask)).
  rewrite Zmod_0_l, Z.lxor_0_l.
  rewrite iter_crc_step_lxor.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.lxor_spec. btauto.
Qed.

(* The register advanced over z zero bytes, as the harness computes it. *)
Fixpoint zeros_reg (z: nat) (r: Z) : Z := match z with O => r | S z' => ref_crc_byte (zeros_reg z' r) 0 end.

Lemma zeros_reg_iter z r: zeros_reg z r = Nat.iter (8 * z) crc_step r.
Proof.
  induction z; cbn [zeros_reg]; [reflexivity | ].
  rewrite IHz. unfold ref_crc_byte. rewrite Z.lxor_0_r.
  replace (8 * S z)%nat with (8 + 8 * z)%nat by lia. rewrite Nat.iter_add. reflexivity.
Qed.

Lemma crc32_combine_val_zeros x y z: 0 <= z < 2 ^ 63 ->
  crc32_combine_val x y z = Z.lxor (zeros_reg (Z.to_nat z) (x mod 2 ^ 32)) (y mod 2 ^ 32).
Proof. intros. rewrite crc32_combine_val_shift, zeros_reg_iter by auto. reflexivity. Qed.

(* Continuing is concatenating: crc32(crc32(c, A), B) = crc32(c, A B). *)
Lemma ref_crc32_app c d1 d2: is_bytes d1 -> ref_crc32 (ref_crc32 c d1) d2 = ref_crc32 c (d1 ++ d2).
Proof.
  intros H1.
  assert (R: is32 (fold_left ref_crc_byte d1 (Z.lxor (c mod 2 ^ 32) crc_mask))).
  { apply crc_fold_range; auto. apply lxor_lt_pow2; [lia | apply is32_mod | apply crc_mask_range]. }
  unfold ref_crc32 at 1 3. rewrite fold_left_app.
  unfold ref_crc32.
  rewrite is32_mod_id by (apply lxor_lt_pow2; [lia | apply R | apply crc_mask_range]).
  rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity.
Qed.
