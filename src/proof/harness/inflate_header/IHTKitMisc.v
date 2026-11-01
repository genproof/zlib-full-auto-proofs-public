(* Law inflate_header, theory part: bit facts of FLG/XFL/OS, the CRC of a prefix, the input offered *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_header.IHTDefs.
Require Import Zlib.proof.crc32.Combine.
Import ListNotations.
Local Open Scope Z_scope.

(* the facts about state->flags = 8 + 256 * FLG, as one boolean test per FLG *)
Definition ihm_chk (F: Z) : bool :=
  let x := 8 + 256 * F in
  (s32 x =? x) && (Z.land x 255 =? 8) &&
  Bool.eqb (Z.land x 57344 =? 0) (Z.land F 224 =? 0) &&
  Bool.eqb (Z.land x 512 =? 0) (Z.land F 2 =? 0) &&
  Bool.eqb (Z.land x 1024 =? 0) (Z.land F 4 =? 0) &&
  Bool.eqb (Z.land x 2048 =? 0) (Z.land F 8 =? 0) &&
  Bool.eqb (Z.land x 4096 =? 0) (Z.land F 16 =? 0) &&
  (Z.land (Z.shiftr x 8) 1 =? Z.land F 1) &&
  (Z.land (Z.shiftr x 9) 1 =? Z.land (Z.shiftr F 1) 1).

Lemma ihm_chk_all : forallb ihm_chk (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ihm_chk_ok F : 0 <= F <= 255 -> ihm_chk F = true.
Proof.
  intros R. pose proof ihm_chk_all as A. rewrite forallb_forall in A. apply A.
  apply in_map_iff. exists (Z.to_nat F). split; [lia|]. apply in_seq. lia.
Qed.

Lemma ihm_bits : ih_bits_stmt.
Proof.
  split.
  - intros F R. pose proof (ihm_chk_ok F R) as C. unfold ihm_chk in C. cbv zeta in C.
    repeat rewrite andb_true_iff in C.
    destruct C as [[[[[[[[C1 C2] C3] C4] C5] C6] C7] C8] C9].
    apply Z.eqb_eq in C1, C2, C8, C9. apply Bool.eqb_prop in C3, C4, C5, C6, C7.
    repeat split; assumption.
  - intros a b A B. split.
    + change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
      rewrite (Z.mul_comm 256 b), Z.mod_add by lia. apply Z.mod_small. lia.
    + rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
      replace ((a + 256 * b) / 256) with b.
      * unfold s32. rewrite Z.mod_small by lia. destruct (Z.ltb_spec b (2 ^ 31)); lia.
      * apply Z.div_unique with a; lia.
Qed.

Lemma ihm_crc : ih_crc_stmt.
Proof.
  intros src a b B R L.
  rewrite ref_crc32_app by (apply is_bytes_sublist; exact B).
  f_equal. rewrite <- sublist_split by lia. reflexivity.
Qed.

Lemma ihm_in : ih_in_stmt.
Proof.
  intros src inp pos nx n P PL E N Nn NL.
  set (L := Zlength inp) in *. clearbody L. subst inp.
  split.
  - rewrite sublist_sublist by lia. f_equal; lia.
  - intros Np. rewrite Znth_sublist by lia. f_equal; lia.
Qed.

Lemma ih_misc_proof : ih_bits_stmt /\ ih_crc_stmt /\ ih_in_stmt.
Proof. exact (conj ihm_bits (conj ihm_crc ihm_in)). Qed.
