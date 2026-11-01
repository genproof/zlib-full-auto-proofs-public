(* Facts for the body proof of adler32_z: the sums over a slice, their bounds, and the machine-integer
   operations of the code as operations on Z. *)
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.adler32.Model.

Lemma adler_sums_app s l1 l2: adler_sums s (l1 ++ l2) = adler_sums (adler_sums s l1) l2.
Proof. unfold adler_sums. apply fold_left_app. Qed.

(* The sums over data[i0 .. j). *)
Definition adler_seg (s: Z * Z) (data: list Z) (i0 j: Z) : Z * Z := adler_sums s (sublist i0 j data).

Lemma adler_seg_nil s data i0: adler_seg s data i0 i0 = s.
Proof. unfold adler_seg. rewrite sublist_nil. reflexivity. Qed.

Lemma adler_seg_succ s data i0 j: 0 <= i0 <= j -> j < Zlength data ->
  adler_seg s data i0 (j + 1) = adler_sum_step (adler_seg s data i0 j) (Znth j data).
Proof.
  intros. unfold adler_seg. rewrite (sublist_split i0 j (j + 1)) by lia.
  rewrite adler_sums_app, sublist_len_1 by lia. reflexivity.
Qed.

Lemma adler_seg_trans s data i0 i1 j: 0 <= i0 <= i1 -> i1 <= j <= Zlength data ->
  adler_seg s data i0 j = adler_seg (adler_seg s data i0 i1) data i1 j.
Proof.
  intros. unfold adler_seg. rewrite (sublist_split i0 i1 j) by lia. apply adler_sums_app.
Qed.

Lemma adler_sums_bound: forall l A S, 0 <= A -> 0 <= S -> is_bytes l ->
  0 <= fst (adler_sums (A, S) l) <= A + 255 * Zlength l /\
  0 <= snd (adler_sums (A, S) l) <= S + Zlength l * (A + 255 * Zlength l).
Proof.
  induction l as [|b l IH]; intros A S HA HS HB; simpl.
  - rewrite Zlength_nil. lia.
  - inv HB. rewrite Zlength_cons.
    unfold adler_sums in *. simpl.
    replace (adler_sum_step (A, S) b) with (A + b, S + (A + b)) by reflexivity.
    destruct (IH (A + b) (S + (A + b))) as [[F1 F2] [G1 G2]]; try rep_lia; auto.
    pose proof (Zlength_nonneg l).
    split; [split; rep_lia | split; [lia | ]].
    eapply Z.le_trans; [exact G2 | ].
    assert (b <= 255) by rep_lia. nia.
Qed.

Lemma adler_seg_bound s data i0 j: 0 <= fst s -> 0 <= snd s -> is_bytes data -> 0 <= i0 <= j -> j <= Zlength data ->
  0 <= fst (adler_seg s data i0 j) <= fst s + 255 * (j - i0) /\
  0 <= snd (adler_seg s data i0 j) <= snd s + (j - i0) * (fst s + 255 * (j - i0)).
Proof.
  intros. unfold adler_seg. destruct s as [A S].
  pose proof (adler_sums_bound (sublist i0 j data) A S).
  rewrite Zlength_sublist in H4 by lia. apply H4; auto. apply is_bytes_sublist; auto.
Qed.

(* Congruence of the sums with the reference over the whole prefix. *)
Lemma adler_seg_mod s t data i0 j:
  fst s mod ADLER_BASE = fst t mod ADLER_BASE -> snd s mod ADLER_BASE = snd t mod ADLER_BASE ->
  fst (adler_seg s data i0 j) mod ADLER_BASE = fst (adler_seg t data i0 j) mod ADLER_BASE /\
  snd (adler_seg s data i0 j) mod ADLER_BASE = snd (adler_seg t data i0 j) mod ADLER_BASE.
Proof. intros. unfold adler_seg. apply adler_sums_mod; auto. Qed.

(* ---------------------------------------------------------------------- *)
(* Machine integers                                                        *)
(* ---------------------------------------------------------------------- *)

Lemma adler_lo_int a: 0 <= a <= Int64.max_unsigned ->
  Int64.and (Int64.repr a) (Int64.repr (Int.signed (Int.repr 65535))) = Int64.repr (adler_lo a).
Proof.
  intros. change (Int.signed (Int.repr 65535)) with 65535. unfold Int64.and.
  rewrite !Int64.unsigned_repr by rep_lia. f_equal.
  change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma adler_hi_int a: 0 <= a <= Int64.max_unsigned ->
  Int64.and (Int64.shru (Int64.repr a) (Int64.repr (Int.unsigned (Int.repr 16))))
    (Int64.repr (Int.signed (Int.repr 65535))) = Int64.repr (adler_hi a).
Proof.
  intros. change (Int.signed (Int.repr 65535)) with 65535. change (Int.unsigned (Int.repr 16)) with 16.
  unfold Int64.and, Int64.shru.
  rewrite (Int64.unsigned_repr a), (Int64.unsigned_repr 16) by rep_lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Int64.unsigned_repr.
  2: { split; [apply Z.div_pos; lia | ]. apply (Z.le_trans _ a); [apply Z.div_le_upper_bound; lia | lia]. }
  rewrite Int64.unsigned_repr by rep_lia. f_equal.
  change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma modu_int x: 0 <= x <= Int64.max_unsigned ->
  Int64.modu (Int64.repr x) (Int64.repr (Int.unsigned (Int.repr 65521))) = Int64.repr (x mod ADLER_BASE).
Proof.
  intros. change (Int.unsigned (Int.repr 65521)) with 65521. unfold Int64.modu.
  rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma pack_int s1 s2: 0 <= s1 < 65536 -> 0 <= s2 < 65536 ->
  Int64.or (Int64.repr s1) (Int64.shl (Int64.repr s2) (Int64.repr (Int.unsigned (Int.repr 16)))) =
  Int64.repr (s2 * 65536 + s1).
Proof.
  intros. change (Int.unsigned (Int.repr 16)) with 16.
  unfold Int64.or, Int64.shl.
  rewrite (Int64.unsigned_repr s2), (Int64.unsigned_repr 16) by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536.
  rewrite !Int64.unsigned_repr by rep_lia. f_equal.
  replace (s2 * 65536) with (Z.shiftl s2 16) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  assert (L: Z.land s1 (Z.shiftl s2 16) = 0).
  { apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases j 16).
    + rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    + rewrite (Z.bits_above_log2 s1 j); [reflexivity | lia | ].
      destruct (Z.eq_dec s1 0) as [E|E]; [subst; simpl; lia | ].
      apply (Z.lt_le_trans _ 16); [apply Z.log2_lt_pow2; lia | lia]. }
  rewrite <- Z.lxor_lor by auto. rewrite <- Z.add_nocarry_lxor by auto. lia.
Qed.

(* The two sums over data[i0 .. i). *)
Definition aseg1 (s: Z * Z) (data: list Z) (i0 i: Z) : Z := fst (adler_seg s data i0 i).
Definition aseg2 (s: Z * Z) (data: list Z) (i0 i: Z) : Z := snd (adler_seg s data i0 i).

Lemma aseg1_succ s data i0 i: 0 <= i0 <= i -> i < Zlength data ->
  aseg1 s data i0 i + Znth i data = aseg1 s data i0 (i + 1).
Proof. intros. unfold aseg1. rewrite adler_seg_succ by lia. reflexivity. Qed.

Lemma aseg2_succ s data i0 i: 0 <= i0 <= i -> i < Zlength data ->
  aseg2 s data i0 i + aseg1 s data i0 (i + 1) = aseg2 s data i0 (i + 1).
Proof. intros. unfold aseg1, aseg2. rewrite adler_seg_succ by lia. reflexivity. Qed.

Lemma aseg_nil s data i0: aseg1 s data i0 i0 = fst s /\ aseg2 s data i0 i0 = snd s.
Proof. unfold aseg1, aseg2. rewrite adler_seg_nil. auto. Qed.

Lemma aseg_bound s data i0 i: 0 <= fst s -> 0 <= snd s -> is_bytes data -> 0 <= i0 <= i -> i <= Zlength data ->
  0 <= aseg1 s data i0 i <= fst s + 255 * (i - i0) /\
  0 <= aseg2 s data i0 i <= snd s + (i - i0) * (fst s + 255 * (i - i0)).
Proof. intros. unfold aseg1, aseg2. apply adler_seg_bound; auto. Qed.

Lemma aseg_trans s data i0 i1 i: 0 <= i0 <= i1 -> i1 <= i <= Zlength data ->
  aseg1 s data i0 i = aseg1 (adler_seg s data i0 i1) data i1 i /\
  aseg2 s data i0 i = aseg2 (adler_seg s data i0 i1) data i1 i.
Proof. intros. unfold aseg1, aseg2. rewrite (adler_seg_trans s data i0 i1 i) by lia. auto. Qed.

Lemma ltu64_repr x y: 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.unsigned (Int64.repr x) = x /\ Int64.unsigned (Int64.repr y) = y.
Proof. intros. rewrite !Int64.unsigned_repr by auto. auto. Qed.

Lemma aseg_full s data:
  aseg1 s data 0 (Zlength data) = fst (adler_sums s data) /\ aseg2 s data 0 (Zlength data) = snd (adler_sums s data).
Proof. unfold aseg1, aseg2, adler_seg. rewrite sublist_same by lia. auto. Qed.

(* The result of the long and short paths. *)
Lemma adler32_z_val_sums a data: Zlength data <> 1 ->
  adler32_z_val a data =
    (aseg2 (adler_lo a, adler_hi a) data 0 (Zlength data) mod ADLER_BASE) * 65536 +
    aseg1 (adler_lo a, adler_hi a) data 0 (Zlength data) mod ADLER_BASE.
Proof.
  intros. rewrite adler32_z_val_long.
  - destruct (aseg_full (adler_lo a, adler_hi a) data) as [-> ->]. reflexivity.
  - intros b E. subst. rewrite Zlength_cons, Zlength_nil in H. lia.
Qed.

Lemma aseg_step_mod s0 data A S i j: 0 <= i <= j -> j <= Zlength data ->
  A mod ADLER_BASE = aseg1 s0 data 0 i mod ADLER_BASE -> S mod ADLER_BASE = aseg2 s0 data 0 i mod ADLER_BASE ->
  aseg1 (A, S) data i j mod ADLER_BASE = aseg1 s0 data 0 j mod ADLER_BASE /\
  aseg2 (A, S) data i j mod ADLER_BASE = aseg2 s0 data 0 j mod ADLER_BASE.
Proof.
  intros Hij Hj HA HS. destruct (aseg_trans s0 data 0 i j) as [T1 T2]; try lia.
  rewrite T1, T2. unfold aseg1, aseg2. apply adler_seg_mod; simpl; auto.
Qed.

Lemma aseg_block_bound A S data i j: 0 <= A < 65536 -> 0 <= S < 65536 -> is_bytes data ->
  0 <= i <= j -> j <= Zlength data -> j - i <= 5552 ->
  0 <= aseg1 (A, S) data i j <= Int64.max_unsigned /\ 0 <= aseg2 (A, S) data i j <= Int64.max_unsigned.
Proof.
  intros. destruct (aseg_bound (A, S) data i j) as [B1 B2]; simpl; try lia; auto.
  simpl fst in *; simpl snd in *.
  assert ((j - i) * (A + 255 * (j - i)) <= 5552 * (65536 + 255 * 5552)) by nia.
  split; rep_lia.
Qed.

Lemma mods_int x: 0 <= x <= Int64.max_signed ->
  Int64.mods (Int64.repr x) (Int64.repr 65521) = Int64.repr (x mod ADLER_BASE).
Proof.
  intros. unfold Int64.mods. rewrite !Int64.signed_repr by rep_lia.
  rewrite Z.rem_mod_nonneg by lia. reflexivity.
Qed.

Lemma lor_pack_int s1 s2: 0 <= s1 < 2 ^ 32 -> 0 <= s2 < 2 ^ 32 ->
  Int64.or (Int64.repr s1) (Int64.shl (Int64.repr s2) (Int64.repr (Int.unsigned (Int.repr 16)))) =
  Int64.repr (Z.lor s1 (s2 * 65536)).
Proof.
  intros. change (Int.unsigned (Int.repr 16)) with 16.
  unfold Int64.or, Int64.shl.
  rewrite (Int64.unsigned_repr s2), (Int64.unsigned_repr 16) by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536.
  rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.
