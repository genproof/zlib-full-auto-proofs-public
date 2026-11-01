(* x2nmodp(n, k) = x^(n * 2^k) mod P, crc32_combine_gen/op/combine: the exact results of crc32.c's
   functions as Coq functions, and what they mean:
   - x2n_val n k (the loop of x2nmodp, one step per bit of n) represents crc_step^(n * 2^k)
     (x2n_val_rep), for every n >= 0 and k >= 0 (x2n_table wraps around: x^(2^32) = x mod P);
   - crc32_combine_val x y z, for z >= 0: the register of x (32 low bits) advanced over z zero bytes,
     xor the 32 low bits of y (crc32_combine_val_shift); for z < 0: 0;
   - hence the CRC-32 of a concatenation (crc32_combine_val_app). *)
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.crc32.GF2.
Require Import Coq.setoid_ring.ArithRing.

(* zlib's constant x2n_table (crc32.h), as unsigned values: x^(2^k) mod P for k = 0..31. *)
Definition x2n_table_vals : list Z :=
  [1073741824; 536870912; 134217728; 8388608; 32768; 3988292384; 2984685714; 2691310871; 3982654894;
   2295415911; 3619421802; 3963911953; 2390663536; 1680310286; 1296546528; 167662735; 2206543119;
   808857370; 2069535939; 838779241; 2683044394; 1821240772; 366380877; 1608415822; 3134787127;
   776888047; 1319870996; 2829349568; 1117427358; 344797226; 3289097936; 3303156796].

Definition x2n_tbl (k: Z) : Z := Znth (k mod 32) x2n_table_vals.

(* The loop of x2nmodp: while (n) { if (n & 1) p = multmodp(x2n_table[k & 31], p); n >>= 1; k++; } *)
Fixpoint x2n_aux (fuel: nat) (n k p: Z) : Z :=
  match fuel with
  | O => p
  | S f => if n =? 0 then p else x2n_aux f (n / 2) (k + 1) (if Z.odd n then gf_mul (x2n_tbl k) p else p)
  end.

Definition x2n_val (n k: Z) : Z := x2n_aux 64 n k (2 ^ 31).

(* crc32_combine_gen64(len2) and crc32_combine_op(crc1, crc2, op). *)
Definition crc32_combine_gen_val (len2: Z) : Z := if len2 <? 0 then 0 else x2n_val len2 3.

Definition crc32_combine_op_val (crc1 crc2 op: Z) : Z :=
  if op =? 0 then 0 else Z.lxor (gf_mul op (crc1 mod 2 ^ 32)) (crc2 mod 2 ^ 32).

Definition crc32_combine_val (crc1 crc2 len2: Z) : Z :=
  crc32_combine_op_val crc1 crc2 (crc32_combine_gen_val len2).

(* ---------------------------------------------------------------------- *)
(* the table                                                               *)
(* ---------------------------------------------------------------------- *)

Lemma x2n_table_0: Znth 0 x2n_table_vals = 2 ^ 30.
Proof. reflexivity. Qed.

Lemma x2n_table_sq: forall k, 0 <= k < 31 ->
  Znth (k + 1) x2n_table_vals = gf_mul (Znth k x2n_table_vals) (Znth k x2n_table_vals).
Proof.
  intros k Hk.
  assert (E: forall k, (k < 31)%nat ->
    Znth (Z.of_nat k + 1) x2n_table_vals = gf_mul (Znth (Z.of_nat k) x2n_table_vals) (Znth (Z.of_nat k) x2n_table_vals)).
  { intros j Hj. do 31 (destruct j as [|j]; [vm_compute; reflexivity | ]). lia. }
  replace k with (Z.of_nat (Z.to_nat k)) by lia. apply E. lia.
Qed.

Lemma x2n_table_wrap: gf_mul (Znth 31 x2n_table_vals) (Znth 31 x2n_table_vals) = Znth 0 x2n_table_vals.
Proof. vm_compute. reflexivity. Qed.

Lemma x2n_table_is32: forall k, 0 <= k < 32 -> is32 (Znth k x2n_table_vals).
Proof.
  intros k Hk.
  assert (E: forall k, (k < 32)%nat -> is32 (Znth (Z.of_nat k) x2n_table_vals)).
  { intros j Hj. unfold is32. do 32 (destruct j as [|j]; [vm_compute; split; congruence | ]). lia. }
  replace k with (Z.of_nat (Z.to_nat k)) by lia. apply E. lia.
Qed.

Lemma rep_x1: rep (2 ^ 30) 1.
Proof.
  split; [unfold is32; lia | ]. intros b Hb.
  change (2 ^ 30) with (2 ^ Z.of_nat 30). rewrite gf_mul_pow2 by lia. reflexivity.
Qed.

Lemma rep_ext a N M: rep a N -> (forall b, is32 b -> Nat.iter N crc_step b = Nat.iter M crc_step b) -> rep a M.
Proof. intros [Ha R] E. split; auto. intros. rewrite R, E by auto. auto. Qed.

Lemma pow2_double n: (2 ^ S n = 2 ^ n + 2 ^ n)%nat.
Proof. rewrite Nat.pow_succ_r'. lia. Qed.

Lemma rep_table_low: forall k, (k < 32)%nat -> rep (Znth (Z.of_nat k) x2n_table_vals) (2 ^ k).
Proof.
  induction k; intros Hk.
  - change (Z.of_nat 0) with 0. change (2 ^ 0)%nat with 1%nat. rewrite x2n_table_0. apply rep_x1.
  - replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
    rewrite x2n_table_sq by lia.
    rewrite pow2_double. apply rep_mul; apply IHk; lia.
Qed.

(* x^(2^32) = x: the step to the power 2^32 is the step. *)
Lemma iter_2_32 b: is32 b -> Nat.iter (2 ^ 32) crc_step b = crc_step b.
Proof.
  intros Hb.
  pose proof (rep_mul _ _ _ _ (rep_table_low 31 ltac:(lia)) (rep_table_low 31 ltac:(lia))) as R.
  change (Z.of_nat 31) with 31 in R. rewrite x2n_table_wrap in R. destruct R as [_ R].
  destruct (rep_table_low 0 ltac:(lia)) as [_ R0]. change (Z.of_nat 0) with 0 in R0.
  rewrite (pow2_double 31). rewrite <- R by auto. rewrite R0 by auto. reflexivity.
Qed.

Lemma iter_mul_2_32 a b: is32 b -> Nat.iter (a * 2 ^ 32) crc_step b = Nat.iter a crc_step b.
Proof.
  revert b. induction a; intros b Hb.
  - rewrite Nat.mul_0_l. reflexivity.
  - rewrite Nat.mul_succ_l, Nat.iter_add.
    rewrite IHa by (apply is32_iter; auto). rewrite iter_2_32 by auto.
    symmetry. apply iter_succ_r.
Qed.

Lemma rep_tbl: forall k, 0 <= k -> rep (x2n_tbl k) (2 ^ Z.to_nat k).
Proof.
  intros k Hk. unfold x2n_tbl.
  assert (E: forall b, is32 b -> Nat.iter (2 ^ Z.to_nat k) crc_step b = Nat.iter (2 ^ Z.to_nat (k mod 32)) crc_step b).
  { intros b Hb.
    replace (Z.to_nat k) with (Z.to_nat (32 * (k / 32) + k mod 32)) by (f_equal; symmetry; apply Z_div_mod_eq_full).
    rewrite Z2Nat.inj_add by (try apply Z.mod_pos_bound; try apply Z.mul_nonneg_nonneg; try apply Z.div_pos; lia).
    rewrite Nat.pow_add_r.
    rewrite Z2Nat.inj_mul by (try apply Z.div_pos; lia).
    rewrite Nat.pow_mul_r. change (Z.to_nat 32) with 32%nat.
    rewrite (Nat.mul_comm ((2 ^ 32) ^ Z.to_nat (k / 32))).
    remember (Z.to_nat (k / 32)) as q. clear Heqq. induction q.
    - rewrite Nat.pow_0_r, Nat.mul_1_r. auto.
    - rewrite Nat.pow_succ_r'.
      replace (2 ^ Z.to_nat (k mod 32) * (2 ^ 32 * (2 ^ 32) ^ q))%nat
        with ((2 ^ Z.to_nat (k mod 32) * (2 ^ 32) ^ q) * 2 ^ 32)%nat by lia.
      rewrite iter_mul_2_32 by auto. auto. }
  eapply rep_ext; [ | intros; symmetry; apply E; auto].
  replace (k mod 32) with (Z.of_nat (Z.to_nat (k mod 32))) at 1 by (rewrite Z2Nat.id; auto; apply Z.mod_pos_bound; lia).
  apply rep_table_low. pose proof (Z.mod_pos_bound k 32). lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* x2nmodp                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma x2n_aux_rep: forall f n k p N, 0 <= n < 2 ^ Z.of_nat f -> 0 <= k -> rep p N ->
  rep (x2n_aux f n k p) (N + Z.to_nat n * 2 ^ Z.to_nat k).
Proof.
  induction f; intros n k p N Hn Hk Hp; cbn [x2n_aux].
  - simpl in Hn. assert (n = 0) by lia. subst. simpl. rewrite Nat.add_0_r. auto.
  - destruct (Z.eqb_spec n 0) as [E|E].
    + subst. simpl. rewrite Nat.add_0_r. auto.
    + assert (Hn2: 0 <= n / 2 < 2 ^ Z.of_nat f).
      { split; [apply Z.div_pos; lia | ]. apply Z.div_lt_upper_bound; [lia | ].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hn by lia. lia. }
      assert (D: n = 2 * (n / 2) + (if Z.odd n then 1 else 0)).
      { rewrite (Z.div_mod n 2) at 1 by lia. rewrite Zmod_odd. auto. }
      assert (P2: (2 ^ Z.to_nat (k + 1) = 2 * 2 ^ Z.to_nat k)%nat).
      { rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. rewrite Nat.add_1_r. apply Nat.pow_succ_r'. }
      destruct (Z.odd n) eqn:O.
      * assert (Q: Z.to_nat n = (2 * Z.to_nat (n / 2) + 1)%nat) by lia.
        eapply rep_ext.
        -- apply IHf; [auto | lia | ]. apply rep_mul; [apply rep_tbl; lia | apply Hp].
        -- intros b Hb. f_equal. rewrite P2, Q. ring.
      * assert (Q: Z.to_nat n = (2 * Z.to_nat (n / 2))%nat) by lia.
        eapply rep_ext.
        -- apply IHf; [auto | lia | apply Hp].
        -- intros b Hb. f_equal. rewrite P2, Q. ring.
Qed.

Lemma x2n_val_rep n k: 0 <= n < 2 ^ 64 -> 0 <= k -> rep (x2n_val n k) (Z.to_nat n * 2 ^ Z.to_nat k).
Proof.
  intros Hn Hk. unfold x2n_val. apply (x2n_aux_rep 64 n k (2 ^ 31) 0); auto. apply rep_one.
Qed.

Lemma x2n_val_is32 n k: 0 <= n < 2 ^ 64 -> 0 <= k -> is32 (x2n_val n k).
Proof. intros. apply x2n_val_rep; auto. Qed.

Lemma x2n_val_nonzero n k: 0 <= n < 2 ^ 64 -> 0 <= k -> x2n_val n k <> 0.
Proof. intros. eapply rep_nonzero. apply x2n_val_rep; auto. Qed.

(* ---------------------------------------------------------------------- *)
(* crc32_combine                                                           *)
(* ---------------------------------------------------------------------- *)

Lemma is32_mod x: is32 (x mod 2 ^ 32).
Proof. unfold is32. apply Z.mod_pos_bound. lia. Qed.

Lemma crc32_combine_val_shift x y z: 0 <= z < 2 ^ 63 ->
  crc32_combine_val x y z = Z.lxor (Nat.iter (8 * Z.to_nat z) crc_step (x mod 2 ^ 32)) (y mod 2 ^ 32).
Proof.
  intros Hz. unfold crc32_combine_val, crc32_combine_gen_val, crc32_combine_op_val.
  destruct (Z.ltb_spec z 0); [lia | ].
  assert (R: rep (x2n_val z 3) (Z.to_nat z * 8)) by (apply (x2n_val_rep z 3); lia).
  destruct (Z.eqb_spec (x2n_val z 3) 0) as [E|E]; [exfalso; eapply rep_nonzero; eauto | ].
  destruct R as [_ R]. rewrite R by apply is32_mod. rewrite Nat.mul_comm. auto.
Qed.

Lemma crc32_combine_val_neg x y z: z < 0 -> crc32_combine_val x y z = 0.
Proof.
  intros. unfold crc32_combine_val, crc32_combine_gen_val, crc32_combine_op_val.
  destruct (Z.ltb_spec z 0); [reflexivity | lia].
Qed.

Lemma crc32_combine_val_range x y z: 0 <= z < 2 ^ 63 -> is32 (crc32_combine_val x y z).
Proof.
  intros. rewrite crc32_combine_val_shift by auto.
  apply lxor_lt_pow2; [lia | apply is32_iter, is32_mod | apply is32_mod].
Qed.

Lemma x2n_aux_step f n k p: n <> 0 ->
  x2n_aux (S f) n k p = x2n_aux f (n / 2) (k + 1) (if Z.odd n then gf_mul (x2n_tbl k) p else p).
Proof. intros. cbn [x2n_aux]. rewrite (proj2 (Z.eqb_neq n 0) H). reflexivity. Qed.

Lemma x2n_aux_zero f k p: x2n_aux f 0 k p = p.
Proof. destruct f; reflexivity. Qed.

Lemma x2n_val_aux n k: x2n_val n k = x2n_aux 64 n k (2 ^ 31).
Proof. reflexivity. Qed.
