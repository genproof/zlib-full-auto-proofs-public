(* Part: bits_stmt of fact_result.v (bit reversal and the backwards increment). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pb_testbit_1 : forall j, 0 <= j -> Z.testbit 1 j = (j =? 0).
Proof.
  intros j Hj. destruct (Z.eq_dec j 0) as [->|Hn]; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq j 0) Hn).
  change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma pb_ones : forall n, Z.ones n = 2 ^ n - 1.
Proof. intros; rewrite Z.ones_equiv; lia. Qed.

Lemma pb_rl_nonneg : forall k i r c, 0 <= r -> 0 <= reverse_loop k i r c.
Proof.
  induction k; intros; cbn [reverse_loop]; [lia|]. apply IHk.
  apply Z.lor_nonneg; split.
  - rewrite Z.shiftl_nonneg; lia.
  - apply Z.land_nonneg; lia.
Qed.

Lemma pb_rl_bits : forall k i r c m, 0 <= m ->
  Z.testbit (reverse_loop k i r c) m =
  if m <? Z.of_nat k then Z.testbit c (i + Z.of_nat k - 1 - m) else Z.testbit r (m - Z.of_nat k).
Proof.
  induction k; intros i r c m Hm; cbn [reverse_loop].
  - change (Z.of_nat 0) with 0. destruct (m <? 0) eqn:E; [lia|]. f_equal; lia.
  - rewrite IHk by lia. rewrite Nat2Z.inj_succ.
    destruct (Z.lt_trichotomy m (Z.of_nat k)) as [Hl|[He|Hg]].
    + rewrite (proj2 (Z.ltb_lt _ _) Hl), (proj2 (Z.ltb_lt m (Z.succ (Z.of_nat k)))) by lia.
      f_equal; lia.
    + subst m. rewrite Z.ltb_irrefl, (proj2 (Z.ltb_lt _ _)) by lia.
      rewrite Z.sub_diag, Z.lor_spec, Z.shiftl_spec_low, Z.land_spec, Z.shiftr_spec by lia.
      simpl. rewrite andb_true_r. f_equal; lia.
    + rewrite (proj2 (Z.ltb_ge m (Z.of_nat k))), (proj2 (Z.ltb_ge m (Z.succ (Z.of_nat k)))) by lia.
      rewrite Z.lor_spec, Z.shiftl_spec_high, Z.land_spec, pb_testbit_1 by lia.
      rewrite (proj2 (Z.eqb_neq _ 0)) by lia. rewrite andb_false_r, orb_false_r. f_equal; lia.
Qed.

Lemma pb_rev_nonneg : forall c n, 0 <= reverse_bits c n.
Proof. intros; apply pb_rl_nonneg; lia. Qed.

Lemma pb_rev_bits : forall c n m, 0 <= n -> 0 <= m ->
  Z.testbit (reverse_bits c n) m = (m <? n) && Z.testbit c (n - 1 - m).
Proof.
  intros. unfold reverse_bits. rewrite pb_rl_bits by lia. rewrite Z2Nat.id by lia.
  destruct (m <? n); simpl. f_equal; lia. apply Z.testbit_0_l.
Qed.

Lemma pb_lt_pow : forall x n, 0 <= x -> 0 <= n -> (forall m, n <= m -> Z.testbit x m = false) -> x < 2 ^ n.
Proof.
  intros x n Hx Hn H.
  assert (x = x mod 2 ^ n).
  { apply Z.bits_inj'; intros m Hm. destruct (Z.lt_ge_cases m n).
    - rewrite Z.mod_pow2_bits_low by lia; auto.
    - rewrite Z.mod_pow2_bits_high by lia; auto. }
  rewrite H0. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma pb_bits_high : forall x n m, 0 <= x < 2 ^ n -> 0 <= n <= m -> Z.testbit x m = false.
Proof.
  intros. destruct (Z.eq_dec x 0) as [->|Hx]; [apply Z.testbit_0_l|].
  apply Z.bits_above_log2; [lia|]. assert (Z.log2 x < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma pb_mul_add_bits : forall a b p j, 0 <= p -> 0 <= b < 2 ^ p -> 0 <= j ->
  Z.testbit (a * 2 ^ p + b) j = if j <? p then Z.testbit b j else Z.testbit a (j - p).
Proof.
  intros a b p j Hp Hb Hj. assert (0 < 2 ^ p) by (apply Z.pow_pos_nonneg; lia).
  destruct (j <? p) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E].
  - rewrite <- (Z.mod_pow2_bits_low _ p j) by lia. f_equal.
    rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small; lia.
  - replace j with ((j - p) + p) at 1 by lia. rewrite <- Z.div_pow2_bits by lia. f_equal.
    rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma pb_bincr_steps : forall t k h p, (t <= k)%nat -> 0 <= p ->
  (forall i, p - Z.of_nat t < i <= p -> Z.testbit h i = true) ->
  bincr_loop k h (2 ^ p) = bincr_loop (k - t) h (2 ^ (p - Z.of_nat t)).
Proof.
  induction t; intros k h p Hk Hp H.
  - rewrite Nat.sub_0_r. f_equal; f_equal; lia.
  - destruct k as [|k]; [lia|]. simpl bincr_loop at 1.
    assert (Hb : Z.testbit h p = true) by (apply H; lia).
    replace (Z.land h (2 ^ p) =? 0) with false.
    2:{ symmetry; apply Z.eqb_neq; intro E.
        assert (Z.testbit (Z.land h (2 ^ p)) p = false) by (rewrite E; apply Z.testbit_0_l).
        rewrite Z.land_spec, Z.pow2_bits_true, Hb in H0 by lia. discriminate. }
    rewrite Z.shiftr_div_pow2, Z.pow_1_r by lia. simpl Nat.sub.
    destruct (Z.eq_dec p 0) as [->|Hp0].
    + destruct t.
      * simpl. rewrite Nat.sub_0_r. reflexivity.
      * exfalso. assert (Z.testbit h (-1) = true) by (apply H; rewrite Nat2Z.inj_succ, Nat2Z.inj_succ; lia).
        rewrite Z.testbit_neg_r in H0 by lia. discriminate.
    + replace (2 ^ p / 2) with (2 ^ (p - 1)).
      2:{ replace p with ((p - 1) + 1) at 2 by lia. rewrite Z.pow_add_r, Z.pow_1_r by lia.
          rewrite Z.div_mul; lia. }
      rewrite IHt by (try lia; intros; apply H; rewrite Nat2Z.inj_succ; lia).
      f_equal; f_equal; rewrite Nat2Z.inj_succ; lia.
Qed.

Lemma pb_first_zero : forall c N, 0 <= N ->
  (forall j, 0 <= j < N -> Z.testbit c j = true) \/
  (exists j0, 0 <= j0 < N /\ Z.testbit c j0 = false /\ forall i, 0 <= i < j0 -> Z.testbit c i = true).
Proof.
  intros c N HN. pattern N; apply natlike_ind; [left; intros; lia| |lia].
  intros x Hx [IH|IH].
  - destruct (Z.testbit c x) eqn:E.
    + left; intros j Hj. destruct (Z.eq_dec j x); [subst; auto|apply IH; lia].
    + right; exists x; split; [lia|]; split; auto.
  - right. destruct IH as (j0 & ? & ? & ?). exists j0; split; [lia|auto].
Qed.

Lemma bits_ok2 : bits_stmt.
Proof.
  unfold bits_stmt. split; [|split; [|split; [|split]]].
  - intros c n Hn. split; [apply pb_rev_nonneg|].
    apply pb_lt_pow; [apply pb_rev_nonneg|lia|].
    intros m Hm. rewrite pb_rev_bits by lia. rewrite (proj2 (Z.ltb_ge m n)) by lia. reflexivity.
  - intros c n r Hc Hr. apply Z.bits_inj'; intros m Hm.
    rewrite Z.land_spec, pb_rev_bits, pb_rev_bits by lia.
    replace (2 ^ r - 1) with (Z.ones r) by (rewrite Z.ones_equiv; lia).
    destruct (Z.lt_ge_cases m r).
    + rewrite Z.ones_spec_low, (proj2 (Z.ltb_lt m r)), (proj2 (Z.ltb_lt m n)) by lia.
      rewrite Z.div_pow2_bits by lia. simpl. rewrite andb_true_r. f_equal; lia.
    + rewrite Z.ones_spec_high, (proj2 (Z.ltb_ge m r)) by lia. apply andb_false_r.
  - intros c r Hr Hc. apply Z.bits_inj'; intros m Hm.
    rewrite pb_rev_bits by lia.
    destruct (m <? r) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; simpl.
    + rewrite pb_rev_bits by lia. rewrite (proj2 (Z.ltb_lt _ r)) by lia. simpl. f_equal; lia.
    + symmetry. apply (pb_bits_high c r); lia.
  - intros c n d Hc Hn Hd. apply Z.bits_inj'; intros m Hm.
    rewrite pb_rev_bits, pb_rev_bits by lia.
    destruct (m <? n) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E].
    + rewrite (proj2 (Z.ltb_lt m (n + d))) by lia. simpl.
      rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec_high by lia. f_equal; lia.
    + destruct (m <? n + d) eqn:E2; simpl; auto.
      rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec_low by lia. reflexivity.
  - intros c n Hn Hc. unfold MAXBITS in Hn. unfold next_huff.
    set (h := reverse_bits c n).
    assert (Hh : forall m, 0 <= m -> Z.testbit h m = (m <? n) && Z.testbit c (n - 1 - m))
      by (intros; apply pb_rev_bits; lia).
    rewrite Z.shiftl_1_l.
    destruct (pb_first_zero c n) as [Hall|(j0 & Hj0 & Hz & Hlow)]; [lia| |].
    + (* c = 2^n - 1: the increment wraps to 0 *)
      rewrite (pb_bincr_steps (Z.to_nat n) 16 h (n - 1)); try lia.
      2:{ intros i Hi. rewrite Z2Nat.id in Hi by lia. rewrite Hh by lia.
          rewrite (proj2 (Z.ltb_lt i n)) by lia. apply Hall; lia. }
      rewrite Z2Nat.id by lia.
      replace (16 - Z.to_nat n)%nat with (S (15 - Z.to_nat n)) by lia.
      replace (2 ^ (n - 1 - n)) with 0 by (rewrite Z.pow_neg_r; lia).
      simpl bincr_loop. rewrite Z.land_0_r. simpl. destruct (15 - Z.to_nat n)%nat; simpl; [|].
      all: symmetry; apply Z.bits_inj'; intros m Hm; rewrite pb_rev_bits by lia;
        rewrite Z.testbit_0_l; destruct (m <? n) eqn:E; auto; simpl;
        replace ((c + 1) mod 2 ^ n) with 0; [apply Z.testbit_0_l|].
      all: assert (c = Z.ones n) by (apply Z.bits_inj'; intros j Hj; destruct (Z.lt_ge_cases j n);
             [rewrite Z.ones_spec_low by lia; apply Hall; lia
             |rewrite Z.ones_spec_high by lia; apply (pb_bits_high c n); lia]);
           rewrite H, pb_ones; replace (2 ^ n - 1 + 1) with (1 * 2 ^ n) by lia;
           rewrite Z.mod_mul; [reflexivity|]; assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia); lia.
    + (* the first zero bit j0 of c *)
      set (q := n - 1 - j0).
      rewrite (pb_bincr_steps (Z.to_nat j0) 16 h (n - 1)); try lia.
      2:{ intros i Hi. rewrite Z2Nat.id in Hi by lia. rewrite Hh by lia.
          rewrite (proj2 (Z.ltb_lt i n)) by lia. apply Hlow; lia. }
      rewrite Z2Nat.id by lia. fold q.
      replace (16 - Z.to_nat j0)%nat with (S (15 - Z.to_nat j0)) by lia. simpl bincr_loop.
      replace (Z.land h (2 ^ q) =? 0) with true.
      2:{ symmetry; apply Z.eqb_eq. apply Z.bits_inj'; intros m Hm.
          rewrite Z.land_spec, Z.pow2_bits_eqb, Z.testbit_0_l by lia.
          destruct (Z.eqb_spec q m); [subst m|apply andb_false_r].
          rewrite Hh by lia. rewrite (proj2 (Z.ltb_lt _ n)) by lia.
          replace (n - 1 - q) with j0 by lia. rewrite Hz. reflexivity. }
      assert (Hq : 0 < 2 ^ q) by (apply Z.pow_pos_nonneg; lia).
      rewrite (proj2 (Z.eqb_neq (2 ^ q) 0)) by lia.
      assert (Hj : 0 < 2 ^ j0) by (apply Z.pow_pos_nonneg; lia).
      assert (Hj1 : 2 ^ (j0 + 1) = 2 * 2 ^ j0) by (rewrite Z.pow_add_r, Z.pow_1_r; lia).
      (* c + 1 = a * 2^(j0+1) + 2^j0 *)
      set (a := c / 2 ^ (j0 + 1)).
      assert (Hcm : c mod 2 ^ (j0 + 1) = 2 ^ j0 - 1).
      { rewrite <- pb_ones. apply Z.bits_inj'; intros m Hm.
        destruct (Z.lt_ge_cases m (j0 + 1)).
        - rewrite Z.mod_pow2_bits_low by lia. destruct (Z.lt_ge_cases m j0).
          + rewrite Z.ones_spec_low by lia. apply Hlow; lia.
          + rewrite Z.ones_spec_high by lia. replace m with j0 by lia. auto.
        - rewrite Z.mod_pow2_bits_high, Z.ones_spec_high by lia. reflexivity. }
      assert (Hc1 : c + 1 = a * 2 ^ (j0 + 1) + 2 ^ j0).
      { pose proof (Z.div_mod c (2 ^ (j0 + 1))). unfold a. lia. }
      assert (Hlt : c + 1 < 2 ^ n).
      { assert (c <> 2 ^ n - 1).
        { intro E. rewrite <- pb_ones in E.
          rewrite E, Z.ones_spec_low in Hz by lia. discriminate. }
        lia. }
      rewrite Z.mod_small by lia.
      assert (Hlo : 0 <= Z.land h (2 ^ q - 1) < 2 ^ q).
      { rewrite <- pb_ones. rewrite Z.land_ones by lia. apply Z.mod_pos_bound; lia. }
      replace (Z.land h (2 ^ q - 1) + 2 ^ q) with (1 * 2 ^ q + Z.land h (2 ^ q - 1)) by lia.
      apply Z.bits_inj'; intros m Hm.
      rewrite pb_mul_add_bits, pb_rev_bits, Hc1 by lia.
      destruct (m <? q) eqn:Em; [apply Z.ltb_lt in Em | apply Z.ltb_ge in Em].
      * rewrite <- pb_ones. rewrite Z.land_spec, Z.ones_spec_low, andb_true_r, Hh by lia.
        rewrite (proj2 (Z.ltb_lt m n)) by lia. simpl.
        rewrite pb_mul_add_bits by lia.
        rewrite (proj2 (Z.ltb_ge (n - 1 - m) (j0 + 1))) by lia.
        unfold a. rewrite Z.div_pow2_bits by lia. f_equal; lia.
      * rewrite pb_testbit_1 by lia.
        destruct (m <? n) eqn:En; [apply Z.ltb_lt in En | apply Z.ltb_ge in En]; simpl.
        -- rewrite pb_mul_add_bits by lia.
           rewrite (proj2 (Z.ltb_lt (n - 1 - m) (j0 + 1))) by lia.
           rewrite Z.pow2_bits_eqb by lia.
           destruct (Z.eqb_spec (m - q) 0), (Z.eqb_spec j0 (n - 1 - m)); auto; lia.
        -- apply Z.eqb_neq; lia.
Qed.
