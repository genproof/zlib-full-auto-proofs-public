(* The body of multmodp: a(x) * b(x) mod P, bit by bit (GF2.gf_mul). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.crc32.code.
Require Import Zlib.proof.crc32.SpecCombine Zlib.proof.crc32.MultInt.
#[local] Existing Instance Zlib.units.Crc32.CS.

Lemma body_multmodp: semax_body Vprog Gprog_multmodp f_multmodp multmodp_spec.
Proof.
  start_function.
  forward. forward.
  forward_loop (EX j: Z,
     PROP (0 <= j)
     LOCAL (temp _m (Vlong (Int64.repr (Z.shiftr (2 ^ 31) j)));
            temp _p (Vlong (Int64.repr (xsum (Z.to_nat (Z.min j 32)) (gf_term a b))));
            temp _a (Vlong (Int64.repr a));
            temp _b (Vlong (Int64.repr (Nat.iter (Z.to_nat j) crc_step b))))
     SEP ())
    break: (PROP () LOCAL (temp _p (Vlong (Int64.repr (gf_mul a b)))) SEP ()).
  - Exists 0. entailer!.
  - Intros j.
    assert (Hbj: is32 (Nat.iter (Z.to_nat j) crc_step b)) by (apply is32_iter; unfold is32; lia).
    assert (Hpj: is32 (xsum (Z.to_nat (Z.min j 32)) (gf_term a b))).
    { apply xsum_range. intros. unfold gf_term. destruct (Z.testbit _ _); [apply is32_iter; unfold is32; lia | unfold is32; lia]. }
    forward_if (PROP () LOCAL (temp _m (Vlong (Int64.repr (Z.shiftr (2 ^ 31) j)));
        temp _p (Vlong (Int64.repr (xsum (Z.to_nat (Z.min (j + 1) 32)) (gf_term a b))));
        temp _a (Vlong (Int64.repr a)); temp _b (Vlong (Int64.repr (Nat.iter (Z.to_nat j) crc_step b)))) SEP ()).
    + (* the bit 31 - j of a is set *)
      change (Z.pow_pos 2 31) with (2 ^ 31) in H2.
      rewrite and_m_int in H2 by lia.
      destruct ((j <=? 31) && Z.testbit a (31 - j))%bool eqn:B; [ | contradiction].
      apply andb_prop in B. destruct B as [Bj Bt]. apply Z.leb_le in Bj.
      forward.
      forward_if.
      * (* no lower bit: break *)
        forward. entailer!.
        change (Z.pow_pos 2 31) with (2 ^ 31) in H3.
        rewrite shiftr_2_31_low in H3 by lia.
        replace (2 ^ (31 - j) - 1) with (Z.ones (31 - j)) in H3 by (rewrite Z.ones_equiv; lia).
        rewrite Z.land_ones in H3 by lia.
        assert (Hm: a mod 2 ^ (31 - j) = 0).
        { assert (0 <= a mod 2 ^ (31 - j) < 2 ^ (31 - j)) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
          assert (2 ^ (31 - j) <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
          apply repr_inj_unsigned64 in H3; rep_lia. }
        rewrite (gf_mul_break a b j) by auto. rewrite xsum_succ_term by lia.
        rewrite gf_term_set by auto. rewrite xor64_repr32 by auto. reflexivity.
      * forward. entailer!.
        rewrite xsum_succ_term by lia. rewrite gf_term_set by auto. rewrite xor64_repr32 by auto. reflexivity.
    + (* the bit is clear (or j > 31) *)
      change (Z.pow_pos 2 31) with (2 ^ 31) in H2.
      rewrite and_m_int in H2 by lia.
      forward. entailer!.
      destruct (Z.leb_spec j 31).
      * destruct (Z.testbit a (31 - j)) eqn:Bt.
        -- simpl in H2. exfalso. pose proof (shiftr_2_31_range j). rewrite shiftr_2_31_low in H2 by lia.
           assert (0 < 2 ^ (31 - j) <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
           apply repr_inj_unsigned64 in H2; rep_lia.
        -- rewrite xsum_succ_term by lia. rewrite gf_term_unset by auto. rewrite Z.lxor_0_r. reflexivity.
      * rewrite xsum_high by lia. reflexivity.
    + forward.
      rewrite m_shift_int by lia.
      forward_if (PROP () LOCAL (temp _m (Vlong (Int64.repr (Z.shiftr (2 ^ 31) (j + 1))));
        temp _p (Vlong (Int64.repr (xsum (Z.to_nat (Z.min (j + 1) 32)) (gf_term a b))));
        temp _a (Vlong (Int64.repr a)); temp _t'1 (Vlong (Int64.repr (Nat.iter (Z.to_nat (j + 1)) crc_step b)))) SEP ()).
      * rewrite b_odd_int in H2 by auto.
        destruct (Z.odd (Nat.iter (Z.to_nat j) crc_step b)) eqn:O; [ | contradiction].
        forward. entailer!.
        rewrite b_step_odd_int by auto.
        rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. reflexivity.
      * rewrite b_odd_int in H2 by auto.
        destruct (Z.odd (Nat.iter (Z.to_nat j) crc_step b)) eqn:O.
        { exfalso. discriminate H2. }
        forward. entailer!.
        rewrite b_step_even_int by auto.
        rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. reflexivity.
      * forward. Exists (j + 1). entailer!.
  - forward.
Qed.
