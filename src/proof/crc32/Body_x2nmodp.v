(* The body of x2nmodp: x^(n * 2^k) mod P by repeated multiplication with the constant x2n_table. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.crc32.code.
Require Import Zlib.proof.crc32.SpecCombine Zlib.proof.crc32.MultInt.
#[local] Existing Instance Zlib.units.Crc32.CS.

Lemma x2n_tbl_is32 k: is32 (x2n_tbl k).
Proof. unfold x2n_tbl. apply x2n_table_is32. apply Z.mod_pos_bound. lia. Qed.

Lemma x2n_idx k: 0 <= k -> 0 <= Int.unsigned (Int.and (Int.repr k) (Int.repr 31)) < 32.
Proof.
  intros. rewrite k31_int by auto. rewrite Int.unsigned_repr; pose proof (Z.mod_pos_bound k 32); rep_lia.
Qed.

Lemma x2n_load {d: Inhabitant val} k: 0 <= k ->
  @Znth val d (Int.unsigned (Int.and (Int.repr k) (Int.repr 31))) x2n_table_rep = Vint (Int.repr (x2n_tbl k)).
Proof.
  intros. rewrite k31_int by auto. pose proof (Z.mod_pos_bound k 32).
  rewrite Int.unsigned_repr by rep_lia. unfold x2n_table_rep, x2n_tbl.
  assert (Zlength x2n_table_vals = 32) by reflexivity.
  rewrite Znth_map by lia. reflexivity.
Qed.

(* The fuel-driven model must not be unfolded by the entailment tactics. *)
Opaque x2n_aux x2n_val.

Lemma body_x2nmodp: semax_body Vprog Gprog_x2nmodp f_x2nmodp x2nmodp_spec.
Proof.
  start_function.
  forward.
  forward_while (EX f: nat, EX n': Z, EX k': Z, EX p': Z,
     PROP (0 <= n' < 2 ^ Z.of_nat f; n' <= Int64.max_signed; 0 <= k'; x2n_aux f n' k' p' = x2n_val n k; is32 p')
     LOCAL (temp _p (Vlong (Int64.repr p')); temp _n (Vlong (Int64.repr n')); temp _k (Vint (Int.repr k'));
            gvars gv)
     SEP (x2n_table_at tsh gv)).
  - Exists 64%nat n k (2 ^ 31). rewrite x2n_val_aux. entailer!. repeat split; try rep_lia; unfold is32; lia.
  - entailer!.
  - assert (Hn0: n' <> 0) by (intro; subst n'; contradiction).
    destruct f as [|f].
    { match goal with H: 0 <= n' < 2 ^ Z.of_nat 0 |- _ => simpl in H; lia end. }
    match goal with H: x2n_aux (S _) _ _ _ = _ |- _ => rewrite x2n_aux_step in H by auto end.
    forward_if (PROP () LOCAL (temp _p (Vlong (Int64.repr (if Z.odd n' then gf_mul (x2n_tbl k') p' else p')));
                               temp _n (Vlong (Int64.repr n')); temp _k (Vint (Int.repr k')); gvars gv)
                        SEP (x2n_table_at tsh gv)).
    + match goal with H: Int64.and _ _ <> _ |- _ => rewrite odd_int64 in H by rep_lia end.
      destruct (Z.odd n') eqn:O; [ | contradiction].
      unfold x2n_table_at.
      assert (Hl: Z.land k' 31 = k' mod 32) by (change 31 with (Z.ones 5); apply Z.land_ones; lia).
      assert (Hlr: 0 <= Z.land k' 31 < 32) by (rewrite Hl; apply Z.mod_pos_bound; lia).
      assert (Hv: @Znth val Vundef (Z.land k' 31) x2n_table_rep = Vint (Int.repr (x2n_tbl k'))).
      { rewrite Hl. unfold x2n_table_rep, x2n_tbl. assert (Zlength x2n_table_vals = 32) by reflexivity.
        rewrite Znth_map by (pose proof (Z.mod_pos_bound k' 32); lia). reflexivity. }
      forward.
      all: try (entailer!; rewrite Hv; simpl; auto).
      rewrite Hv.
      pose proof (x2n_tbl_is32 k'). unfold is32 in *.
      forward_call (x2n_tbl k', p').
      all: try (split; rep_lia).
      forward. entailer!.
    + match goal with H: Int64.and _ _ = _ |- _ => rewrite odd_int64 in H by rep_lia end.
      destruct (Z.odd n') eqn:O.
      { exfalso. apply Int64.one_not_zero. auto. }
      forward. entailer!.
    + forward. forward.
      rewrite shr1_int64 by lia.
      assert (Hp': is32 (if Z.odd n' then gf_mul (x2n_tbl k') p' else p'))
        by (destruct (Z.odd n'); [apply gf_mul_range | ]; auto).
      Exists (f, n' / 2, k' + 1, if Z.odd n' then gf_mul (x2n_tbl k') p' else p').
      entailer!.
      assert (2 ^ Z.of_nat (S f) = 2 * 2 ^ Z.of_nat f) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia).
      unfold is32 in Hp'.
      repeat split; try (apply Z.div_pos; lia); try lia.
      * apply Z.div_lt_upper_bound; lia.
      * apply (Z.le_trans _ n'); [apply Z.div_le_upper_bound; lia | lia].
  - forward. entailer!.
    assert (n' = 0) by (apply repr_inj_unsigned64 in HRE; rep_lia). subst n'.
    match goal with H: x2n_aux _ 0 _ _ = _ |- _ => rewrite x2n_aux_zero in H; rewrite H; auto end.
Qed.
