(** * compressBound's formula computed in 64-bit unsigned arithmetic

    The one-shot laws (harness/rt_roundtrip.c, api_short_output.c, res_compress_bound.c) compute
    [n + (n >> 12) + (n >> 14) + (n >> 25) + 13] in size_t for n <= PTRDIFF_MAX, the formula of compress.c's
    compressBound_z.  It does not wrap there (the sum is below 2^63 + 2^52), so it is [DModel3.compressBound_z n]
    (whose test [bound < sourceLen] is then false).  [cb_formula_z]: the sum in Z; [cb_formula_i64]: the value
    main's statement computes, in the form VST gives it once the shift amounts and 13 are simplified. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DModel3.

(* the sum for n <= PTRDIFF_MAX is below 2^64 *)
Lemma cb_formula_range n :
  0 <= n <= 9223372036854775807 ->
  0 <= n + Z.shiftr n 12 + Z.shiftr n 14 + Z.shiftr n 25 + 13 <= Int64.max_unsigned.
Proof.
  intros Hn.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 12) with 4096. change (2 ^ 14) with 16384. change (2 ^ 25) with 33554432.
  pose proof (Z.div_pos n 4096 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos n 16384 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos n 33554432 ltac:(lia) ltac:(lia)).
  assert (n / 4096 < 2251799813685248) by (apply Z.div_lt_upper_bound; lia).
  assert (n / 16384 < 562949953421312) by (apply Z.div_lt_upper_bound; lia).
  assert (n / 33554432 < 274877906944) by (apply Z.div_lt_upper_bound; lia).
  rep_lia.
Qed.

(* compressBound_z n is the formula without wrap-around for n <= PTRDIFF_MAX *)
Lemma cb_formula_z n :
  0 <= n <= 9223372036854775807 ->
  compressBound_z n = n + Z.shiftr n 12 + Z.shiftr n 14 + Z.shiftr n 25 + 13.
Proof.
  intros Hn. pose proof (cb_formula_range n Hn) as R.
  assert (S : 0 <= Z.shiftr n 12 /\ 0 <= Z.shiftr n 14 /\ 0 <= Z.shiftr n 25)
    by (rewrite !Z.shiftr_nonneg; lia).
  unfold compressBound_z, u64.
  rewrite Z.mod_small by (unfold Int64.max_unsigned, Int64.modulus in R; simpl in R; lia).
  destruct (_ <? n) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity].
Qed.

(* the value of main's [original_len + (original_len >> 12) + (original_len >> 14) + (original_len >> 25) + 13] *)
Lemma cb_formula_i64 n :
  0 <= n <= 9223372036854775807 ->
  Int64.add (Int64.add (Int64.add (Int64.add (Int64.repr n) (Int64.shru (Int64.repr n) (Int64.repr 12)))
                                  (Int64.shru (Int64.repr n) (Int64.repr 14)))
                       (Int64.shru (Int64.repr n) (Int64.repr 25)))
            (Int64.repr 13)
  = Int64.repr (compressBound_z n).
Proof.
  intros Hn. rewrite (cb_formula_z n Hn).
  unfold Int64.shru. rewrite !(Int64.unsigned_repr n) by rep_lia.
  change (Int64.unsigned (Int64.repr 12)) with 12. change (Int64.unsigned (Int64.repr 14)) with 14.
  change (Int64.unsigned (Int64.repr 25)) with 25.
  apply Int64.eqm_samerepr.
  repeat first [apply Int64.eqm_add | (eapply Int64.eqm_trans; [apply Int64.eqm_sym, Int64.eqm_unsigned_repr |])
               | apply Int64.eqm_refl].
Qed.
