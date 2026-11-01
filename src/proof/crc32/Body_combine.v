(* The bodies of crc32_combine_gen64, crc32_combine_gen, crc32_combine_op, crc32_combine64, crc32_combine. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.crc32.code.
Require Import Zlib.proof.crc32.SpecCombine Zlib.proof.crc32.MultInt.
#[local] Existing Instance Zlib.units.Crc32.CS.

Ltac hsigned :=
  repeat match goal with H: context [Int64.signed (Int64.repr ?x)] |- _ =>
    rewrite (Int64.signed_repr x) in H by rep_lia end.

Lemma body_crc32_combine_gen64: semax_body Vprog Gprog_crc32_combine_gen64 f_crc32_combine_gen64 crc32_combine_gen64_spec.
Proof.
  start_function.
  forward_if.
  - hsigned. forward. entailer!.
    unfold crc32_combine_gen_val. destruct (Z.ltb_spec len2 0); [auto | lia].
  - hsigned.
    forward_call (len2, 3, gv, tsh).
    forward. entailer!.
    unfold crc32_combine_gen_val. destruct (Z.ltb_spec len2 0); [lia | auto].
Qed.

Lemma body_crc32_combine_gen: semax_body Vprog Gprog_crc32_combine_gen f_crc32_combine_gen crc32_combine_gen_spec.
Proof.
  start_function.
  forward_call (len2, gv, tsh).
  forward.
Qed.

Lemma body_crc32_combine_op: semax_body Vprog Gprog_crc32_combine_op f_crc32_combine_op crc32_combine_op_spec.
Proof.
  start_function.
  forward_if.
  - assert (op = 0) by (match goal with H: Int64.repr op = _ |- _ => apply repr_inj_unsigned64 in H; rep_lia end).
    subst op. forward.
  - assert (op <> 0) by (intro; subst op; contradiction).
    assert (0 <= crc1 mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
    forward_call (op, crc1 mod 2 ^ 32).
    { entailer!. simpl. change (Int.unsigned (Int.repr (-1))) with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. }
    forward. entailer!.
    change (Int.unsigned (Int.repr (-1))) with (Z.ones 32). rewrite Z.land_ones by lia.
    unfold crc32_combine_op_val. destruct (Z.eqb_spec op 0); [lia | ].
    rewrite xor64_repr32; auto. apply gf_mul_range. apply is32_mod. apply is32_mod.
Qed.

Lemma body_crc32_combine64: semax_body Vprog Gprog_crc32_combine64 f_crc32_combine64 crc32_combine64_spec.
Proof.
  start_function.
  forward_call (len2, gv, tsh).
  assert (0 <= crc32_combine_gen_val len2 <= Int64.max_unsigned).
  { unfold crc32_combine_gen_val. destruct (Z.ltb_spec len2 0); [rep_lia | ].
    pose proof (x2n_val_is32 len2 3). unfold is32 in H3. rep_lia. }
  forward_call (crc1, crc2, crc32_combine_gen_val len2).
  forward.
Qed.

Lemma body_crc32_combine: semax_body Vprog Gprog_crc32_combine f_crc32_combine crc32_combine_spec.
Proof.
  start_function.
  forward_call (crc1, crc2, len2, gv, tsh).
  forward.
Qed.
