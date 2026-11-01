(* The CRC-32 reference functions of harness/zlib_common.h (ref_crc_byte, ref_crc32): specifications and
   bodies, shared by every law whose harness uses them.  Their Clight is the same term in every harness
   unit (taken here from harness/crc32_ref.c's unit), so one body proof serves all (Assembly.entry_shared).
   ref_crc32 reads the slice [lo, lo + len) of an object (adler32/Bytes.v cbuf_ok, isnull = false). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.crc32.Spec Zlib.proof.crc32.IntFacts Zlib.proof.adler32.Ptr.
Require Zlib.harness.x_crc32_ref.code.
Module HC := Zlib.harness.x_crc32_ref.code.
#[local] Existing Instance Zlib.units.Crc32.CS.

Definition ref_crc_byte_spec :=
  DECLARE HC._ref_crc_byte
  WITH c: Z, b: Z
  PRE [ tulong, tuchar ]
    PROP (0 <= c < 2 ^ 32; 0 <= b <= Byte.max_unsigned)
    PARAMS (Vlong (Int64.repr c); Vint (Int.repr b)) SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (ref_crc_byte c b))) SEP ().

Definition ref_crc32_spec :=
  DECLARE HC._ref_crc32
  WITH c: Z, buf: val, sh: share, p: val, lo: Z, n: Z, contents: list val, len: Z, data: list Z
  PRE [ tulong, tptr tuchar, tulong ]
    PROP (0 <= c <= Int64.max_unsigned; 0 <= len <= Int64.max_unsigned;
          cbuf_ok false buf sh p lo n len contents data)
    PARAMS (Vlong (Int64.repr c); buf; Vlong (Int64.repr len))
    SEP (data_at sh (tarray tuchar n) contents p)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (ref_crc32 c data))) SEP (data_at sh (tarray tuchar n) contents p).

Definition Vprog_hr : varspecs := [].
Definition Gprog_ref_crc_byte : funspecs := [].
Definition Gprog_ref_crc32 : funspecs := [ref_crc_byte_spec].

Lemma crc_step_odd64 x: 0 <= x < 2 ^ 32 -> Z.odd x = true ->
  Int64.xor (Int64.shru (Int64.repr x) (Int64.repr (Int.unsigned (Int.repr 1)))) (Int64.repr 3988292384) =
  Int64.repr (crc_step x).
Proof.
  intros Hx O. change (Int.unsigned (Int.repr 1)) with 1.
  unfold crc_step. rewrite O. unfold Int64.xor, Int64.shru.
  rewrite (Int64.unsigned_repr x), (Int64.unsigned_repr 1) by rep_lia.
  assert (0 <= Z.shiftr x 1 < 2 ^ 32).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma crc_step_even64 x: 0 <= x < 2 ^ 32 -> Z.odd x = false ->
  Int64.shru (Int64.repr x) (Int64.repr (Int.unsigned (Int.repr 1))) = Int64.repr (crc_step x).
Proof.
  intros Hx O. change (Int.unsigned (Int.repr 1)) with 1.
  unfold crc_step. rewrite O. unfold Int64.shru. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma odd_and64 x: 0 <= x < 2 ^ 32 ->
  Int64.and (Int64.repr x) (Int64.repr 1) = if Z.odd x then Int64.repr 1 else Int64.zero.
Proof.
  intros. unfold Int64.and. rewrite !Int64.unsigned_repr by rep_lia.
  change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite Zmod_odd. destruct (Z.odd x); reflexivity.
Qed.

Lemma body_ref_crc_byte: semax_body Vprog_hr Gprog_ref_crc_byte HC.f_ref_crc_byte ref_crc_byte_spec.
Proof.
  start_function.
  forward.
  assert (Hx: 0 <= Z.lxor c b < 2 ^ 32) by (apply lxor_lt_pow2; rep_lia).
  forward_for_simple_bound 8 (EX k: Z,
     PROP () LOCAL (temp HC._c (Vlong (Int64.repr (Nat.iter (Z.to_nat k) crc_step (Z.lxor c b))))) SEP ()).
  - entailer!. unfold Int64.xor. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
  - assert (Hk: 0 <= Nat.iter (Z.to_nat i) crc_step (Z.lxor c b) < 2 ^ 32) by (apply iter_crc_step_range; auto).
    forward_if.
    + match goal with H: Int64.and _ _ <> _ |- _ => rewrite odd_and64 in H by auto end.
      destruct (Z.odd (Nat.iter (Z.to_nat i) crc_step (Z.lxor c b))) eqn:O; [ | contradiction].
      forward. entailer!.
      rewrite crc_step_odd64 by auto. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. reflexivity.
    + match goal with H: Int64.and _ _ = _ |- _ => rewrite odd_and64 in H by auto end.
      destruct (Z.odd (Nat.iter (Z.to_nat i) crc_step (Z.lxor c b))) eqn:O.
      { exfalso. apply Int64.one_not_zero. auto. }
      forward. entailer!.
      rewrite crc_step_even64 by auto. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. reflexivity.
  - forward.
Qed.

Lemma body_ref_crc32: semax_body Vprog_hr Gprog_ref_crc32 HC.f_ref_crc32 ref_crc32_spec.
Proof.
  start_function.
  destruct H1 as (Hbuf & Hsh & Hlo & Hn & Hlen & Hby & Hsub). subst buf.
  assert_PROP (field_compatible (tarray tuchar n) [] p) as FC by entailer!.
  assert_PROP (Zlength contents = n) by (entailer!; rewrite Zlength_correct in *; auto).
  forward.
  set (c0 := Z.lxor (c mod 2^32) crc_mask).
  assert (Hc0: 0 <= c0 < 2 ^ 32) by (apply lxor_lt_pow2; [lia | apply Z.mod_pos_bound; lia | apply crc_mask_range]).
  rewrite crc_pre_int by auto. fold c0.
  forward_for_simple_bound len (EX i: Z,
     PROP () LOCAL (temp HC._c (Vlong (Int64.repr (crc_reg c0 data i)));
                    temp HC._buf (offset_val lo p); temp HC._n (Vlong (Int64.repr len)))
     SEP (data_at sh (tarray tuchar n) contents p)).
  - entailer!.
  - assert (E: force_val (sem_add_ptr_long tuchar (offset_val lo p) (Vlong (Int64.repr i))) =
               field_address (tarray tuchar n) [ArraySubsc (lo + i)] p) by (apply add_ptr_long; auto; lia).
    assert (Hb: @Znth val Vundef (lo + i) contents = Vint (Int.repr (Znth i data))) by (apply (Znth_cbuf lo len); auto; lia).
    assert (Hb2: 0 <= Znth i data <= Byte.max_unsigned) by (apply is_bytes_Znth; auto; lia).
    forward.
    { entailer!. rewrite Hb. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Hb.
    assert (Hc: 0 <= crc_reg c0 data i < 2 ^ 32) by (apply crc_reg_range; auto).
    forward_call (crc_reg c0 data i, Znth i data).
    forward. entailer!. rewrite crc_reg_succ by lia. auto.
  - assert (Hr: 0 <= crc_reg c0 data len < 2 ^ 32) by (apply crc_reg_range; auto).
    forward. entailer!.
    rewrite crc_pre_int by rep_lia. f_equal.
    rewrite Z.mod_small by auto.
    unfold ref_crc32. fold c0. rewrite <- crc_reg_full. auto.
Qed.
