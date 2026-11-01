(* The harness helper le32 of harness/zlib_common.h (the 4 bytes p[0..4), little-endian): its value, its
   specification (at the compspecs of the adler32 unit, like be32 in HarnessLib.v) and its body, shared by
   every inflate law whose harness uses it.  Its Clight is the same term in every harness unit that keeps it;
   the body is taken from harness/inflate_check.c's unit.  The slice is given as in HarnessLib.v's be32:
   [cbuf_ok false buf sh p lo n 4 contents data] (adler32/Bytes.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.adler32.Bytes.
Require Zlib.units.Adler32.
Require Zlib.harness.x_inflate_check.code.
Module HK := Zlib.harness.x_inflate_check.code.

(* le32(p): the 4 bytes p[0..4), little-endian *)
Definition le32 (l: list Z) : Z :=
  Znth 3 l * 2 ^ 24 + Znth 2 l * 2 ^ 16 + Znth 1 l * 2 ^ 8 + Znth 0 l.

Lemma ik_add_ptr_c {cs: compspecs} p n k c:
  field_compatible (tarray tuchar n) [] p -> 0 <= k + c < n -> 0 <= c <= Int.max_signed ->
  force_val (sem_add_ptr_int tuchar Signed (offset_val k p) (Vint (Int.repr c))) =
  field_address (tarray tuchar n) [ArraySubsc (k + c)] p.
Proof.
  intros FC Hk Hc. rewrite arr_field_address by auto.
  destruct p; try (destruct FC; contradiction). simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal. normalize.
  all: try (rewrite Int.signed_repr by rep_lia; f_equal; lia).
Qed.

Lemma ik_lor_low x y k: 0 <= k -> 0 <= y < 2 ^ k -> Z.lor (x * 2 ^ k) y = x * 2 ^ k + y.
Proof.
  intros Hk Hy. rewrite <- Z.add_lor_land. replace (Z.land (x * 2 ^ k) y) with 0; [lia | ].
  symmetry. apply Z.bits_inj_0. intros m.
  rewrite Z.land_spec. destruct (Z.lt_ge_cases m 0) as [Hm | Hm].
  - rewrite Z.testbit_neg_r by lia. reflexivity.
  - destruct (Z.lt_ge_cases m k) as [Hm' | Hm'].
    + rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + rewrite <- (Z.mod_small y (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
Qed.

Lemma ik_le32_or a b c d:
  0 <= a <= 255 -> 0 <= b <= 255 -> 0 <= c <= 255 -> 0 <= d <= 255 ->
  Int64.or (Int64.or (Int64.or (Int64.shl (Int64.repr a) (Int64.repr 24)) (Int64.shl (Int64.repr b) (Int64.repr 16)))
    (Int64.shl (Int64.repr c) (Int64.repr 8))) (Int64.repr d) =
  Int64.repr (a * 2 ^ 24 + b * 2 ^ 16 + c * 2 ^ 8 + d).
Proof.
  intros Ha Hb Hc Hd.
  assert (S: forall x k, 0 <= x <= 255 -> 0 <= k <= 24 -> Int64.shl (Int64.repr x) (Int64.repr k) = Int64.repr (x * 2 ^ k)).
  { intros x k Hx Hk. unfold Int64.shl. rewrite !Int64.unsigned_repr by rep_lia.
    rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  assert (O: forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
    Int64.or (Int64.repr x) (Int64.repr y) = Int64.repr (Z.lor x y)).
  { intros x y Hx Hy. unfold Int64.or. rewrite !Int64.unsigned_repr by lia. reflexivity. }
  rewrite (S a 24), (S b 16), (S c 8) by lia.
  assert (P: forall k, 0 <= k <= 24 -> 2 ^ k <= 2 ^ 24) by (intros; apply Z.pow_le_mono_r; lia).
  pose proof (P 16 ltac:(lia)). pose proof (P 8 ltac:(lia)).
  rewrite O by (simpl; rep_lia).
  rewrite ik_lor_low by (simpl; lia).
  rewrite O by (simpl; rep_lia).
  replace (a * 2 ^ 24 + b * 2 ^ 16) with ((a * 2 ^ 8 + b) * 2 ^ 16) by ring.
  rewrite ik_lor_low by (simpl; lia).
  rewrite O by (simpl; rep_lia).
  replace ((a * 2 ^ 8 + b) * 2 ^ 16 + c * 2 ^ 8) with ((a * 2 ^ 16 + b * 2 ^ 8 + c) * 2 ^ 8) by ring.
  rewrite ik_lor_low by (simpl; lia).
  f_equal; ring.
Qed.

Section Le32.
#[local] Existing Instance Zlib.units.Adler32.CS.

Definition le32_spec :=
  DECLARE HK._le32
  WITH buf : val, sh : share, p : val, lo : Z, n : Z, contents : list val, data : list Z
  PRE [ tptr tuchar ]
    PROP (cbuf_ok false buf sh p lo n 4 contents data)
    PARAMS (buf)
    SEP (data_at sh (tarray tuchar n) contents p)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (le32 data)))
    SEP (data_at sh (tarray tuchar n) contents p).

Definition Vprog_le32 : varspecs := [].
Definition Gprog_le32 : funspecs := [].

Lemma body_le32: @semax_body Vprog_le32 Gprog_le32 Zlib.units.Adler32.CS HK.f_le32 le32_spec.
Proof.
  start_function.
  match goal with H: cbuf_ok false _ _ _ _ _ _ _ _ |- _ => destruct H as (Hbuf & Hsh & Hlo & Hn & Hlen & Hby & Hsub) end.
  subst buf.
  assert_PROP (field_compatible (tarray tuchar n) [] p) as FC by entailer!.
  assert_PROP (Zlength contents = n) by (entailer!; rewrite Zlength_correct in *; auto).
  assert (Hb: forall i, 0 <= i < 4 -> @Znth val Vundef (lo + i) contents = Vint (Int.repr (Znth i data))) by
    (intros; apply (Znth_cbuf lo 4); auto; lia).
  assert (Hr: forall i, 0 <= i < 4 -> 0 <= Znth i data <= Byte.max_unsigned) by (intros; apply is_bytes_Znth; auto; lia).
  assert (E: forall i, 0 <= i < 4 -> force_val (sem_add_ptr_int tuchar Signed (offset_val lo p) (Vint (Int.repr i))) =
    field_address (tarray tuchar n) [ArraySubsc (lo + i)] p) by
    (intros; apply ik_add_ptr_c; auto; rep_lia).
  pose proof (E 0 ltac:(lia)) as E0. pose proof (E 1 ltac:(lia)) as E1.
  pose proof (E 2 ltac:(lia)) as E2. pose proof (E 3 ltac:(lia)) as E3.
  rewrite Z.add_0_r in E0.
  assert (B: forall i, 0 <= i < 4 -> Int.unsigned (Int.repr (Znth i data)) = Znth i data) by
    (intros i Hi; pose proof (Hr i Hi); rewrite Int.unsigned_repr by rep_lia; reflexivity).
  pose proof (Hb 0 ltac:(lia)) as B0. rewrite Z.add_0_r in B0.
  forward. { entailer!. rewrite (Hb 3) by lia. simpl. rewrite (B 3) by lia. pose proof (Hr 3 ltac:(lia)). rep_lia. }
  forward. { entailer!. rewrite (Hb 2) by lia. simpl. rewrite (B 2) by lia. pose proof (Hr 2 ltac:(lia)). rep_lia. }
  forward. { entailer!. rewrite (Hb 1) by lia. simpl. rewrite (B 1) by lia. pose proof (Hr 1 ltac:(lia)). rep_lia. }
  forward. { entailer!. rewrite B0. simpl. rewrite (B 0) by lia. pose proof (Hr 0 ltac:(lia)). rep_lia. }
  rewrite B0, !Hb by lia.
  forward.
  entailer!. simpl. rewrite !B by lia.
  rewrite ik_le32_or by (apply Hr; lia).
  reflexivity.
Qed.

End Le32.
