(* The Adler-32 reference function of harness/zlib_common.h (ref_adler32): specification and body,
   shared by every law whose harness uses it (its Clight is the same term in every harness unit; taken
   here from harness/adler32_ref.c's unit).  It reads the slice [lo, lo + len) of an object
   (Bytes.v cbuf_ok, isnull = false). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.adler32.Spec Zlib.proof.adler32.Facts Zlib.proof.adler32.Ptr.
Require Zlib.harness.x_adler32_ref.code.
Module HA := Zlib.harness.x_adler32_ref.code.
#[local] Existing Instance Zlib.units.Adler32.CS.

Definition ref_adler32_spec :=
  DECLARE HA._ref_adler32
  WITH a: Z, buf: val, sh: share, p: val, lo: Z, n: Z, contents: list val, len: Z, data: list Z
  PRE [ tulong, tptr tuchar, tulong ]
    PROP (0 <= a <= Int64.max_unsigned; 0 <= len <= Int64.max_unsigned;
          cbuf_ok false buf sh p lo n len contents data)
    PARAMS (Vlong (Int64.repr a); buf; Vlong (Int64.repr len))
    SEP (data_at sh (tarray tuchar n) contents p)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (ref_adler32 a data))) SEP (data_at sh (tarray tuchar n) contents p).

Definition Vprog_hr : varspecs := [].
Definition Gprog_ref_adler32 : funspecs := [].

(* The reference state after i bytes. *)
Definition aref (a: Z) (data: list Z) (i: Z) : Z * Z :=
  fold_left adler_ref_step (sublist 0 i data) (adler_lo a, adler_hi a).

Lemma aref_succ a data i: 0 <= i < Zlength data ->
  aref a data (i + 1) = adler_ref_step (aref a data i) (Znth i data).
Proof.
  intros. unfold aref. rewrite (sublist_split 0 i (i + 1)) by lia.
  rewrite fold_left_app, sublist_len_1 by lia. reflexivity.
Qed.

Lemma aref_range a data i: 0 <= fst (aref a data i) < 65536 /\ 0 <= snd (aref a data i) < 65536.
Proof.
  unfold aref. generalize (sublist 0 i data). intros l.
  assert (0 <= fst (adler_lo a, adler_hi a) < 65536 /\ 0 <= snd (adler_lo a, adler_hi a) < 65536)
    by (simpl; split; [apply adler_lo_range | apply adler_hi_range]).
  revert H. generalize (adler_lo a, adler_hi a). induction l as [|b l IH]; intros s Hs; simpl; auto.
  apply IH. unfold adler_ref_step; simpl.
  split; (split; [apply Z.mod_pos_bound; unfold ADLER_BASE; lia | ];
          apply (Z.lt_trans _ ADLER_BASE); [apply Z.mod_pos_bound; unfold ADLER_BASE; lia | unfold ADLER_BASE; lia]).
Qed.

Lemma or_pack_int s1 s2: 0 <= s1 < 65536 -> 0 <= s2 < 65536 ->
  Int64.or (Int64.shl (Int64.repr s2) (Int64.repr (Int.unsigned (Int.repr 16)))) (Int64.repr s1) =
  Int64.repr (s2 * 65536 + s1).
Proof. intros. rewrite Int64.or_commut. apply pack_int; auto. Qed.

Lemma modu65521 x: 0 <= x <= Int64.max_unsigned ->
  Int64.modu (Int64.repr x) (Int64.repr 65521) = Int64.repr (x mod ADLER_BASE).
Proof. intros. unfold Int64.modu. rewrite !Int64.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma body_ref_adler32: semax_body Vprog_hr Gprog_ref_adler32 HA.f_ref_adler32 ref_adler32_spec.
Proof.
  start_function.
  destruct H1 as (Hbuf & Hsh & Hlo & Hn & Hlen & Hby & Hsub). subst buf.
  assert_PROP (field_compatible (tarray tuchar n) [] p) as FC by entailer!.
  assert_PROP (Zlength contents = n) by (entailer!; rewrite Zlength_correct in *; auto).
  forward. forward.
  rewrite adler_lo_int, adler_hi_int by auto.
  forward_for_simple_bound len (EX i: Z,
     PROP () LOCAL (temp HA._s1 (Vlong (Int64.repr (fst (aref a data i))));
                    temp HA._s2 (Vlong (Int64.repr (snd (aref a data i))));
                    temp HA._buf (offset_val lo p); temp HA._n (Vlong (Int64.repr len)))
     SEP (data_at sh (tarray tuchar n) contents p)).
  - entailer!.
  - assert (E: force_val (sem_add_ptr_long tuchar (offset_val lo p) (Vlong (Int64.repr i))) =
               field_address (tarray tuchar n) [ArraySubsc (lo + i)] p) by (apply add_ptr_long; auto; lia).
    assert (Hb: @Znth val Vundef (lo + i) contents = Vint (Int.repr (Znth i data))) by (apply (Znth_cbuf lo len); auto; lia).
    assert (Hb2: 0 <= Znth i data <= Byte.max_unsigned) by (apply is_bytes_Znth; auto; lia).
    destruct (aref_range a data i) as [R1 R2].
    forward.
    { entailer!. rewrite Hb. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Hb.
    forward. forward.
    entailer!.
    rewrite aref_succ by lia. unfold adler_ref_step. simpl fst; simpl snd.
    rewrite (modu65521 (fst (aref a data i) + Znth i data)) by rep_lia.
    assert (0 <= (fst (aref a data i) + Znth i data) mod ADLER_BASE < ADLER_BASE)
      by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    rewrite add64_repr. rewrite modu65521 by (unfold ADLER_BASE in *; rep_lia).
    split; auto.
  - destruct (aref_range a data len) as [R1 R2].
    forward.
    rewrite or_pack_int by auto.
    entailer!.
    unfold ref_adler32, adler_pack. unfold aref. rewrite sublist_same by lia. auto.
Qed.
