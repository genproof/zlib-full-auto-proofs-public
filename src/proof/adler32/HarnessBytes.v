(* bytes_copy and bytes_same of harness/zlib_common.h: specifications and bodies, shared by every law
   whose harness uses them (the same Clight term in every harness unit; taken here from
   harness/adler32_ref.c's unit).  The source buffers are slices (Bytes.v cbuf_ok, isnull = false). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.adler32.Spec Zlib.proof.adler32.Ptr.
Require Zlib.harness.x_adler32_ref.code.
Module HA := Zlib.harness.x_adler32_ref.code.
#[local] Existing Instance Zlib.units.Adler32.CS.

(* d[0..len) := the bytes of the slice. *)
Definition bytes_copy_spec :=
  DECLARE HA._bytes_copy
  WITH d: val, dsh: share, s: val, sh: share, p: val, lo: Z, n: Z, contents: list val, len: Z, data: list Z
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share dsh; 0 <= len <= Int64.max_unsigned; cbuf_ok false s sh p lo n len contents data)
    PARAMS (d; s; Vlong (Int64.repr len))
    SEP (data_at_ dsh (tarray tuchar len) d; data_at sh (tarray tuchar n) contents p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at dsh (tarray tuchar len) (bytes_rep data) d; data_at sh (tarray tuchar n) contents p).

(* 1 when the two slices hold the same bytes, 0 otherwise. *)
Definition bytes_same_spec :=
  DECLARE HA._bytes_same
  WITH a: val, sha: share, pa: val, loa: Z, na: Z, ca: list val, da: list Z,
       b: val, shb: share, pb: val, lob: Z, nb: Z, cb: list val, db: list Z, len: Z
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (0 <= len <= Int64.max_unsigned; cbuf_ok false a sha pa loa na len ca da;
          cbuf_ok false b shb pb lob nb len cb db)
    PARAMS (a; b; Vlong (Int64.repr len))
    SEP (data_at sha (tarray tuchar na) ca pa; data_at shb (tarray tuchar nb) cb pb)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if list_eq_dec Z.eq_dec da db then 1 else 0)))
    SEP (data_at sha (tarray tuchar na) ca pa; data_at shb (tarray tuchar nb) cb pb).

Definition Vprog_hb : varspecs := [].
Definition Gprog_bytes : funspecs := [].

Lemma copy_step data i len: 0 <= i < len -> Zlength data = len ->
  upd_Znth i (bytes_rep (sublist 0 i data) ++ Zrepeat Vundef (len - i)) (Vint (Int.repr (Znth i data))) =
  bytes_rep (sublist 0 (i + 1) data) ++ Zrepeat Vundef (len - (i + 1)).
Proof.
  intros. unfold bytes_rep.
  rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
  rewrite map_app. simpl map.
  rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_sublist by lia; rewrite Zlength_Zrepeat by lia; lia).
  rewrite Zlength_map, Zlength_sublist by lia. rewrite Z.sub_0_r, Z.sub_diag.
  replace (len - i) with (1 + (len - (i + 1))) by lia.
  rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
  rewrite <- app_assoc. f_equal.
Qed.

Lemma body_bytes_copy: semax_body Vprog_hb Gprog_bytes HA.f_bytes_copy bytes_copy_spec.
Proof.
  start_function.
  match goal with H: cbuf_ok false _ _ _ _ _ _ _ _ |- _ => destruct H as (Hbuf & Hsh & Hlo & Hn & Hlen & Hby & Hsub) end.
  subst s.
  assert_PROP (field_compatible (tarray tuchar n) [] p) as FC by entailer!.
  assert_PROP (Zlength contents = n) by (entailer!; rewrite Zlength_correct in *; auto).
  forward_for_simple_bound len (EX i: Z,
     PROP () LOCAL (temp HA._d d; temp HA._s (offset_val lo p); temp HA._n (Vlong (Int64.repr len)))
     SEP (data_at dsh (tarray tuchar len) (bytes_rep (sublist 0 i data) ++ Zrepeat Vundef (len - i)) d;
          data_at sh (tarray tuchar n) contents p)).
  - entailer!. rewrite sublist_nil. unfold bytes_rep. simpl map. rewrite app_nil_l.
    apply derives_refl.
  - assert (E: force_val (sem_add_ptr_long tuchar (offset_val lo p) (Vlong (Int64.repr i))) =
               field_address (tarray tuchar n) [ArraySubsc (lo + i)] p) by (apply add_ptr_long; auto; lia).
    assert (Hb: @Znth val Vundef (lo + i) contents = Vint (Int.repr (Znth i data))) by (apply (Znth_cbuf lo len); auto; lia).
    assert (Hb2: 0 <= Znth i data <= Byte.max_unsigned) by (apply is_bytes_Znth; auto; lia).
    forward.
    { entailer!. rewrite Hb. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Hb.
    forward.
    rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
    rewrite copy_step by lia.
    entailer!.
  - forward. entailer!. rewrite sublist_same by lia. rewrite Z.sub_diag. simpl. rewrite app_nil_r. auto.
Qed.

Lemma body_bytes_same: semax_body Vprog_hb Gprog_bytes HA.f_bytes_same bytes_same_spec.
Proof.
  start_function.
  match goal with H: cbuf_ok false a _ _ _ _ _ _ _ |- _ => destruct H as (Ha & Hsha & Hloa & Hna & Hlena & Hbya & Hsuba) end.
  match goal with H: cbuf_ok false b _ _ _ _ _ _ _ |- _ => destruct H as (Hb & Hshb & Hlob & Hnb & Hlenb & Hbyb & Hsubb) end.
  subst a b.
  assert_PROP (field_compatible (tarray tuchar na) [] pa) as FCa by entailer!.
  assert_PROP (field_compatible (tarray tuchar nb) [] pb) as FCb by entailer!.
  assert_PROP (Zlength ca = na /\ Zlength cb = nb) as Eab by (entailer!; rewrite !Zlength_correct in *; auto).
  destruct Eab as [Ea Eb].
  forward_for_simple_bound len (EX i: Z,
     PROP (sublist 0 i da = sublist 0 i db)
     LOCAL (temp HA._a (offset_val loa pa); temp HA._b (offset_val lob pb); temp HA._n (Vlong (Int64.repr len)))
     SEP (data_at sha (tarray tuchar na) ca pa; data_at shb (tarray tuchar nb) cb pb)).
  - entailer!.
  - cbv beta. Intros.
    assert (E1: force_val (sem_add_ptr_long tuchar (offset_val loa pa) (Vlong (Int64.repr i))) =
               field_address (tarray tuchar na) [ArraySubsc (loa + i)] pa) by (apply add_ptr_long; auto; lia).
    assert (E2: force_val (sem_add_ptr_long tuchar (offset_val lob pb) (Vlong (Int64.repr i))) =
               field_address (tarray tuchar nb) [ArraySubsc (lob + i)] pb) by (apply add_ptr_long; auto; lia).
    assert (B1: @Znth val Vundef (loa + i) ca = Vint (Int.repr (Znth i da))) by (apply (Znth_cbuf loa len); auto; lia).
    assert (B2: @Znth val Vundef (lob + i) cb = Vint (Int.repr (Znth i db))) by (apply (Znth_cbuf lob len); auto; lia).
    assert (R1: 0 <= Znth i da <= Byte.max_unsigned) by (apply is_bytes_Znth; auto; lia).
    assert (R2: 0 <= Znth i db <= Byte.max_unsigned) by (apply is_bytes_Znth; auto; lia).
    forward.
    { entailer!. rewrite B1. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite B1.
    forward.
    { entailer!. rewrite B2. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite B2.
    forward_if.
    + forward. entailer!.
      destruct (list_eq_dec Z.eq_dec da db) as [D|D]; [ | reflexivity].
      subst db. contradiction.
    + forward. entailer!.
      assert (EZ: Znth i da = Znth i db) by (first [assumption | apply repr_inj_unsigned; rep_lia]).
      rewrite (sublist_split 0 i (i + 1) da) by lia. rewrite (sublist_split 0 i (i + 1) db) by lia.
      rewrite !sublist_len_1 by lia. rewrite EZ. f_equal. auto.
  - forward. entailer!.
    match goal with H: sublist 0 _ da = sublist 0 _ db |- _ => rewrite !sublist_same in H by lia; subst db end.
    destruct (list_eq_dec Z.eq_dec da da); [auto | contradiction].
Qed.
