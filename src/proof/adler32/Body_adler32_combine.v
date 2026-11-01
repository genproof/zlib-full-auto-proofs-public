(* The bodies of adler32_combine_ (the static function) and adler32_combine. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.adler32.code.
Require Import Zlib.proof.adler32.Spec Zlib.proof.adler32.Facts.
#[local] Existing Instance Zlib.units.Adler32.CS.

Ltac vnorm :=
  rewrite ?adler_lo_int, ?adler_hi_int by auto;
  rewrite ?add64_repr, ?sub64_repr, ?mul64_repr;
  try change (Int.unsigned (Int.repr 65521)) with 65521;
  try change (Int.signed (Int.repr 1)) with 1;
  try change (Int.unsigned (Int.repr 1)) with 1.

Ltac hnorm H :=
  rewrite ?add64_repr, ?sub64_repr in H;
  rewrite ?Int64.unsigned_repr in H by rep_lia;
  try change (Int.unsigned (Int.repr 65521)) with 65521 in H;
  try change (Int64.unsigned (Int64.repr 131042)) with 131042 in H;
  try match type of H with context [Int64.unsigned (Int64.shl ?a ?b)] =>
    let v := eval vm_compute in (Int64.unsigned (Int64.shl a b)) in
    change (Int64.unsigned (Int64.shl a b)) with v in H end;
  rewrite ?Int64.unsigned_repr in H by rep_lia.

Ltac shl_const :=
  repeat match goal with |- context [Int64.shl ?a ?b] =>
    let v := eval vm_compute in (Int64.unsigned (Int64.shl a b)) in
    replace (Int64.shl a b) with (Int64.repr v)
      by (rewrite <- (Int64.repr_unsigned (Int64.shl a b)); f_equal; vm_compute; reflexivity)
  end.

Lemma body_adler32_combine_: semax_body Vprog Gprog_adler32_combine_ f_adler32_combine_ adler32_combine__spec.
Proof.
  start_function.
  forward_if (PROP (0 <= len2) LOCAL (temp _adler1 (Vlong (Int64.repr x)); temp _adler2 (Vlong (Int64.repr y)); temp _len2 (Vlong (Int64.repr len2))) SEP ()).
  - rewrite !Int64.signed_repr in H2 by rep_lia.
    forward. entailer!. unfold adler32_combine_result. destruct (Z.ltb_spec len2 0); [auto | lia].
  - forward. entailer!. rewrite !Int64.signed_repr in H2 by rep_lia. lia.
  - Intros.
    forward.
    { entailer!. destruct H3 as [_ H3]. apply (f_equal Int.unsigned) in H3. vm_compute in H3. discriminate. }
    rewrite mods_int by rep_lia.
    set (r := len2 mod ADLER_BASE).
    assert (Hr: 0 <= r < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    pose proof (adler_lo_range x). pose proof (adler_hi_range x).
    pose proof (adler_lo_range y). pose proof (adler_hi_range y).
    set (x1 := adler_lo x) in *. set (x2 := adler_hi x) in *.
    set (y1 := adler_lo y) in *. set (y2 := adler_hi y) in *.
    forward. rewrite Int64.unsigned_repr by (unfold ADLER_BASE in *; rep_lia).
    forward. vnorm. fold x1.
    forward. rewrite Int.unsigned_repr by (unfold ADLER_BASE in *; rep_lia).
    forward.
    assert (0 <= r * x1 < 2 ^ 32) by (unfold ADLER_BASE in *; nia).
    forward. vnorm. fold x1 y1.
    forward. vnorm. fold x2 y2.
    rewrite ?(Int.unsigned_repr r) by (unfold ADLER_BASE in *; rep_lia).
    replace (Int64.modu (Int64.repr (r * x1)) (Int64.repr 65521)) with (Int64.repr ((r * x1) mod ADLER_BASE))
      by (rewrite <- modu_int by (unfold ADLER_BASE in *; rep_lia); reflexivity).
    rewrite ?add64_repr.
    set (m := (r * x1) mod ADLER_BASE).
    assert (Hm: 0 <= m < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    set (s1a := x1 + (y1 + 65521 - 1)).
    set (s2a := m + (x2 + y2 + 65521 - r)).
    set (s1b := if s1a <? ADLER_BASE then s1a else s1a - ADLER_BASE).
    forward_if (PROP () LOCAL (temp _sum1 (Vlong (Int64.repr s1b)); temp _sum2 (Vlong (Int64.repr s2a))) SEP ()).
    + hnorm H8. forward. entailer!. unfold s1b. destruct (Z.ltb_spec s1a ADLER_BASE); unfold ADLER_BASE in *; [lia | auto].
    + hnorm H8. forward. entailer!. unfold s1b. destruct (Z.ltb_spec s1a ADLER_BASE); unfold ADLER_BASE in *; [auto | lia].
    + assert (Hs1b: 0 <= s1b < 3 * 65536) by (unfold s1b, s1a, ADLER_BASE in *; destruct (Z.ltb_spec (x1 + (y1 + 65521 - 1)) 65521); lia).
      set (s1c := if s1b <? ADLER_BASE then s1b else s1b - ADLER_BASE).
      forward_if (PROP () LOCAL (temp _sum1 (Vlong (Int64.repr s1c)); temp _sum2 (Vlong (Int64.repr s2a))) SEP ()).
      * hnorm H8. forward. entailer!. unfold s1c. destruct (Z.ltb_spec s1b ADLER_BASE); unfold ADLER_BASE in *; [lia | auto].
      * hnorm H8. forward. entailer!. unfold s1c. destruct (Z.ltb_spec s1b ADLER_BASE); unfold ADLER_BASE in *; [auto | lia].
      * assert (Hs1c: 0 <= s1c < 3 * 65536) by (unfold s1c, ADLER_BASE in *; destruct (Z.ltb_spec s1b 65521); lia).
        assert (Hs2a: 0 <= s2a < 5 * 65536) by (unfold s2a, ADLER_BASE in *; lia).
        set (s2b := if s2a <? 2 * ADLER_BASE then s2a else s2a - 2 * ADLER_BASE).
        forward_if (PROP () LOCAL (temp _sum1 (Vlong (Int64.repr s1c)); temp _sum2 (Vlong (Int64.repr s2b))) SEP ()).
        -- hnorm H8. forward. shl_const. rewrite sub64_repr. entailer!.
           unfold s2b. destruct (Z.ltb_spec s2a (2 * ADLER_BASE)); unfold ADLER_BASE in *; [lia | ].
           all: try (f_equal; f_equal; lia).
        -- hnorm H8. forward. entailer!. unfold s2b. destruct (Z.ltb_spec s2a (2 * ADLER_BASE)); unfold ADLER_BASE in *; [auto | lia].
        -- assert (Hs2b: 0 <= s2b < 5 * 65536) by (unfold s2b, ADLER_BASE in *; destruct (Z.ltb_spec s2a (2 * 65521)); lia).
           set (s2c := if s2b <? ADLER_BASE then s2b else s2b - ADLER_BASE).
           forward_if (PROP () LOCAL (temp _sum1 (Vlong (Int64.repr s1c)); temp _sum2 (Vlong (Int64.repr s2c))) SEP ()).
           ++ hnorm H8. forward. entailer!. unfold s2c. destruct (Z.ltb_spec s2b ADLER_BASE); unfold ADLER_BASE in *; [lia | auto].
           ++ hnorm H8. forward. entailer!. unfold s2c. destruct (Z.ltb_spec s2b ADLER_BASE); unfold ADLER_BASE in *; [auto | lia].
           ++ assert (Hs2c: 0 <= s2c < 5 * 65536) by (unfold s2c, ADLER_BASE in *; destruct (Z.ltb_spec s2b 65521); lia).
              forward.
              rewrite lor_pack_int by lia.
              entailer!.
              unfold adler32_combine_result. destruct (Z.ltb_spec len2 0); [lia | ].
              unfold adler32_combine_impl. cbv zeta. fold r x1 x2 y1 y2 m.
              replace (x1 + y1 + ADLER_BASE - 1) with s1a by (unfold s1a, ADLER_BASE; lia).
              replace (m + x2 + y2 + ADLER_BASE - r) with s2a by (unfold s2a, ADLER_BASE; lia).
              fold s1b s1c s2b s2c. reflexivity.
Qed.

Lemma body_adler32_combine: semax_body Vprog Gprog_adler32_combine f_adler32_combine adler32_combine_spec.
Proof.
  start_function.
  forward_call (x, y, len2).
  forward.
Qed.
