(* The body of adler32_z: the one-byte path, the short path (len < 16), and the long path (blocks of
   NMAX = 5552 bytes, 16 bytes unrolled, one reduction per block). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.adler32.code.
Require Import Zlib.proof.adler32.Spec Zlib.proof.adler32.Facts Zlib.proof.adler32.Ptr.
#[local] Existing Instance Zlib.units.Adler32.CS.

Ltac strip_repr :=
  rewrite ?sub64_repr, ?add64_repr;
  try change (Int.unsigned (Int.repr 65521)) with 65521;
  try match goal with |- Vlong _ = Vlong _ => f_equal end;
  try match goal with |- Int64.repr _ = Int64.repr _ => f_equal end.

Ltac print_goal := match goal with |- ?g => idtac g end.

Ltac hnorm H :=
  rewrite ?add64_repr, ?sub64_repr in H;
  rewrite ?Int64.unsigned_repr in H by rep_lia;
  try change (Int.unsigned (Int.repr 65521)) with 65521 in H;
  try change (Int.signed (Int.repr 16)) with 16 in H;
  try change (Int.signed (Int.repr 5552)) with 5552 in H;
  rewrite ?Int64.unsigned_repr in H by rep_lia.

(* Normalise the machine values of adler/sum2 after `adler += b; sum2 += adler` at data index j. *)
Ltac adler_norm_step j :=
  rewrite (Int.unsigned_repr (Znth j _)) by rep_lia;
  rewrite add64_repr;
  rewrite aseg1_succ by lia.

(* One byte through a pointer that is incremented: t = buf; buf = t + 1; b = *t; adler += b; sum2 += adler. *)
Ltac adler_byte_inc lo p n len contents data :=
  match goal with |- context [temp _adler (Vlong (Int64.repr (aseg1 ?s data ?i0 ?j)))] =>
  forward; forward;
  rewrite add_ptr_1 by auto;
  replace (lo + j + 1) with (lo + (j + 1)) by lia;
  let Hfa := fresh "Hfa" in
  assert (Hfa: offset_val (lo + j) p = field_address (tarray tuchar n) [ArraySubsc (lo + j)] p)
    by (apply offset_field_address; auto; lia);
  rewrite Hfa;
  let Hb := fresh "Hb" in let Hb2 := fresh "Hb2" in
  assert (Hb: @Znth val Vundef (lo + j) contents = Vint (Int.repr (Znth j data)))
    by (apply (Znth_cbuf lo len); auto; lia);
  assert (Hb2: 0 <= Znth j data <= Byte.max_unsigned) by (apply is_bytes_Znth; auto; lia);
  forward;
  [ entailer!; rewrite Hb; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia | ];
  rewrite Hb;
  forward;
  rewrite (Int.unsigned_repr (Znth j data)) by rep_lia; rewrite add64_repr; rewrite aseg1_succ by lia;
  forward;
  rewrite add64_repr; rewrite aseg2_succ by lia;
  clear Hfa Hb Hb2
  end.

(* One byte at a constant offset c from buf (DO1(buf, c)): b = buf[c]; adler += b; sum2 += adler. *)
Ltac adler_byte_at lo p n len contents data i c :=
  let Hfa := fresh "Hfa" in
  assert (Hfa: force_val (sem_add_ptr_int tuchar Signed (offset_val (lo + i) p) (Vint (Int.repr c))) =
               field_address (tarray tuchar n) [ArraySubsc (lo + (i + c))] p)
    by (rewrite (add_ptr_c p n (lo + i) c) by (auto; rep_lia); f_equal; f_equal; f_equal; lia);
  let Hb := fresh "Hb" in let Hb2 := fresh "Hb2" in
  assert (Hb: @Znth val Vundef (lo + (i + c)) contents = Vint (Int.repr (Znth (i + c) data)))
    by (apply (Znth_cbuf lo len); auto; lia);
  assert (Hb2: 0 <= Znth (i + c) data <= Byte.max_unsigned) by (apply is_bytes_Znth; auto; lia);
  forward;
  [ entailer!; match goal with |- context [@Znth val ?d ?x contents] =>
      replace (@Znth val d x contents) with (Vint (Int.repr (Znth (i + c) data))) by (rewrite <- Hb; f_equal; lia) end;
    simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia | ];
  match goal with |- context [@Znth val ?d ?x contents] =>
      replace (@Znth val d x contents) with (Vint (Int.repr (Znth (i + c) data))) by (rewrite <- Hb; f_equal; lia) end;
  forward;
  rewrite (Int.unsigned_repr (Znth (i + c) data)) by rep_lia; rewrite add64_repr;
  match goal with |- context [temp _adler (Vlong (Int64.repr (aseg1 ?s data ?i0 ?j + Znth (i + c) data)))] =>
    replace (aseg1 s data i0 j + Znth (i + c) data) with (aseg1 s data i0 (i + c + 1))
      by (replace (Znth (i + c) data) with (Znth j data) by (f_equal; lia);
          rewrite aseg1_succ by lia; f_equal; lia)
  end;
  forward;
  rewrite add64_repr;
  match goal with |- context [temp _sum2 (Vlong (Int64.repr (aseg2 ?s data ?i0 ?j + aseg1 ?s data ?i0 (i + c + 1))))] =>
    replace (aseg2 s data i0 j + aseg1 s data i0 (i + c + 1)) with (aseg2 s data i0 (i + c + 1))
      by (replace (aseg1 s data i0 (i + c + 1)) with (aseg1 s data i0 (j + 1)) by (f_equal; lia);
          rewrite aseg2_succ by lia; f_equal; lia)
  end;
  clear Hfa Hb Hb2.

Ltac do16 lo p n len contents data i :=
  adler_byte_at lo p n len contents data i 0;
  adler_byte_at lo p n len contents data i 1;
  adler_byte_at lo p n len contents data i 2;
  adler_byte_at lo p n len contents data i 3;
  adler_byte_at lo p n len contents data i 4;
  adler_byte_at lo p n len contents data i 5;
  adler_byte_at lo p n len contents data i 6;
  adler_byte_at lo p n len contents data i 7;
  adler_byte_at lo p n len contents data i 8;
  adler_byte_at lo p n len contents data i 9;
  adler_byte_at lo p n len contents data i 10;
  adler_byte_at lo p n len contents data i 11;
  adler_byte_at lo p n len contents data i 12;
  adler_byte_at lo p n len contents data i 13;
  adler_byte_at lo p n len contents data i 14;
  adler_byte_at lo p n len contents data i 15.

Ltac close_eqs :=
  repeat match goal with
  | |- _ /\ _ => split
  | |- Vlong _ = Vlong _ => f_equal
  | |- Vint _ = Vint _ => f_equal
  | |- Int64.repr _ = Int64.repr _ => f_equal
  | |- Int.repr _ = Int.repr _ => f_equal
  | |- offset_val _ _ = offset_val _ _ => f_equal
  | |- aseg1 _ _ _ _ = aseg1 _ _ _ _ => f_equal
  | |- aseg2 _ _ _ _ = aseg2 _ _ _ _ => f_equal
  end; try lia.

Lemma body_adler32_z: semax_body Vprog Gprog_adler32_z f_adler32_z adler32_z_spec.
Proof.
  start_function.
  forward. forward.
  rewrite adler_lo_int, adler_hi_int by auto.
  pose proof (adler_lo_range adler). pose proof (adler_hi_range adler).
  set (a1 := adler_lo adler) in *. set (a2 := adler_hi adler) in *.
  destruct isnull.
  - simpl in H1. subst buf. forward_if (False); [forward | contradiction].
  - destruct H1 as (Hbuf & Hsh & Hlo & Hn & Hlen & Hby & Hsub). subst buf. simpl.
    assert_PROP (isptr p) as Hp by entailer!.
    assert_PROP (field_compatible (tarray tuchar n) [] p) as FC by entailer!.
    assert_PROP (Zlength contents = n) by (entailer!; rewrite Zlength_correct in *; auto).
    assert (Htok: tok = true \/ 0 < n) by (destruct tok; [left; auto | right; apply H2; auto]).
    forward_if (PROP () LOCAL (temp _sum2 (Vlong (Int64.repr a2)); temp _adler (Vlong (Int64.repr a1));
                               temp _buf (offset_val lo p); temp _len (Vlong (Int64.repr len)))
       SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
    { apply cbuf_test_eq; auto; lia. }
    { destruct p; try contradiction. simpl in H5. discriminate. }
    { forward. entailer!. }
    forward_if (PROP (len <> 1) LOCAL (temp _sum2 (Vlong (Int64.repr a2)); temp _adler (Vlong (Int64.repr a1));
                               temp _buf (offset_val lo p); temp _len (Vlong (Int64.repr len)))
         SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
    + (* ---- the one-byte path ---- *)
      apply Int64.same_if_eq in H5. apply repr_inj_unsigned64 in H5; [ | rep_lia | rep_lia].
      rewrite H5 in *. clear H5.
      destruct data as [|b0 [|b1 l]];
        [rewrite Zlength_nil in Hlen; lia | | rewrite !Zlength_cons in Hlen; pose proof (Zlength_nonneg l); lia].
      clear Hlen.
      assert (Hb: @Znth val Vundef lo contents = Vint (Int.repr b0)).
      { rewrite <- (Z.add_0_r lo) at 1. apply (Znth_cbuf lo 1 contents [b0] 0); auto; lia. }
      assert (Hb0: 0 <= b0 <= 255) by (inv Hby; rep_lia).
      assert (E: force_val (sem_add_ptr_int tuchar Signed (offset_val lo p) (Vint (Int.repr 0))) =
                 field_address (tarray tuchar n) [ArraySubsc lo] p).
      { rewrite (add_ptr_c p n lo 0) by (auto; rep_lia). rewrite Z.add_0_r. auto. }
      forward.
      { entailer!. rewrite Hb. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite Hb.
      forward.
      rewrite (Int.unsigned_repr b0) by rep_lia. rewrite add64_repr.
      set (s1 := (a1 + b0) mod ADLER_BASE).
      assert (Hs1: 0 <= s1 < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
      forward_if (PROP () LOCAL (temp _sum2 (Vlong (Int64.repr a2)); temp _adler (Vlong (Int64.repr s1)))
         SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
      * rewrite ?add64_repr in H5. rewrite ?Int64.unsigned_repr in H5 by rep_lia.
        try change (Int.unsigned (Int.repr 65521)) with 65521 in H5.
        forward. entailer!. strip_repr.
        unfold s1, ADLER_BASE. rewrite <- (Z.mod_add _ (-1)) by lia.
        rewrite Z.mod_small by lia. lia.
      * rewrite ?add64_repr in H5. rewrite ?Int64.unsigned_repr in H5 by rep_lia.
        try change (Int.unsigned (Int.repr 65521)) with 65521 in H5.
        forward. entailer!. strip_repr. unfold s1, ADLER_BASE. rewrite Z.mod_small by lia. auto.
      * forward. rewrite add64_repr.
        set (t := a2 + s1).
        forward_if (PROP () LOCAL (temp _sum2 (Vlong (Int64.repr (if t <? ADLER_BASE then t else t - ADLER_BASE)));
                                   temp _adler (Vlong (Int64.repr s1)))
           SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
        -- rewrite ?Int64.unsigned_repr in H5 by (unfold t, ADLER_BASE in *; rep_lia).
           try change (Int.unsigned (Int.repr 65521)) with 65521 in H5.
           forward. entailer!. strip_repr.
           destruct (Z.ltb_spec t ADLER_BASE); [unfold ADLER_BASE in *; lia | auto].
        -- rewrite ?Int64.unsigned_repr in H5 by (unfold t, ADLER_BASE in *; rep_lia).
           try change (Int.unsigned (Int.repr 65521)) with 65521 in H5.
           forward. entailer!. strip_repr.
           destruct (Z.ltb_spec t ADLER_BASE); [auto | unfold ADLER_BASE in *; lia].
        -- assert (Ht: 0 <= (if t <? ADLER_BASE then t else t - ADLER_BASE) < 65536).
           { unfold t, ADLER_BASE in *. destruct (Z.ltb_spec (a2 + s1) 65521); lia. }
           forward.
           rewrite pack_int by (unfold ADLER_BASE in *; lia).
           entailer!.
    + forward. entailer!.
    + Intros. rename H5 into Hlen1.
      (* the second Z_NULL test (dead) *)
      forward_if (PROP () LOCAL (temp _sum2 (Vlong (Int64.repr a2)); temp _adler (Vlong (Int64.repr a1));
                                 temp _buf (offset_val lo p); temp _len (Vlong (Int64.repr len)))
         SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
      { apply cbuf_test_eq; auto; lia. }
      { destruct p; try contradiction. simpl in H5. discriminate. }
      { forward. entailer!. }
      forward_if (PROP (16 <= len) LOCAL (temp _sum2 (Vlong (Int64.repr a2)); temp _adler (Vlong (Int64.repr a1));
                                 temp _buf (offset_val lo p); temp _len (Vlong (Int64.repr len)))
         SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
      * (* ---- the short path: len < 16 ---- *)
        rewrite ?Int64.unsigned_repr in H5 by rep_lia.
        try change (Int64.unsigned (Int64.repr (Int.signed (Int.repr 16)))) with 16 in H5.
        set (s0 := (a1, a2)).
        forward_loop (EX i: Z,
            PROP (0 <= i <= len)
            LOCAL (temp _sum2 (Vlong (Int64.repr (aseg2 s0 data 0 i)));
                   temp _adler (Vlong (Int64.repr (aseg1 s0 data 0 i)));
                   temp _buf (offset_val (lo + i) p); temp _len (Vlong (Int64.repr (len - i))))
            SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p))
          break: (PROP () LOCAL (temp _sum2 (Vlong (Int64.repr (aseg2 s0 data 0 len)));
                                 temp _adler (Vlong (Int64.repr (aseg1 s0 data 0 len))))
            SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
        -- Exists 0. destruct (aseg_nil s0 data 0) as [E1 E2]. rewrite E1, E2. entailer!.
        -- Intros i. forward. forward.
           forward_if (PROP (i < len)
              LOCAL (temp _sum2 (Vlong (Int64.repr (aseg2 s0 data 0 i)));
                     temp _adler (Vlong (Int64.repr (aseg1 s0 data 0 i)));
                     temp _buf (offset_val (lo + i) p); temp _len (Vlong (Int64.repr (len - (i + 1)))))
              SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
           ++ assert (i <> len) by (intro; subst i; rewrite Z.sub_diag in H7; contradiction).
              forward. entailer!.
              repeat split; try lia; try (strip_repr; lia).
           ++ assert (i = len) by (apply repr_inj_unsigned64 in H7; rep_lia). subst i.
              forward. entailer!.
           ++ Intros.
              adler_byte_inc lo p n len contents data.
              Exists (i + 1). entailer!.
        -- assert (Bd: 0 <= aseg1 s0 data 0 len <= 65535 + 255 * 15 /\ 0 <= aseg2 s0 data 0 len <= 65535 + 15 * (65535 + 255 * 15)).
           { destruct (aseg_bound s0 data 0 len) as [B1 B2]; unfold s0 in *; simpl fst in *; simpl snd in *; try lia; auto.
             split; [lia | ]. split; [lia | ]. assert (len * (a1 + 255 * len) <= 15 * (65535 + 255 * 15)) by nia. lia. }
           set (A := aseg1 s0 data 0 len) in *. set (S := aseg2 s0 data 0 len) in *.
           forward_if (PROP () LOCAL (temp _sum2 (Vlong (Int64.repr S)); temp _adler (Vlong (Int64.repr (A mod ADLER_BASE))))
             SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
           ++ hnorm H6.
              forward. entailer!. strip_repr.
              unfold ADLER_BASE. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
           ++ hnorm H6.
              forward. entailer!. strip_repr. unfold ADLER_BASE. rewrite Z.mod_small by lia. auto.
           ++ forward.
              rewrite modu_int by rep_lia.
              assert (0 <= A mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
              assert (0 <= S mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
              forward.
              rewrite pack_int by (unfold ADLER_BASE in *; lia).
              entailer!.
              rewrite adler32_z_val_sums by lia. fold a1 a2 s0. auto.
      * forward. entailer!. rewrite !Int64.unsigned_repr in H5 by rep_lia. lia.
      * Intros. rename H5 into Hlen16.
        set (s0 := (a1, a2)).
        forward_while (EX i: Z, EX A: Z, EX S: Z,
            PROP (0 <= i <= len; A mod ADLER_BASE = aseg1 s0 data 0 i mod ADLER_BASE;
                  S mod ADLER_BASE = aseg2 s0 data 0 i mod ADLER_BASE;
                  0 <= A < 65536; 0 <= S < 65536; i = 0 \/ (A < ADLER_BASE /\ S < ADLER_BASE))
            LOCAL (temp _sum2 (Vlong (Int64.repr S)); temp _adler (Vlong (Int64.repr A));
                   temp _buf (offset_val (lo + i) p); temp _len (Vlong (Int64.repr (len - i))))
            SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
        -- Exists 0 a1 a2. destruct (aseg_nil s0 data 0) as [E1 E2]. rewrite E1, E2. entailer!.
        -- entailer!.
        -- hnorm HRE.
           forward. forward.
           replace (Int.divs (Int.repr 5552) (Int.repr 16)) with (Int.repr 347) by reflexivity.
           change (Int.signed (Int.repr 5552)) with 5552. rewrite sub64_repr.
           forward_loop (EX k: Z,
               PROP (0 <= k < 347)
               LOCAL (temp _n (Vint (Int.repr (347 - k)));
                      temp _len (Vlong (Int64.repr (len - i - 5552)));
                      temp _sum2 (Vlong (Int64.repr (aseg2 (A, S) data i (i + 16 * k))));
                      temp _adler (Vlong (Int64.repr (aseg1 (A, S) data i (i + 16 * k))));
                      temp _buf (offset_val (lo + (i + 16 * k)) p))
               SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p))
             continue: (EX k: Z,
               PROP (0 <= k < 347)
               LOCAL (temp _n (Vint (Int.repr (347 - k)));
                      temp _len (Vlong (Int64.repr (len - i - 5552)));
                      temp _sum2 (Vlong (Int64.repr (aseg2 (A, S) data i (i + 16 * k + 16))));
                      temp _adler (Vlong (Int64.repr (aseg1 (A, S) data i (i + 16 * k + 16))));
                      temp _buf (offset_val (lo + (i + 16 * k + 16)) p))
               SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p))
             break: (PROP ()
               LOCAL (temp _len (Vlong (Int64.repr (len - i - 5552)));
                      temp _sum2 (Vlong (Int64.repr (aseg2 (A, S) data i (i + 5552))));
                      temp _adler (Vlong (Int64.repr (aseg1 (A, S) data i (i + 5552))));
                      temp _buf (offset_val (lo + (i + 5552)) p))
               SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
           ++ Exists 0. destruct (aseg_nil (A, S) data i) as [E1 E2]. rewrite Z.add_0_r, E1, E2. entailer!.
           ++ Intros k.
              do16 lo p n len contents data (i + 16 * k).
              forward.
              rewrite add_ptr_n by (auto; rep_lia).
              Exists k. entailer!; close_eqs.
           ++ Intros k. forward. forward.
              rewrite ?sub_repr.
              forward_if.
              ** forward. Exists (k + 1). entailer!.
                 assert (k <> 346) by (intro; subst k; contradiction).
                 close_eqs.
              ** forward. entailer!.
                 assert (k = 346).
                 { match goal with H: Int.repr (347 - k - 1) = _ |- _ => apply repr_inj_unsigned in H; rep_lia end. }
                 subst k. close_eqs.
           ++ destruct (aseg_block_bound A S data i (i + 5552)) as [B1 B2]; try lia; auto.
              forward. forward.
              rewrite !modu_int by auto.
              destruct (aseg_step_mod s0 data A S i (i + 5552)) as [M1 M2]; try lia; auto.
              Exists (i + 5552, aseg1 (A, S) data i (i + 5552) mod ADLER_BASE, aseg2 (A, S) data i (i + 5552) mod ADLER_BASE).
              assert (0 <= aseg1 (A, S) data i (i + 5552) mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
              assert (0 <= aseg2 (A, S) data i (i + 5552) mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
              entailer!.
              rewrite !Zmod_mod. unfold ADLER_BASE in *.
              repeat split; try lia; try (rewrite ?M1, ?M2; auto); try close_eqs.
        -- (* the tail: len - i < NMAX *)
           hnorm HRE.
           assert (Hfin: forall A' S', A' = aseg1 s0 data 0 len mod ADLER_BASE -> S' = aseg2 s0 data 0 len mod ADLER_BASE ->
                     0 <= A' < ADLER_BASE /\ 0 <= S' < ADLER_BASE).
           { intros A' S' -> ->. split; apply Z.mod_pos_bound; unfold ADLER_BASE; lia. }
           forward_if (PROP () LOCAL (temp _sum2 (Vlong (Int64.repr (aseg2 s0 data 0 len mod ADLER_BASE)));
                                      temp _adler (Vlong (Int64.repr (aseg1 s0 data 0 len mod ADLER_BASE))))
             SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
           ++ (* len - i <> 0 *)
              forward_while (EX k: Z,
                  PROP (0 <= k; i + 16 * k <= len)
                  LOCAL (temp _sum2 (Vlong (Int64.repr (aseg2 (A, S) data i (i + 16 * k))));
                         temp _adler (Vlong (Int64.repr (aseg1 (A, S) data i (i + 16 * k))));
                         temp _buf (offset_val (lo + (i + 16 * k)) p);
                         temp _len (Vlong (Int64.repr (len - (i + 16 * k)))))
                  SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
              ** Exists 0. destruct (aseg_nil (A, S) data i) as [E1 E2]. rewrite Z.add_0_r, E1, E2. entailer!.
              ** entailer!.
              ** hnorm HRE0. forward.
                 do16 lo p n len contents data (i + 16 * k).
                 forward.
                 rewrite add_ptr_n by (auto; rep_lia).
                 Exists (k + 1). entailer!; close_eqs.
              ** hnorm HRE0.
                 forward_loop (EX m: Z,
                     PROP (i + 16 * k <= m <= len)
                     LOCAL (temp _sum2 (Vlong (Int64.repr (aseg2 (A, S) data i m)));
                            temp _adler (Vlong (Int64.repr (aseg1 (A, S) data i m)));
                            temp _buf (offset_val (lo + m) p);
                            temp _len (Vlong (Int64.repr (len - m))))
                     SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p))
                   break: (PROP ()
                     LOCAL (temp _sum2 (Vlong (Int64.repr (aseg2 (A, S) data i len)));
                            temp _adler (Vlong (Int64.repr (aseg1 (A, S) data i len))))
                     SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
                 --- Exists (i + 16 * k). entailer!; close_eqs.
                 --- Intros m. forward. forward.
                     forward_if (PROP (m < len)
                        LOCAL (temp _sum2 (Vlong (Int64.repr (aseg2 (A, S) data i m)));
                               temp _adler (Vlong (Int64.repr (aseg1 (A, S) data i m)));
                               temp _buf (offset_val (lo + m) p); temp _len (Vlong (Int64.repr (len - (m + 1)))))
                        SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
                     +++ assert (m <> len) by (intro; subst m; match goal with H: Int64.repr (?a - ?a) <> _ |- _ => rewrite Z.sub_diag in H; contradiction end).
                         forward. entailer!. repeat split; try lia; try (strip_repr; lia).
                     +++ assert (m = len) by (match goal with H: Int64.repr (len - m) = _ |- _ => apply repr_inj_unsigned64 in H; rep_lia end). subst m.
                         forward. entailer!.
                     +++ Intros.
                         adler_byte_inc lo p n len contents data.
                         Exists (m + 1). entailer!.
                 --- destruct (aseg_block_bound A S data i len) as [B1 B2]; try lia; auto.
                     destruct (aseg_step_mod s0 data A S i len) as [M1 M2]; try lia; auto.
                     forward. forward.
                     rewrite !modu_int by auto.
                     entailer!; rewrite M1, M2; auto.
           ++ (* len = i *)
              assert (i = len) by (match goal with H: Int64.repr (len - i) = _ |- _ => apply repr_inj_unsigned64 in H; rep_lia end). subst i.
              forward. entailer!.
              destruct H10 as [H10 | [HA HS]]; [lia | ].
              rewrite <- H6, <- H7. rewrite !Z.mod_small by (unfold ADLER_BASE in *; lia). auto.
           ++ destruct (Hfin _ _ eq_refl eq_refl) as [F1 F2].
              forward.
              rewrite pack_int by (unfold ADLER_BASE in *; lia).
              entailer!.
              rewrite adler32_z_val_sums by lia. fold a1 a2 s0. auto.
Qed.
