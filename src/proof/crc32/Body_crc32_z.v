(* The body of crc32_z (byte-wise table loop, no braided CRC: -DZ_TESTW=). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.crc32.code.
Require Import Zlib.proof.crc32.Spec Zlib.proof.crc32.IntFacts.
#[local] Existing Instance Zlib.units.Crc32.CS.

(* One byte of the loops: t = buf; buf = t + 1; b = *t; v = crc_table[(crc ^ b) & 0xff]; crc = (crc >> 8) ^ v. *)

Ltac crc_byte lo p n len contents data c0 :=
  match goal with |- context [temp _crc (Vlong (Int64.repr (crc_reg c0 data ?i)))] =>
  forward; forward;
  rewrite add_ptr_1 by auto;
  replace (lo + i + 1) with (lo + (i + 1)) by lia;
  let Hfa := fresh "Hfa" in
  assert_PROP (offset_val (lo + i) p = field_address (tarray tuchar n) [ArraySubsc (lo + i)] p) as Hfa
    by (entailer!; rewrite arr_field_address by (auto; lia); simpl; f_equal; lia);
  rewrite Hfa;
  let Hb := fresh "Hb" in let Hb2 := fresh "Hb2" in
  assert (Hb: @Znth val Vundef (lo + i) contents = Vint (Int.repr (Znth i data)))
    by (apply (Znth_cbuf lo len); auto; lia);
  assert (Hb2: 0 <= Znth i data <= Byte.max_unsigned) by (apply is_bytes_Znth; auto; lia);
  forward;
  [ entailer!; rewrite Hb; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia | ];
  rewrite Hb;
  let Hc := fresh "Hc" in
  assert (Hc: 0 <= crc_reg c0 data i < 2 ^ 32) by (apply crc_reg_range; auto);
  forward;
  [ entailer!; rewrite crc_idx_int by auto; pose proof (Z_land_255_range (Z.lxor (crc_reg c0 data i) (Znth i data))); lia
  | entailer!; rewrite crc_table_load by auto; simpl; auto | ];
  rewrite crc_table_load by auto;
  forward;
  rewrite crc_update_int by auto;
  rewrite crc_reg_succ by lia;
  clear Hfa Hb Hb2 Hc
  end.

Ltac close_eqs :=
  repeat match goal with
  | |- _ /\ _ => split
  | |- Vlong _ = Vlong _ => f_equal
  | |- Int64.repr _ = Int64.repr _ => f_equal
  | |- offset_val _ _ = offset_val _ _ => f_equal
  | |- crc_reg _ _ _ = crc_reg _ _ _ => f_equal
  end; try lia.

Lemma body_crc32_z: semax_body Vprog Gprog_crc32_z f_crc32_z crc32_z_spec.
Proof.
  start_function.
  destruct isnull.
  - simpl in H1. subst buf.
    forward_if (False); [forward | contradiction].
  - destruct H1 as (Hbuf & Hsh & Hlo & Hn & Hlen & Hby & Hsub). subst buf. simpl.
    assert_PROP (isptr p) by entailer!.
    assert_PROP (Zlength contents = n) by (entailer!; rewrite Zlength_correct in *; auto).
    forward_if (PROP () LOCAL (temp _crc (Vlong (Int64.repr crc)); temp _buf (offset_val lo p); temp _len (Vlong (Int64.repr len)); gvars gv)
       SEP (crc_table_at tsh gv; if tok then malloc_token vsh (tarray tuchar n) p else emp; data_at sh (tarray tuchar n) contents p)).
    { rewrite sepcon_assoc. apply cbuf_test_eq_frame; auto; try lia.
      destruct tok; [left; auto | right; apply H2; auto]. }
    + destruct p; try contradiction. simpl in H3. discriminate.
    + forward. entailer!.
    + forward.
      set (c0 := Z.lxor (crc mod 2^32) crc_mask).
      assert (Hc0: 0 <= c0 < 2 ^ 32).
      { apply lxor_lt_pow2; [lia | apply Z.mod_pos_bound; lia | apply crc_mask_range]. }
      rewrite crc_pre_int by auto. fold c0.
      unfold crc_table_at.
      forward_while (EX j: Z,
        PROP (0 <= j; 8 * j <= len)
        LOCAL (temp _crc (Vlong (Int64.repr (crc_reg c0 data (8 * j))));
               temp _buf (offset_val (lo + 8*j) p); temp _len (Vlong (Int64.repr (len - 8*j))); gvars gv)
        SEP (data_at tsh (tarray tuint 256) crc_table_rep (gv _crc_table);
             if tok then malloc_token vsh (tarray tuchar n) p else emp;
             data_at sh (tarray tuchar n) contents p)).
      * Exists 0. entailer!.
      * entailer!.
      * forward.
        do 8 crc_byte lo p n len contents data c0.
        Exists (j + 1). entailer!.
        close_eqs.
      * forward_while (EX i: Z,
          PROP (8 * j <= i <= len)
          LOCAL (temp _crc (Vlong (Int64.repr (crc_reg c0 data i)));
                 temp _buf (offset_val (lo + i) p); temp _len (Vlong (Int64.repr (len - i))); gvars gv)
          SEP (data_at tsh (tarray tuint 256) crc_table_rep (gv _crc_table);
               if tok then malloc_token vsh (tarray tuchar n) p else emp;
               data_at sh (tarray tuchar n) contents p)).
        -- Exists (8 * j). entailer!.
        -- entailer!.
        -- assert (i < len).
           { destruct (zlt i len); auto. assert (i = len) by lia. subst i.
             rewrite Z.sub_diag in HRE0. contradiction. }
           forward.
           crc_byte lo p n len contents data c0.
           Exists (i + 1). entailer!.
           close_eqs.
        -- assert (i = len).
           { apply repr_inj_unsigned64 in HRE0; [lia | rep_lia | rep_lia]. }
           subst i.
           assert (Hr: 0 <= crc_reg c0 data len < 2 ^ 32) by (apply crc_reg_range; auto).
           forward.
           entailer!.
           rewrite crc_post_int by auto. f_equal. f_equal.
           unfold ref_crc32. fold c0. rewrite <- crc_reg_full. reflexivity.
Qed.
