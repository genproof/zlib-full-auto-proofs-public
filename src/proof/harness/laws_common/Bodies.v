(* The bodies of the helpers of harness/laws_common.h against their specifications (Spec.v), one lemma per
   helper.  The byte loops follow src/proof/adler32/HarnessBytes.v (bytes_copy, bytes_same): copy_of fills its
   new object with the invariant [bytes_rep (sublist 0 i data) ++ Zrepeat Vundef (len - i)] (copy_step), and
   bytes_eq keeps [sublist 0 i da = sublist 0 i db] until the first difference. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.adler32.Ptr.
Require Zlib.proof.adler32.HarnessBytes.

Section ByteBodies.
#[local] Existing Instance Zlib.units.Adler32.CS.

Lemma body_upto : semax_body Vprog_lc Gprog_upto HL.f_upto upto_spec.
Proof.
  start_function.
  forward_call tt.
  Intros v.
  forward_if (PROP () LOCAL (temp HL._t'2 (Vlong (Int64.repr (Z.min v max)))) SEP ()).
  - forward. entailer!. rewrite Z.min_l by lia. auto.
  - forward. entailer!. rewrite Z.min_r by lia. auto.
  - forward. Exists (Z.min v max). entailer!.
Qed.

Lemma body_clip : semax_body Vprog_lc Gprog_clip HL.f_clip clip_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL (temp HL._t'1 (Vint (Int.repr (Z.min n Int.max_unsigned)))) SEP ()).
  - forward. entailer!. rewrite Z.min_l by rep_lia. auto.
  - forward. entailer!. rewrite Int.unsigned_repr in * by rep_lia. rewrite Z.min_r by rep_lia. auto.
  - forward.
Qed.

Lemma body_any_bytes : semax_body Vprog_lc Gprog_any_bytes HL.f_alloc_any_bytes any_bytes_spec.
Proof.
  start_function.
  forward_call (tarray tuchar n, gv).
  { simpl. rep_lia. }
  Intros q.
  destruct (eq_dec q nullval) as [Eq | Nq].
  - subst q.
    forward_if (PROP () LOCAL (temp HL._bytes nullval) SEP (mem_mgr gv)).
    + exfalso. discriminate.
    + forward. entailer!.
    + forward. Exists nullval (Zrepeat 0 n).
      assert (B0: is_bytes (Zrepeat 0 n)) by (apply Forall_forall; intros x Hx; unfold Zrepeat in Hx; apply repeat_spec in Hx; subst x; rep_lia).
      entailer!. rewrite Zlength_Zrepeat by lia. auto.
  - Intros.
    forward_if (EX bs : list Z,
      PROP (Zlength bs = n; is_bytes bs) LOCAL (temp HL._bytes q)
      SEP (mem_mgr gv; malloc_token Ews (tarray tuchar n) q; data_at Ews (tarray tuchar n) (bytes_rep bs) q)).
    + forward_call (q, n, Ews).
      { rewrite if_false by auto. cancel. }
      Intros bs. rewrite if_false by auto.
      Exists bs. entailer!.
    + exfalso. auto.
    + Intros bs. forward. Exists q bs. entailer!. rewrite if_false by auto. cancel.
Qed.

Lemma body_copy_of : semax_body Vprog_lc Gprog_copy_of HL.f_copy_of copy_of_spec.
Proof.
  start_function.
  match goal with H: cbuf_ok false _ _ _ _ _ _ _ _ |- _ => destruct H as (Hbuf & Hsh & Hlo & Hn & Hlen & Hby & Hsub) end.
  subst buf.
  assert_PROP (field_compatible (tarray tuchar n) [] p) as FC by entailer!.
  assert_PROP (Zlength contents = n) by (entailer!; rewrite Zlength_correct in *; auto).
  forward_call (tarray tuchar len, gv).
  { simpl. rep_lia. }
  Intros q.
  destruct (eq_dec q nullval) as [Eq | Nq].
  - subst q.
    forward.
    forward_loop (PROP () LOCAL (temp HL._copy nullval; temp HL._i (Vlong (Int64.repr 0)))
                  SEP (mem_mgr gv; data_at sh (tarray tuchar n) contents p))
      break: (PROP () LOCAL (temp HL._copy nullval) SEP (mem_mgr gv; data_at sh (tarray tuchar n) contents p)).
    + entailer!.
    + forward_if (PROP () LOCAL (temp HL._t'2 (Vint (Int.repr 0)); temp HL._copy nullval)
                  SEP (mem_mgr gv; data_at sh (tarray tuchar n) contents p)).
      * exfalso. discriminate.
      * forward. entailer!.
      * forward_if. { exfalso. lia. } forward. entailer!.
    + forward. Exists nullval. entailer!.
  - Intros.
    forward.
    forward_loop (EX i : Z,
        PROP (0 <= i <= len)
        LOCAL (temp HL._copy q; temp HL._i (Vlong (Int64.repr i)); temp HL._source (offset_val lo p);
               temp HL._n (Vlong (Int64.repr len)))
        SEP (mem_mgr gv; data_at sh (tarray tuchar n) contents p; malloc_token Ews (tarray tuchar len) q;
             data_at Ews (tarray tuchar len) (bytes_rep (sublist 0 i data) ++ Zrepeat Vundef (len - i)) q))
      break: (PROP () LOCAL (temp HL._copy q)
        SEP (mem_mgr gv; data_at sh (tarray tuchar n) contents p; malloc_token Ews (tarray tuchar len) q;
             data_at Ews (tarray tuchar len) (bytes_rep data) q)).
    + Exists 0. entailer!. rewrite sublist_nil. unfold bytes_rep. simpl map. rewrite app_nil_l.
      apply derives_refl.
    + Intros i.
      forward_if (PROP () LOCAL (temp HL._t'2 (Vint (if zlt i len then Int.one else Int.zero));
                                 temp HL._copy q; temp HL._i (Vlong (Int64.repr i));
                                 temp HL._source (offset_val lo p); temp HL._n (Vlong (Int64.repr len)))
        SEP (mem_mgr gv; data_at sh (tarray tuchar n) contents p; malloc_token Ews (tarray tuchar len) q;
             data_at Ews (tarray tuchar len) (bytes_rep (sublist 0 i data) ++ Zrepeat Vundef (len - i)) q)).
      * forward. entailer!. destruct (zlt _ _); reflexivity.
      * exfalso. contradiction.
      * forward_if.
        -- destruct (zlt i len) as [Lt | Ge]; [ | exfalso; auto ].
           assert (E: force_val (sem_add_ptr_long tuchar (offset_val lo p) (Vlong (Int64.repr i))) =
                      field_address (tarray tuchar n) [ArraySubsc (lo + i)] p) by (apply add_ptr_long; auto; rep_lia).
           assert (Hb: @Znth val Vundef (lo + i) contents = Vint (Int.repr (Znth i data))) by (apply (Znth_cbuf lo len); auto; lia).
           assert (Hb2: 0 <= Znth i data <= Byte.max_unsigned) by (apply is_bytes_Znth; auto; lia).
           forward.
           { entailer!. rewrite Hb. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
           rewrite Hb.
           forward.
           forward.
           Exists (i + 1).
           rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
           rewrite HarnessBytes.copy_step by lia.
           entailer!.
        -- destruct (zlt i len) as [Lt | Ge]; [exfalso; apply Int.one_not_zero; auto | ].
           forward. entailer!.
           assert (i = Zlength data) by lia. subst i.
           rewrite sublist_same by lia. rewrite Z.sub_diag. simpl. rewrite app_nil_r. auto.
    + forward. Exists q. entailer!. rewrite if_false by auto. cancel.
Qed.

Lemma body_bytes_eq : semax_body Vprog_lc Gprog_bytes_eq HL.f_bytes_eq bytes_eq_spec.
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
     LOCAL (temp HL._a (offset_val loa pa); temp HL._b (offset_val lob pb); temp HL._n (Vlong (Int64.repr len)))
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

End ByteBodies.

Section StreamBodies.
#[local] Existing Instance Zlib.units.Compress.CS.

Lemma body_offer : semax_body Vprog_lc Gprog_offer HL.f_set_buffer offer_spec.
Proof.
  start_function.
  unfold zs_val.
  forward. forward. forward. forward.
  (* the casts (uInt) in_len, (uInt) out_len read the size_t values back: in_len, out_len < 2^64; normalizing
     them first keeps entailer! from unfolding the whole struct *)
  rewrite !Int64.Z_mod_modulus_eq, !Z.mod_small by rep_lia.
  entailer!.
Qed.

Lemma body_new_stream : semax_body Vprog_lc Gprog_new_stream HL.f_new_stream new_stream_spec.
Proof.
  start_function.
  unfold zs_val.
  forward. forward. forward.
  forward_call (sp, sh, nullval, 0, nullval, 0, ni, ai, ti, no, ao, to, msg, st, nullval, nullval, nullval, dt, ad, rs).
  entailer!.
Qed.

End StreamBodies.

Lemma laws_common_bodies : laws_common_ok.
Proof.
  split; [exact body_upto | ].
  split; [exact body_clip | ].
  split; [exact body_any_bytes | ].
  split; [exact body_copy_of | ].
  split; [exact body_bytes_eq | ].
  split; [exact body_offer | exact body_new_stream].
Qed.
