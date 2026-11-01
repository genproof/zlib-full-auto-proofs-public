(* The body of copy_of against CopyOfNull.copy_of_spec_n: with a Z_NULL source (len = 0) it allocates an object of
   0 bytes and never enters the copy loop; otherwise it is the proof of Spec.copy_of_spec's body
   (laws_common/Bodies.v, body_copy_of), repeated here because the specification has the extra flag. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.laws_common.CopyOfNull.
Require Import Zlib.proof.adler32.Ptr.
Require Zlib.proof.adler32.HarnessBytes.
Require Zlib.units.Adler32.
#[local] Existing Instance Zlib.units.Adler32.CS.

Lemma copy_of_n_body : copy_of_n_stmt.
Proof.
  intros _. start_function.
  destruct isnull.
  - destruct H0 as (-> & -> & ->).
    forward_call (tarray tuchar 0, gv).
    Intros q.
    destruct (eq_dec q nullval) as [Eq | Nq].
    + subst q.
      forward.
      forward_loop (PROP () LOCAL (temp HL._copy nullval; temp HL._i (Vlong (Int64.repr 0))) SEP (mem_mgr gv))
        break: (PROP () LOCAL (temp HL._copy nullval) SEP (mem_mgr gv)).
      * entailer!.
      * forward_if (PROP () LOCAL (temp HL._t'2 (Vint (Int.repr 0)); temp HL._copy nullval) SEP (mem_mgr gv)).
        -- exfalso. discriminate.
        -- forward. entailer!.
        -- forward_if. { exfalso. lia. } forward. entailer!.
      * forward. Exists nullval. entailer!.
    + Intros.
      forward.
      forward_loop (PROP () LOCAL (temp HL._copy q; temp HL._i (Vlong (Int64.repr 0));
                                   temp HL._n (Vlong (Int64.repr 0)))
                    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar 0) q; data_at_ Ews (tarray tuchar 0) q))
        break: (PROP () LOCAL (temp HL._copy q)
                SEP (mem_mgr gv; malloc_token Ews (tarray tuchar 0) q; data_at_ Ews (tarray tuchar 0) q)).
      * entailer!.
      * forward_if (PROP () LOCAL (temp HL._t'2 (Vint Int.zero); temp HL._copy q;
                                   temp HL._i (Vlong (Int64.repr 0)); temp HL._n (Vlong (Int64.repr 0)))
                    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar 0) q; data_at_ Ews (tarray tuchar 0) q)).
        -- forward. entailer!.
        -- exfalso. contradiction.
        -- forward_if. { exfalso. lia. } forward. entailer!.
      * forward. Exists q. rewrite if_false by auto. entailer!.
  - cbv beta iota in H0. {
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
      + forward. Exists q. entailer!. rewrite if_false by auto. cancel. }
Qed.
