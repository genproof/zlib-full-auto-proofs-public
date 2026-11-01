(* The body of bytes_eq against BytesEqNull.bytes_eq_spec_n: the loop compares a[i] and b[i] for i < len and
   returns 0 at the first difference, 1 otherwise; with a or b Z_NULL (len = 0) it never enters the loop. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.adler32.Ptr.
Require Import Zlib.proof.harness.laws_common.Spec Zlib.proof.harness.laws_common.BytesEqNull.
Require Zlib.units.Adler32.
#[local] Existing Instance Zlib.units.Adler32.CS.

Lemma bytes_eq_n_body : bytes_eq_n_stmt.
Proof.
  intros _. start_function.
  (* a Z_NULL argument: len = 0, the loop is not entered *)
  assert (Hnull: isa = true \/ isb = true -> len = 0 /\ da = [] /\ db = []).
  { intros Hab.
    assert (len = 0) by (destruct isa, isb; try tauto; destruct Hab; try discriminate; tauto).
    subst len. split; [reflexivity | ]. split.
    - destruct isa; [tauto | ]. destruct H0 as (_ & _ & _ & _ & Hl & _). apply Zlength_nil_inv; auto.
    - destruct isb; [tauto | ]. destruct H1 as (_ & _ & _ & _ & Hl & _). apply Zlength_nil_inv; auto. }
  destruct (orb isa isb) eqn:Eab.
  - destruct (Hnull ltac:(destruct isa, isb; simpl in Eab; auto; discriminate)) as (-> & -> & ->).
    forward_for_simple_bound 0 (EX i: Z,
       PROP () LOCAL (temp HL._a a; temp HL._b b; temp HL._n (Vlong (Int64.repr 0)))
       SEP (if isa then emp else data_at sha (tarray tuchar na) ca pa;
            if isb then emp else data_at shb (tarray tuchar nb) cb pb)).
    + entailer!.
    + lia.
    + forward.
  - destruct isa; [discriminate | ]. destruct isb; [discriminate | ]. clear Eab Hnull.
    destruct H0 as (-> & Hsha & Hloa & Hna & Hlena & Hbya & Hsuba).
    destruct H1 as (-> & Hshb & Hlob & Hnb & Hlenb & Hbyb & Hsubb).
    assert_PROP (field_compatible (tarray tuchar na) [] pa /\ Zlength ca = na) as HPa
      by (entailer!; rewrite Zlength_correct in *; auto).
    destruct HPa as [FCa Hca].
    assert_PROP (field_compatible (tarray tuchar nb) [] pb /\ Zlength cb = nb) as HPb
      by (entailer!; rewrite Zlength_correct in *; auto).
    destruct HPb as [FCb Hcb].
    forward_for_simple_bound len (EX i: Z,
       PROP (sublist 0 i da = sublist 0 i db)
       LOCAL (temp HL._a (offset_val loa pa); temp HL._b (offset_val lob pb); temp HL._n (Vlong (Int64.repr len)))
       SEP (data_at sha (tarray tuchar na) ca pa; data_at shb (tarray tuchar nb) cb pb)).
    + entailer!.
    + cbv beta. Intros.
      assert (Ea: force_val (sem_add_ptr_long tuchar (offset_val loa pa) (Vlong (Int64.repr i))) =
                  field_address (tarray tuchar na) [ArraySubsc (loa + i)] pa) by (apply add_ptr_long; auto; lia).
      assert (Eb: force_val (sem_add_ptr_long tuchar (offset_val lob pb) (Vlong (Int64.repr i))) =
                  field_address (tarray tuchar nb) [ArraySubsc (lob + i)] pb) by (apply add_ptr_long; auto; lia).
      assert (Ba: @Znth val Vundef (loa + i) ca = Vint (Int.repr (Znth i da))) by (apply (Znth_cbuf loa len); auto; lia).
      assert (Bb: @Znth val Vundef (lob + i) cb = Vint (Int.repr (Znth i db))) by (apply (Znth_cbuf lob len); auto; lia).
      assert (Ra: 0 <= Znth i da <= Byte.max_unsigned) by (apply is_bytes_Znth; auto; lia).
      assert (Rb: 0 <= Znth i db <= Byte.max_unsigned) by (apply is_bytes_Znth; auto; lia).
      forward.
      { entailer!. rewrite Ba. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      forward.
      { entailer!. rewrite Bb. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite Ba, Bb.
      forward_if.
      * forward.
        destruct (list_eq_dec Z.eq_dec da db) as [E | E]; [subst db; contradiction | entailer!].
      * forward. entailer!.
        rewrite !(sublist_split 0 i (i + 1)) by lia. rewrite H1, !sublist_len_1 by lia. rewrite H2. auto.
    + forward. entailer!.
      assert (E: da = db).
      { rewrite <- (sublist_same 0 (Zlength da) da), <- (sublist_same 0 (Zlength da) db) by lia. auto. }
      destruct (list_eq_dec Z.eq_dec da db); [auto | contradiction].
Qed.
