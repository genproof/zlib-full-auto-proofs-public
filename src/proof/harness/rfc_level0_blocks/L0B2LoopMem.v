(* Law rfc_level0_blocks, main: the memory of one deflate() call of the do-while (L0B2SegLoop.v; ported from
   rfc_level0_size's L0S2LoopMem.v).  The call's input
   object is the slice [pos, pos + len) of the data's object; its output space is the next aout bytes of the
   output object after the bytes O produced so far.  When the output space is not empty, deflate_spec needs
   no witness that next_out is weakly valid (WVnone); when it is (all of room written: |O| = room, which
   Level0Calls.lf_range allows after a gzip trailer that did not fit), the byte just before next_out, the last
   byte produced, is lent as the witness (WVbefore).  Each lemma opens the object into the call's piece and a rest, with the entailment
   that closes it again after the call. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.Level0Calls.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2Kit.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* an array of bytes cut at a and c *)
Lemma l0_cut3 sh n a c (l : list val) p :
  0 <= a <= c -> c <= n -> Zlength l = n ->
  data_at sh (tarray tuchar n) l p |--
  data_at sh (tarray tuchar a) (sublist 0 a l) p *
  data_at sh (tarray tuchar (c - a)) (sublist a c l) (offset_val a p) *
  data_at sh (tarray tuchar (n - c)) (sublist c n l) (offset_val c p).
Proof.
  intros Ha Hc Hl. assert_PROP (field_compatible (tarray tuchar n) [] p) as FC by entailer!.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a c l p) by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l. cancel.
Qed.

Lemma l0_glue3 sh n a c (l : list val) p :
  0 <= a <= c -> c <= n -> Zlength l = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar a) (sublist 0 a l) p *
  data_at sh (tarray tuchar (c - a)) (sublist a c l) (offset_val a p) *
  data_at sh (tarray tuchar (n - c)) (sublist c n l) (offset_val c p)
  |-- data_at sh (tarray tuchar n) l p.
Proof.
  intros Ha Hc Hl FC.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a c l p) by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l. cancel.
Qed.

(* the input object of the call: the slice [pos, pos + len) of the data *)
Lemma l0_in_open n (D : list Z) dp pos len :
  0 <= pos -> 0 <= len -> pos + len <= n -> Zlength D = n ->
  data_at Ews (tarray tuchar n) (map vi D) dp |--
  EX Rr : mpred,
  !! (Rr * data_at Ews (tarray tuchar len) (map vi (sublist pos (pos + len) D)) (offset_val pos dp)
        |-- data_at Ews (tarray tuchar n) (map vi D) dp) &&
  (data_at Ews (tarray tuchar len) (map vi (sublist pos (pos + len) D)) (offset_val pos dp) * Rr).
Proof.
  intros Hp Hl Hn HD. assert_PROP (field_compatible (tarray tuchar n) [] dp) as FC by entailer!.
  assert (HL : Zlength (map vi D) = n) by (rewrite Zlength_map; auto).
  sep_apply (l0_cut3 Ews n pos (pos + len) (map vi D) dp); try lia.
  replace (pos + len - pos) with len by lia.
  rewrite !sublist_map.
  Exists (data_at Ews (tarray tuchar pos) (map vi (sublist 0 pos D)) dp *
          data_at Ews (tarray tuchar (n - (pos + len))) (map vi (sublist (pos + len) n D)) (offset_val (pos + len) dp)).
  entailer!.
  eapply derives_trans; [ | apply (l0_glue3 Ews (Zlength D) pos (pos + len) (map vi D) dp); auto; try lia ].
  rewrite !sublist_map. replace (pos + len - pos) with len by lia. cancel.
Qed.

(* the output space of the call: aout bytes after O in the object of room bytes, 0 < aout <= room - |O| *)
Lemma l0_out_open room (O : list Z) cp aout :
  0 <= Zlength O -> 0 <= aout -> Zlength O + aout <= room ->
  l0_comp room O cp |--
  EX Rr : mpred,
  !! (forall zo : list Z, 0 <= Zlength zo <= aout ->
        Rr * data_at Ews (tarray tuchar aout)
               (map vi zo ++ sublist (Zlength zo) aout (Zrepeat Vundef aout)) (offset_val (Zlength O) cp)
        |-- l0_comp room (O ++ zo) cp) &&
  (data_at Ews (tarray tuchar aout) (Zrepeat Vundef aout) (offset_val (Zlength O) cp) * Rr).
Proof.
  intros HO Ha Hb. unfold l0_comp. Intros.
  assert_PROP (field_compatible (tarray tuchar room) [] cp) as FC by entailer!.
  set (L := map vi O ++ Zrepeat Vundef (room - Zlength O)).
  assert (HL : Zlength L = room) by (unfold L; list_solve).
  sep_apply (l0_cut3 Ews room (Zlength O) (Zlength O + aout) L cp); try lia.
  replace (Zlength O + aout - Zlength O) with aout by lia.
  assert (E1 : sublist 0 (Zlength O) L = map vi O) by (unfold L; list_solve).
  assert (E2 : sublist (Zlength O) (Zlength O + aout) L = Zrepeat Vundef aout) by (unfold L; list_solve).
  assert (E3 : sublist (Zlength O + aout) room L = Zrepeat Vundef (room - (Zlength O + aout)))
    by (unfold L; list_solve).
  rewrite E1, E2, E3.
  Exists (malloc_token Ews (tarray tuchar room) cp *
          data_at Ews (tarray tuchar (Zlength O)) (map vi O) cp *
          data_at Ews (tarray tuchar (room - (Zlength O + aout))) (Zrepeat Vundef (room - (Zlength O + aout)))
            (offset_val (Zlength O + aout) cp)).
  entailer!.
  intros zo Hz.
  set (L' := map vi (O ++ zo) ++ Zrepeat Vundef (room - Zlength (O ++ zo))).
  assert (HL' : Zlength L' = room) by (unfold L'; list_solve).
  cancel.
  eapply derives_trans; [ | apply (l0_glue3 Ews room (Zlength O) (Zlength O + aout) L' cp); auto; try lia ].
  replace (Zlength O + aout - Zlength O) with aout by lia.
  replace (sublist 0 (Zlength O) L') with (map vi O) by (unfold L'; list_solve).
  replace (sublist (Zlength O) (Zlength O + aout) L')
    with (map vi zo ++ sublist (Zlength zo) aout (Zrepeat Vundef aout)) by (unfold L'; list_solve).
  replace (sublist (Zlength O + aout) room L') with (Zrepeat Vundef (room - (Zlength O + aout)))
    by (unfold L'; list_solve).
  cancel.
Qed.

(* the output space of the call with deflate_spec's witness [W] that next_out is weakly valid: none when the
   space is not empty, the last byte produced when it is (then something was produced: |O| > 0) *)
Lemma l0_out_open_w room (O : list Z) cp aout :
  0 <= Zlength O -> 0 <= aout -> Zlength O + aout <= room -> (aout = 0 -> 0 < Zlength O) ->
  l0_comp room O cp |--
  EX W : wvw, EX Rr : mpred,
  !! ((aout = 0 -> wv_ok W) /\
      forall zo : list Z, 0 <= Zlength zo <= aout ->
        Rr * wv_at W (offset_val (Zlength O) cp) *
        data_at Ews (tarray tuchar aout)
          (map vi zo ++ sublist (Zlength zo) aout (Zrepeat Vundef aout)) (offset_val (Zlength O) cp)
        |-- l0_comp room (O ++ zo) cp) &&
  (data_at Ews (tarray tuchar aout) (Zrepeat Vundef aout) (offset_val (Zlength O) cp) *
   wv_at W (offset_val (Zlength O) cp) * Rr).
Proof.
  intros HO Ha Hb H0.
  destruct (Z.eq_dec aout 0) as [-> | Hne].
  - specialize (H0 eq_refl).
    unfold l0_comp. Intros.
    assert_PROP (field_compatible (tarray tuchar room) [] cp) as FC by entailer!.
    set (L := map vi O ++ Zrepeat Vundef (room - Zlength O)).
    assert (HL : Zlength L = room) by (unfold L; list_solve).
    sep_apply (l0_cut3 Ews room (Zlength O - 1) (Zlength O) L cp); try lia.
    replace (Zlength O - (Zlength O - 1)) with 1 by lia.
    assert (E2 : sublist (Zlength O - 1) (Zlength O) L = [vi (Znth (Zlength O - 1) O)]).
    { unfold L. list_solve. }
    rewrite E2.
    rewrite (data_at_singleton_array_eq Ews tuchar (vi (Znth (Zlength O - 1) O))) by reflexivity.
    assert (Pc : isptr cp) by (destruct FC; auto).
    Exists (WVbefore Ews (vi (Znth (Zlength O - 1) O))).
    Exists (malloc_token Ews (tarray tuchar room) cp *
            data_at Ews (tarray tuchar (Zlength O - 1)) (sublist 0 (Zlength O - 1) L) cp *
            data_at Ews (tarray tuchar (room - Zlength O)) (sublist (Zlength O) room L) (offset_val (Zlength O) cp)).
    unfold wv_at. rewrite offset_offset_val. replace (Zlength O + -1) with (Zlength O - 1) by lia.
    change (Zrepeat Vundef 0) with (@nil val).
    rewrite (data_at_tuchar_zero_array_eq Ews (offset_val (Zlength O) cp)) by (destruct cp; try contradiction; exact I).
    entailer!.
    split; [intros _; cbn; apply writable_readable; apply writable_Ews|].
    intros zo Hz.
    assert (Ez : zo = []) by (destruct zo; [reflexivity | rewrite Zlength_cons in Hz; pose proof (Zlength_nonneg zo); lia]).
    subst zo. replace (O ++ []) with O by (symmetry; apply app_nil_r). cbn [map app].
    change (sublist 0 0 (@nil val)) with (@nil val).
    rewrite (data_at_tuchar_zero_array_eq Ews (offset_val (Zlength O) cp)) by (destruct cp; try contradiction; exact I).
    fold L. rewrite sepcon_emp.
    rewrite <- (data_at_singleton_array_eq Ews tuchar (vi (Znth (Zlength O - 1) O)) [vi (Znth (Zlength O - 1) O)])
      by reflexivity.
    rewrite <- E2. cancel.
    eapply derives_trans; [ | apply (l0_glue3 Ews room (Zlength O - 1) (Zlength O) L cp); auto; lia ].
    replace (Zlength O - (Zlength O - 1)) with 1 by lia.
    cancel.
  - sep_apply (l0_out_open room O cp aout HO Ha Hb). Intros Rr.
    Exists WVnone Rr. unfold wv_at.
    apply andp_right; [apply prop_right; split; [intros; lia | intros zo Hz; rewrite sepcon_emp; auto] | cancel].
Qed.
