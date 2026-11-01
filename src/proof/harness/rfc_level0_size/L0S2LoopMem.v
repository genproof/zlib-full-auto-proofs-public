(* Law rfc_level0_size, main: the memory of one deflate() call of the do-while (L0S2LoopCall.v, L0S2SegLoop.v).  The call's input
   object is the slice [pos, pos + len) of the data's object; its output space is the next aout bytes of the
   output object after the bytes O produced so far.  The output object always has room left (|O| < room, from
   Level0CallsFit.ff_range), so the output space is never empty and deflate_spec needs no witness that next_out is
   weakly valid (WVnone).  Each lemma opens the object into the call's piece and a rest, with the entailment
   that closes it again after the call. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2Kit.
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
