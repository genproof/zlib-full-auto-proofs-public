(* Law rj_truncated, main: the memory of one deflate() call of the do-while (RTSegLoop.v).  The call's input
   object is the slice [pos, pos + len) of the data's object; its output space is the next aout bytes of the
   compressed object after the bytes O produced so far, with deflate_spec's witness that next_out is weakly valid
   when aout = 0 (the 0-byte object's malloc token, or the byte before next_out).  Each lemma opens the object
   into the call's pieces and a rest, with the entailment that closes it again after the call. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.RTKit.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

(* an array of bytes cut at a and c *)
Lemma rt_cut3 {cs : compspecs} sh n a c (l : list val) p :
  0 <= a <= c -> c <= n -> Zlength l = n ->
  @data_at cs sh (tarray tuchar n) l p |--
  @data_at cs sh (tarray tuchar a) (sublist 0 a l) p *
  @data_at cs sh (tarray tuchar (c - a)) (sublist a c l) (offset_val a p) *
  @data_at cs sh (tarray tuchar (n - c)) (sublist c n l) (offset_val c p).
Proof.
  intros Ha Hc Hl. assert_PROP (field_compatible (tarray tuchar n) [] p) as FC by entailer!.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a c l p) by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l. cancel.
Qed.

Lemma rt_glue3 {cs : compspecs} sh n a c (l : list val) p :
  0 <= a <= c -> c <= n -> Zlength l = n -> field_compatible (tarray tuchar n) [] p ->
  @data_at cs sh (tarray tuchar a) (sublist 0 a l) p *
  @data_at cs sh (tarray tuchar (c - a)) (sublist a c l) (offset_val a p) *
  @data_at cs sh (tarray tuchar (n - c)) (sublist c n l) (offset_val c p)
  |-- @data_at cs sh (tarray tuchar n) l p.
Proof.
  intros Ha Hc Hl FC.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a c l p) by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l. cancel.
Qed.

Lemma rt_map_vi (l : list Z) : bytes_rep l = map vi l.
Proof. reflexivity. Qed.

(* the input object of the call: the slice [pos, pos + len) of the data *)
Lemma rt_in_open n (D : list Z) dp pos len :
  0 <= pos -> 0 <= len -> pos + len <= n -> Zlength D = n ->
  data_at Ews (tarray tuchar n) (bytes_rep D) dp |--
  EX Rr : mpred,
  !! (Rr * @data_at Zlib.proof.deflate.DCS.CS Ews (tarray tuchar len) (map vi (sublist pos (pos + len) D))
            (offset_val pos dp) |-- data_at Ews (tarray tuchar n) (bytes_rep D) dp) &&
  (@data_at Zlib.proof.deflate.DCS.CS Ews (tarray tuchar len) (map vi (sublist pos (pos + len) D))
     (offset_val pos dp) * Rr).
Proof.
  intros Hp Hl Hn HD. assert_PROP (field_compatible (tarray tuchar n) [] dp) as FC by entailer!.
  assert (HL : Zlength (bytes_rep D) = n) by (unfold bytes_rep; rewrite Zlength_map; auto).
  sep_apply (rt_cut3 Ews n pos (pos + len) (bytes_rep D) dp); try lia.
  replace (pos + len - pos) with len by lia.
  rewrite rt_map_vi, !sublist_map.
  Exists (data_at Ews (tarray tuchar pos) (map vi (sublist 0 pos D)) dp *
          data_at Ews (tarray tuchar (n - (pos + len))) (map vi (sublist (pos + len) n D)) (offset_val (pos + len) dp)).
  rewrite rt_bytes_dcs.
  entailer!.
  try rewrite rt_bytes_dcs.
  eapply derives_trans; [ | apply (rt_glue3 Ews (Zlength D) pos (pos + len) (map vi D) dp); auto; try lia ].
  rewrite !sublist_map. replace (pos + len - pos) with len by lia. cancel.
Qed.

Lemma rt_tuchar_dcs sh (v : val) q :
  @data_at Zlib.proof.deflate.DCS.CS sh tuchar v q = @data_at CS.CS sh tuchar v q.
Proof. apply equal_f. apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

(* the output space of the call: aout = clip(b - |O|) bytes after O in the object of b bytes; W the witness that
   next_out is weakly valid when aout = 0 *)
Definition rt_aout (b : Z) (O : list Z) : Z := Z.min (b - Zlength O) Int.max_unsigned.

Lemma rt_out_open b (O : list Z) cp :
  0 <= Zlength O <= b -> b <= Ptrofs.max_unsigned ->
  rt_comp b O cp |--
  EX W : wvw, EX Rr : mpred,
  !! ((rt_aout b O = 0 -> wv_ok W) /\
      forall zo : list Z, 0 <= Zlength zo <= rt_aout b O ->
        Rr * wv_at W (offset_val (Zlength O) cp) *
        @data_at Zlib.proof.deflate.DCS.CS Ews (tarray tuchar (rt_aout b O))
          (map vi zo ++ sublist (Zlength zo) (rt_aout b O) (Zrepeat Vundef (rt_aout b O))) (offset_val (Zlength O) cp)
        |-- rt_comp b (O ++ zo) cp) &&
  (@data_at Zlib.proof.deflate.DCS.CS Ews (tarray tuchar (rt_aout b O)) (Zrepeat Vundef (rt_aout b O))
     (offset_val (Zlength O) cp) * wv_at W (offset_val (Zlength O) cp) * Rr).
Proof.
  intros HO Hb. unfold rt_comp. Intros.
  assert_PROP (field_compatible (tarray tuchar b) [] cp) as FC by entailer!.
  set (aout := rt_aout b O).
  assert (Ha : 0 <= aout <= b - Zlength O) by (unfold aout, rt_aout; rep_lia).
  set (L := bytes_rep O ++ Zrepeat Vundef (b - Zlength O)).
  assert (HL : Zlength L = b) by (unfold L, bytes_rep; list_solve).
  sep_apply (rt_cut3 Ews b (Zlength O) (Zlength O + aout) L cp); try lia.
  replace (Zlength O + aout - Zlength O) with aout by lia.
  assert (E1 : sublist 0 (Zlength O) L = bytes_rep O) by (unfold L, bytes_rep; list_solve).
  assert (E2 : sublist (Zlength O) (Zlength O + aout) L = Zrepeat Vundef aout) by (unfold L, bytes_rep; list_solve).
  assert (E3 : sublist (Zlength O + aout) b L = Zrepeat Vundef (b - (Zlength O + aout)))
    by (unfold L, bytes_rep; list_solve).
  rewrite E1, E2, E3.
  (* closing: the three parts with zo written in the middle one *)
  assert (CL : forall zo : list Z, 0 <= Zlength zo <= aout ->
      data_at Ews (tarray tuchar (Zlength O)) (bytes_rep O) cp *
      data_at Ews (tarray tuchar aout) (map vi zo ++ sublist (Zlength zo) aout (Zrepeat Vundef aout))
        (offset_val (Zlength O) cp) *
      data_at Ews (tarray tuchar (b - (Zlength O + aout))) (Zrepeat Vundef (b - (Zlength O + aout)))
        (offset_val (Zlength O + aout) cp)
      |-- data_at Ews (tarray tuchar b) (bytes_rep (O ++ zo) ++ Zrepeat Vundef (b - Zlength (O ++ zo))) cp).
  { intros zo Hz.
    set (L' := bytes_rep (O ++ zo) ++ Zrepeat Vundef (b - Zlength (O ++ zo))).
    assert (HL' : Zlength L' = b) by (unfold L', bytes_rep; list_solve).
    eapply derives_trans; [ | apply (rt_glue3 Ews b (Zlength O) (Zlength O + aout) L' cp); auto; try lia ].
    replace (Zlength O + aout - Zlength O) with aout by lia.
    replace (sublist 0 (Zlength O) L') with (bytes_rep O) by (unfold L', bytes_rep; list_solve).
    replace (sublist (Zlength O) (Zlength O + aout) L')
      with (map vi zo ++ sublist (Zlength zo) aout (Zrepeat Vundef aout)) by (unfold L', bytes_rep, vi; list_solve).
    replace (sublist (Zlength O + aout) b L') with (Zrepeat Vundef (b - (Zlength O + aout)))
      by (unfold L', bytes_rep; list_solve).
    cancel. }
  destruct (Z.eq_dec aout 0) as [A0 | A0].
  2:{ (* space: no witness needed *)
    Exists WVnone (malloc_token Ews (tarray tuchar b) cp *
                   data_at Ews (tarray tuchar (Zlength O)) (bytes_rep O) cp *
                   data_at Ews (tarray tuchar (b - (Zlength O + aout))) (Zrepeat Vundef (b - (Zlength O + aout)))
                     (offset_val (Zlength O + aout) cp)).
    unfold wv_at. rewrite rt_bytes_dcs. entailer!.
    try (split; [intros; first [contradiction | simpl; lia | simpl; auto] | ]).
    intros zo Hz. rewrite rt_bytes_dcs. sep_apply (CL zo Hz). cancel. }
  destruct (Z.eq_dec (Zlength O) 0) as [O0 | O0].
  - (* no byte before next_out: the 0-byte object's token *)
    assert (Hb0 : b = 0) by (unfold aout, rt_aout in A0; rep_lia).
    replace (malloc_token Ews (tarray tuchar b) cp) with (malloc_token Ews (tarray tuchar 0) cp)
      by (rewrite Hb0; reflexivity).
    Exists (WVtok (tarray tuchar 0))
           (data_at Ews (tarray tuchar (Zlength O)) (bytes_rep O) cp *
            data_at Ews (tarray tuchar (b - (Zlength O + aout))) (Zrepeat Vundef (b - (Zlength O + aout)))
              (offset_val (Zlength O + aout) cp)).
    unfold wv_at. rewrite rt_bytes_dcs, rt_tok_dcs, O0, isptr_offset_val_zero by auto. entailer!.
    try (split; [intros; first [contradiction | simpl; lia | simpl; auto] | ]).
    intros zo Hz. pose proof (CL zo Hz) as C.
    rewrite O0, Z.add_0_l, isptr_offset_val_zero in C by auto. sep_apply C. cancel.
  - (* the byte before next_out: the last byte of O *)
    assert (Hb' : Zlength O = b) by (unfold aout, rt_aout in A0; rep_lia).
    assert (HOb : Zlength (bytes_rep O) = Zlength O) by (unfold bytes_rep; list_solve).
    sep_apply (rt_cut3 Ews (Zlength O) (Zlength O - 1) (Zlength O) (bytes_rep O) cp); try lia.
    replace (Zlength O - (Zlength O - 1)) with 1 by lia. rewrite Z.sub_diag.
    set (v := Znth (Zlength O - 1) (bytes_rep O)).
    replace (sublist (Zlength O - 1) (Zlength O) (bytes_rep O)) with [v]
      by (unfold v; list_solve).
    rewrite (data_at_singleton_array_eq Ews tuchar v [v]) by reflexivity.
    Exists (WVbefore Ews v)
           (malloc_token Ews (tarray tuchar b) cp *
            data_at Ews (tarray tuchar (Zlength O - 1)) (sublist 0 (Zlength O - 1) (bytes_rep O)) cp *
            data_at Ews (tarray tuchar 0) (sublist (Zlength O) (Zlength O) (bytes_rep O)) (offset_val (Zlength O) cp) *
            data_at Ews (tarray tuchar (b - (Zlength O + aout))) (Zrepeat Vundef (b - (Zlength O + aout)))
              (offset_val (Zlength O + aout) cp)).
    unfold wv_at. rewrite rt_bytes_dcs, rt_tuchar_dcs.
    replace (offset_val (-1) (offset_val (Zlength O) cp)) with (offset_val (Zlength O - 1) cp)
      by (rewrite offset_offset_val; f_equal; lia).
    entailer!.
    try (split; [intros; first [contradiction | simpl; lia | simpl; auto] | ]).
    intros zo Hz.
    assert (G : data_at Ews (tarray tuchar (Zlength O - 1)) (sublist 0 (Zlength O - 1) (bytes_rep O)) cp *
                data_at Ews tuchar v (offset_val (Zlength O - 1) cp) *
                data_at Ews (tarray tuchar 0) (sublist (Zlength O) (Zlength O) (bytes_rep O)) (offset_val (Zlength O) cp)
                |-- data_at Ews (tarray tuchar (Zlength O)) (bytes_rep O) cp).
    { eapply derives_trans; [ | apply (rt_glue3 Ews (Zlength O) (Zlength O - 1) (Zlength O) (bytes_rep O) cp);
                                auto; try lia; rewrite Hb'; auto ].
      replace (Zlength O - (Zlength O - 1)) with 1 by lia. rewrite Z.sub_diag.
      replace (sublist (Zlength O - 1) (Zlength O) (bytes_rep O)) with [v] by (unfold v; list_solve).
      rewrite (data_at_singleton_array_eq Ews tuchar v [v]) by reflexivity.
      cancel. }
    sep_apply G. sep_apply (CL zo Hz). cancel.
Qed.
