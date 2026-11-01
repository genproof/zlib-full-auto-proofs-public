(* Law inflate_dict, theory part: the first inflate() call after the right dictionary (zlib: DICT
   with havedict 1) is the call from the TYPE version of the state (check 1, adler 1), or it leaves at once
   (flush Z_BLOCK / Z_TREES, or no input) with nothing consumed or produced. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_dict.ITTheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Helpers                                                                                        *)

Lemma itd1_pull_sm: forall m v, pull (set_mode m v) = set_mode (pull m) v.
Proof. reflexivity. Qed.

Lemma itd1_needbits_sm: forall k n m v, needbits_f k n (set_mode m v) = set_mode (needbits_f k n m) v.
Proof.
  induction k as [|k IH]; intros n m v; [reflexivity|].
  cbn [needbits_f].
  change (m_bits (set_mode m v)) with (m_bits m).
  change (m_have (set_mode m v)) with (m_have m).
  destruct (m_bits m <? n); [|reflexivity].
  destruct (m_have m =? 0); [reflexivity|].
  rewrite itd1_pull_sm. apply IH.
Qed.

Lemma itd1_typedo_sm: forall flush m v,
  i_last (m_s m) <> 0 \/ m_leave (needbits 3 m) <> 1 ->
  c_TYPEDO flush (set_mode m v) = c_TYPEDO flush m.
Proof.
  intros flush m v H. unfold c_TYPEDO.
  change (i_last (m_s (set_mode m v))) with (i_last (m_s m)).
  destruct (i_last (m_s m) =? 0) eqn:E; [|reflexivity].
  apply Z.eqb_eq in E.
  cbv zeta. unfold needbits. rewrite itd1_needbits_sm.
  set (X := needbits_f 4 3 m) in *.
  change (m_leave (set_mode X v)) with (m_leave X).
  destruct (m_leave X =? 1) eqn:E2.
  - apply Z.eqb_eq in E2. destruct H as [H|H]; contradiction.
  - reflexivity.
Qed.

(* needbits 3 leaves only when nothing is there: the machine is the same, with leave = 1 *)
Lemma itd1_needbits_leave: forall m,
  m_leave m = 0 -> 0 <= m_bits m <= 39 -> m_leave (needbits 3 m) = 1 -> needbits 3 m = set_leave m.
Proof.
  intros m L B H. unfold needbits in *. cbn [needbits_f] in *.
  destruct (m_bits m <? 3) eqn:E1.
  - destruct (m_have m =? 0) eqn:E2; [reflexivity|].
    cbn [needbits_f] in H.
    replace (m_bits (pull m) <? 3) with false in H.
    + exfalso. cbv iota in H. change (m_leave (pull m)) with (m_leave m) in H. lia.
    + symmetry. apply Z.ltb_ge. change (m_bits (pull m)) with (u32 (m_bits m + 8)).
      unfold u32. rewrite Z.mod_small; [lia|]. split; [lia|]. cbn. lia.
  - exfalso. lia.
Qed.

Lemma itd1_loop2_same: forall flush fx dx m m' o,
  stepf2 flush fx dx m = stepf2 flush fx dx m' -> loop2 flush fx dx m o -> loop2 flush fx dx m' o.
Proof.
  intros flush fx dx m m' o E H. inversion H; subst.
  - apply loop2_ret. rewrite <- E. assumption.
  - apply loop2_leave; [rewrite <- E; assumption | assumption].
  - eapply loop2_next; [rewrite <- E; eassumption | assumption | assumption].
Qed.

Lemma itd1_step2_DICT: forall flush fx dx f m, m_mode m = DICT -> step2 flush fx dx f m = c_DICT flush m.
Proof. intros flush fx dx f m H. unfold step2. rewrite H. reflexivity. Qed.

Lemma itd1_step2_TYPEDO: forall flush fx dx f m, m_mode m = TYPEDO -> step2 flush fx dx f m = c_TYPEDO flush m.
Proof. intros flush fx dx f m H. unfold step2. rewrite H. reflexivity. Qed.

(* updatewindow with no data keeps a well-formed allocated window *)
Lemma itd1_updatewindow_nil: forall s, i_wsize s <> 0 -> wstruct s -> updatewindow s [] = s.
Proof.
  intros s W [H1 [H2 [H3 H4]]]. unfold updatewindow.
  rewrite Zlength_nil.
  destruct (i_wsize s =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
  destruct (i_wsize s <=? 0) eqn:E1; [apply Z.leb_le in E1; lia|].
  replace (Z.min (i_wsize s - i_wnext s) 0) with 0 by lia.
  rewrite sublist_of_nil. cbn [app]. replace (0 - 0) with 0 by lia. cbn [Z.eqb negb].
  rewrite Z.add_0_r.
  replace (i_wnext s =? i_wsize s) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite sublist_rejoin by lia. rewrite sublist_same by lia.
  replace (if i_whave s <? i_wsize s then i_whave s + 0 else i_whave s) with (i_whave s)
    by (destruct (i_whave s <? i_wsize s); lia).
  destruct s; reflexivity.
Qed.

Lemma itd1_leave_fin: forall flush S h inp ao a msg tin tout,
  i_wsize S <> 0 -> wstruct S -> i_win S = true -> 0 <= i_total S <= Int64.max_unsigned ->
  0 <= tin <= Int64.max_unsigned -> 0 <= tout <= Int64.max_unsigned ->
  let M := MS S h inp ao 0 [] (i_hold S) (i_bits S) (Zlength inp) ao Z_OK 1 a msg tin tout 0 0 in
  exists dt, leave_fin flush M = Res Z_BUF_ERROR M dt.
Proof.
  intros flush S h inp ao a msg tin tout W WS WI T TI TO M.
  assert (Er: restore M = M) by (unfold restore; subst M; destruct S; reflexivity).
  assert (Eok: leave_ok flush M = true).
  { unfold leave_ok. subst M; cbn [m_s]. destruct (i_wsize S =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
    reflexivity. }
  assert (EU: forall l, upd_s M (fun s => set_i_win (updatewindow s (sublist l (Zlength (m_ow M)) (m_ow M))) true) = M).
  { intro l. change (m_ow M) with (@nil Z). rewrite sublist_of_nil. unfold upd_s. change (m_s M) with S.
    rewrite itd1_updatewindow_nil by assumption. subst M. destruct S; cbn in WI |- *; subst; reflexivity. }
  unfold leave_fin. rewrite Eok, Er. cbv beta iota zeta. rewrite EU.
  assert (Et: forall x, 0 <= x <= Int64.max_unsigned -> u64 x = x).
  { intros x X. unfold u64. apply Z.mod_small. cbn in X |- *. lia. }
  assert (Ei: u32 (m_in M - m_have M) = 0).
  { subst M. unfold m_have. cbn [m_in m_inp m_nx]. replace (Zlength inp - (Zlength inp - 0)) with 0 by lia.
    reflexivity. }
  assert (Eo: u32 (m_out M - m_left M) = 0).
  { subst M. unfold m_left. cbn [m_out m_aout m_ow]. rewrite Zlength_nil.
    replace (ao - (ao - 0)) with 0 by lia. reflexivity. }
  rewrite Eo, Ei, !Z.add_0_r. rewrite (Et (m_tin M)) by exact TI. rewrite (Et (m_tout M)) by exact TO.
  assert (EM: upd_s (set_m_tout (set_m_tin M (m_tin M)) (m_tout M)) (fun s => set_i_total s (u64 (i_total s + 0))) = M).
  { unfold upd_s. cbv beta. rewrite Z.add_0_r. change (i_total (m_s (set_m_tout (set_m_tin M (m_tin M)) (m_tout M)))) with (i_total S).
    rewrite (Et _ T). subst M. destruct S; reflexivity. }
  rewrite EM. cbv beta iota zeta. rewrite andb_false_r. cbv iota.
  eexists. f_equal.
Qed.

(* ---------------------------------------------------------------------------------------------- *)

Lemma itd1_live: forall L, live_ok L -> i_mode (l_s L) = DICT -> live_ok (set_l_s L (d1_ty (l_s L))).
Proof.
  intros L [P [S [MW [HW [S3 [WS [W0 [HD WH]]]]]]]] MD.
  assert (Wne: i_wbits (l_s L) <> 0).
  { intro E. destruct (W0 E) as [W1 _]. destruct (WH E (land3_wrap _ W1)) as [_ M].
    rewrite MD in M. unfold DICT, HEAD, BAD, SYNC, MEM in M. lia. }
  unfold live_ok; cbn [l_sp l_s l_h l_hsh l_xb l_nb l_cb set_l_s].
  unfold d1_ty.
  split; [exact P|]. split.
  { destruct S; constructor; cbn [i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits
      i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits
      i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was set_i_mode set_i_check];
    auto; unfold Zlib.proof.inflate.Model.TYPE, HEAD, SYNC, lrange; rep_lia. }
  split.
  { constructor; cbn [i_mode set_i_mode set_i_check]; unfold decode_mode;
      unfold Zlib.proof.inflate.Model.TYPE, LENLENS, CODELENS, LENEXT, DISTEXT, MATCH, DIST, LEN_, LEN, LIT;
      intros; lia. }
  split; [exact HW|]. split.
  { constructor; cbn [i_mode set_i_mode set_i_check]; unfold decode_mode;
      unfold Zlib.proof.inflate.Model.TYPE, HEAD, LENEXT, DISTEXT, LEN_, LEN, DIST, MATCH, LIT; intros; lia. }
  split; [exact WS|].
  cbn [i_wbits i_wrap i_win i_head i_flags i_mode set_i_mode set_i_check].
  split; [intro E; contradiction|]. split; [exact HD|]. intros E; contradiction.
Qed.

Lemma itd1_call: forall G z L flush inp res,
  it_ok G -> live_ok L -> zf_ok z -> d1_st G (zf_tout z) (l_s L) ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  run2 flush lenfix_list distfix_list (m_init (z_adl z 1) (set_l_s L (d1_ty (l_s L))) inp) res \/
  (r_ret res = Z_BUF_ERROR /\ m_inp (r_m res) = inp /\ m_snx (r_m res) = 0 /\ m_ow (r_m res) = [] /\
   m_sow (r_m res) = 0 /\ m_aout (r_m res) = zf_ao z /\ m_tout (r_m res) = zf_tout z /\
   post_st G 6 0 (zf_tout z) (m_s (r_m res))).
Proof.
  intros G z L flush inp res OK LV ZF [ZL [MD [HD PS]]] [o [LP RS]].
  set (s := l_s L) in *.
  set (S := d1_ty s) in *.
  assert (SW: swf s) by apply LV.
  pose proof PS as [_ [_ [_ [_ [WI [WS _]]]]]].
  assert (Wne: i_wsize S <> 0) by (destruct WS as [_ [? _]]; lia).
  set (M2 := m_init (z_adl z 1) (set_l_s L S) inp).
  assert (E2: M2 = MS (set_i_mode S TYPEDO) (l_h L) inp (zf_ao z) 0 [] (i_hold s) (i_bits s) (Zlength inp)
                      (zf_ao z) Z_OK 0 1 (zf_msg z) (zf_tin z) (zf_tout z) 0 0) by reflexivity.
  assert (E0: m_init z L inp = MS s (l_h L) inp (zf_ao z) 0 [] (i_hold s) (i_bits s) (Zlength inp)
                      (zf_ao z) Z_OK 0 (zf_adler z) (zf_msg z) (zf_tin z) (zf_tout z) 0 0).
  { unfold m_init. cbv zeta. fold s. rewrite MD. reflexivity. }
  assert (St0: stepf2 flush lenfix_list distfix_list (m_init z L inp) = c_TYPE flush (set_mode M2 Zlib.proof.inflate.Model.TYPE)).
  { unfold stepf2. rewrite itd1_step2_DICT by (rewrite E0; exact MD).
    rewrite E0. unfold c_DICT. cbn [m_s]. rewrite HD. reflexivity. }
  assert (St2: stepf2 flush lenfix_list distfix_list M2 = c_TYPEDO flush M2).
  { unfold stepf2. apply itd1_step2_TYPEDO. reflexivity. }
  (* the leave case *)
  assert (LV2: stepf2 flush lenfix_list distfix_list (m_init z L inp) = IBrk (set_leave (set_mode M2 Zlib.proof.inflate.Model.TYPE)) ->
               r_ret res = Z_BUF_ERROR /\ m_inp (r_m res) = inp /\ m_snx (r_m res) = 0 /\ m_ow (r_m res) = [] /\
               m_sow (r_m res) = 0 /\ m_aout (r_m res) = zf_ao z /\ m_tout (r_m res) = zf_tout z /\
               post_st G 6 0 (zf_tout z) (m_s (r_m res))).
  { intro St. inversion LP; subst.
    - congruence.
    - rewrite St in H. inversion H; subst m'. clear H.
      assert (EM: set_leave (set_mode M2 Zlib.proof.inflate.Model.TYPE) =
                  MS S (l_h L) inp (zf_ao z) 0 [] (i_hold S) (i_bits S) (Zlength inp) (zf_ao z) Z_OK 1 1
                     (zf_msg z) (zf_tin z) (zf_tout z) 0 0) by reflexivity.
      rewrite EM in RS. inversion RS; subst.
      + exfalso. match goal with Hw: i_win (m_s _) = false |- _ => cbn [m_s] in Hw end. congruence.
      + destruct ZF as [_ [_ [ZT1 [ZT2 _]]]].
        destruct (itd1_leave_fin flush S (l_h L) inp (zf_ao z) 1 (zf_msg z) (zf_tin z) (zf_tout z))
          as [dt Edt]; auto.
        { apply SW. }
        rewrite Edt. cbn [r_ret r_m m_inp m_snx m_ow m_sow m_aout m_tout m_s]. do 7 (split; [reflexivity|]). exact PS.
    - rewrite St in H. inversion H; subst m'. exfalso. apply H0. reflexivity. }
  destruct (orb (flush =? Z_BLOCK) (flush =? Z_TREES)) eqn:FB.
  { right. apply LV2. rewrite St0. unfold c_TYPE. rewrite FB. reflexivity. }
  assert (St0': stepf2 flush lenfix_list distfix_list (m_init z L inp) = c_TYPEDO flush (set_mode M2 Zlib.proof.inflate.Model.TYPE)).
  { rewrite St0. unfold c_TYPE. rewrite FB. reflexivity. }
  destruct (Z.eq_dec (i_last (m_s M2)) 0) as [LZ|LZ];
    [destruct (Z.eq_dec (m_leave (needbits 3 M2)) 1) as [NL|NL]|].
  - right. apply LV2. rewrite St0'. unfold c_TYPEDO.
    change (i_last (m_s (set_mode M2 Zlib.proof.inflate.Model.TYPE))) with (i_last (m_s M2)). rewrite LZ. cbn [Z.eqb negb].
    cbv zeta.
    assert (NL': m_leave (needbits 3 (set_mode M2 Zlib.proof.inflate.Model.TYPE)) = 1).
    { unfold needbits in *. rewrite itd1_needbits_sm. exact NL. }
    rewrite itd1_needbits_leave; [|reflexivity| |exact NL'].
    + reflexivity.
    + cbn [m_bits]. rewrite E2. cbn [m_bits]. apply SW.
  - left. exists o. split; [|exact RS].
    eapply itd1_loop2_same; [|exact LP]. rewrite St0', St2. apply itd1_typedo_sm. right; exact NL.
  - left. exists o. split; [|exact RS].
    eapply itd1_loop2_same; [|exact LP]. rewrite St0', St2. apply itd1_typedo_sm. left; exact LZ.
Qed.

Lemma itd1_facts :
  (forall L, live_ok L -> i_mode (l_s L) = DICT -> live_ok (set_l_s L (d1_ty (l_s L)))) /\
  (forall G z L flush inp res,
     it_ok G -> live_ok L -> zf_ok z -> d1_st G (zf_tout z) (l_s L) ->
     run2 flush lenfix_list distfix_list (m_init z L inp) res ->
     run2 flush lenfix_list distfix_list (m_init (z_adl z 1) (set_l_s L (d1_ty (l_s L))) inp) res \/
     (r_ret res = Z_BUF_ERROR /\ m_inp (r_m res) = inp /\ m_snx (r_m res) = 0 /\ m_ow (r_m res) = [] /\
      m_sow (r_m res) = 0 /\ m_aout (r_m res) = zf_ao z /\ m_tout (r_m res) = zf_tout z /\
      post_st G 6 0 (zf_tout z) (m_s (r_m res)))).
Proof.
  split; [exact itd1_live | exact itd1_call].
Qed.
