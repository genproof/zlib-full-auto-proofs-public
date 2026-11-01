(* inflate(), cases COPY_ (14: mode COPY, falls into COPY) and COPY (15: copy = min(length, have, left)
   stored bytes by memcpy from the input object to the output object; mode TYPE when length = 0) in
   Delta_cases5 (Model2.v c_COPY_, c_COPY). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.Steps2 Zlib.proof.inflate.MwfLemmas Zlib.proof.inflate.STKit5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the modes of stored blocks need nothing of the state *)
Lemma mwf3_set_mode_stored: forall m md,
  mwf3 m -> m_mode m <> LENGTH -> m_mode m <> DONE -> m_mode m <> BAD ->
  md = COPY_ \/ md = COPY \/ md = Model.TYPE -> mwf3 (set_mode m md).
Proof.
  intros m md [W [A B C D]] H1 H2 H3 Hmd.
  assert (Hne: forall P: Prop, md = HEAD \/ md = LENLENS \/ md = CODELENS \/ decode_mode md \/ md = LENEXT \/
                               md = DISTEXT -> P).
  { intros P X. exfalso. unfold decode_mode in X.
    unfold HEAD, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, COPY_, COPY, Model.TYPE in *. lia. }
  split.
  - apply mwf_set_mode_plain; [exact W | | | | | ].
    + unfold HEAD, SYNC, COPY_, COPY, Model.TYPE in *. lia.
    + intro X. apply Hne. tauto.
    + intro X. apply Hne. tauto.
    + intro X. apply Hne. tauto.
    + left. apply mwf_out_eq; assumption.
  - constructor; cbn [set_mode upd_s set_m_s m_s i_mode set_i_mode i_wbits i_wsize i_wrap i_win i_length
                      i_offset i_lencode i_lenbits].
    + intro X. apply Hne. tauto.
    + intro X. apply Hne. tauto.
    + intro X. apply Hne. tauto.
    + intro X. apply Hne. tauto.
Qed.

Lemma case_COPY_5 {Espec: OracleKind} (F: frame) : case_ok5 F COPY 15 -> case_ok5 F COPY_ 14.
Proof.
  intros HY m HM HL W.
  assert (E1: stepf2 (f_flush F) lenfix_list distfix_list m =
              stepf2 (f_flush F) lenfix_list distfix_list (set_mode m COPY)).
  { rewrite (stepf2_COPY_ _ _ _ _ HM). unfold c_COPY_. symmetry.
    exact (stepf2_COPY (f_flush F) lenfix_list distfix_list (set_mode m COPY) eq_refl). }
  assert (W1: mwf3 (set_mode m COPY)).
  { apply mwf3_set_mode_stored; [exact W | | | | right; left; reflexivity];
      rewrite HM; unfold COPY_, LENGTH, DONE, BAD; lia. }
  apply (case_fallthrough5 F m COPY 14); [lia | exact HY | ].
  case_body_stmt.
  eapply ConseqFacts.semax_post''; [ | apply semax_store_mode5].
  unfold fall_post5. Exists (set_mode m COPY).
  apply andp_right; [ | apply andp_left2; apply derives_refl].
  apply prop_right. split; [exact E1 | ]. split; [reflexivity | ]. split; [exact HL | exact W1].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* case COPY: the slices of the input and output objects memcpy works on                         *)

Lemma arr_slice: forall sh p n (c: list val) a k,
  0 <= a -> 0 <= k -> a + k <= n -> Zlength c = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) c p =
  data_at sh (tarray tuchar a) (sublist 0 a c) p *
  data_at sh (tarray tuchar k) (sublist a (a + k) c) (offset_val a p) *
  data_at sh (tarray tuchar (n - (a + k))) (sublist (a + k) n c) (offset_val (a + k) p).
Proof.
  intros sh p n c a k Ha Hk Hn Hc FC.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a (a + k) c p) by lia.
  rewrite <- !(offset_val_field_address0_tuchar n) by (auto; lia).
  replace (a + k - a) with k by lia. reflexivity.
Qed.

Lemma out_rep_slice: forall sh p lo n c ow k,
  0 <= lo -> 0 <= k -> lo + Zlength ow + k <= n -> Zlength c = n -> field_compatible (tarray tuchar n) [] p ->
  out_rep (OutBuf sh p lo n c) ow =
  data_at sh (tarray tuchar (lo + Zlength ow)) (sublist 0 lo c ++ byte_vals ow) p *
  data_at sh (tarray tuchar k) (sublist (lo + Zlength ow) (lo + Zlength ow + k) c) (offset_val (lo + Zlength ow) p) *
  data_at sh (tarray tuchar (n - (lo + Zlength ow + k))) (sublist (lo + Zlength ow + k) n c)
    (offset_val (lo + Zlength ow + k) p).
Proof.
  intros sh p lo n c ow k H1 H2 H3 H4 FC. unfold out_rep.
  pose proof (Zlength_byte_vals ow). pose proof (Zlength_nonneg ow).
  rewrite (arr_slice sh p n _ (lo + Zlength ow) k) by (auto; try lia; list_solve).
  f_equal; [f_equal | ]; f_equal; list_solve.
Qed.

Lemma out_rep_slice_app: forall sh p lo n c ow d,
  0 <= lo -> lo + Zlength ow + Zlength d <= n -> Zlength c = n -> field_compatible (tarray tuchar n) [] p ->
  out_rep (OutBuf sh p lo n c) (ow ++ d) =
  data_at sh (tarray tuchar (lo + Zlength ow)) (sublist 0 lo c ++ byte_vals ow) p *
  data_at sh (tarray tuchar (Zlength d)) (byte_vals d) (offset_val (lo + Zlength ow) p) *
  data_at sh (tarray tuchar (n - (lo + Zlength ow + Zlength d))) (sublist (lo + Zlength ow + Zlength d) n c)
    (offset_val (lo + Zlength ow + Zlength d) p).
Proof.
  intros sh p lo n c ow d H1 H3 H4 FC. unfold out_rep.
  pose proof (Zlength_byte_vals ow). pose proof (Zlength_byte_vals d).
  pose proof (Zlength_nonneg ow). pose proof (Zlength_nonneg d).
  rewrite byte_vals_app, Zlength_app.
  rewrite (arr_slice sh p n _ (lo + Zlength ow) (Zlength d)) by (auto; try lia; list_solve).
  f_equal; [f_equal | ]; f_equal; list_solve.
Qed.

Lemma in_rep_slice: forall sh p lo n c inp nx k,
  in_ok (InBuf sh p lo n c) inp -> 0 <= nx -> 0 <= k -> nx + k <= Zlength inp ->
  field_compatible (tarray tuchar n) [] p ->
  in_rep (InBuf sh p lo n c) =
  data_at sh (tarray tuchar (lo + nx)) (sublist 0 (lo + nx) c) p *
  data_at sh (tarray tuchar k) (byte_vals (sublist nx (nx + k) inp)) (offset_val (lo + nx) p) *
  data_at sh (tarray tuchar (n - (lo + nx + k))) (sublist (lo + nx + k) n c) (offset_val (lo + nx + k) p).
Proof.
  intros sh p lo n c inp nx k (Hsh & Hp & Hlo & Hn & Hc & Hmax & Hsub & Hb) H1 H2 H3 FC. unfold in_rep.
  rewrite (arr_slice sh p n c (lo + nx) k) by (auto; lia).
  f_equal; f_equal. f_equal.
  rewrite <- sublist_byte_vals.
  assert (E: byte_vals inp = sublist lo (lo + Zlength inp) c) by (rewrite Hsub; reflexivity).
  rewrite E. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma c_COPY_brk: forall m,
  i_length (m_s m) <> 0 ->
  Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m) <> 0 ->
  c_COPY m = IBrk (upd_s (set_m_nx (set_m_ow m (m_ow m ++ inbytes m (Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m))))
                            (m_nx m + Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m)))
                (fun s => set_i_length s (i_length s - Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m)))).
Proof.
  intros m H1 H2. unfold c_COPY. rewrite (proj2 (Z.eqb_neq _ _) H1). simpl negb. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) H2). reflexivity.
Qed.

Ltac fix_post :=
  match goal with |- context [RA_normal (match ?R with _ => _ end)] => destruct R; simpl RA_normal end.

Ltac fix_break R HR :=
  match goal with |- context [RA_break ?X] =>
    replace (RA_break X) with (RA_break R) by (destruct R; reflexivity) end;
  rewrite HR.

Lemma copy_body5 {Espec: OracleKind} (F: frame) (m: mst) (R: ret_assert) :
  m_mode m = COPY -> m_leave m = 0 -> mwf m ->
  RA_break R = RA_normal (case_post2 F m) ->
  semax Delta_cases5 (loop_state F m) (case_body 15) R.
Proof.
  intros HM HL W HR.
  pose proof (stepf2_COPY (f_flush F) lenfix_list distfix_list m HM) as E0.
  pose proof (mwf_left m W) as HLEFT. pose proof (mwf_have m W) as HHAVE.
  pose proof (sw_length _ (mw_s _ W)) as HLEN.
  case_body_stmt.
  rewrite loop_state_split_st.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  unfold loop_state_st. frame_simpl.
  abbreviate_semax.
  forward.
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
  - unfold urange in HLEN.
    match goal with |- semax _ (PROPx ?P (LOCALx (temp _copy _ :: ?Q) (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _copy (Vint (Int.repr (Z.min (i_length (m_s m)) (m_have m)))) :: Q) (SEPx R))) end.
    + forward. fix_post.
      entailer!.
      rewrite Z.min_r by lia. reflexivity.
    + forward. fix_post.
      entailer!.
      rewrite Z.min_l by lia. reflexivity.
    + match goal with |- semax _ (PROPx ?P (LOCALx (temp _copy _ :: ?Q) (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _copy (Vint (Int.repr (Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m)))) :: Q) (SEPx R))) end.
      * forward. fix_post.
        entailer!.
        rewrite Z.min_r by lia. reflexivity.
      * forward. fix_post.
        entailer!.
        rewrite Z.min_l by lia. reflexivity.
      * assert (Hc: 0 <= Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m) <= m_have m /\
                    Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m) <= m_left m /\
                    Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m) <= i_length (m_s m)) by lia.
        match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          forward_if (PROPx (@cons Prop (Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m) <> 0) P) (LOCALx Q (SEPx R))) end.
        -- assert (E: stepf2 flush lenfix_list distfix_list m = IBrk (set_leave m)).
           { rewrite E0. unfold c_COPY. rewrite (proj2 (Z.eqb_neq _ _) H1'). simpl negb. cbv zeta.
             rewrite H2. reflexivity. }
           forward. forward.
           fix_break R HR. unfold case_post2, RA_normal.
           Exists (set_leave m).
           apply andp_right; [apply prop_right; exact E | ].
           rewrite loop_state_split_st. unfold loop_state_st. frame_simpl_goal.
           rewrite mem_rep_io_set_leave.
           mnorm_goal.
           entailer!.
        -- forward. fix_post. entailer!.
        -- Intros. rename H2 into Hc0.
           pose proof (c_COPY_brk m H1' Hc0) as E. rewrite <- E0 in E.
           pose proof (mw_nx _ W) as WNX. pose proof (mw_inp _ W) as WINP. pose proof (mw_ow _ W) as WOW.
           remember (Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m)) as c eqn:Hceq.
           destruct ib as [ | ish ip ilo inn ic].
           { exfalso. unfold in_ok in H. unfold m_have in Hc. rewrite H, Zlength_nil in Hc. lia. }
           destruct ob as [osh op olo onn oc].
           pose proof H as Hin. pose proof H0 as Hout.
           destruct H as (Hish & Hip & Hilo & Hinn & Hic & Himax & Hisub & Hib).
           destruct H0 as (Hosh & Hop & Holo & Haout & Hon & Hoc & Homax).
           cbn [in_ptr out_ptr].
           assert_PROP (field_compatible (tarray tuchar inn) [] ip) by (unfold in_rep; entailer!).
           assert_PROP (field_compatible (tarray tuchar onn) [] op) by (unfold out_rep; entailer!).
           unfold m_have, m_left in Hc.
           remember (sublist (m_nx m) (m_nx m + c) (m_inp m)) as data eqn:Hd.
           assert (HZ: Zlength data = c) by (subst data; rewrite Zlength_sublist by lia; lia).
           rewrite (in_rep_slice ish ip ilo inn ic (m_inp m) (m_nx m) c) by (auto; lia).
           rewrite (out_rep_slice osh op olo onn oc (m_ow m) c) by (auto; lia).
           rewrite <- Hd. rewrite <- HZ in *.
           sep_apply (data_at_data_at_ osh (tarray tuchar (Zlength data))).
           forward_call (osh, offset_val (olo + Zlength (m_ow m)) op, ish, offset_val (ilo + m_nx m) ip, data).
           { rewrite Hd. unfold bytes_ok. apply Forall_sublist. exact Hib. }
           forward. forward. forward. forward. forward. forward. forward.
           fix_break R HR. unfold case_post2, RA_normal.
           match type of E with _ = IBrk ?m' => Exists m' end.
           apply andp_right; [apply prop_right; exact E | ].
           rewrite loop_state_split_st. unfold loop_state_st.
           cbn [f_gv f_shs f_strmp f_sp f_headp f_winp f_hsh f_xb f_nb f_cb f_ib f_ob f_gsh f_tsh f_dt f_vres
                f_vhere f_vlast f_vhbuf f_flush in_ptr out_ptr].
           match goal with |- context [mem_rep_io ?F (upd_s ?m1 ?f)] =>
             replace (mem_rep_io F (upd_s m1 f)) with (mem_rep_io F m) by reflexivity end.
           mnorm_goal.
           assert (HI: inbytes m (Zlength data) = data) by (unfold inbytes; rewrite <- Hd; reflexivity).
           rewrite HI.
           rewrite (in_rep_slice ish ip ilo inn ic (m_inp m) (m_nx m) (Zlength data)) by (auto; lia).
           rewrite (out_rep_slice_app osh op olo onn oc (m_ow m) data) by (auto; lia).
           rewrite <- Hd.
           entailer!.
           unfold m_have, m_left. cbn [upd_s set_m_s set_m_nx set_m_ow m_inp m_nx m_ow m_aout].
           rewrite Zlength_app.
           split; [f_equal; lia | ]. split; [f_equal; lia | ].
           split; f_equal; f_equal; lia.
  - assert (H1': i_length (m_s m) = 0).
    { unfold urange in HLEN. apply (f_equal Int.unsigned) in H1.
      rewrite Int.unsigned_repr in H1 by lia. exact H1. }
    assert (E: stepf2 flush lenfix_list distfix_list m = IBrk (set_mode m Model.TYPE)).
    { rewrite E0. unfold c_COPY. rewrite H1'. reflexivity. }
    forward. forward.
    rewrite HR. unfold case_post2, RA_normal.
    Exists (set_mode m Model.TYPE).
    apply andp_right; [apply prop_right; exact E | ].
    rewrite loop_state_split_st. unfold loop_state_st. frame_simpl_goal.
    rewrite mem_rep_io_set_mode.
    mnorm_goal.
    entailer!.
Qed.

Lemma case_COPY5 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_ok5 F COPY 15.
Proof.
  intros HF m HM HL [W W3].
  rewrite seq_split by lia. eapply semax_seq; [ | apply semax_ff].
  apply copy_body5; auto.
Qed.
