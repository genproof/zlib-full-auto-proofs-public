(* copy of cases5_LD for case LEN's fallthrough *)
(* inflate(), the switch cases LENEXT, DIST (21-22), version 5 (Delta_cases5, case_post2 over Model2.v, mwf3; header cases
   FLAGS .. COMMENT with the header buffers' tokens: CaseHyps5.v, CaseKitT5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.LdKit5 Zlib.proof.inflate.NeedKit5.
Require Import Zlib.proof.inflate.LdNb5 Zlib.proof.inflate.LdLenext5 Zlib.proof.inflate.DsTab5
  Zlib.proof.inflate.DsLoop1_5 Zlib.proof.inflate.DsLoop2_5 Zlib.proof.inflate.DsLink5 Zlib.proof.inflate.DsTail5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* if (leave) break; with the locals here / last holding values                                   *)

Lemma ld_ifleave0 {Espec: OracleKind} (F: frame) (m: mst) (hv lv: reptype t_code):
  m_leave m = 0 ->
  semax Delta_cases5 (ld_hl F m hv lv) ld_ifleave (normal_ret_assert (ld_hl F m hv lv)).
Proof.
  intros HL. unfold ld_hl, ld_locals, ld_ifleave. rewrite HL. abbreviate_semax.
  forward_if.
  - exfalso. auto.
  - forward. entailer!.
Qed.

Lemma ld_ifleave1 {Espec: OracleKind} (F: frame) (m0 m: mst) (hv lv: reptype t_code) (c: statement)
    (R: ret_assert):
  mwf m -> m_leave m = 1 ->
  RA_break R = RA_normal (case_post2 F m0) ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk m ->
  semax Delta_cases5 (ld_hl F m hv lv) (Ssequence ld_ifleave c) R.
Proof.
  intros W HL HR E.
  apply semax_seq with (Q := !! (m_leave m = 0) && loop_state F m).
  - eapply semax_pre; [ apply andp_left2, ld_hl_loop_state | ].
    apply (semax_ifleave5 F m0 m R W HR). intros _. exact E.
  - apply semax_extract_prop. intros HL0. rewrite HL in HL0. discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the case DIST                                                                                  *)

Definition ds_q (F: frame) (m0: mst) : environ -> mpred :=
  EX b1: Z, EX M: mst, EX h: entry, EX lv: reptype t_code,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m0 = ds_tail_m h (ds_drop b1 M) /\
        mwf3 M /\ m_mode M = DIST /\ m_leave M = 0 /\ 0 <= b1 /\ entry_ok h /\ final_ok DISTS h /\
        b1 + e_bits h <= 15 /\ b1 + e_bits h <= m_bits M) &&
    ld_hl F (ds_drop b1 M) (ent h) lv.

Lemma ds_drop0: forall m, mwf m -> ds_drop 0 m = m.
Proof.
  intros m W. pose proof (mw_bits _ W) as B.
  destruct m as [s h inp aout nx ow hold bits in_ out ret leave adler msg tin tout snx sow].
  destruct s. simpl in B.
  unfold ds_drop, dropbits, upd_s, set_m_bits, set_m_hold, set_m_s, set_i_back; simpl.
  rewrite Z.add_0_r, Z.shiftr_0_r, Z.sub_0_r. unfold u32. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma ld_land240: forall op, 0 <= op <= 255 ->
  (Int.and (Int.repr op) (Int.repr 240) = Int.repr 0 <-> Z.land op 240 = 0).
Proof.
  intros op H. rewrite and_repr.
  assert (0 <= Z.land op 240 <= 255).
  { split; [apply Z.land_nonneg; lia | ].
    destruct (Z.eq_dec (Z.land op 240) 0) as [E|E]; [lia|].
    assert (P: 0 < Z.land op 240) by (pose proof (proj2 (Z.land_nonneg op 240) (or_introl (proj1 H))); lia).
    pose proof (Z.log2_land op 240 ltac:(lia) ltac:(lia)) as L.
    pose proof (Z.log2_spec _ P) as [_ S].
    assert (L7: Z.log2 240 = 7) by reflexivity.
    assert (L8: 2 ^ Z.succ (Z.log2 (Z.land op 240)) <= 2 ^ 8) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 8) with 256 in L8. lia. }
  split; intro E.
  - apply repr_inj_unsigned in E; rep_lia.
  - rewrite E. reflexivity.
Qed.

Lemma ld_post_mono {Espec: OracleKind} (Delta: tycontext) (P Q1 Q2: environ -> mpred) (c: statement) (R: ret_assert):
  Q1 |-- Q2 -> semax Delta P c (overridePost Q1 R) -> semax Delta P c (overridePost Q2 R).
Proof.
  intros HQ H. eapply semax_post; [ | | | | exact H]; destruct R; simpl; intros;
    apply andp_left2; first [apply HQ | apply derives_refl].
Qed.

Lemma ds_step_leave1: forall fl m0 here m1,
  m_mode m0 = DIST ->
  lookup1 lenfix_list distfix_list (i_distcode (m_s m0)) (i_distbits (m_s m0)) m0 = (here, m1, false) ->
  stepf2 fl lenfix_list distfix_list m0 = IBrk m1.
Proof. intros fl m0 here m1 HM E1. rewrite (stepf2_DIST _ _ _ m0 HM), c_DIST_eq. unfold ds_m. rewrite E1. reflexivity. Qed.

Lemma ds_step_final: forall fl m0 here m1,
  m_mode m0 = DIST ->
  lookup1 lenfix_list distfix_list (i_distcode (m_s m0)) (i_distbits (m_s m0)) m0 = (here, m1, true) ->
  Z.land (e_op here) 240 <> 0 ->
  stepf2 fl lenfix_list distfix_list m0 = ds_tail_m here m1.
Proof.
  intros fl m0 here m1 HM E1 L. rewrite (stepf2_DIST _ _ _ m0 HM), c_DIST_eq. unfold ds_m. rewrite E1.
  rewrite (proj2 (Z.eqb_neq _ _) L). reflexivity.
Qed.

Lemma ds_step_link: forall fl m0 here m1 h2 m2 ok,
  m_mode m0 = DIST ->
  lookup1 lenfix_list distfix_list (i_distcode (m_s m0)) (i_distbits (m_s m0)) m0 = (here, m1, true) ->
  Z.land (e_op here) 240 = 0 ->
  lookup2 lenfix_list distfix_list (i_distcode (m_s m0)) here m1 = (h2, m2, ok) ->
  stepf2 fl lenfix_list distfix_list m0 = if ok then ds_tail_m h2 (ds_drop (e_bits here) m2) else IBrk m2.
Proof.
  intros fl m0 here m1 h2 m2 ok HM E1 L E2. rewrite (stepf2_DIST _ _ _ m0 HM), c_DIST_eq. unfold ds_m. rewrite E1.
  rewrite L. simpl Z.eqb. cbv iota. rewrite E2. destruct ok; reflexivity.
Qed.

Lemma ds_q_intro: forall F m0 b1 M h lv,
  stepf2 (f_flush F) lenfix_list distfix_list m0 = ds_tail_m h (ds_drop b1 M) ->
  mwf3 M -> m_mode M = DIST -> m_leave M = 0 -> 0 <= b1 -> entry_ok h -> final_ok DISTS h ->
  b1 + e_bits h <= 15 -> b1 + e_bits h <= m_bits M ->
  ld_hl F (ds_drop b1 M) (ent h) lv |-- ds_q F m0.
Proof.
  intros. unfold ds_q. apply (exp_right b1), (exp_right M), (exp_right h), (exp_right lv).
  apply andp_right; [ apply prop_right; do 8 (split; [assumption|]); assumption | apply derives_refl ].
Qed.

Lemma ds_lif_ok {Espec: OracleKind} (F: frame) (m0 m1: mst) (here: entry) (lv: reptype t_code) (R: ret_assert):
  frame_ok5 F -> mwf3 m0 -> m_mode m0 = DIST -> m_leave m0 = 0 ->
  lookup1 lenfix_list distfix_list (i_distcode (m_s m0)) (i_distbits (m_s m0)) m0 = (here, m1, true) ->
  RA_break R = RA_normal (case_post2 F m0) ->
  semax Delta_cases5 (ld_hl F m1 (ent here) lv) (Ssequence ds_ltest (Sifthenelse ds_lcond ds_link Sskip))
    (overridePost (ds_q F m0) R).
Proof.
  intros HF W3 HM HL E1 HR. pose proof W3 as [W S3].
  assert (D: decode_mode (i_mode (m_s m0)))
    by (change (i_mode (m_s m0)) with (m_mode m0); rewrite HM; unfold decode_mode; auto 10).
  destruct (md_tables _ (mw_md _ W) D) as [_ (sz & SZ & TV)].
  pose proof (tv_rb _ _ _ _ TV) as RB.
  pose proof (lookup1_ok lenfix_list distfix_list (i_distcode (m_s m0)) (i_distbits (m_s m0)) m0 W HL ltac:(lia)
                (fun i Hi => proj2 (proj1 (tv_root_bits _ _ _ _ i TV Hi)))) as LK.
  rewrite E1 in LK. destruct LK as (W1 & S1 & OK1 & _).
  destruct (OK1 eq_refl) as (L1 & B1 & i & Hi & Eh).
  pose proof (tv_root_bits _ _ _ _ i TV Hi) as [RBh EOh]. rewrite <- Eh in RBh, EOh.
  assert (M1: m_mode m1 = DIST) by (unfold m_mode in *; rewrite S1; exact HM).
  assert (W31: mwf3 m1) by (split; [exact W1 | rewrite S1; exact S3]).
  pose proof EOh as (EO1 & EO2 & EO3).
  assert (LINK: Z.land (e_op here) 240 = 0 ->
    sub_ok DISTS (tab_entry lenfix_list distfix_list (m_s m0) (i_distcode (m_s m0))) (i_distbits (m_s m0)) sz here).
  { intros LK0. assert (ISL: islink DISTS (e_op here) = true) by (unfold islink; rewrite LK0; reflexivity).
    rewrite Eh in ISL |- *. exact (tv_sub _ _ _ _ i TV Hi ISL). }
  assert (FIN: Z.land (e_op here) 240 <> 0 -> e_bits here <= i_distbits (m_s m0) /\ final_ok DISTS here).
  { intros LK0. assert (ISL: islink DISTS (e_op here) = false)
      by (unfold islink; rewrite (proj2 (Z.eqb_neq _ _) LK0); apply andb_false_r).
    rewrite Eh in ISL |- *. exact (tv_final _ _ _ _ i TV Hi ISL). }
  clear OK1 Eh Hi i.
  rewrite ds_ltest_eq, ds_lcond_eq.
  unfold ld_hl at 1, ld_locals. abbreviate_semax.
  forward.
  { unfold ent. entailer!. rep_lia. }
  unfold ent at 1. cbv beta iota.
  forward_if.
  - (* a sub-table *)
    assert (LK0: Z.land (e_op here) 240 = 0) by (apply ld_land240; [lia | assumption]).
    specialize (LINK LK0).
    pose proof LINK as (SB & SO1 & SO2 & SBT).
    assert (SB2: forall j, 0 <= j < 2 ^ e_op here ->
      e_bits here + e_bits (tab_entry lenfix_list distfix_list (m_s m1) (i_distcode (m_s m0)) (e_val here + j)) <= 15).
    { intros j Hj. rewrite S1. destruct (SBT j Hj) as (_ & _ & _ & A & _). lia. }
    subst POSTCONDITION. unfold abbreviate.
    eapply semax_pre with (P' := ld_hl F m1 (ent here) lv).
    { unfold ld_hl, ld_locals. entailer!. }
    eapply ld_post_mono; [ | rewrite <- S1 in SZ, LINK;
      apply (ds_link_ok (ds_loop2_ok ds_tab_ok) _ F m0 m1 here lv sz R HF W1 M1 L1 SZ LINK EOh B1 HR) ].
    + apply exp_left. intros h2. apply exp_left. intros m2.
      apply derives_extract_prop. intros E2.
      rewrite S1 in E2.
      pose proof (lookup2_ok lenfix_list distfix_list (i_distcode (m_s m0)) here m1 W1 L1 ltac:(lia) ltac:(lia) SB2)
        as LK2.
      rewrite E2 in LK2. destruct LK2 as (W2 & S2 & OK2 & _).
      destruct (OK2 eq_refl) as (L2 & B2 & j & Hj & Eh2). rewrite S1 in Eh2.
      destruct (SBT j Hj) as (_ & EO2' & _ & A2 & F2). cbv zeta in EO2', A2, F2. rewrite <- Eh2 in EO2', A2, F2.
      apply ds_q_intro.
      * exact (ds_step_link _ m0 here m1 h2 m2 true HM E1 LK0 E2).
      * split; [exact W2 | rewrite S2, S1; exact S3].
      * unfold m_mode in *. rewrite S2. exact M1.
      * exact L2.
      * lia.
      * exact EO2'.
      * exact F2.
      * lia.
      * lia.
    + intros h2 m2 E2. rewrite S1 in E2. exact (ds_step_link _ m0 here m1 h2 m2 false HM E1 LK0 E2).
  - (* a final entry *)
    assert (LK0: Z.land (e_op here) 240 <> 0) by (intro X; apply H1; apply ld_land240; [lia | exact X]).
    destruct (FIN LK0) as [FB FF].
    forward.
    destruct R as [Rn Rb Rc Rr]. simpl RA_normal.
    rewrite <- (ds_drop0 m1 W1).
    eapply derives_trans; [ | apply ds_q_intro with (b1 := 0) (M := m1) (h := here) (lv := lv) ].
    + unfold ld_hl, ld_locals. rewrite (ds_drop0 m1 W1). entailer!.
    + rewrite (ds_drop0 m1 W1). exact (ds_step_final _ m0 here m1 HM E1 LK0).
    + exact W31.
    + exact M1.
    + exact L1.
    + lia.
    + exact EOh.
    + exact FF.
    + lia.
    + lia.
Qed.

Lemma case_DIST5 {Espec: OracleKind} (F: frame): frame_ok5 F -> case_ok5 F DISTEXT 23 -> case_ok5 F DIST 22.
Proof.
  intros HF HY m HM HL W3. pose proof W3 as [W S3].
  assert (D: decode_mode (i_mode (m_s m)))
    by (change (i_mode (m_s m)) with (m_mode m); rewrite HM; unfold decode_mode; auto 10).
  destruct (md_tables _ (mw_md _ W) D) as [_ (sz & SZ & TV)].
  pose proof (tv_rb _ _ _ _ TV) as RB.
  apply (case_fallthrough5 F m DISTEXT 22); [lia | exact HY | ].
  change (case_body 22) with ds_body. rewrite ds_body_eq.
  rewrite loop_state_ld_hl.
  eapply semax_seq'; [ apply (ds_loop1_ok ds_tab_ok _ F m _ _ HF W HM HL) | ].
  apply extract_exists_pre; intros here. apply extract_exists_pre; intros m1.
  apply extract_exists_pre; intros ok. apply semax_extract_prop; intros E1.
  pose proof (lookup1_ok lenfix_list distfix_list (i_distcode (m_s m)) (i_distbits (m_s m)) m W HL ltac:(lia)
                (fun i Hi => proj2 (proj1 (tv_root_bits _ _ _ _ i TV Hi)))) as LK.
  rewrite E1 in LK. destruct LK as (W1 & S1 & OK1 & NOK1).
  destruct ok.
  - destruct (OK1 eq_refl) as (L1 & _).
    eapply semax_seq'; [ apply (ld_ifleave0 F m1 _ _ L1) | ].
    eapply semax_seq; [ apply (ds_lif_ok F m m1 here _ _ HF W3 HM HL E1); reflexivity | ].
    unfold ds_q.
    apply extract_exists_pre; intros b1. apply extract_exists_pre; intros M.
    apply extract_exists_pre; intros h. apply extract_exists_pre; intros lv.
    apply semax_extract_prop; intros (ET & WM & MM & LM & B0 & EOK & FOK & BB1 & BB2).
    apply (ds_tail_ok _ F m M b1 h lv _ HF WM MM LM B0 EOK FOK BB1 BB2 ET); reflexivity.
  - apply (ld_ifleave1 F m m1); [ exact W1 | exact (NOK1 eq_refl) | reflexivity | ].
    exact (ds_step_leave1 _ m here m1 HM E1).
Qed.

Lemma ln_cases5_LD {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  (case_ok5 F DIST 22 -> case_ok5 F LENEXT 21) /\ (case_ok5 F DISTEXT 23 -> case_ok5 F DIST 22).
Proof.
  intros HF. split.
  - exact (ld_lenext_ok ld_nb_ok _ F HF).
  - exact (case_DIST5 F HF).
Qed.
