(* case DISTEXT: the whole case from its NEEDBITS (DmKit5.dx_case_stmt) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.DmKit5.
Require Import Zlib.proof.inflate.Steps2 Zlib.proof.inflate.NeedKit5 Zlib.proof.inflate.ModeKit5.
Require Import Zlib.proof.inflate.NeedBits Zlib.proof.inflate.DxNb5 Zlib.proof.inflate.DxRest5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the model                                                                                      *)

Lemma dx_needbits_f_s: forall k n m, m_s (needbits_f k n m) = m_s m.
Proof.
  induction k; intros n m; simpl; auto.
  destruct (m_bits m <? n); auto. destruct (m_have m =? 0); auto. rewrite IHk. reflexivity.
Qed.

Lemma dx_needbits_f_ok: forall k n m,
  m_leave m = 0 -> 0 <= m_bits m -> n <= 32 -> n <= m_bits m + 8 * Z.of_nat k ->
  m_leave (needbits_f k n m) <> 1 -> n <= m_bits (needbits_f k n m) /\ m_leave (needbits_f k n m) = 0.
Proof.
  induction k; intros n m L B N F E; simpl in *.
  - split; [lia | auto].
  - destruct (Z.ltb_spec (m_bits m) n).
    + destruct (m_have m =? 0).
      * simpl in E. lia.
      * apply IHk; auto; unfold pull; simpl; unfold u32; rewrite ?Z.mod_small; lia.
    + split; [lia | auto].
Qed.

Lemma dx_needbits_ok: forall n m,
  mwf m -> m_leave m = 0 -> n <= 32 -> m_leave (needbits n m) <> 1 ->
  n <= m_bits (needbits n m) /\ m_leave (needbits n m) = 0.
Proof. intros n m W L N E. apply dx_needbits_f_ok; auto; try (destruct W; simpl; lia). Qed.

(* the fallthrough machine satisfies mwf3 *)
Lemma dx_mwf3: forall m, mwf m -> swf3 (m_s m) -> m_mode m = DISTEXT ->
  i_extra (m_s m) <= m_bits m -> mwf3 (set_mode (dx_m m) MATCH).
Proof.
  intros m W X HM HB.
  pose proof (md_distext _ (mw_md _ W) HM) as HX. pose proof (sw_extra _ (mw_s _ W)) as HX0.
  pose proof (proj2 (proj2 (md_back _ (mw_md _ W))) HM) as HBK.
  pose proof (md_length _ (mw_md _ W) (or_intror (or_intror HM))) as HLN.
  pose proof (md_offset _ (mw_md _ W) (or_introl HM)) as HOF.
  pose proof (s3_distext _ X HM) as HO.
  pose proof (md_tables _ (mw_md _ W) (or_intror (or_intror (or_intror (or_intror (or_introl HM)))))) as [TL TD].
  pose proof (s3_len _ X (or_intror (or_intror (or_intror (or_intror (or_introl HM)))))) as TL3.
  assert (OE: m_out m = m_aout m) by (apply mwf_out_eq; auto; rewrite HM; unfold DISTEXT, LENGTH, DONE, BAD; lia).
  set (ex := i_extra (m_s m)) in *.
  assert (P13: 2 ^ ex <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). change (2 ^ 13) with 8192 in P13.
  assert (P0: 0 < 2 ^ ex) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound (m_hold m) (2 ^ ex) P0) as HMOD.
  assert (U: u32 (i_offset (m_s m) + bitsn m ex) = i_offset (m_s m) + bitsn m ex).
  { unfold u32, bitsn. rewrite Z.mod_small; [reflexivity | ]. lia. }
  set (off := u32 (i_offset (m_s m) + bitsn m ex)) in *.
  unfold bitsn in U.
  assert (E: set_mode (dx_m m) MATCH =
             dropbits ex (upd_s m (fun s => set_i_mode (set_i_offset (set_i_back s (i_back s + ex)) off) MATCH)))
    by reflexivity.
  rewrite E.
  assert (W2: mwf (upd_s m (fun s => set_i_mode (set_i_offset (set_i_back s (i_back s + ex)) off) MATCH))).
  { pose proof W as W'. destruct W' as [MD SW HW INP AOUT NX OW HOLD BITS IN OUT RET LEAVE ADLER TIN TOUT SNX SOW OUTEQ].
    constructor; cbn [upd_s set_m_s m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler
      m_tin m_tout m_snx m_sow]; auto.
    all: match goal with
      | |- modewf _ =>
          destruct MD; constructor; cbn [set_i_mode set_i_offset set_i_back i_mode i_offset i_back i_length i_extra];
          intros; try (unfold LENLENS, CODELENS, LENEXT, DIST, DISTEXT, MATCH in *; lia);
          try exact (conj TL TD); try lia;
          repeat split; intros; unfold LENEXT, DIST, DISTEXT, MATCH in *; lia
      | |- swf _ =>
          destruct SW; constructor; cbn [set_i_mode set_i_offset set_i_back i_mode i_offset i_back]; auto;
          try (unfold HEAD, MATCH, SYNC; lia); unfold urange; rep_lia
      | |- _ => idtac
      end.
    }
  split.
  - apply mwf_dropbits; [exact W2 | ]. cbn. lia.
  - constructor; cbn [dropbits upd_s set_m_s set_m_hold set_m_bits m_s set_i_mode set_i_offset set_i_back i_mode
      i_offset i_back]; intros; try (unfold HEAD, LENEXT, DISTEXT, MATCH in *; lia).
    exact TL3.
Qed.

Lemma dx_m0: forall m, mwf m -> i_extra (m_s m) = 0 -> dx_m m = m.
Proof.
  intros m W E. pose proof (mw_bits _ W) as B. pose proof (sw_offset _ (mw_s _ W)) as O. unfold urange in O.
  destruct m as [s h inp aout nx ow hold bits in_ out ret leave adler msg tin tout snx sow].
  destruct s. simpl in *. subst.
  unfold dx_m, dropbits, upd_s, bitsn, set_m_bits, set_m_hold, set_m_s, set_i_offset, set_i_back, u32; simpl.
  rewrite ?Z.add_0_r, ?Z.shiftr_0_r, ?Z.sub_0_r, ?Z.pow_0_r, ?Z.mod_1_r, ?Z.add_0_r.
  rewrite !Z.mod_small by rep_lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* VST                                                                                            *)

Lemma dx_post_over {Espec: OracleKind} (Delta: tycontext) (P Q Q': environ -> mpred) (c: statement) (R: ret_assert):
  semax Delta P c (normal_ret_assert Q') -> Q' |-- Q -> semax Delta P c (overridePost Q R).
Proof.
  intros H HQ. destruct R.
  eapply semax_post; [ | | | | exact H]; intros; simpl_ret_assert;
    first [apply andp_left2; exact HQ | apply andp_left2, FF_left].
Qed.

Definition dx_q (F: frame) (m: mst) : environ -> mpred :=
  EX m2: mst,
    !! (c_DISTEXT m = c_MATCH (set_mode m2 MATCH) /\ mwf3 (set_mode m2 MATCH) /\ m_leave m2 = 0) &&
    loop_state F m2.

(* t'166 = state->extra; *)
Lemma dx_t166_ok {Espec: OracleKind} (F: frame) (m: mst):
  semax Delta_cases5 (loop_state F m)
    (Sset _t'166 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                            (Tstruct _inflate_state noattr)) _extra tuint))
    (normal_ret_assert
      (PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
       (LOCALx (temp _t'166 (zv (i_extra (m_s m))) :: loop_locals F m)
       (SEPx [mem_rep F m; locals_rep F])))).
Proof.
  unfold loop_state, loop_locals. rewrite mem_rep_esplit. Intros. abbreviate_semax.
  forward. entailer!.
Qed.

Lemma dx_case_ok : dx_nb_stmt -> dx_case_stmt.
Proof.
  intros HNB Espec F HF HMt m HM HL W3.
  pose proof W3 as [W X].
  pose proof (md_distext _ (mw_md _ W) HM) as HX. pose proof (sw_extra _ (mw_s _ W)) as HX0.
  pose proof (s3_distext _ X HM) as HO.
  apply (case_fallthrough5 F m MATCH 23); [lia | exact HMt | ].
  change (case_body 23) with dx_body. rewrite dx_body_eq.
  apply semax_seq with (Q := dx_q F m).
  - eapply semax_seq'; [apply dx_t166_ok | ].
    forward_if.
    + (* extra <> 0 *)
      assert (EX0: i_extra (m_s m) <> 0).
      { intro E. match goal with H: Int.repr _ <> Int.zero |- _ => apply H end. rewrite E. reflexivity. }
      unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
      apply semax_pre with (P' := loop_state F m); [ unfold loop_state, loop_locals; entailer! | ].
      apply (semax_needbits_seq5 F m m (i_extra (m_s m)) dx_nb dx_rest); [apply HNB; auto | auto | lia | reflexivity | | ].
      * intro E1. rewrite (stepf2_DISTEXT _ _ _ m HM). unfold c_DISTEXT.
        rewrite (proj2 (Z.eqb_neq _ _) EX0). cbn [negb]. rewrite E1. reflexivity.
      * apply semax_extract_prop. intro L1.
        pose proof (dx_needbits_ok (i_extra (m_s m)) m W HL ltac:(lia) ltac:(lia)) as [B1 _].
        pose proof (dx_needbits_f_s 4 (i_extra (m_s m)) m) as NS. change (needbits_f 4) with needbits in NS.
        pose proof (mwf_needbits (i_extra (m_s m)) m W ltac:(lia)) as W1.
        set (m1 := needbits (i_extra (m_s m)) m) in *.
        assert (HM1: m_mode m1 = DISTEXT) by (unfold m_mode; rewrite NS; exact HM).
        assert (X1: swf3 (m_s m1)) by (rewrite NS; exact X).
        assert (XE: i_extra (m_s m1) = i_extra (m_s m)) by (rewrite NS; reflexivity).
        eapply dx_post_over; [apply dx_rest_ok; auto; [rewrite XE; lia | rewrite NS; exact HO] | ].
        unfold dx_q. Exists (dx_m m1).
        apply andp_right; [apply prop_right | apply derives_refl].
        split; [ | split].
        -- unfold c_DISTEXT. rewrite (proj2 (Z.eqb_neq _ _) EX0). cbn [negb]. fold m1.
           rewrite (proj2 (Z.eqb_neq _ _)) by lia. unfold dx_m. rewrite XE. reflexivity.
        -- apply dx_mwf3; auto. rewrite XE. lia.
        -- exact L1.
    + (* extra = 0 *)
      assert (EX0: i_extra (m_s m) = 0).
      { match goal with H: Int.repr _ = Int.zero |- _ => apply repr_inj_unsigned in H; rep_lia end. }
      forward.
      match goal with |- _ |-- ?G => replace G with (dx_q F m) by reflexivity end.
      unfold dx_q. Exists m.
      apply andp_right.
      * apply prop_right. split; [ | split; [ | exact HL]].
        -- unfold c_DISTEXT. rewrite EX0. reflexivity.
        -- rewrite <- (dx_m0 m W EX0). apply dx_mwf3; auto. pose proof (mw_bits _ W). lia.
      * unfold loop_state, loop_locals. entailer!.
  - unfold dx_q. Intros m2. apply semax_extract_prop. intros (E2 & W2 & L2).
    rewrite dx_fin_eq.
    eapply dx_post_over; [apply semax_store_mode5 | ].
    unfold fall_post5. Exists (set_mode m2 MATCH).
    apply andp_right; [apply prop_right | apply derives_refl].
    split; [ | split; [reflexivity | split; [exact L2 | exact W2]]].
    rewrite (stepf2_DISTEXT _ _ _ m HM), (stepf2_MATCH _ _ _ (set_mode m2 MATCH) eq_refl). exact E2.
Qed.
