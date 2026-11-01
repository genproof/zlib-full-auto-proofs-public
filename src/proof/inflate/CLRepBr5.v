(* case CODELENS (CLRep5.v): the three branches of the repeat codes 16 / 17 / 18 (CLKit5.cl_rep, cl_rep_m) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CLKit5.
Require Import Zlib.proof.inflate.CLRepNB5.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the three branches *)
Definition cl_r16 : statement :=
  match cl_rep with Ssequence _ (Sifthenelse _ (Ssequence _ r) _) => r | _ => Sskip end.
Definition cl_r17 : statement :=
  match cl_rep with Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ (Ssequence _ r) _))) => r | _ => Sskip end.
Definition cl_r18 : statement :=
  match cl_rep with Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ _ (Ssequence _ r)))) => r | _ => Sskip end.

Ltac cl_rep_eval x :=
  let y := eval cbv beta iota zeta delta [cl_r16 cl_r17 cl_r18 cl_body cl_while cl_loopbody cl_iter cl_branch cl_big cl_rep
    case_body inflate_LS find_switch f_inflate fn_body ls_drop] in x in exact y.
Definition cl_r16_c : statement := ltac:(cl_rep_eval cl_r16).
Definition cl_r17_c : statement := ltac:(cl_rep_eval cl_r17).
Definition cl_r18_c : statement := ltac:(cl_rep_eval cl_r18).
Lemma cl_r16_eq: cl_r16 = cl_r16_c. Proof. reflexivity. Qed.
Lemma cl_r17_eq: cl_r17 = cl_r17_c. Proof. reflexivity. Qed.
Lemma cl_r18_eq: cl_r18 = cl_r18_c. Proof. reflexivity. Qed.

Definition cl_ifleave : statement := Sifthenelse (Etempvar _leave tint) Sbreak Sskip.

Lemma cl_rep_eq: cl_rep =
  Ssequence (Sset _t'294 (Efield (Evar _here (Tstruct ___gp_code noattr)) _val tushort))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'294 tushort) (Econst_int (Int.repr 16) tint) tint)
      (Ssequence (Ssequence (needbits_var 2 _t'309 _t'65 _t'308) cl_ifleave) cl_r16)
      (Ssequence (Sset _t'295 (Efield (Evar _here (Tstruct ___gp_code noattr)) _val tushort))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'295 tushort) (Econst_int (Int.repr 17) tint) tint)
          (Ssequence (Ssequence (needbits_var 3 _t'303 _t'66 _t'302) cl_ifleave) cl_r17)
          (Ssequence (Ssequence (needbits_var 7 _t'299 _t'67 _t'298) cl_ifleave) cl_r18)))).
Proof. reflexivity. Qed.

Definition cl_rep_post (F: frame) (m: mst) (here: entry) : ret_assert :=
    {| RA_normal := EX m2: mst, EX len: Z, EX copy: Z,
         !! (cl_rep_m here m = (m2, len, copy, true) /\ m_mode m2 = CODELENS /\ m_leave m2 = 0) &&
         loop_state_hc F m2 (ent here) len copy;
       RA_break := EX m2: mst,
         !! ((cl_rep_m here m = (m2, 0, 0, false) /\ m_leave m2 = 1) \/
             (cl_rep_m here m = (m2, 0, 0, true) /\ m_mode m2 = BAD /\ m_leave m2 = 0)) &&
         loop_state_h F m2 (ent here);
       RA_continue := FF;
       RA_return := fun _ => FF |}.

(* NEEDBITS's outcome: the state unchanged; enough bits, or leave *)
Lemma cl_nb_ok: forall k n m, m_leave m = 0 -> 0 <= m_bits m -> m_bits m + 8 * Z.of_nat k < 2 ^ 32 ->
  n <= m_bits m + 8 * Z.of_nat k ->
  m_s (needbits_f k n m) = m_s m /\
  ((m_leave (needbits_f k n m) = 0 /\ n <= m_bits (needbits_f k n m)) \/ m_leave (needbits_f k n m) = 1).
Proof.
  induction k; intros n m HL H0 H1 H2; simpl.
  - split; auto. left. split; auto. lia.
  - destruct (m_bits m <? n) eqn:E.
    + destruct (m_have m =? 0).
      * split; [reflexivity | right; reflexivity].
      * assert (B: m_bits (pull m) = m_bits m + 8).
        { unfold pull. cbn [m_bits set_m_bits]. unfold u32. rewrite Z.mod_small by lia. reflexivity. }
        destruct (IHk n (pull m)) as [IA IB].
        { exact HL. }
        { lia. }
        { rewrite B. lia. }
        { rewrite B. lia. }
        split; [exact IA | exact IB].
    + split; auto. left. apply Z.ltb_ge in E. split; auto.
Qed.

Lemma cl_nb: forall n m, mwf m -> m_leave m = 0 -> 0 <= n <= 32 ->
  mwf (needbits n m) /\ m_s (needbits n m) = m_s m /\
  ((m_leave (needbits n m) = 0 /\ n <= m_bits (needbits n m)) \/ m_leave (needbits n m) = 1).
Proof.
  intros n m W HL Hn. pose proof (mw_bits _ W).
  split; [apply mwf_needbits; [exact W | lia] | ].
  apply cl_nb_ok; auto; simpl; lia.
Qed.

(* do { c } while (0) as the last statement *)
Lemma cl_semax_dowhile0_last {Espec: OracleKind} (Delta: tycontext) (P: environ -> mpred) (c: statement)
    (R: ret_assert):
  semax Delta P c (normal_ret_assert (RA_normal R)) -> semax Delta P (Sloop c Sbreak) R.
Proof.
  intros H1.
  apply semax_loop with (Q' := RA_normal R).
  - destruct R. eapply semax_post; [ | | | | exact H1]; intros; simpl_ret_assert;
      first [apply andp_left2, derives_refl | apply andp_left2, FF_left].
  - eapply semax_pre; [ | apply semax_break]. destruct R. simpl_ret_assert. apply andp_left2, derives_refl.
Qed.

Lemma cl_r16_ok {Espec: OracleKind} (F: frame) (m: mst) (here: entry):
  frame_ok5 F -> mwf m -> m_mode m = CODELENS -> m_leave m = 0 -> entry_ok here -> e_bits here <= 15 ->
  e_val here = 16 ->
  semax Delta_cases5 (loop_state_h F m (ent here))
    (Ssequence (Ssequence (needbits_var 2 _t'309 _t'65 _t'308) cl_ifleave) cl_r16) (cl_rep_post F m here).
Proof.
  intros HF W HM HL HE HB HV.
  pose proof HE as (Eo & Eb & Ev).
  destruct (cl_nb (e_bits here + 2) m W HL ltac:(lia)) as (W1 & S1 & [[L1 N1] | L1]).
  - apply semax_seq with (Q := loop_state_h F (needbits (e_bits here + 2) m) (ent here)).
    + eapply semax_seq'; [apply semax_needbits_var16; auto; lia | ].
      unfold cl_ifleave, loop_state_h, loop_locals, cl_rep_post. rewrite L1. abbreviate_semax.
      forward_if.
      * contradiction.
      * forward. entailer!.
    + remember (needbits (e_bits here + 2) m) as m1 eqn:Em1.
      assert (CRE: cl_rep_m here m =
        (let m' := dropbits (e_bits here) m1 in
         if i_have (m_s m') =? 0 then (set_bad m' M_repeat, 0, 0, true) else
         (dropbits 2 m', Znth (i_have (m_s m') - 1) (i_lens (m_s m')), 3 + bitsn m' 2, true))).
      { unfold cl_rep_m. rewrite HV. cbn [Z.eqb Pos.eqb]. rewrite <- Em1, L1. reflexivity. }
      clear Em1.
      pose proof (mw_bits _ W1) as WB1. pose proof (mw_hold _ W1) as WH1. unfold lrange in WH1.
      pose proof (sw_lens _ (mw_s _ W1)) as [LL LF]. pose proof (sw_have _ (mw_s _ W1)) as HV0.
      pose proof (mw_md _ W1) as MD. assert (HM1: m_mode m1 = CODELENS) by (unfold m_mode; rewrite S1; exact HM).
      destruct (md_codelens _ MD HM1) as (HHV & HN & HD & _).
      rewrite cl_r16_eq. unfold cl_r16_c.
      rewrite loop_state_h_cl. unfold loop_state_clh, cl_sep, ent. abbreviate_semax. unfold loop_locals.
      freeze [1;2;5;6;7;8;9;10;11;13;14;16;17] FR.
      match goal with |- semax _ (PROPx ?P (LOCALx _ (SEPx ?S))) _ _ =>
        apply cl_semax_dowhile0 with (Q := PROPx P (LOCALx (loop_locals F (dropbits (e_bits here) m1)) (SEPx S))) end.
      { forward. { entailer!. rep_lia. }
        forward. { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
        forward. forward.
        unfold loop_locals, dropbits, m_have, m_left. mnorm_goal.
        entailer!. split.
        - rewrite cl_long_shru_eq by rep_lia. reflexivity.
        - rewrite cl_u32_repr. reflexivity. }
      unfold loop_locals. abbreviate_semax.
      forward.
      forward_if.
      * (* have == 0: BAD *)
        assert (CR: cl_rep_m here m = (set_bad (dropbits (e_bits here) m1) M_repeat, 0, 0, true)).
        { rewrite CRE. cbv zeta.
          replace (i_have (m_s (dropbits (e_bits here) m1))) with 0 by (symmetry; exact H1). reflexivity. }
        destruct HF as [(Hshs & _) _]. unfold cl_strm, strm_rep.
        remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.
        forward. forward. forward.
        unfold cl_rep_post. cbn [RA_break].
        Exists (set_bad (dropbits (e_bits here) m1) M_repeat).
        apply andp_right; [apply prop_right; right; split; [exact CR | split; [reflexivity | exact L1]] | ].
        assert (MR: mem_rest_cl F (set_bad (dropbits (e_bits here) m1) M_repeat) = mem_rest_cl F m1) by reflexivity.
        thaw FR. rewrite loop_state_h_cl. unfold loop_state_clh, cl_sep, loop_locals, cl_strm, strm_rep, ent. rewrite MR.
        unfold set_bad, m_have, m_left. mnorm_goal. cbn [msg_val msg_ident]. rewrite <- Eza, <- Ezf.
        entailer!.
      * forward. assert (HI: 0 <= i_have (m_s m1) - 1 < 320) by lia.
        assert (LV: 0 <= Znth (i_have (m_s m1) - 1) (i_lens (m_s m1)) <= 65535).
        { pose proof LF as LF'. rewrite Forall_forall in LF'. apply LF'. apply Znth_In. lia. }
        forward. { entailer!. lia. }
        assert (WH2: 0 <= m_hold (dropbits (e_bits here) m1) <= Int64.max_unsigned)
          by (cbn [dropbits m_hold set_m_bits set_m_hold]; apply Zshiftr_range; lia).
        forward.
        apply cl_semax_dowhile0_last.
        forward. forward.
        assert (CR: cl_rep_m here m = (dropbits 2 (dropbits (e_bits here) m1), Znth (i_have (m_s m1) - 1) (i_lens (m_s m1)),
                                        3 + bitsn (dropbits (e_bits here) m1) 2, true)).
        { rewrite CRE. cbv zeta.
          replace (i_have (m_s (dropbits (e_bits here) m1)) =? 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
          reflexivity. }
        rewrite Int64.unsigned_repr by lia. cl_mask_simpl. rewrite cl_int_and_ones by lia. rewrite add_repr.
        change (Int.unsigned (Int.repr 2)) with 2. rewrite cl_long_shru_eq by rep_lia. rewrite sub_repr.
        unfold cl_rep_post. cbn [RA_normal].
        Exists (dropbits 2 (dropbits (e_bits here) m1)) (Znth (i_have (m_s m1) - 1) (i_lens (m_s m1)))
          (3 + bitsn (dropbits (e_bits here) m1) 2).
        apply andp_right; [apply prop_right; split; [exact CR | split; [exact HM1 | exact L1]] | ].
        assert (MR: mem_rest_cl F (dropbits 2 (dropbits (e_bits here) m1)) = mem_rest_cl F m1) by reflexivity.
        assert (SR: cl_strm F (dropbits 2 (dropbits (e_bits here) m1)) = cl_strm F m1) by reflexivity.
        thaw FR. rewrite loop_state_hc_cl. unfold loop_state_clhc, cl_sep, loop_locals, ent. rewrite MR, SR.
        unfold bitsn, m_have, m_left. mnorm_goal. rewrite cl_u32_repr.
        entailer!.
  - apply semax_seq with (Q := PROP (False) LOCAL () SEP ()).
    + eapply semax_seq'; [apply semax_needbits_var16; auto; lia | ].
      unfold cl_ifleave, loop_state_h, loop_locals, cl_rep_post. rewrite L1. abbreviate_semax.
      forward_if.
      * forward. unfold cl_rep_post. cbn [RA_break].
        Exists (needbits (e_bits here + 2) m). unfold loop_state_h, loop_locals. rewrite L1.
        entailer!. left. split; auto. unfold cl_rep_m. rewrite HV. cbn [Z.eqb Pos.eqb]. rewrite L1. reflexivity.
      * exfalso. apply Int.one_not_zero. assumption.
    + Intros. contradiction.
Qed.

Lemma cl_r17_ok {Espec: OracleKind} (F: frame) (m: mst) (here: entry):
  frame_ok5 F -> mwf m -> m_mode m = CODELENS -> m_leave m = 0 -> entry_ok here -> e_bits here <= 15 ->
  e_val here = 17 ->
  semax Delta_cases5 (loop_state_h F m (ent here))
    (Ssequence (Ssequence (needbits_var 3 _t'303 _t'66 _t'302) cl_ifleave) cl_r17) (cl_rep_post F m here).
Proof.
  intros HF W HM HL HE HB HV.
  pose proof HE as (Eo & Eb & Ev).
  destruct (cl_nb (e_bits here + 3) m W HL ltac:(lia)) as (W1 & S1 & [[L1 N1] | L1]).
  - apply semax_seq with (Q := loop_state_h F (needbits (e_bits here + 3) m) (ent here)).
    + eapply semax_seq'; [apply semax_needbits_var17; auto; lia | ].
      unfold cl_ifleave, loop_state_h, loop_locals, cl_rep_post. rewrite L1. abbreviate_semax.
      forward_if.
      * contradiction.
      * forward. entailer!.
    + remember (needbits (e_bits here + 3) m) as m1 eqn:Em1.
      assert (CRE: cl_rep_m here m =
        (let m' := dropbits (e_bits here) m1 in (dropbits 3 m', 0, 3 + bitsn m' 3, true))).
      { unfold cl_rep_m. rewrite HV. cbn [Z.eqb Pos.eqb]. rewrite <- Em1, L1. reflexivity. }
      clear Em1.
      pose proof (mw_bits _ W1) as WB1. pose proof (mw_hold _ W1) as WH1. unfold lrange in WH1.
      pose proof (mw_md _ W1) as MD. assert (HM1: m_mode m1 = CODELENS) by (unfold m_mode; rewrite S1; exact HM).
      rewrite cl_r17_eq. unfold cl_r17_c.
      rewrite loop_state_h_cl. unfold loop_state_clh, cl_sep, ent. abbreviate_semax. unfold loop_locals.
      freeze [1;2;5;6;7;8;9;10;11;13;14;16;17] FR.
      match goal with |- semax _ (PROPx ?P (LOCALx _ (SEPx ?S))) _ _ =>
        apply cl_semax_dowhile0 with (Q := PROPx P (LOCALx (loop_locals F (dropbits (e_bits here) m1)) (SEPx S))) end.
      { forward. { entailer!. rep_lia. }
        forward. { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
        forward. forward.
        unfold loop_locals, dropbits, m_have, m_left. mnorm_goal.
        entailer!. split.
        - rewrite cl_long_shru_eq by rep_lia. reflexivity.
        - rewrite cl_u32_repr. reflexivity. }
      unfold loop_locals. abbreviate_semax.
      assert (WH2: 0 <= m_hold (dropbits (e_bits here) m1) <= Int64.max_unsigned)
        by (cbn [dropbits m_hold set_m_bits set_m_hold]; apply Zshiftr_range; lia).
      forward. forward.
      apply cl_semax_dowhile0_last.
      forward. forward.
      rewrite Int64.unsigned_repr by lia. cl_mask_simpl. rewrite cl_int_and_ones by lia. rewrite add_repr.
      change (Int.unsigned (Int.repr 3)) with 3. rewrite cl_long_shru_eq by rep_lia. rewrite sub_repr.
      unfold cl_rep_post. cbn [RA_normal].
      Exists (dropbits 3 (dropbits (e_bits here) m1)) 0 (3 + bitsn (dropbits (e_bits here) m1) 3).
      apply andp_right; [apply prop_right; split; [exact CRE | split; [exact HM1 | exact L1]] | ].
      assert (MR: mem_rest_cl F (dropbits 3 (dropbits (e_bits here) m1)) = mem_rest_cl F m1) by reflexivity.
      assert (SR: cl_strm F (dropbits 3 (dropbits (e_bits here) m1)) = cl_strm F m1) by reflexivity.
      thaw FR. rewrite loop_state_hc_cl. unfold loop_state_clhc, cl_sep, loop_locals, ent. rewrite MR, SR.
      unfold bitsn, m_have, m_left. mnorm_goal. rewrite cl_u32_repr.
      entailer!.
  - apply semax_seq with (Q := PROP (False) LOCAL () SEP ()).
    + eapply semax_seq'; [apply semax_needbits_var17; auto; lia | ].
      unfold cl_ifleave, loop_state_h, loop_locals, cl_rep_post. rewrite L1. abbreviate_semax.
      forward_if.
      * forward. unfold cl_rep_post. cbn [RA_break].
        Exists (needbits (e_bits here + 3) m). unfold loop_state_h, loop_locals. rewrite L1.
        entailer!. left. split; auto. unfold cl_rep_m. rewrite HV. cbn [Z.eqb Pos.eqb]. rewrite L1. reflexivity.
      * exfalso. apply Int.one_not_zero. assumption.
    + Intros. contradiction.
Qed.

Lemma cl_r18_ok {Espec: OracleKind} (F: frame) (m: mst) (here: entry):
  frame_ok5 F -> mwf m -> m_mode m = CODELENS -> m_leave m = 0 -> entry_ok here -> e_bits here <= 15 ->
  e_val here <> 16 -> e_val here <> 17 ->
  semax Delta_cases5 (loop_state_h F m (ent here))
    (Ssequence (Ssequence (needbits_var 7 _t'299 _t'67 _t'298) cl_ifleave) cl_r18) (cl_rep_post F m here).
Proof.
  intros HF W HM HL HE HB HV16 HV17.
  pose proof HE as (Eo & Eb & Ev).
  destruct (cl_nb (e_bits here + 7) m W HL ltac:(lia)) as (W1 & S1 & [[L1 N1] | L1]).
  - apply semax_seq with (Q := loop_state_h F (needbits (e_bits here + 7) m) (ent here)).
    + eapply semax_seq'; [apply semax_needbits_var18; auto; lia | ].
      unfold cl_ifleave, loop_state_h, loop_locals, cl_rep_post. rewrite L1. abbreviate_semax.
      forward_if.
      * contradiction.
      * forward. entailer!.
    + remember (needbits (e_bits here + 7) m) as m1 eqn:Em1.
      assert (CRE: cl_rep_m here m =
        (let m' := dropbits (e_bits here) m1 in (dropbits 7 m', 0, 11 + bitsn m' 7, true))).
      { unfold cl_rep_m. rewrite (proj2 (Z.eqb_neq _ _) HV16), (proj2 (Z.eqb_neq _ _) HV17). rewrite <- Em1, L1. reflexivity. }
      clear Em1.
      pose proof (mw_bits _ W1) as WB1. pose proof (mw_hold _ W1) as WH1. unfold lrange in WH1.
      pose proof (mw_md _ W1) as MD. assert (HM1: m_mode m1 = CODELENS) by (unfold m_mode; rewrite S1; exact HM).
      rewrite cl_r18_eq. unfold cl_r18_c.
      rewrite loop_state_h_cl. unfold loop_state_clh, cl_sep, ent. abbreviate_semax. unfold loop_locals.
      freeze [1;2;5;6;7;8;9;10;11;13;14;16;17] FR.
      match goal with |- semax _ (PROPx ?P (LOCALx _ (SEPx ?S))) _ _ =>
        apply cl_semax_dowhile0 with (Q := PROPx P (LOCALx (loop_locals F (dropbits (e_bits here) m1)) (SEPx S))) end.
      { forward. { entailer!. rep_lia. }
        forward. { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
        forward. forward.
        unfold loop_locals, dropbits, m_have, m_left. mnorm_goal.
        entailer!. split.
        - rewrite cl_long_shru_eq by rep_lia. reflexivity.
        - rewrite cl_u32_repr. reflexivity. }
      unfold loop_locals. abbreviate_semax.
      assert (WH2: 0 <= m_hold (dropbits (e_bits here) m1) <= Int64.max_unsigned)
        by (cbn [dropbits m_hold set_m_bits set_m_hold]; apply Zshiftr_range; lia).
      forward. forward.
      apply cl_semax_dowhile0_last.
      forward. forward.
      rewrite Int64.unsigned_repr by lia. cl_mask_simpl. rewrite cl_int_and_ones by lia. rewrite add_repr.
      change (Int.unsigned (Int.repr 7)) with 7. rewrite cl_long_shru_eq by rep_lia. rewrite sub_repr.
      unfold cl_rep_post. cbn [RA_normal].
      Exists (dropbits 7 (dropbits (e_bits here) m1)) 0 (11 + bitsn (dropbits (e_bits here) m1) 7).
      apply andp_right; [apply prop_right; split; [exact CRE | split; [exact HM1 | exact L1]] | ].
      assert (MR: mem_rest_cl F (dropbits 7 (dropbits (e_bits here) m1)) = mem_rest_cl F m1) by reflexivity.
      assert (SR: cl_strm F (dropbits 7 (dropbits (e_bits here) m1)) = cl_strm F m1) by reflexivity.
      thaw FR. rewrite loop_state_hc_cl. unfold loop_state_clhc, cl_sep, loop_locals, ent. rewrite MR, SR.
      unfold bitsn, m_have, m_left. mnorm_goal. rewrite cl_u32_repr.
      entailer!.
  - apply semax_seq with (Q := PROP (False) LOCAL () SEP ()).
    + eapply semax_seq'; [apply semax_needbits_var18; auto; lia | ].
      unfold cl_ifleave, loop_state_h, loop_locals, cl_rep_post. rewrite L1. abbreviate_semax.
      forward_if.
      * forward. unfold cl_rep_post. cbn [RA_break].
        Exists (needbits (e_bits here + 7) m). unfold loop_state_h, loop_locals. rewrite L1.
        entailer!. left. split; auto. unfold cl_rep_m. rewrite (proj2 (Z.eqb_neq _ _) HV16), (proj2 (Z.eqb_neq _ _) HV17). rewrite L1. reflexivity.
      * exfalso. apply Int.one_not_zero. assumption.
    + Intros. contradiction.
Qed.

Lemma cl_rep_post_eq: forall F m here, cl_rep_post F m here =
    {| RA_normal := EX m2: mst, EX len: Z, EX copy: Z,
         !! (cl_rep_m here m = (m2, len, copy, true) /\ m_mode m2 = CODELENS /\ m_leave m2 = 0) &&
         loop_state_hc F m2 (ent here) len copy;
       RA_break := EX m2: mst,
         !! ((cl_rep_m here m = (m2, 0, 0, false) /\ m_leave m2 = 1) \/
             (cl_rep_m here m = (m2, 0, 0, true) /\ m_mode m2 = BAD /\ m_leave m2 = 0)) &&
         loop_state_h F m2 (ent here);
       RA_continue := FF;
       RA_return := fun _ _ => FF |}.
Proof. reflexivity. Qed.

