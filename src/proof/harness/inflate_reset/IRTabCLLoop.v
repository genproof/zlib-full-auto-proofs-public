(* Law inflate_reset, TABLE / LENLENS / CODELENS: CODELENS's while loop in lockstep (IRTabKit.irt_clloop_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Require Import Zlib.proof.harness.inflate_reset.IRTabKit.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* srel under CODELENS's state changes                                                            *)

Lemma clp_tab_codes s s' t i : i_codes s' = i_codes s ->
  tab_entry lenfix_list distfix_list s' t i = tab_entry lenfix_list distfix_list s t i.
Proof. intros E. destruct t; simpl; try reflexivity. rewrite E; reflexivity. Qed.

Lemma clp_treach kind sa sb sa' sb' t rb :
  treach_eq kind sa sb t rb -> i_codes sa' = i_codes sa -> i_codes sb' = i_codes sb ->
  treach_eq kind sa' sb' t rb.
Proof.
  unfold treach_eq. intros T Ea Eb i Hi. cbv zeta.
  assert (Ha: forall j, tab_entry lenfix_list distfix_list sa' t j = tab_entry lenfix_list distfix_list sa t j)
    by (intros; apply clp_tab_codes; auto).
  assert (Hb: forall j, tab_entry lenfix_list distfix_list sb' t j = tab_entry lenfix_list distfix_list sb t j)
    by (intros; apply clp_tab_codes; auto).
  destruct (T i Hi) as [A B]. rewrite !Ha, !Hb. split; [exact A|].
  intros L j Hj. rewrite !Ha, !Hb. apply B; auto.
Qed.

Lemma clp_srel_bad no sa sb : srel no sa sb -> srel no (set_i_mode sa BAD) (set_i_mode sb BAD).
Proof.
  intros S. destruct S; constructor; unfold lenlive, decode_mode; simpl; auto;
    cbv [HEAD TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT BAD COPY_ COPY EXTRA]; try lia.
  - destruct sr_check as [?|[?|[_ ?]]]; auto.
Qed.

Lemma clp_srel_one no sa sb v : srel no sa sb -> i_mode sb = CODELENS ->
  Zlength (i_lens sa) = 320 -> Zlength (i_lens sb) = 320 -> 0 <= i_have sb < 320 ->
  srel no (set_i_have (set_i_lens sa (upd_Znth (i_have sa) (i_lens sa) v)) (i_have sa + 1))
          (set_i_have (set_i_lens sb (upd_Znth (i_have sb) (i_lens sb) v)) (i_have sb + 1)).
Proof.
  intros S Md La Lb Hh.
  destruct (sr_nlen _ _ _ S (or_intror Md)) as (E1 & E2 & E3).
  pose proof (sr_codelens _ _ _ S Md) as CL.
  assert (LL: forall k, 0 <= k < i_have sb + 1 ->
            Znth k (upd_Znth (i_have sa) (i_lens sa) v) = Znth k (upd_Znth (i_have sb) (i_lens sb) v)).
  { clear - CL E3 La Lb Hh. intros k Hk. rewrite E3. destruct (Z.eq_dec k (i_have sb)).
    + subst k. rewrite !upd_Znth_same by lia. reflexivity.
    + rewrite !upd_Znth_diff by lia. apply CL; lia. }
  clear CL.
  destruct S; constructor; simpl; auto.
  - intros _. split; [auto|]. split; [auto|]. rewrite E3; reflexivity.
  - intros E. exfalso. rewrite Md in E. cbv in E. discriminate.
Qed.

Lemma clp_fill_fields n len s :
  i_mode (lens_fill n len s) = i_mode s /\ i_wrap (lens_fill n len s) = i_wrap s /\
  i_head (lens_fill n len s) = i_head s /\ i_wbits (lens_fill n len s) = i_wbits s.
Proof.
  revert s; induction n; intros s; cbn [lens_fill]; [auto|].
  destruct (IHn (set_i_have (set_i_lens s (upd_Znth (i_have s) (i_lens s) len)) (i_have s + 1))) as (A & B & C & D).
  rewrite A, B, C, D. auto.
Qed.

Lemma clp_srel_fill : forall n no sa sb len, srel no sa sb -> i_mode sb = CODELENS ->
  Zlength (i_lens sa) = 320 -> Zlength (i_lens sb) = 320 -> 0 <= i_have sb -> i_have sb + Z.of_nat n <= 320 ->
  srel no (lens_fill n len sa) (lens_fill n len sb).
Proof.
  induction n; intros no sa sb len S Md La Lb H0 Hn; cbn [lens_fill]; [exact S|].
  destruct (sr_nlen _ _ _ S (or_intror Md)) as (_ & _ & E3).
  rewrite Nat2Z.inj_succ in Hn.
  apply IHn.
  - apply clp_srel_one; auto. lia.
  - exact Md.
  - simpl. rewrite upd_Znth_Zlength; lia.
  - simpl. rewrite upd_Znth_Zlength; lia.
  - simpl. lia.
  - simpl. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Kr through CODELENS's operations                                                               *)

Section Ops.
Variables (W0 wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z).

Lemma clp_mf_msg ma mb e : irk_mf ma = irk_mf mb -> irk_mf (set_m_msg ma e) = irk_mf (set_m_msg mb e).
Proof. unfold irk_mf. intros E. injection E; intros. destruct ma, mb; cbn in *; subst; reflexivity. Qed.

Lemma clp_kr_bad e ma mb : Kr W0 wrap src pos inp aout ma mb -> m_mode mb <> HEAD ->
  Kr W0 wrap src pos inp aout (set_bad ma e) (set_bad mb e).
Proof.
  intros K Hh.
  assert (K1: Kr W0 wrap src pos inp aout (set_m_msg ma (Some e)) (set_m_msg mb (Some e))).
  { apply (irk_mach _ _ _ _ _ _ ma mb); auto; try reflexivity.
    apply clp_mf_msg. apply (irk_mf_of_Kr _ _ _ _ _ _ _ _ K). }
  unfold set_bad, set_mode, upd_s.
  pose proof K1 as [[S] _ _ Kw Kh _ _ _].
  apply irk_state; auto.
  - apply clp_srel_bad; exact S.
  - simpl. cbv; discriminate.
Qed.

Lemma clp_kr_drop n ma mb : Kr W0 wrap src pos inp aout ma mb -> m_mode mb <> HEAD ->
  Kr W0 wrap src pos inp aout (dropbits n ma) (dropbits n mb).
Proof.
  intros K Hh. apply (irk_mach _ _ _ _ _ _ ma mb); auto; try reflexivity.
  apply irk_dropbits. apply (irk_mf_of_Kr _ _ _ _ _ _ _ _ K).
Qed.

Lemma clp_kr_need k n ma mb : Kr W0 wrap src pos inp aout ma mb -> m_mode mb <> HEAD ->
  Kr W0 wrap src pos inp aout (needbits_f k n ma) (needbits_f k n mb) /\
  m_s (needbits_f k n ma) = m_s ma /\ m_s (needbits_f k n mb) = m_s mb.
Proof.
  intros K Hh. destruct (irk_needbits k n ma mb (irk_mf_of_Kr _ _ _ _ _ _ _ _ K)) as (A & B & C & D & E & F).
  split; [|auto]. apply (irk_mach _ _ _ _ _ _ ma mb); auto.
Qed.

Lemma clp_kr_fill n len ma mb : Kr W0 wrap src pos inp aout ma mb -> m_mode mb = CODELENS ->
  Zlength (i_lens (m_s ma)) = 320 -> Zlength (i_lens (m_s mb)) = 320 -> 0 <= i_have (m_s mb) ->
  i_have (m_s mb) + Z.of_nat n <= 320 ->
  Kr W0 wrap src pos inp aout (upd_s ma (lens_fill n len)) (upd_s mb (lens_fill n len)).
Proof.
  intros K Md La Lb H0 Hn. pose proof K as [[S] _ _ Kw Kh _ _ _].
  destruct (clp_fill_fields n len (m_s ma)) as (A1 & A2 & A3 & A4).
  destruct (clp_fill_fields n len (m_s mb)) as (B1 & B2 & B3 & B4).
  unfold upd_s. apply irk_state; auto.
  - apply clp_srel_fill; auto.
  - rewrite B1. unfold m_mode in Md. rewrite Md. cbv; discriminate.
  - rewrite B2; auto.
  - rewrite B3; auto.
Qed.

Lemma clp_kr_lookup : forall k t nb ma mb, Kr W0 wrap src pos inp aout ma mb -> m_mode mb <> HEAD -> 0 <= nb ->
  (forall i, 0 <= i < 2 ^ nb ->
     tab_entry lenfix_list distfix_list (m_s ma) t i = tab_entry lenfix_list distfix_list (m_s mb) t i) ->
  forall ha ma1 oka hb mb1 okb,
  lookup1_f k lenfix_list distfix_list t nb ma = (ha, ma1, oka) ->
  lookup1_f k lenfix_list distfix_list t nb mb = (hb, mb1, okb) ->
  ha = hb /\ oka = okb /\ Kr W0 wrap src pos inp aout ma1 mb1 /\ m_s ma1 = m_s ma /\ m_s mb1 = m_s mb.
Proof.
  induction k; intros t nb ma mb K Hh Hnb TE ha ma1 oka hb mb1 okb EA EB; cbn [lookup1_f] in EA, EB;
    pose proof (kr_rel _ _ _ _ _ _ _ _ K) as MR;
    assert (BE: bitsn ma nb = bitsn mb nb) by (unfold bitsn; rewrite (mr_hold _ _ MR); reflexivity);
    assert (BR: 0 <= bitsn mb nb < 2 ^ nb) by (unfold bitsn; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia);
    rewrite BE, (TE _ BR) in EA.
  - injection EA as <- <- <-. injection EB as <- <- <-. auto.
  - rewrite (mr_bits _ _ MR) in EA.
    assert (HE: m_have ma = m_have mb) by (unfold m_have; rewrite (mr_inp _ _ MR), (mr_nx _ _ MR); reflexivity).
    rewrite HE in EA.
    destruct (e_bits _ <=? m_bits mb).
    + injection EA as <- <- <-. injection EB as <- <- <-. auto.
    + destruct (m_have mb =? 0).
      * injection EA as <- <- <-. injection EB as <- <- <-. split; [auto|]. split; [auto|].
        split; [|split; reflexivity].
        apply (irk_mach _ _ _ _ _ _ ma mb); auto; try reflexivity.
        apply irk_leave. apply (irk_mf_of_Kr _ _ _ _ _ _ _ _ K).
      * assert (K1: Kr W0 wrap src pos inp aout (pull ma) (pull mb)).
        { apply (irk_mach _ _ _ _ _ _ ma mb); auto; try reflexivity.
          apply irk_pull. apply (irk_mf_of_Kr _ _ _ _ _ _ _ _ K). }
        destruct (IHk t nb (pull ma) (pull mb) K1 Hh Hnb TE ha ma1 oka hb mb1 okb EA EB) as (A & B & C & D & E).
        auto.
Qed.

End Ops.

(* ---------------------------------------------------------------------------------------------- *)
(* One pass and the loop                                                                          *)

Definition clrel (W0 wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (oa ob: clout) : Prop :=
  match oa, ob with
  | CLnext ma', CLnext mb' => Kr W0 wrap src pos inp aout ma' mb'
  | CLleave ma', CLleave mb' => Kr W0 wrap src pos inp aout ma' mb'
  | CLbad ma', CLbad mb' => Kr W0 wrap src pos inp aout ma' mb'
  | _, _ => False
  end.

Lemma clp_ms_drop n m : m_s (dropbits n m) = m_s m.
Proof. reflexivity. Qed.

Lemma clp_mode_bad m e : m_mode (set_bad m e) = BAD.
Proof. reflexivity. Qed.

Lemma clp_one_fill v :
  (fun s => set_i_have (set_i_lens s (upd_Znth (i_have s) (i_lens s) v)) (i_have s + 1)) = lens_fill 1 v.
Proof. reflexivity. Qed.

Section Pass.
Variables (W0 wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z).

Lemma clp_tail ma mb lena lenb copya copyb : Kr W0 wrap src pos inp aout ma mb -> m_mode mb = CODELENS ->
  lena = lenb -> copya = copyb -> 0 <= copyb ->
  Zlength (i_lens (m_s ma)) = 320 -> Zlength (i_lens (m_s mb)) = 320 -> 0 <= i_have (m_s mb) ->
  i_nlen (m_s mb) + i_ndist (m_s mb) <= 320 ->
  clrel W0 wrap src pos inp aout
    (if m_mode ma =? BAD then CLbad ma else
     if i_nlen (m_s ma) + i_ndist (m_s ma) <? i_have (m_s ma) + copya then CLbad (set_bad ma M_repeat) else
     CLnext (upd_s ma (lens_fill (Z.to_nat copya) lena)))
    (if m_mode mb =? BAD then CLbad mb else
     if i_nlen (m_s mb) + i_ndist (m_s mb) <? i_have (m_s mb) + copyb then CLbad (set_bad mb M_repeat) else
     CLnext (upd_s mb (lens_fill (Z.to_nat copyb) lenb))).
Proof.
  intros K Md <- <- Hc La Lb H0 Hn. pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) as S.
  assert (MdS: i_mode (m_s mb) = CODELENS) by exact Md.
  assert (MdA: m_mode ma = CODELENS) by (unfold m_mode; rewrite (sr_mode _ _ _ S); exact Md).
  destruct (sr_nlen _ _ _ S (or_intror MdS)) as (E1 & E2 & E3).
  rewrite MdA, Md, E1, E2, E3. change (CODELENS =? BAD) with false. cbv iota.
  destruct (Z.ltb_spec (i_nlen (m_s mb) + i_ndist (m_s mb)) (i_have (m_s mb) + copya)); cbn [clrel].
  - apply clp_kr_bad; auto. rewrite Md. cbv; discriminate.
  - apply clp_kr_fill; auto. rewrite Z2Nat.id; lia.
Qed.

Lemma clp_iter ma mb : Kr W0 wrap src pos inp aout ma mb -> mwf3x ma -> mwf3x mb -> m_leave mb = 0 ->
  m_mode mb = CODELENS ->
  clrel W0 wrap src pos inp aout (codelens_iter lenfix_list distfix_list ma) (codelens_iter lenfix_list distfix_list mb).
Proof.
  intros K Wa Wb L Md. pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) as S.
  assert (MdS: i_mode (m_s mb) = CODELENS) by exact Md.
  assert (Hh: m_mode mb <> HEAD) by (rewrite Md; cbv; discriminate).
  pose proof (mw_s _ (Zlib.proof.inflate.Step3Inv.m3_w _ Wa)) as SWa. pose proof (mw_s _ (Zlib.proof.inflate.Step3Inv.m3_w _ Wb)) as SWb.
  destruct (sw_lens _ SWa) as [ZLa _]. destruct (sw_lens _ SWb) as [ZLb _].
  pose proof (sw_lenbits _ SWb) as LBr.
  destruct (md_codelens _ (mw_md _ (Zlib.proof.inflate.Step3Inv.m3_w _ Wb)) MdS) as (H0 & Hnl & Hnd & _ & _ & _).
  destruct (sr_nlen _ _ _ S (or_intror MdS)) as (E1 & E2 & E3).
  pose proof (sr_cltab _ _ _ S MdS) as CT.
  assert (TE: forall i, 0 <= i < 2 ^ i_lenbits (m_s mb) ->
     tab_entry lenfix_list distfix_list (m_s ma) (i_lencode (m_s mb)) i =
     tab_entry lenfix_list distfix_list (m_s mb) (i_lencode (m_s mb)) i)
    by (intros i Hi; exact (proj1 (CT i Hi))).
  unfold codelens_iter, lookup1, needbits.
  rewrite (sr_lencode _ _ _ S), (sr_lenbits _ _ _ S (or_introl MdS)).
  destruct (lookup1_f 3 lenfix_list distfix_list (i_lencode (m_s mb)) (i_lenbits (m_s mb)) ma)
    as [[ha ma1] oka] eqn:EA.
  destruct (lookup1_f 3 lenfix_list distfix_list (i_lencode (m_s mb)) (i_lenbits (m_s mb)) mb)
    as [[hb mb1] okb] eqn:EB.
  destruct (clp_kr_lookup W0 wrap src pos inp aout 3 (i_lencode (m_s mb)) (i_lenbits (m_s mb)) ma mb K Hh ltac:(lia) TE _ _ _ _ _ _ EA EB)
    as (<- & <- & K1 & Sa1 & Sb1).
  assert (Hh1: m_mode mb1 <> HEAD) by (unfold m_mode; rewrite Sb1; exact Hh).
  destruct oka; cbv beta iota zeta delta [negb]; [|exact K1].
  destruct (e_val ha <? 16).
  - cbn [clrel]. rewrite clp_one_fill. apply clp_kr_fill.
    + apply clp_kr_drop; auto.
    + unfold m_mode. rewrite clp_ms_drop, Sb1. exact Md.
    + rewrite clp_ms_drop, Sa1. exact ZLa.
    + rewrite clp_ms_drop, Sb1. exact ZLb.
    + rewrite clp_ms_drop, Sb1. lia.
    + rewrite clp_ms_drop, Sb1. simpl. lia.
  - destruct (e_val ha =? 16); [|destruct (e_val ha =? 17)].
    + destruct (clp_kr_need W0 wrap src pos inp aout 4 (e_bits ha + 2) ma1 mb1 K1 Hh1) as (K2 & Sa2 & Sb2).
      set (na := needbits_f 4 (e_bits ha + 2) ma1) in *. set (nb := needbits_f 4 (e_bits ha + 2) mb1) in *.
      rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K2)).
      destruct (m_leave nb =? 1); cbv beta iota zeta delta [negb]; [exact K2|].
      assert (Hh2: m_mode nb <> HEAD) by (unfold m_mode; rewrite Sb2, Sb1; exact Hh).
      pose proof (clp_kr_drop W0 wrap src pos inp aout (e_bits ha) na nb K2 Hh2) as K3.
      assert (EH: i_have (m_s (dropbits (e_bits ha) na)) = i_have (m_s (dropbits (e_bits ha) nb)))
        by (rewrite !clp_ms_drop, Sa2, Sb2, Sa1, Sb1; exact E3).
      rewrite EH.
      destruct (Z.eqb_spec (i_have (m_s (dropbits (e_bits ha) nb))) 0) as [Z0|Z0];
        cbv beta iota zeta delta [negb].
      * rewrite !clp_mode_bad, Z.eqb_refl. cbn [clrel]. apply clp_kr_bad; auto.
      * rewrite clp_ms_drop, Sb2, Sb1 in Z0.
        assert (Hh3: m_mode (dropbits (e_bits ha) nb) <> HEAD) by exact Hh2.
        apply clp_tail.
        -- apply clp_kr_drop; auto.
        -- unfold m_mode. rewrite !clp_ms_drop, Sb2, Sb1. exact Md.
        -- rewrite !clp_ms_drop, Sa2, Sb2, Sa1, Sb1. apply (sr_codelens _ _ _ S MdS). lia.
        -- unfold bitsn. rewrite (mr_hold _ _ (kr_rel _ _ _ _ _ _ _ _ K3)). reflexivity.
        -- pose proof (Z.mod_pos_bound (m_hold (dropbits (e_bits ha) nb)) (2 ^ 2) ltac:(lia)).
           unfold bitsn. lia.
        -- rewrite !clp_ms_drop, Sa2, Sa1. exact ZLa.
        -- rewrite !clp_ms_drop, Sb2, Sb1. exact ZLb.
        -- rewrite !clp_ms_drop, Sb2, Sb1. lia.
        -- rewrite !clp_ms_drop, Sb2, Sb1. lia.
    + destruct (clp_kr_need W0 wrap src pos inp aout 4 (e_bits ha + 3) ma1 mb1 K1 Hh1) as (K2 & Sa2 & Sb2).
      set (na := needbits_f 4 (e_bits ha + 3) ma1) in *. set (nb := needbits_f 4 (e_bits ha + 3) mb1) in *.
      rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K2)).
      destruct (m_leave nb =? 1); cbv beta iota zeta delta [negb]; [exact K2|].
      assert (Hh2: m_mode nb <> HEAD) by (unfold m_mode; rewrite Sb2, Sb1; exact Hh).
      pose proof (clp_kr_drop W0 wrap src pos inp aout (e_bits ha) na nb K2 Hh2) as K3.
      apply clp_tail.
      * apply clp_kr_drop; auto.
      * unfold m_mode. rewrite !clp_ms_drop, Sb2, Sb1. exact Md.
      * reflexivity.
      * unfold bitsn. rewrite (mr_hold _ _ (kr_rel _ _ _ _ _ _ _ _ K3)). reflexivity.
      * pose proof (Z.mod_pos_bound (m_hold (dropbits (e_bits ha) nb)) (2 ^ 3) ltac:(lia)).
        unfold bitsn. lia.
      * rewrite !clp_ms_drop, Sa2, Sa1. exact ZLa.
      * rewrite !clp_ms_drop, Sb2, Sb1. exact ZLb.
      * rewrite !clp_ms_drop, Sb2, Sb1. lia.
      * rewrite !clp_ms_drop, Sb2, Sb1. lia.
    + destruct (clp_kr_need W0 wrap src pos inp aout 4 (e_bits ha + 7) ma1 mb1 K1 Hh1) as (K2 & Sa2 & Sb2).
      set (na := needbits_f 4 (e_bits ha + 7) ma1) in *. set (nb := needbits_f 4 (e_bits ha + 7) mb1) in *.
      rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K2)).
      destruct (m_leave nb =? 1); cbv beta iota zeta delta [negb]; [exact K2|].
      assert (Hh2: m_mode nb <> HEAD) by (unfold m_mode; rewrite Sb2, Sb1; exact Hh).
      pose proof (clp_kr_drop W0 wrap src pos inp aout (e_bits ha) na nb K2 Hh2) as K3.
      apply clp_tail.
      * apply clp_kr_drop; auto.
      * unfold m_mode. rewrite !clp_ms_drop, Sb2, Sb1. exact Md.
      * reflexivity.
      * unfold bitsn. rewrite (mr_hold _ _ (kr_rel _ _ _ _ _ _ _ _ K3)). reflexivity.
      * pose proof (Z.mod_pos_bound (m_hold (dropbits (e_bits ha) nb)) (2 ^ 7) ltac:(lia)).
        unfold bitsn. lia.
      * rewrite !clp_ms_drop, Sa2, Sa1. exact ZLa.
      * rewrite !clp_ms_drop, Sb2, Sb1. exact ZLb.
      * rewrite !clp_ms_drop, Sb2, Sb1. lia.
      * rewrite !clp_ms_drop, Sb2, Sb1. lia.
Qed.

Lemma clp_loop : forall k ma mb, Kr W0 wrap src pos inp aout ma mb -> mwf3x ma -> mwf3x mb -> m_leave mb = 0 ->
  m_mode mb = CODELENS ->
  clrel W0 wrap src pos inp aout (codelens_loop lenfix_list distfix_list k ma)
    (codelens_loop lenfix_list distfix_list k mb).
Proof.
  induction k; intros ma mb K Wa Wb L Md; [exact K|].
  pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) as S.
  assert (MdS: i_mode (m_s mb) = CODELENS) by exact Md.
  assert (MdA: m_mode ma = CODELENS) by (unfold m_mode; rewrite (sr_mode _ _ _ S); exact Md).
  assert (LA: m_leave ma = 0) by (rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K)); exact L).
  destruct (sr_nlen _ _ _ S (or_intror MdS)) as (E1 & E2 & E3).
  cbn [codelens_loop]. rewrite E1, E2, E3.
  destruct (Z.ltb_spec (i_have (m_s mb)) (i_nlen (m_s mb) + i_ndist (m_s mb))) as [Hlt|Hge]; [|exact K].
  pose proof (clp_iter ma mb K Wa Wb L Md) as R.
  pose proof (Zlib.proof.inflate.Step3Tables.tb_codelens_iter ma Wa LA MdA ltac:(rewrite E1, E2, E3; exact Hlt))
    as CA.
  pose proof (Zlib.proof.inflate.Step3Tables.tb_codelens_iter mb Wb L Md Hlt) as CB.
  destruct (codelens_iter lenfix_list distfix_list ma) as [a|a|a];
    destruct (codelens_iter lenfix_list distfix_list mb) as [b|b|b];
    cbn [clrel Zlib.proof.inflate.Step3Tables.cl_ok] in R, CA, CB |- *; try contradiction; auto.
  destruct CA as (Wa' & _ & _ & _). destruct CB as (Wb' & Lb' & Mdb' & _).
  apply IHk; auto.
Qed.

End Pass.

Lemma irt_clloop_ok : irt_clloop_stmt.
Proof.
  intros k W0 wrap src pos inp aout ma mb K Wa Wb L Md.
  exact (clp_loop W0 wrap src pos inp aout k ma mb K Wa Wb L Md).
Qed.
