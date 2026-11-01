(* Law api_reset, TABLE / LENLENS / CODELENS: CODELENS in lockstep under the wide invariant mwf3xW, its while
   loop (x_inflate_reset's IRTabCLLoop.v) and the LENS and DISTS tables after it (IRTabCLPost.v).  Only the
   lemmas that take the invariant are restated; the rest (the relation under CODELENS's state changes, the
   lookups, the tables in the final code space) is reused from those files. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Require Import Zlib.proof.harness.inflate_reset.IRTabKit.
Require Import Zlib.proof.harness.inflate_reset.IRTabCLLoop.
Require Import Zlib.proof.harness.inflate_reset.IRTabCLPost.
Require Import Zlib.proof.inflate.Step3Tables.
Require Import Zlib.proof.inflate.StepWTables.
Require Import Zlib.proof.harness.api_reset.ARSimTabKit.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop                                                                                       *)

Section PassW.
Variables (W0 wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z).

Lemma clp_iterW ma mb : Kr W0 wrap src pos inp aout ma mb -> mwf3xW ma -> mwf3xW mb -> m_leave mb = 0 ->
  m_mode mb = CODELENS ->
  clrel W0 wrap src pos inp aout (codelens_iter lenfix_list distfix_list ma) (codelens_iter lenfix_list distfix_list mb).
Proof.
  intros K Wa Wb L Md. pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) as S.
  assert (MdS: i_mode (m_s mb) = CODELENS) by exact Md.
  assert (Hh: m_mode mb <> HEAD) by (rewrite Md; cbv; discriminate).
  pose proof (mwW_s _ (m3W_w _ Wa)) as SWa. pose proof (mwW_s _ (m3W_w _ Wb)) as SWb.
  destruct (sw_lens _ SWa) as [ZLa _]. destruct (sw_lens _ SWb) as [ZLb _].
  pose proof (sw_lenbits _ SWb) as LBr.
  destruct (md_codelens _ (mwW_md _ (m3W_w _ Wb)) MdS) as (H0 & Hnl & Hnd & _ & _ & _).
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

Lemma clp_loopW : forall k ma mb, Kr W0 wrap src pos inp aout ma mb -> mwf3xW ma -> mwf3xW mb -> m_leave mb = 0 ->
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
  pose proof (clp_iterW ma mb K Wa Wb L Md) as R.
  pose proof (Zlib.proof.inflate.StepWTables.tb_codelens_iter ma Wa LA MdA ltac:(rewrite E1, E2, E3; exact Hlt))
    as CA.
  pose proof (Zlib.proof.inflate.StepWTables.tb_codelens_iter mb Wb L Md Hlt) as CB.
  destruct (codelens_iter lenfix_list distfix_list ma) as [a|a|a];
    destruct (codelens_iter lenfix_list distfix_list mb) as [b|b|b];
    cbn [clrel Zlib.proof.inflate.StepWTables.cl_ok] in R, CA, CB |- *; try contradiction; auto.
  destruct CA as (Wa' & _ & _ & _). destruct CB as (Wb' & Lb' & Mdb' & _).
  apply IHk; auto.
Qed.

End PassW.

Lemma irt_clloop_okW : irt_clloop_stmtW.
Proof.
  intros k W0 wrap src pos inp aout ma mb K Wa Wb L Md.
  exact (clp_loopW W0 wrap src pos inp aout k ma mb K Wa Wb L Md).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* After the loop                                                                                 *)

Lemma irc_sideW (C3: Zlib.proof.inflate.Cover3.cover3_stmt) m :
  mwf3xW m -> m_mode m = CODELENS -> i_nlen (m_s m) + i_ndist (m_s m) <= i_have (m_s m) ->
  inputs_ok LENS (irc_L1 (m_s m)) 9 /\ cap_ok LENS (irc_L1 (m_s m)) 9 (Zlength (irc_o1 (m_s m))) /\
  Forall entry_ok (irc_o1 (m_s m)) /\ Zlength (irc_o1 (m_s m)) = ENOUGH_CODES /\
  inputs_ok DISTS (irc_L2 (m_s m)) 6 /\
  (forall root used t, inflate_table_model LENS (irc_L1 (m_s m)) 9 (irc_o1 (m_s m)) = ROk root used t ->
     Zlength t = ENOUGH_CODES /\ Forall entry_ok t /\ tab_ok LENS t root used /\ 1 <= used <= ENOUGH_LENS /\
     cap_ok DISTS (irc_L2 (m_s m)) 6 (Zlength (sublist used ENOUGH_CODES t)) /\
     Forall entry_ok (sublist used ENOUGH_CODES t) /\
     Zlength (sublist used ENOUGH_CODES t) = ENOUGH_CODES - used /\
     (forall root2 used2 u,
        inflate_table_model DISTS (irc_L2 (m_s m)) 6 (sublist used ENOUGH_CODES t) = ROk root2 used2 u ->
        tab_ok DISTS u root2 used2 /\ used2 <= ENOUGH_CODES - used)).
Proof.
  intros W1 Md1 Hh0.
  pose proof (irk_cover2 C3) as C2.
  pose proof (mwW_md _ (m3W_w _ W1)) as MD. pose proof (mwW_s _ (m3W_w _ W1)) as S.
  destruct (md_codelens _ MD Md1) as (H0 & Hnl & Hnd & LC & TV & LE).
  destruct (sw_lens _ S) as [ZL FL]. destruct (sw_codes _ S) as [ZC FC].
  set (s1 := irc_s1 (m_s m)).
  assert (S1: swf s1) by (destruct S; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES; lia).
  assert (IN1: inputs_ok LENS (sublist 0 (0 + i_nlen s1) (i_lens s1)) 9).
  { unfold inputs_ok. simpl. rewrite Zlength_sublist by lia. split; [unfold LENS; lia|].
    split; [unfold max_codes; simpl; lia|]. split; [|lia].
    apply tb_forall_sublist; try lia. intros k Hk. split.
    - rewrite Forall_forall in FL. apply FL. apply Znth_In; lia.
    - apply LE; lia. }
  assert (CAP1: cap_ok LENS (sublist 0 (0 + i_nlen s1) (i_lens s1)) 9 (ENOUGH_CODES - i_next s1)).
  { unfold cap_ok. simpl. unfold LENS, CODES, DISTS, ENOUGH_LENS, ENOUGH_CODES. split; [intros; lia|].
    split; intros; lia. }
  assert (IN2: inputs_ok DISTS (irc_L2 (m_s m)) 6).
  { unfold inputs_ok, irc_L2. rewrite Zlength_sublist by lia. split; [unfold DISTS; lia|].
    split; [unfold max_codes; simpl; lia|]. split; [|lia].
    apply tb_forall_sublist; try lia. intros k Hk. split.
    - rewrite Forall_forall in FL. apply FL. apply Znth_In; lia.
    - apply LE; lia. }
  assert (ZO: Zlength (irc_o1 (m_s m)) = ENOUGH_CODES)
    by (unfold irc_o1; rewrite Zlength_sublist; unfold ENOUGH_CODES in *; lia).
  assert (FO: Forall entry_ok (irc_o1 (m_s m))) by (unfold irc_o1; apply Forall_sublist; auto).
  split; [exact IN1|]. split; [unfold cap_ok, LENS, CODES, DISTS, ENOUGH_LENS; rewrite ZO; unfold ENOUGH_CODES; split; [intros; lia|]; split; intros; lia|].
  split; [exact FO|]. split; [exact ZO|]. split; [exact IN2|].
  intros root used t M.
  destruct (call_table LENS 0 (i_nlen s1) 9 s1) as [[[r1 c1] n1] b1] eqn:CT1.
  destruct (tb_call_table LENS 0 (i_nlen s1) 9 s1 r1 c1 n1 b1 C2 S1 ltac:(lia) ltac:(simpl; lia) ltac:(simpl; lia)
              IN1 CAP1 ltac:(unfold LENS, CODES; lia) CT1) as (ZC1 & FC1 & R1 & Rn1 & Ry1).
  unfold call_table in CT1. change (i_next s1) with 0 in CT1.
  change (sublist 0 (0 + i_nlen s1) (i_lens s1)) with (irc_L1 (m_s m)) in CT1.
  change (sublist 0 ENOUGH_CODES (i_codes s1)) with (irc_o1 (m_s m)) in CT1.
  rewrite M in CT1. cbn [it_ret it_tab it_adv it_bits] in CT1. inversion CT1; subst r1 c1 n1 b1; clear CT1.
  destruct (Ry1 eq_refl) as (used1 & t1 & M1 & En1 & Ec1 & Zt1 & T1 & U1 & U1L).
  change (sublist 0 (0 + i_nlen s1) (i_lens s1)) with (irc_L1 (m_s m)) in M1.
  change (sublist (i_next s1) ENOUGH_CODES (i_codes s1)) with (irc_o1 (m_s m)) in M1.
  rewrite M in M1. inversion M1; subst used1 t1; clear M1.
  specialize (U1L eq_refl). change (i_next s1) with 0 in *.
  assert (Ft: Forall entry_ok t).
  { exact FC1. }
  split; [lia|]. split; [exact Ft|]. split; [exact T1|]. split; [lia|].
  assert (ZO2: Zlength (sublist used ENOUGH_CODES t) = ENOUGH_CODES - used)
    by (rewrite Zlength_sublist; unfold ENOUGH_CODES, ENOUGH_LENS in *; lia).
  assert (CAP2: cap_ok DISTS (irc_L2 (m_s m)) 6 (Zlength (sublist used ENOUGH_CODES t))).
  { rewrite ZO2. unfold cap_ok, LENS, CODES, DISTS, ENOUGH_LENS, ENOUGH_DISTS, ENOUGH_CODES in *.
    split; [intros; lia|]. split; intros; lia. }
  assert (FO2: Forall entry_ok (sublist used ENOUGH_CODES t)) by (apply Forall_sublist; auto).
  split; [exact CAP2|]. split; [exact FO2|]. split; [exact ZO2|].
  intros root2 used2 u M2.
  destruct (C3 DISTS (irc_L2 (m_s m)) 6 _ root2 used2 u IN2 ltac:(unfold DISTS, CODES; lia) CAP2 FO2 M2)
    as (T2 & U2 & _).
  split; [exact T2|]. lia.
Qed.

Lemma irt_clpost_okW : Zlib.proof.inflate.Cover3.cover3_stmt -> tabdet_stmt -> irt_clpost_stmtW.
Proof.
  intros C3 TD W0 wrap src pos inp aout ma mb K Wa Wb L Md Hh.
  pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) as S.
  assert (Mdb: i_mode (m_s mb) = CODELENS) by exact Md.
  assert (Hhd: m_mode mb <> HEAD) by (rewrite Md; unfold CODELENS, HEAD; lia).
  assert (Ma: m_mode ma = CODELENS) by (unfold m_mode in *; rewrite (sr_mode _ _ _ S); exact Md).
  destruct (sr_nlen _ _ _ S (or_intror Mdb)) as (En & Ed & Ehv).
  assert (Ha: i_nlen (m_s ma) + i_ndist (m_s ma) <= i_have (m_s ma)) by lia.
  destruct (irc_sideW C3 ma Wa Ma Ha) as (INa & CAPa & FOa & ZOa & IN2a & Ra).
  destruct (irc_sideW C3 mb Wb Md Hh) as (INb & CAPb & FOb & ZOb & IN2b & Rb).
  pose proof (mwW_md _ (m3W_w _ Wb)) as MD. destruct (md_codelens _ MD Mdb) as (_ & Hnl & Hnd & _).
  pose proof (sw_lens _ (mwW_s _ (m3W_w _ Wa))) as [ZLa _].
  pose proof (sw_lens _ (mwW_s _ (m3W_w _ Wb))) as [ZLb _].
  pose proof (sr_codelens _ _ _ S Mdb) as CL.
  assert (EL1: irc_L1 (m_s ma) = irc_L1 (m_s mb)).
  { unfold irc_L1. rewrite En. apply irc_sub_eq; try lia. intros k Hk. apply CL; lia. }
  assert (EL2: irc_L2 (m_s ma) = irc_L2 (m_s mb)).
  { unfold irc_L2. rewrite En, Ed. apply irc_sub_eq; try lia. intros k Hk. apply CL; lia. }
  assert (E256: Znth 256 (i_lens (m_s ma)) = Znth 256 (i_lens (m_s mb))) by (apply CL; lia).
  rewrite (irc_eq ma), (irc_eq mb). unfold irc_rhs. cbv zeta.
  rewrite E256. destruct (Znth 256 (i_lens (m_s mb)) =? 0).
  { cbn [irt_rr]. apply irc_bad0; auto. }
  rewrite EL1 in *. rewrite EL2 in *.
  destruct (TD LENS (irc_L1 (m_s mb)) 9 (irc_o1 (m_s ma)) (irc_o1 (m_s mb)) INb
              ltac:(unfold LENS, CODES; lia) CAPa FOa ltac:(lia) FOb) as (Er & Eadv & Eb & Ok).
  rewrite Er, Eadv, Eb.
  destruct (Z.eqb_spec (it_ret (inflate_table_model LENS (irc_L1 (m_s mb)) 9 (irc_o1 (m_s mb)))) 0) as [R0|R0].
  2:{ cbn [negb irt_rr]. rewrite irc_bad_eq, irc_bad_eq.
      apply irc_kr_new; auto; [unfold BAD, HEAD; lia | apply irc_srel_badF; auto | reflexivity ..]. }
  cbn [negb].
  destruct (inflate_table_model LENS (irc_L1 (m_s mb)) 9 (irc_o1 (m_s ma))) as [ | ta | root used t1] eqn:MA;
    cbn [it_ret] in Er; [rewrite <- Er in R0; discriminate .. |].
  destruct (Ok root used t1 eq_refl) as (t2 & MB & TL1).
  rewrite MB. cbn [it_ret it_tab it_adv it_bits].
  rewrite !sublist_nil, !app_nil_l, !Z.add_0_l.
  destruct (Ra root used t1 eq_refl) as (Zt1 & Ft1 & T1 & U1 & CAP2a & FO2a & ZO2a & Da).
  destruct (Rb root used t2 MB) as (Zt2 & Ft2 & T2 & U2 & CAP2b & FO2b & ZO2b & Db).
  destruct (TD DISTS (irc_L2 (m_s mb)) 6 (sublist used ENOUGH_CODES t1) (sublist used ENOUGH_CODES t2) IN2b
              ltac:(unfold DISTS, CODES; lia) CAP2a FO2a ltac:(lia) FO2b) as (Er2 & Eadv2 & Eb2 & Ok2).
  rewrite Er2, Eadv2, Eb2.
  destruct (Z.eqb_spec (it_ret (inflate_table_model DISTS (irc_L2 (m_s mb)) 6 (sublist used ENOUGH_CODES t2))) 0)
    as [R2|R2].
  2:{ cbn [negb irt_rr]. rewrite irc_bad_eq, irc_bad_eq.
      apply irc_kr_new; auto; [unfold BAD, HEAD; lia | apply irc_srel_badG; auto | reflexivity ..]. }
  cbn [negb].
  destruct (inflate_table_model DISTS (irc_L2 (m_s mb)) 6 (sublist used ENOUGH_CODES t1))
    as [ | ua | root2 used2 u1] eqn:MA2; cbn [it_ret] in Er2; [rewrite <- Er2 in R2; discriminate .. |].
  destruct (Ok2 root2 used2 u1 eq_refl) as (u2 & MB2 & TL2).
  rewrite MB2. cbn [it_ret it_tab it_adv it_bits irt_rr].
  destruct (Da root2 used2 u1 eq_refl) as [TD2 UD2].
  assert (Zs1: Zlength (sublist 0 used t1) = used) by (rewrite Zlength_sublist; unfold ENOUGH_CODES, ENOUGH_LENS in *; lia).
  assert (Zs2: Zlength (sublist 0 used t2) = used) by (rewrite Zlength_sublist; unfold ENOUGH_CODES, ENOUGH_LENS in *; lia).
  split; [|split; [exact L | reflexivity]].
  rewrite irc_len_eq, irc_len_eq.
  change (set_m_ret ma 0) with (set_m_msg (set_m_ret ma 0) (m_msg ma)).
  change (set_m_ret mb 0) with (set_m_msg (set_m_ret mb 0) (m_msg mb)).
  rewrite (mr_msg _ _ (kr_rel _ _ _ _ _ _ _ _ K)).
  apply irc_kr_new; auto; [unfold LEN_, HEAD; lia | | reflexivity ..].
  apply irc_srel_len; [exact S | exact Mdb | |].
  - apply irc_tl_lens; auto; unfold ENOUGH_CODES, ENOUGH_LENS in *; lia.
  - apply irc_tl_dists with used2; auto.
Qed.


(* CODELENS: the loop, then the tables *)
Lemma irst_clW : irt_clloop_stmtW -> irt_clpost_stmtW -> irt_cl_stmtW.
Proof.
  intros LP PO W0 wrap src pos inp aout ma mb K Wa Wb L Md.
  pose proof (LP 320%nat W0 wrap src pos inp aout ma mb K Wa Wb L Md) as R.
  assert (Ma: m_mode ma = CODELENS)
    by (unfold m_mode in *; rewrite (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K))); exact Md).
  assert (La: m_leave ma = 0) by (rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K)); exact L).
  pose proof (Zlib.proof.inflate.StepWTables.tb_codelens_loop 320 mb Wb L Md) as LB.
  pose proof (Zlib.proof.inflate.StepWTables.tb_codelens_loop 320 ma Wa La Ma) as LA.
  pose proof (sw_have _ (mwW_s _ (m3W_w _ Wb))) as Hb.
  pose proof (sw_have _ (mwW_s _ (m3W_w _ Wa))) as Ha.
  specialize (LB ltac:(simpl; lia)). specialize (LA ltac:(simpl; lia)).
  unfold irt_cl.
  destruct (codelens_loop lenfix_list distfix_list 320 ma) as [ma'|ma'|ma'];
    destruct (codelens_loop lenfix_list distfix_list 320 mb) as [mb'|mb'|mb']; try contradiction;
    cbn [irt_rr]; auto.
  destruct LA as (Wa' & _). destruct LB as (Wb' & Lb' & Mb' & Hf).
  apply PO; auto.
Qed.