(* Law api_reset, TABLE / LENLENS / CODELENS: LENLENS in lockstep under the wide invariant mwf3xW, its loop,
   the zeros, the code length code, then CODELENS (x_inflate_reset's IRTabLL.v).  Only the lemmas that take
   the invariant are restated; the others are reused from IRTabLL.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Require Import Zlib.proof.harness.inflate_reset.IRTabKit.
Require Import Zlib.proof.harness.inflate_reset.IRTabLL.
Require Import Zlib.proof.inflate.Step3Tables.
Require Import Zlib.proof.inflate.StepWTables.
Require Import Zlib.proof.harness.api_reset.ARSimTabKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma irl_step_wfW m : mwf3xW m -> m_mode m = LENLENS -> m_leave m = 0 ->
  i_have (m_s m) < i_ncode (m_s m) -> m_leave (needbits 3 m) <> 1 ->
  mwf3xW (irl_step m) /\ m_mode (irl_step m) = LENLENS /\ m_leave (irl_step m) = 0.
Proof.
  intros W Md L H N.
  destruct (tb_lenlens_loop 1 m W Md L) as [W1 M1].
  rewrite irl_loop_S, (proj2 (Z.ltb_lt _ _) H), (proj2 (Z.eqb_neq _ _) N) in W1, M1.
  cbn [lenlens_loop] in W1, M1. split; [exact W1|]. split; [exact M1|].
  destruct (needbits_ok 3 m (m3W_w _ W) L ltac:(lia) N) as [_ NL].
  exact NL.
Qed.

Lemma irl_kr_stepW W0 wrap src pos inp aout ma mb :
  Kr W0 wrap src pos inp aout ma mb -> mwf3xW ma -> mwf3xW mb -> m_mode mb = LENLENS ->
  i_have (m_s mb) < i_ncode (m_s mb) ->
  Kr W0 wrap src pos inp aout (needbits 3 ma) (needbits 3 mb) /\
  (m_leave (needbits 3 mb) <> 1 -> Kr W0 wrap src pos inp aout (irl_step ma) (irl_step mb)).
Proof.
  intros K Wa Wb Md Hc.
  assert (Hh: m_mode mb <> HEAD) by (rewrite Md; unfold LENLENS, HEAD; lia).
  destruct (irk_needbits 4 3 ma mb (irk_mf_of_Kr _ _ _ _ _ _ _ _ K)) as (E2 & Sa2 & Sb2 & I2 & A2 & O2).
  assert (K2: Kr W0 wrap src pos inp aout (needbits 3 ma) (needbits 3 mb)) by (apply irk_mach with ma mb; auto).
  split; [exact K2|]. intros _.
  pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K2)) as S2.
  pose proof (kr_wrap _ _ _ _ _ _ _ _ K2) as Kw2. pose proof (kr_head _ _ _ _ _ _ _ _ K2) as Kh2.
  assert (Hd: bitsn (needbits 3 ma) 3 = bitsn (needbits 3 mb) 3) by (unfold irk_mf, bitsn, needbits in *; congruence).
  pose proof (mwW_md _ (m3W_w _ Wb)) as MD. pose proof (mwW_s _ (m3W_w _ Wb)) as Sb.
  destruct (md_lenlens _ MD Md) as (Hc1 & H0 & _).
  destruct (sw_lens _ (mwW_s _ (m3W_w _ Wa))) as [ZLa _]. destruct (sw_lens _ Sb) as [ZLb _].
  unfold irl_step. rewrite Hd.
  change (needbits_f 4 3 ma) with (needbits 3 ma) in Sa2, E2.
  change (needbits_f 4 3 mb) with (needbits 3 mb) in Sb2, E2.
  set (ma2 := needbits 3 ma) in *. set (mb2 := needbits 3 mb) in *. clearbody ma2 mb2.
  assert (Md2: i_mode (m_s mb2) = LENLENS) by (rewrite Sb2; exact Md).
  apply irk_mach with (upd_s ma2 (fun _ => set_i_have (set_i_lens (m_s ma2) (upd_Znth (Znth (i_have (m_s ma2)) order)
        (i_lens (m_s ma2)) (bitsn mb2 3))) (i_have (m_s ma2) + 1)))
     (upd_s mb2 (fun _ => set_i_have (set_i_lens (m_s mb2) (upd_Znth (Znth (i_have (m_s mb2)) order)
        (i_lens (m_s mb2)) (bitsn mb2 3))) (i_have (m_s mb2) + 1))); try reflexivity.
  - unfold upd_s. apply irk_state; auto.
    + apply irl_srel_upd; auto; rewrite ?Sa2, ?Sb2; auto; lia.
    + cbn. rewrite Md2. unfold LENLENS, HEAD; lia.
  - unfold m_mode, upd_s; cbn. rewrite Md2. unfold LENLENS, HEAD; lia.
  - apply irk_dropbits. apply irk_set_s. exact E2.
Qed.

Lemma irl_loopW : forall k W0 wrap src pos inp aout ma mb,
  Kr W0 wrap src pos inp aout ma mb -> mwf3xW ma -> mwf3xW mb -> m_mode mb = LENLENS -> m_leave mb = 0 ->
  Kr W0 wrap src pos inp aout (lenlens_loop k ma) (lenlens_loop k mb).
Proof.
  induction k; intros W0 wrap src pos inp aout ma mb K Wa Wb Md L; [exact K|].
  pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) as S.
  assert (Ma: m_mode ma = LENLENS) by (unfold m_mode in *; rewrite (sr_mode _ _ _ S); exact Md).
  assert (La: m_leave ma = 0) by (rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K)); exact L).
  destruct (sr_nlen _ _ _ S (or_introl Md)) as (_ & _ & Eh).
  assert (Ec: i_ncode (m_s ma) = i_ncode (m_s mb)) by (apply (sr_ncode _ _ _ S Md)).
  rewrite !irl_loop_S, Eh, Ec.
  destruct (Z.ltb_spec (i_have (m_s mb)) (i_ncode (m_s mb))) as [Hc|Hc]; [|exact K].
  destruct (irl_kr_stepW _ _ _ _ _ _ ma mb K Wa Wb Md Hc) as [K2 K3].
  assert (EL: m_leave (needbits 3 ma) = m_leave (needbits 3 mb))
    by (apply (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K2))).
  rewrite EL. destruct (Z.eqb_spec (m_leave (needbits 3 mb)) 1) as [L2|L2]; [exact K2|].
  destruct (irl_step_wfW ma Wa Ma La ltac:(rewrite Eh, Ec; exact Hc) ltac:(rewrite EL; exact L2)) as (Wa3 & Ma3 & La3).
  destruct (irl_step_wfW mb Wb Md L Hc L2) as (Wb3 & Mb3 & Lb3).
  apply IHk; auto.
Qed.

(* one stream: the preconditions of inflate_table and the CODELENS machine's invariant (StepWTables.LENLENS_ok) *)
Lemma irl_preW m1 :
  mwf3xW m1 -> m_mode m1 = LENLENS ->
  exists L0, lenlens_zero 19 (m_s m1) = set_i_have (set_i_lens (m_s m1) L0) 19 /\ Zlength L0 = 320 /\
    Forall (fun x => 0 <= x <= 65535) L0 /\ (forall x, 0 <= x < 19 -> 0 <= Znth x L0 <= 7) /\
    inputs_ok CODES (sublist 0 19 L0) 7 /\ cap_ok CODES (sublist 0 19 L0) 7 (Zlength (irl_old (m_s m1))) /\
    Forall entry_ok (irl_old (m_s m1)) /\ Zlength (irl_old (m_s m1)) = ENOUGH_CODES.
Proof.
  intros W1 Md1.
  pose proof (mwW_md _ (m3W_w _ W1)) as MD. pose proof (mwW_s _ (m3W_w _ W1)) as S.
  destruct (md_lenlens _ MD Md1) as (Hc & H0 & Hnl & Hnd & LE).
  destruct (sw_lens _ S) as [ZL FL]. destruct (sw_codes _ S) as [ZC FC].
  destruct (tb_lenlens_zero 19 (m_s m1) ltac:(lia) ltac:(simpl; lia) ZL FL LE) as (L0 & EZ & ZL0 & FL0 & LE0).
  exists L0. split; [exact EZ|]. split; [exact ZL0|]. split; [exact FL0|].
  assert (LE7: forall x, 0 <= x < 19 -> 0 <= Znth x L0 <= 7).
  { intros x Hx. destruct (tb_order_surj x Hx) as (k & Hk & <-). split; [|apply LE0; auto].
    rewrite Forall_forall in FL0. apply FL0. apply Znth_In. pose proof (tb_order_range k Hk). lia. }
  split; [exact LE7|].
  assert (F07: Forall (fun x => 0 <= x <= 7) (sublist 0 19 L0)).
  { apply tb_forall_sublist; simpl; try lia. intros k Hk. apply LE7; lia. }
  assert (ZO: Zlength (irl_old (m_s m1)) = ENOUGH_CODES)
    by (unfold irl_old; rewrite Zlength_sublist; unfold ENOUGH_CODES in *; lia).
  split.
  { unfold inputs_ok. rewrite Zlength_sublist by lia. split; [unfold CODES; lia|].
    split; [unfold max_codes; simpl; lia|]. split; [|lia].
    eapply Forall_impl; [|exact F07]. unfold MAXBITS; simpl; intros; lia. }
  split.
  { rewrite ZO. pose proof (tb_maxlen_le _ F07) as ML.
    unfold cap_ok. unfold LENS, CODES, DISTS, ENOUGH_CODES. split; [|split; intros; lia].
    intros _. split; [lia|]. split; [lia|]. rewrite Z.shiftl_1_l.
    assert (2 ^ maxlen (sublist 0 19 L0) <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 7) with 128 in *. lia. }
  split; [unfold irl_old; apply Forall_sublist; auto | exact ZO].
Qed.

Lemma irl_wfW m1 L0 root used t :
  mwf3xW m1 -> m_mode m1 = LENLENS -> Zlength L0 = 320 -> Forall (fun x => 0 <= x <= 65535) L0 ->
  Zlength t = ENOUGH_CODES -> Forall entry_ok t -> tab_ok CODES t root used -> 1 <= used <= ENOUGH_CODES ->
  mwf3xW (set_mode (upd_s (set_m_ret (set_m_s m1 (irl_s1 (m_s m1) L0 (sublist 0 0 (i_codes (m_s m1)) ++ t)
           (0 + used) root)) 0) (fun s => set_i_have s 0)) CODELENS).
Proof.
  intros W1 Md1 ZL0 FL0 Zt Ft T U.
  pose proof (mwW_s _ (m3W_w _ W1)) as S.
  pose proof (mwW_md _ (m3W_w _ W1)) as MD.
  destruct (md_lenlens _ MD Md1) as (_ & _ & Hnl & Hnd & _). clear MD.
  rewrite sublist_nil, app_nil_l.
  pose proof (tv_rb _ _ _ _ T) as RB.
  rewrite irl_cl_eq. unfold irl_s1.
  apply tb_new_s.
  + apply tb_set_ret; auto; lia.
  + apply swf_set_mode; [|md_neq]. unfold irl_s0. destruct S; constructor; simpl; auto; unfold ENOUGH_CODES in *; try lia.
  + constructor; simpl; intros; try md_neq.
    * split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [|intros; lia].
      apply tb_tvalid_at with used t; [lia | unfold ENOUGH_CODES in *; lia | | exact T].
      intros i Hi. cbn [i_codes set_i_mode set_i_have set_i_lenbits set_i_next set_i_codes].
      rewrite Z.add_0_l. reflexivity.
    * unfold decode_mode in *; md_neq.
  + simpl. first [apply (x3_head _ (m3W_x _ W1)) | (intros ?HH; exfalso; revert HH; md_neq)].
  + simpl; intros; md_neq.
  + simpl; intros; md_neq.
  + simpl; intros D; unfold decode_mode in D; md_neq.
  + apply mwfW_out_eq; [apply (m3W_w _ (tb_set_ret m1 0 W1 ltac:(lia))) |
      change (m_mode (set_m_ret m1 0)) with (m_mode m1); rewrite Md1; md_neq ..].
  + simpl; split; md_neq.
Qed.

Lemma irl_postW (C3: Zlib.proof.inflate.Cover3.cover3_stmt) (TD: tabdet_stmt) (CL: irt_cl_stmtW)
  W0 wrap src pos inp aout ma mb :
  Kr W0 wrap src pos inp aout ma mb -> mwf3xW ma -> mwf3xW mb -> m_mode mb = LENLENS -> m_leave mb = 0 ->
  irt_rr W0 wrap src pos inp aout (irt_llpost ma) (irt_llpost mb).
Proof.
  intros K Wa Wb Md L.
  pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) as S.
  assert (Mdb: i_mode (m_s mb) = LENLENS) by exact Md.
  assert (Hh: m_mode mb <> HEAD) by (rewrite Md; unfold LENLENS, HEAD; lia).
  assert (Ma: m_mode ma = LENLENS) by (unfold m_mode in *; rewrite (sr_mode _ _ _ S); exact Md).
  destruct (sr_nlen _ _ _ S (or_introl Mdb)) as (_ & _ & Eh).
  pose proof (sr_lenlens _ _ _ S Mdb) as LL.
  pose proof (mwW_md _ (m3W_w _ Wb)) as MD. destruct (md_lenlens _ MD Mdb) as (Hc & H0 & _). clear MD.
  destruct (sw_lens _ (mwW_s _ (m3W_w _ Wa))) as [ZLa _]. destruct (sw_lens _ (mwW_s _ (m3W_w _ Wb))) as [ZLb _].
  destruct (irl_preW ma Wa Ma) as (La & EZa & ZLa0 & FLa0 & _ & INa & CAPa & FOa & ZOa).
  destruct (irl_preW mb Wb Md) as (Lb & EZb & ZLb0 & FLb0 & _ & INb & CAPb & FOb & ZOb).
  assert (EL: sublist 0 19 La = sublist 0 19 Lb)
    by (apply (irl_L_eq (m_s ma) (m_s mb)); auto; lia).
  rewrite (irl_post_eq _ _ EZa), (irl_post_eq _ _ EZb). unfold irl_rhs. cbv zeta.
  rewrite EL. rewrite EL in CAPa, INa.
  destruct (TD CODES (sublist 0 19 Lb) 7 (irl_old (m_s ma)) (irl_old (m_s mb)) INb
              ltac:(intros; rewrite Zlength_sublist; lia) CAPa FOa ltac:(lia) FOb) as (Er & Eadv & Eb & Ok).
  rewrite Er, Eadv, Eb.
  destruct (Z.eqb_spec (it_ret (inflate_table_model CODES (sublist 0 19 Lb) 7 (irl_old (m_s mb)))) 0) as [R0|R0].
  2:{ cbn [negb irt_rr]. rewrite !irl_bad_eq.
      apply irl_kr; auto; [unfold BAD, HEAD; cbn; lia | apply irl_srel_bad; auto | reflexivity ..]. }
  cbn [negb].
  destruct (inflate_table_model CODES (sublist 0 19 Lb) 7 (irl_old (m_s ma))) as [ | ta | root used t1] eqn:MA;
    cbn [it_ret] in Er; [rewrite <- Er in R0; discriminate .. |].
  destruct (Ok root used t1 eq_refl) as (t2 & MB & TL).
  rewrite MB. cbn [it_tab it_adv it_bits].
  rewrite ZOa in CAPa. rewrite ZOb in CAPb. rewrite <- EL in MA, CAPa, INa.
  destruct (irl_tab C3 (m_s ma) La root used t1 (mwW_s _ (m3W_w _ Wa)) ZLa0 FLa0 INa CAPa MA) as (Zt1 & Ft1 & T1 & U1).
  destruct (irl_tab C3 (m_s mb) Lb root used t2 (mwW_s _ (m3W_w _ Wb)) ZLb0 FLb0 INb CAPb MB) as (Zt2 & Ft2 & T2 & U2).
  pose proof (irl_wfW ma La root used t1 Wa Ma ZLa0 FLa0 Zt1 Ft1 T1 U1) as Wa'.
  pose proof (irl_wfW mb Lb root used t2 Wb Md ZLb0 FLb0 Zt2 Ft2 T2 U2) as Wb'.
  apply CL; [ | exact Wa' | exact Wb' | exact L | reflexivity].
  rewrite !irl_cl_eq.
  apply irl_kr; auto; [unfold CODELENS, HEAD; cbn; lia | apply irl_srel_cl; auto; apply irl_tl_of; exact TL
                      | reflexivity ..].
Qed.

Lemma irt_ll_okW : Zlib.proof.inflate.Cover3.cover3_stmt -> tabdet_stmt -> irt_cl_stmtW -> irt_ll_stmtW.
Proof.
  intros C3 TD CL W0 wrap src pos inp aout ma mb K Wa Wb L Md.
  pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) as S.
  assert (Ma: m_mode ma = LENLENS) by (unfold m_mode in *; rewrite (sr_mode _ _ _ S); exact Md).
  assert (La: m_leave ma = 0) by (rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K)); exact L).
  pose proof (irl_loopW 19 _ _ _ _ _ _ ma mb K Wa Wb Md L) as K1.
  destruct (tb_lenlens_loop 19 ma Wa Ma La) as [Wa1 Ma1].
  destruct (tb_lenlens_loop 19 mb Wb Md L) as [Wb1 Mb1].
  unfold irt_ll.
  set (ma1 := lenlens_loop 19 ma) in *. set (mb1 := lenlens_loop 19 mb) in *. clearbody ma1 mb1.
  assert (EL: m_leave ma1 = m_leave mb1) by (apply (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K1))).
  rewrite EL. destruct (Z.eqb_spec (m_leave mb1) 1) as [L1|L1]; [exact K1|].
  assert (L1': m_leave mb1 = 0) by (destruct (leave_cases _ (m3W_w _ Wb1)); auto; contradiction).
  apply irl_postW; auto.
Qed.

