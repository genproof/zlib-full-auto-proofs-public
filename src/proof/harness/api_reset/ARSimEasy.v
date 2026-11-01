(* Law api_reset, the theory: the groups of modes HEAD, the header (FLAGS .. HCRC), the dictionary and block
   type (DICTID, DICT, TYPE, TYPEDO), the blocks (STORED .. SYNC) and the decoding (LEN_ .. LIT, with
   inflate_fast) under the wide machine invariant: x_inflate_reset's IRSimHead/Hdr/Dict/Block/Dec/Fast.v for
   calls of up to 2^32-1 bytes.

   Those files prove their groups under Inv3.mwf3, but use of it only a few fields that mwfW has as well
   (the input position, the tables of a decode mode, the output count): every helper lemma that does not
   mention mwf3 is reused as it is, and only the final lemmas (and the two Dec helpers that carry mwf3) are
   restated here with mwf3W.  Each group is proved in its own module, which imports its IRSim file there
   only: the files share names of tactics (irh_red) and lemmas (irh_Kr). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_reset.ARSimDefs.
Require Import Zlib.proof.inflate.StepWKit.
Require Zlib.proof.harness.inflate_reset.IRSimHead.
Require Zlib.proof.harness.inflate_reset.IRSimHdr.
Require Zlib.proof.harness.inflate_reset.IRSimDict.
Require Zlib.proof.harness.inflate_reset.IRSimBlock.
Require Zlib.proof.harness.inflate_reset.IRSimFast.
Require Zlib.proof.harness.inflate_reset.IRSimDec.
Import ListNotations.
Local Open Scope Z_scope.

(* HEAD: IRSimHead.head_core reads of the invariant only the input position (mw_nx) *)
Module ARHead.
Import Zlib.proof.harness.inflate_reset.IRSimHead.

Lemma head_coreW W0 wrap src pos inp aout flush ma mb :
  ir_ctx src pos inp -> Kr W0 wrap src pos inp aout ma mb -> mwf3W mb -> m_leave mb = 0 -> m_mode mb = HEAD ->
  (wrap = 0 -> i_wbits (m_s ma) = i_wbits (m_s mb)) ->
  sim_post W0 wrap src pos inp aout (stepf2 flush lenfix_list distfix_list ma)
    (stepf2 flush lenfix_list distfix_list mb).
Proof.
  intros Hc K Hwf Hl Hmd Hw0.
  destruct K as [R Hinp Haout Hwrap Hhead Hwa Hwb Hhd].
  pose proof (irh_mrel_eq _ _ R) as Ema.
  pose proof (mr_s _ _ R) as S.
  assert (Hmda : m_mode ma = HEAD) by (unfold m_mode; rewrite (sr_mode _ _ _ S); exact Hmd).
  rewrite (irh_step_head flush ma Hmda), (irh_step_head flush mb Hmd).
  rewrite Ema. set (sa := m_s ma) in *. set (ha := m_h ma) in *. clearbody sa ha. clear Ema R Hmda.
  pose proof (mwW_nx _ (proj1 Hwf)) as Hnx.
  subst inp aout.
  unfold c_HEAD2. cbv beta zeta. rewrite !irh_nb_sh16.
  change (i_wrap (m_s (set_m_h (set_m_s mb sa) ha))) with (i_wrap sa).
  rewrite (sr_wrap _ _ _ S), Hwrap.
  destruct (Z.eqb_spec wrap 0) as [Wz|Wz].
  { cbn [sim_post]. irh_norm; apply irh_Kr'; irh_red; auto.
    eapply irh_srel; [exact S|..]; irh_red; auto; try (subst wrap; auto; fail). }
  destruct (Hhd Wz Hmd) as [Hhd1 Hhd2].
  pose proof Hc as (Hpos & Hsrc & Hbytes & _).
  destruct (irh_nb mb src pos Hc Hnx Hhd1) as (nx' & Hn' & [[E Hp]|[E Hp]]); rewrite E.
  { rewrite !irh_lv1. cbn [sim_post]. irh_norm; apply irh_Kr'; irh_red; auto.
    intros _ _. split; [|exact Hhd2]. unfold ir_hd. split; [lia|]. split; reflexivity. }
  set (H2 := ir_le (sublist 0 2 src)) in *.
  irh_red. rewrite Hl. change (0 =? 1) with false. cbv iota.
  rewrite (sr_head _ _ _ S), (sr_wrap _ _ _ S), Hhead, Hwrap. cbv iota. irh_red.
  assert (L2 : 2 <= Zlength src) by lia.
  destruct (negb (Z.land wrap 2 =? 0) && (H2 =? 35615))%bool eqn:G.
  { pose proof (irh_hdr_gz wrap src L2 Hbytes G) as Hgz.
    cbn [sim_post]. irh_norm; apply irh_Kr'; irh_red;
    rewrite ?(irh_wnew _ _ _ _ _ Hwa Hgz), ?(irh_wnew _ _ _ _ _ Hwb Hgz); irh_side. }
  destruct ((Z.land wrap 1 =? 0) || negb ((H2 mod 256 * 256 + Z.shiftr H2 8) mod 31 =? 0))%bool eqn:G1.
  { cbn [sim_post]. irh_norm; apply irh_Kr'; irh_red; irh_side. }
  destruct (negb (H2 mod 16 =? 8)) eqn:G2.
  { cbn [sim_post]. irh_norm; apply irh_Kr'; irh_red; irh_side. }
  apply orb_false_iff in G1. destruct G1 as [G1a G1b]. apply Z.eqb_neq in G1a. apply negb_false_iff in G1b.
  apply negb_false_iff in G2.
  pose proof (irh_hdr_zl wrap src L2 Hbytes G G1a G1b G2) as Hzl. fold H2 in Hzl.
  destruct (15 <? Z.shiftr H2 4 mod 16 + 8) eqn:G4.
  { cbn [orb sim_post]. irh_norm; apply irh_Kr'; irh_red; irh_side. }
  (* patch F7 (Model2.c_HEAD2): the window size is checked against the stored one before it is stored *)
  assert (Wc : forall w v, wcl W0 wrap src w -> hdr_wb wrap src = Some v ->
    (negb (w =? 0) && (w <? v))%bool = (negb (W0 =? 0) && (W0 <? v))%bool).
  { clear. intros w v [Ew|(Ew & _ & F)] Hv; subst; auto. rewrite (F v Hv), Z.ltb_irrefl, andb_false_r. reflexivity. }
  rewrite (Wc _ _ Hwa Hzl), (Wc _ _ Hwb Hzl).
  destruct (negb (W0 =? 0) && (W0 <? Z.shiftr H2 4 mod 16 + 8))%bool eqn:G5.
  { cbn [orb sim_post]. irh_norm; apply irh_Kr'; irh_red;
    rewrite ?(irh_wnew _ _ _ _ _ Hwa Hzl), ?(irh_wnew _ _ _ _ _ Hwb Hzl); irh_side. }
  destruct (Z.land (Z.shiftr H2 4) 512 =? 0).
  { cbn [orb sim_post]. irh_norm; apply irh_Kr'; irh_red;
    rewrite ?(irh_wnew _ _ _ _ _ Hwa Hzl), ?(irh_wnew _ _ _ _ _ Hwb Hzl); irh_side. }
  { cbn [orb sim_post]. irh_norm; apply irh_Kr'; irh_red;
    rewrite ?(irh_wnew _ _ _ _ _ Hwa Hzl), ?(irh_wnew _ _ _ _ _ Hwb Hzl); irh_side. }
Qed.

Lemma head_simW : head_sim_stmtW.
Proof.
  intros W0 wrap src pos inp aout flush ma mb Hc K Ha Hb Hl Hmd. unfold md_head in Hmd.
  apply head_coreW; auto.
  intros Wz. pose proof (kr_wa _ _ _ _ _ _ _ _ K) as Wa. pose proof (kr_wb _ _ _ _ _ _ _ _ K) as Wb.
  destruct Wa as [Ea|(_ & Wn & _)]; [|congruence]. destruct Wb as [Eb|(_ & Wn & _)]; [|congruence].
  congruence.
Qed.
End ARHead.

(* FLAGS .. HCRC: IRSimHdr.hdr_sim does not use its invariant hypotheses *)
Module ARHdr.
Import Zlib.proof.harness.inflate_reset.IRSimHdr.

Lemma hdr_simW : hdr_sim_stmtW.
Proof.
  intros W0 wrap src pos inp aout flush ma mb Hc K Wa Wb Hl Hmd.
  pose proof (irh_of_Kr _ _ _ _ _ _ _ _ K Hmd) as I.
  assert (Em : m_mode ma = m_mode mb) by exact (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K))).
  apply irh_post. unfold m_mode in Em.
  unfold md_hdr, m_mode in Hmd.
  repeat match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] end.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_FLAGS2 ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_FLAGS2 mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_flags; assumption.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_TIME2 ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_TIME2 mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_time; assumption.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_OS2 ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_OS2 mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_os; assumption.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_EXLEN2 ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_EXLEN2 mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_exlen; assumption.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_EXTRA2 ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_EXTRA2 mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_extra; assumption.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_NAME2 ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_NAME2 mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_name; assumption.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_COMMENT2 ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_COMMENT2 mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_comment; assumption.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_HCRC ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_HCRC mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_hcrc; assumption.
Qed.
End ARHdr.

(* DICTID, DICT, TYPE, TYPEDO: IRSimDict.dict_sim does not use its invariant hypotheses *)
Module ARDict.
Import Zlib.proof.harness.inflate_reset.IRSimDict.

Lemma dict_simW : dict_sim_stmtW.
Proof.
  intros W0 wrap src pos inp aout flush ma mb Hc K Hwa Hwb Hl Hmd.
  pose proof (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K))) as Em.
  assert (Ea : forall md, m_mode mb = md -> m_mode ma = md) by (intros md E; unfold m_mode in *; rewrite Em; exact E).
  unfold md_dict in Hmd. destruct Hmd as [D|[D|[D|D]]].
  - rewrite (irdi_step_DICTID _ _ _ mb D), (irdi_step_DICTID _ _ _ ma (Ea _ D)).
    exact (irdi_dictid W0 wrap src pos inp aout flush ma mb K D).
  - rewrite (irdi_step_DICT _ _ _ mb D), (irdi_step_DICT _ _ _ ma (Ea _ D)).
    exact (irdi_dict W0 wrap src pos inp aout flush ma mb K D).
  - rewrite (irdi_step_TYPE _ _ _ mb D), (irdi_step_TYPE _ _ _ ma (Ea _ D)).
    exact (irdi_type W0 wrap src pos inp aout flush ma mb K D).
  - rewrite (irdi_step_TYPEDO _ _ _ mb D), (irdi_step_TYPEDO _ _ _ ma (Ea _ D)).
    exact (irdi_typedo W0 wrap src pos inp aout flush ma mb K (or_intror D)).
Qed.
End ARDict.

(* STORED .. SYNC: IRSimBlock.block_sim does not use its invariant hypotheses *)
Module ARBlock.
Import Zlib.proof.harness.inflate_reset.IRSimBlock.

Lemma block_simW : block_sim_stmtW.
Proof.
  intros W0 wrap src pos inp aout flush ma mb Hc K Wa Wb Hl Hmd.
  assert (Mm : m_mode ma = m_mode mb) by exact (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K))).
  unfold md_block in Hmd.
  repeat match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] end.
  - irb_case irb_stored (c_STORED flush).
  - irb_case irb_copy_ c_COPY_.
  - irb_case irb_copy c_COPY.
  - irb_case irb_check c_CHECK.
  - irb_case irb_length c_LENGTH.
  - irb_case irb_done c_DONE.
  - replace (stepf2 _ _ _ ma) with (c_BAD ma) by (unfold stepf2, step2; rewrite Mm, Hmd; reflexivity).
    replace (stepf2 _ _ _ mb) with (c_BAD mb) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    unfold c_BAD. cbn [sim_post]. apply irb_bad_kr. exact K.
  - replace (stepf2 _ _ _ ma) with (IRet Z_MEM_ERROR ma) by (unfold stepf2, step2; rewrite Mm, Hmd; reflexivity).
    replace (stepf2 _ _ _ mb) with (IRet Z_MEM_ERROR mb) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    cbn [sim_post]. split; [reflexivity | exact K].
  - replace (stepf2 _ _ _ ma) with (IRet Z_STREAM_ERROR ma) by (unfold stepf2, step2; rewrite Mm, Hmd; reflexivity).
    replace (stepf2 _ _ _ mb) with (IRet Z_STREAM_ERROR mb) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    cbn [sim_post]. split; [reflexivity | exact K].
Qed.
End ARBlock.

(* inflate_fast: IRSimFast.fast_sim reads of the invariant only the tables of LEN (mw_md) *)
Module ARFast.
Import Zlib.proof.harness.inflate_reset.IRSimFast.

Lemma fast_simW : fast_sim_stmtW.
Proof.
  intros W0 wrap src pos inp aout ma mb Hctx HK Wa Wb Hlv Hmd Hout Hhave Hleft Hbits.
  destruct HK as [HR Hinp Haout Hwrap Hhead Hwa Hwb Hhd].
  pose proof (mr_s _ _ HR) as Hs.
  unfold m_mode in Hmd.
  assert (DL: decode_mode (i_mode (m_s mb))) by (rewrite Hmd; unfold decode_mode; auto).
  destruct (md_tables _ (mwW_md _ (proj1 Wb)) DL) as [(szl & _ & TL) (szd & _ & TD)].
  destruct (sr_dectab _ _ _ Hs DL) as [RL RD].
  assert (Ea: restore ma = irf_chg (restore mb) (set_i_bits (set_i_hold (m_s ma) (m_hold mb)) (m_bits mb)) (m_h ma)).
  { transitivity (restore (irf_chg mb (m_s ma) (m_h ma))); [f_equal; apply irf_mrel_eq, HR|reflexivity]. }
  destruct (irf_fastl (set_i_bits (set_i_hold (m_s ma) (m_hold mb)) (m_bits mb))
              (set_i_bits (set_i_hold (m_s mb) (m_hold mb)) (m_bits mb)) (m_h ma) (m_h mb)
              (sr_lencode _ _ _ Hs) (sr_distcode _ _ _ Hs) (sr_lenbits _ _ _ Hs (or_intror DL))
              (sr_distbits _ _ _ Hs DL) (sr_whave _ _ _ Hs) (sr_sane _ _ _ Hs) (sr_wdata _ _ _ Hs)
              (sr_wsize _ _ _ Hs) (sr_wnext _ _ _ Hs) (eq_trans (sr_mode _ _ _ Hs) Hmd) Hmd
              szl szd TL TD RL RD (restore mb)) as (M & md & E1 & E2 & Md).
  assert (Eb: fast lenfix_list distfix_list (restore mb) =
              irf_chg M (set_i_bits (set_i_hold (set_i_mode
                (set_i_bits (set_i_hold (m_s mb) (m_hold mb)) (m_bits mb)) md) (m_hold M)) (m_bits M)) (m_h mb)).
  { rewrite <- E2. f_equal. }
  pose proof (irk_fast lenfix_list distfix_list (restore mb)) as [Ki Ka].
  rewrite Eb in Ki, Ka. rewrite Ea, E1, Eb. clear E1 E2 Ea Eb.
  constructor.
  - constructor; try reflexivity.
    cbn [m_s irf_chg set_m_h set_m_s]. apply irf_srel with (no := m_ow mb = []); [exact Hs|exact Hmd|exact Md].
  - etransitivity; [exact Ki|exact Hinp].
  - etransitivity; [exact Ka|exact Haout].
  - exact Hwrap.
  - exact Hhead.
  - exact Hwa.
  - exact Hwb.
  - intros _ X. change (md = HEAD) in X. irf_nomode X.
Qed.
End ARFast.

(* LEN_ .. LIT: IRSimDec's group with irdc_mwf3_len, irdc_gen and irdc_LEN restated over mwf3W *)
Module ARDec.
Import Zlib.proof.harness.inflate_reset.IRSimDec.

(* LEN_ falls into LEN: the mode change keeps the wide invariant *)
Lemma irdc_mwf3W_len m : mwf3W m -> m_mode m = LEN_ -> mwf3W (set_mode m LEN).
Proof.
  intros [W [W3 Wh]] Hm.
  assert (D: decode_mode (i_mode (m_s m))) by (unfold m_mode in Hm; rewrite Hm; unfold decode_mode; auto).
  split; [|split].
  - apply mwfW_set_mode; auto;
      first [ (intros _; exact (md_tables _ (mwW_md _ W) D))
            | (left; apply mwfW_out_eq; [exact W | ..]; rewrite Hm; unfold LENGTH; irdc_cst; lia)
            | (intros E; exfalso; irdc_cst; lia)
            | (irdc_cst; lia) ].
  - destruct W3. constructor; simpl; intros; try (exfalso; irdc_cst; lia).
    exact (s3_len D).
  - split; intros E; exfalso; unfold m_mode in E; simpl in E; unfold EXLEN, EXTRA in E; irdc_cst; lia.
Qed.

Lemma irdc_genW c P W0 wrap src pos inp aout ma mb :
  irdc_case_stmt c P -> Kr W0 wrap src pos inp aout ma mb -> mwf3W mb -> P (m_mode mb) ->
  decode_mode (m_mode mb) -> sim_post W0 wrap src pos inp aout (c ma) (c mb).
Proof.
  intros L K Wb HP D. apply L; auto.
  eapply irdc_tabs_of; [exact (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) | exact D
                       | exact (mwW_s _ (proj1 Wb)) | exact (mwW_md _ (proj1 Wb))].
Qed.

Lemma irdc_LENW W0 wrap src pos inp aout ma mb :
  fast_sim_stmtW -> ir_ctx src pos inp -> Kr W0 wrap src pos inp aout ma mb -> mwf3W ma -> mwf3W mb ->
  m_leave mb = 0 -> m_mode mb = LEN ->
  sim_post W0 wrap src pos inp aout (c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list) ma)
    (c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list) mb).
Proof.
  intros FS Hc K Wa Wb Hl Hm.
  rewrite !irdc_LEN_eq.
  pose proof (kr_rel _ _ _ _ _ _ _ _ K) as MR.
  assert (Ec: ((6 <=? m_have ma) && (258 <=? m_left ma) && (m_bits ma <? 8))%bool =
              ((6 <=? m_have mb) && (258 <=? m_left mb) && (m_bits mb <? 8))%bool).
  { unfold m_have, m_left. rewrite (mr_inp _ _ MR), (mr_nx _ _ MR), (mr_aout _ _ MR), (mr_ow _ _ MR),
      (mr_bits _ _ MR). reflexivity. }
  rewrite Ec. destruct ((6 <=? m_have mb) && (258 <=? m_left mb) && (m_bits mb <? 8))%bool eqn:C.
  - apply andb_prop in C. destruct C as [C C3]. apply andb_prop in C. destruct C as [C1 C2].
    apply Z.leb_le in C1. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
    assert (Ho: m_out mb = m_aout mb).
    { apply mwfW_out_eq; [exact (proj1 Wb) | ..]; rewrite Hm; irdc_cst; lia. }
    pose proof (FS W0 wrap src pos inp aout ma mb Hc K Wa Wb Hl Hm Ho C1 C2 C3) as K'.
    assert (Em: m_mode (fast lenfix_list distfix_list (restore ma)) =
                m_mode (fast lenfix_list distfix_list (restore mb)))
      by exact (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K'))).
    rewrite Em. cbn [sim_post].
    destruct (m_mode (fast lenfix_list distfix_list (restore mb)) =? Zlib.proof.inflate.Model.TYPE).
    + apply irdc_Kr_back. exact K'.
    + exact K'.
  - apply (irdc_genW _ _ _ _ _ _ _ _ ma mb irdc_lenslow_ok K Wb Hm).
    rewrite Hm. unfold decode_mode. auto.
Qed.

Lemma dec_simW : dec_sim_stmtW.
Proof.
  intros FS W0 wrap src pos inp aout flush ma mb Hc K Wa Wb Hl Hmd.
  pose proof (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K))) as Em.
  assert (Ea : forall md, m_mode mb = md -> m_mode ma = md)
    by (intros md E; unfold m_mode in *; rewrite Em; exact E).
  pose proof Hmd as D.
  unfold decode_mode in Hmd. destruct Hmd as [M|[M|[M|[M|[M|[M|M]]]]]].
  - rewrite (irdc_step_LEN_ _ _ _ mb M), (irdc_step_LEN_ _ _ _ ma (Ea _ M)). unfold c_LEN_.
    apply irdc_LENW; auto.
    + apply irdc_Kr_len; auto.
    + apply irdc_mwf3W_len; auto.
    + apply irdc_mwf3W_len; auto.
  - rewrite (irdc_step_LEN _ _ _ mb M), (irdc_step_LEN _ _ _ ma (Ea _ M)). apply irdc_LENW; auto.
  - rewrite (irdc_step_LENEXT _ _ _ mb M), (irdc_step_LENEXT _ _ _ ma (Ea _ M)).
    exact (irdc_genW _ _ _ _ _ _ _ _ ma mb irdc_lenext K Wb M D).
  - rewrite (irdc_step_DIST _ _ _ mb M), (irdc_step_DIST _ _ _ ma (Ea _ M)).
    exact (irdc_genW _ _ _ _ _ _ _ _ ma mb irdc_dist K Wb M D).
  - rewrite (irdc_step_DISTEXT _ _ _ mb M), (irdc_step_DISTEXT _ _ _ ma (Ea _ M)).
    exact (irdc_genW _ _ _ _ _ _ _ _ ma mb irdc_distext K Wb M D).
  - rewrite (irdc_step_MATCH _ _ _ mb M), (irdc_step_MATCH _ _ _ ma (Ea _ M)).
    exact (irdc_genW _ _ _ _ _ _ _ _ ma mb irdc_match K Wb M D).
  - rewrite (irdc_step_LIT _ _ _ mb M), (irdc_step_LIT _ _ _ ma (Ea _ M)).
    exact (irdc_genW _ _ _ _ _ _ _ _ ma mb irdc_lit K Wb M D).
Qed.
End ARDec.

Lemma ar_sim_easy : head_sim_stmtW /\ hdr_sim_stmtW /\ dict_sim_stmtW /\ block_sim_stmtW /\
  fast_sim_stmtW /\ dec_sim_stmtW.
Proof.
  exact (conj ARHead.head_simW (conj ARHdr.hdr_simW (conj ARDict.dict_simW (conj ARBlock.block_simW
    (conj ARFast.fast_simW ARDec.dec_simW))))).
Qed.
