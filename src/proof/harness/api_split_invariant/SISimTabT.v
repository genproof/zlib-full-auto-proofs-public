(* The case TABLE: NEEDBITS(14), the three counts, then LENLENS (SISimTabLL.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimTabKit.
Require Import Zlib.proof.harness.api_split_invariant.SISimTabLL.
Import ListNotations.
Local Open Scope Z_scope.

Section Case.
Variables (src: list Z) (P0: Z) (O0: list Z).
Hypothesis K : kit_stmt.
Hypothesis AW : awf_stmt.
Hypothesis DEC : sim_ok decode_mode.

(* the istate after the three counts *)
Definition sit_t_cnt (s: istate) (nl nd nc: Z) : istate := set_i_ncode (set_i_ndist (set_i_nlen s nl) nd) nc.

(* from TABLE after the counts (read up to bit q + 14): the step to LENLENS, then LENLENS *)
Lemma sit_tab_next flush m a m4 nl nd nc :
  rel src P0 O0 m a -> awf src a -> m_mode m = TABLE ->
  sit_keep m m4 -> m_s m4 = m_s m -> m_ret m4 = m_ret m -> m_leave m4 = 0 -> bitbuf src P0 m4 ->
  mq P0 m4 = mq P0 m + 14 -> mq P0 m + 14 <= 8 * (P0 + Zlength (m_inp m)) ->
  astep lenfix_list distfix_list src a =
    AGo (mq P0 m + 14) false (AS (set_i_mode (set_i_have (sit_t_cnt (a_s a) nl nd nc) 0) LENLENS) (mq P0 m + 14) (a_O a)) ->
  sit_out flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a
    (c_LENLENS flush lenfix_list distfix_list (fast lenfix_list distfix_list)
       (set_mode (upd_s (upd_s m4 (fun s => sit_t_cnt s nl nd nc)) (fun s => set_i_have s 0)) LENLENS)).
Proof.
  intros R W Md K4 S4 Rt4 L4 B4 Q4 N14 EA.
  assert (Nb: m_mode m <> BAD) by (rewrite Md; sit_mdg).
  pose proof (rl_s _ _ _ _ _ R Nb) as S.
  pose proof (sit_teq_of_seq _ _ S) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
  assert (R5: rel src P0 O0 (set_mode (upd_s (upd_s m4 (fun s => sit_t_cnt s nl nd nc)) (fun s => set_i_have s 0)) LENLENS)
                (AS (set_i_mode (set_i_have (sit_t_cnt (a_s a) nl nd nc) 0) LENLENS) (mq P0 m + 14) (a_O a))).
  { apply (sit_rel_tab src P0 O0 m a); [exact R|rewrite Md; left; reflexivity| | | | | | reflexivity | | | | |].
    - right; left; reflexivity.
    - eapply sit_keep_trans; [exact K4|]. repeat split.
    - apply (sit_bb_eq src P0 m4); try reflexivity. exact B4.
    - reflexivity.
    - cbn [a_q]. rewrite <- Q4. reflexivity.
    - transitivity (m_ret m4); [reflexivity|]. rewrite Rt4. apply (rl_ret _ _ _ _ _ R); [exact Nb|rewrite Md; sit_mdg].
    - unfold sit_t_cnt. sit_cbng. rewrite S4. apply (sit_seq_t _ _ _ _ S).
      + repeat split.
      + repeat split.
      + repeat split; auto.
      + right; left; reflexivity.
    - unfold sit_t_cnt. sit_cbng. rewrite S4. repeat split.
    - reflexivity.
    - reflexivity. }
  pose proof (proj1 (proj2 AW) src a _ _ _ W EA) as W5.
  apply (sit_out_pre _ _ _ _ _ _ _ _ _ (sit_ar1 _ _ _ _ _ _ EA N14)).
  rewrite <- (proj1 K4), <- (proj1 (proj2 K4)).
  exact (sit_ll_case src P0 O0 K AW DEC flush _ _ R5 W5 L4 eq_refl).
Qed.

Lemma sit_tab_case flush m a :
  rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> m_mode m = TABLE ->
  sit_out flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a
    (c_TABLE flush lenfix_list distfix_list (fast lenfix_list distfix_list) m).
Proof.
  intros R W L Md.
  assert (Nb: m_mode m <> BAD) by (rewrite Md; sit_mdg).
  assert (Ma: a_mode a = TABLE) by (rewrite <- (rl_mode _ _ _ _ _ R); exact Md).
  pose proof (rl_s _ _ _ _ _ R Nb) as S.
  pose proof (rl_bb _ _ _ _ _ R) as B.
  pose proof (rl_q _ _ _ _ _ R Nb) as Q.
  pose proof (bb_src _ _ _ B) as Bs.
  assert (Tmm: tmode (m_mode m)) by (rewrite Md; left; reflexivity).
  pose proof K as [[_ [KN [KD [_ [_ [KM _]]]]]] _].
  assert (EA: astep lenfix_list distfix_list src a = a_TABLE src a) by (apply sit_a_TABLE; exact Ma).
  unfold a_TABLE in EA. rewrite Q in EA.
  unfold c_TABLE.
  remember (needbits 14 m) as m1 eqn:Em1d.
  pose proof (KN src P0 m 14 B L ltac:(lia)) as KN1. cbv zeta in KN1. rewrite <- Em1d in KN1.
  destruct KN1 as (B1 & Q1 & Em1 & Ok1 & Nok1).
  destruct (sit_keep_bits _ _ Em1) as (K1 & S1 & Rt1).
  destruct (Z.eqb_spec (m_leave m1) 1) as [L1|L1].
  { (* out of input *)
    destruct (Nok1 ltac:(lia)) as (_ & _ & _ & Bl).
    cbn [sit_out]. exists a. split; [apply ar_refl|].
    split; [exact (sit_rel_bits src P0 O0 m a m1 R K1 S1 Rt1 B1 Q1 Tmm)|].
    intros _. unfold stop_ok. rewrite EA.
    assert (Rok: m_ret m1 = Z_OK) by (rewrite Rt1; apply (rl_ret _ _ _ _ _ R); [exact Nb|rewrite Md; sit_mdg]).
    match type of EA with context [if ?c then _ else _] => destruct c end;
      cbn [abad ago]; (split; [exact Rok|]); right; right; left; cbn [blocked]; left; lia. }
  assert (L1': m_leave m1 = 0) by (destruct (Z.eq_dec (m_leave m1) 0); [auto|]; destruct (Nok1 n); lia).
  destruct (Ok1 L1') as (Bt1 & _ & Hold1).
  pose proof (bb_bits _ _ _ B1) as Bb1.
  pose proof (sit_mq_end _ _ _ B) as Qe.
  pose proof (sit_bb_end _ _ _ B1) as End1. rewrite Q1, (proj1 K1) in End1.
  (* the three counts *)
  destruct (KD src P0 m1 5 B1 ltac:(lia)) as (B2 & Q2 & V1).
  assert (Bt2: m_bits (dropbits 5 m1) = m_bits m1 - 5) by (apply sit_bits_drop; lia).
  destruct (KD src P0 (dropbits 5 m1) 5 B2 ltac:(lia)) as (B3 & Q3 & V2).
  assert (Bt3: m_bits (dropbits 5 (dropbits 5 m1)) = m_bits m1 - 10) by (rewrite sit_bits_drop; lia).
  destruct (KD src P0 (dropbits 5 (dropbits 5 m1)) 4 B3 ltac:(lia)) as (B4 & Q4 & V3).
  rewrite Q1 in Q2, V1. rewrite Q2 in Q3, V2. rewrite Q3 in Q4, V3.
  rewrite V1, V2, V3.
  replace (mq P0 m + 5 + 5) with (mq P0 m + 10) by lia.
  replace (mq P0 m + 5 + 5 + 4) with (mq P0 m + 14) in Q4 by lia.
  assert (N14: mq P0 m + 14 <= 8 * (P0 + Zlength (m_inp m))) by lia.
  pose proof (sit_teq_of_seq _ _ S) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
  assert (K4: sit_keep m (dropbits 4 (dropbits 5 (dropbits 5 m1))))
    by (eapply sit_keep_trans; [exact K1|]; repeat split).
  assert (S4: m_s (dropbits 4 (dropbits 5 (dropbits 5 m1))) = m_s m) by exact S1.
  assert (Rt4: m_ret (dropbits 4 (dropbits 5 (dropbits 5 m1))) = m_ret m) by exact Rt1.
  assert (L4: m_leave (dropbits 4 (dropbits 5 (dropbits 5 m1))) = 0) by exact L1'.
  remember (dropbits 4 (dropbits 5 (dropbits 5 m1))) as m4 eqn:E4. clear E4.
  match type of EA with context [if ?c then _ else _] => destruct c eqn:Tm end.
  { (* too many length or distance codes *)
    unfold abad in EA. cbn [sit_out]. eexists. split; [eapply sit_ar1; [exact EA|exact N14]|].
    split; [|intros X; rewrite sit_leave_bad, sit_leave_upd, L4 in X; discriminate X].
    apply (sit_rel_bad src P0 O0 m a); [exact R| | |reflexivity|reflexivity|reflexivity|].
    - eapply sit_keep_trans; [exact K4|]. repeat split.
    - apply sit_bb_bad, sit_bb_s. exact B4.
    - sit_cbng. rewrite S4. exact (rl_head _ _ _ _ _ R). }
  unfold ago in EA.
  exact (sit_tab_next flush m a m4 _ _ _ R W Md K4 S4 Rt4 L4 B4 Q4 N14 EA).
Qed.

End Case.
