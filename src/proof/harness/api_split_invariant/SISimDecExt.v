(* LENEXT and DISTEXT: the extra bits of a length or of a distance (NEEDBITS(extra)), falling through into
   DIST and MATCH; and LIT, the literal byte. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimDecKit.
Import ListNotations.
Local Open Scope Z_scope.

(* a disjunction of equations, one of which holds by reflexivity *)
Ltac orf := repeat (first [reflexivity | left; reflexivity | right]).


(* NEEDBITS(ex) then DROPBITS(ex) of the extra bits: the bits are the input's at the bit position, which
   moves by ex; when NEEDBITS leaves, the call's input ends before them *)
Lemma needbits_ext src P0 m ex :
  kit_bits_stmt -> bitbuf src P0 m -> m_leave m = 0 -> 0 <= ex <= 32 ->
  let m1 := needbits ex m in
  m1 = set_m_leave (set_m_bits (set_m_hold (set_m_nx m (m_nx m1)) (m_hold m1)) (m_bits m1)) (m_leave m1) /\
  bitbuf src P0 m1 /\ mq P0 m1 = mq P0 m /\
  (m_leave m1 = 1 -> 8 * (P0 + Zlength (m_inp m)) < mq P0 m + ex) /\
  (m_leave m1 <> 1 -> bitsn m1 ex = sbits src (mq P0 m) ex /\
     forall f, let m2 := dropbits ex (upd_s m1 f) in
       bitbuf src P0 m2 /\ mq P0 m2 = mq P0 m + ex /\ m_s m2 = f (m_s m) /\ m_inp m2 = m_inp m /\
       m_aout m2 = m_aout m /\ m_ow m2 = m_ow m /\ m_in m2 = m_in m /\ m_out m2 = m_out m /\
       m_ret m2 = m_ret m /\ m_tout m2 = m_tout m /\ m_leave m2 = 0).
Proof.
  intros KB BB L0 Hn m1.
  destruct KB as (_ & KN & KD & _).
  destruct (KN src P0 m ex BB L0 Hn) as (BB1 & Q1 & E1 & S1 & F1). fold m1 in BB1, Q1, E1, S1, F1. clearbody m1.
  split; [exact E1|]. split; [exact BB1|]. split; [exact Q1|]. split.
  - intros L1. destruct (F1 ltac:(lia)) as (_ & _ & _ & X). exact X.
  - intros L1.
    assert (L1': m_leave m1 = 0).
    { destruct (Z.eq_dec (m_leave m1) 0) as [X|X]; [exact X|]. destruct (F1 X) as (X1 & _). lia. }
    destruct (S1 L1') as (N1 & N2 & N3).
    split; [exact N3|].
    intros f m2.
    assert (BBu: bitbuf src P0 (upd_s m1 f)) by (apply bitbuf_ext with m1; reflexivity || exact BB1).
    assert (Hk: 0 <= ex <= m_bits (upd_s m1 f)) by (change (m_bits (upd_s m1 f)) with (m_bits m1); lia).
    destruct (KD src P0 (upd_s m1 f) ex BBu Hk) as (BB2 & Q2 & _). fold m2 in BB2, Q2.
    split; [exact BB2|]. split; [rewrite Q2; change (mq P0 (upd_s m1 f)) with (mq P0 m1); rewrite Q1; reflexivity|].
    unfold m2. rewrite E1 in L1' |- *. cbn in L1' |- *. repeat split; auto.
Qed.

Lemma sd_lenext : dcase_next LENEXT (fun md => md = DIST).
Proof.
  intros [KB KL] AW HD. apply sim_ok_dgoal. intros flush src P0 O0 m a Rl Aw L Hm.
  rewrite stepf2_LENEXT by exact Hm. unfold c_LENEXT. cbv zeta.
  assert (Ha: a_mode a = LENEXT) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Hm).
  assert (NB: m_mode m <> BAD) by (rewrite Hm; discriminate).
  assert (ND: m_mode m <> DONE) by (rewrite Hm; discriminate).
  assert (Sq: seq (m_s m) (a_s a)) by exact (rl_s _ _ _ _ _ Rl NB).
  assert (Q: a_q a = mq P0 m) by exact (rl_q _ _ _ _ _ Rl NB).
  pose proof (rl_bb _ _ _ _ _ Rl) as BB.
  assert (QI: a_q a <= 8 * (P0 + Zlength (m_inp m))) by (rewrite Q; apply (mq_le src), BB).
  assert (Le: i_length (m_s m) = i_length (a_s a))
    by (apply (se_length _ _ Sq); change (len_live (a_mode a)); rewrite Ha; unfold len_live; orf).
  assert (Ee: i_extra (m_s m) = i_extra (a_s a))
    by (apply (se_extra _ _ Sq); change (ext_live (a_mode a)); rewrite Ha; unfold ext_live; orf).
  assert (Rx: 0 <= i_extra (a_s a) <= 5).
  { split; [exact (proj1 (sw_extra _ (aw_swf _ _ Aw)))|]. apply (md_lenext _ (aw_md _ _ Aw)). exact Ha. }
  pose proof (rl_aout _ _ _ _ _ Rl) as Ao.
  destruct (Z.eqb_spec (i_extra (m_s m)) 0) as [E0|E0]; cbn [negb].
  - set (m3 := set_mode (upd_s m (fun s => set_i_was s (i_length s))) DIST).
    set (a1 := AS (set_i_mode (a_s a) DIST) (a_q a) (a_O a)).
    assert (S: astep lenfix_list distfix_list src a = AGo (a_q a) false a1).
    { rewrite astep_LENEXT by exact Ha. unfold a_LENEXT. rewrite <- Ee, E0. reflexivity. }
    eapply dgoal_go; [exact S|exact QI|].
    rewrite <- (stepf2_DIST flush lenfix_list distfix_list m3) by reflexivity.
    eapply dcont; [exact HD| |eapply awf_go; eauto|exact L|reflexivity|reflexivity|reflexivity].
    eapply rel_dec_next with (m := m) (a := a); try exact Rl; cbn; try reflexivity.
    + rewrite Hm. unfold decode_mode; orf.
    + apply bitbuf_ext with m; try reflexivity. exact BB.
    + lia.
    + left; unfold decode_mode; orf.
    + rewrite Q. reflexivity.
    + exact (rl_O _ _ _ _ _ Rl).
    + apply seq_mode; [apply seq_was; exact Sq| | |]; intros P; [exact Le|exfalso; dmd|exfalso; dmd].
    + unfold win_eq; cbn; auto.
    + exact (rl_head _ _ _ _ _ Rl).
  - assert (Hn: 0 <= i_extra (m_s m) <= 32) by lia.
    destruct (needbits_ext src P0 m (i_extra (m_s m)) KB BB L Hn) as (E1 & BB1 & Q1 & F1 & S1).
    set (m1 := needbits (i_extra (m_s m)) m) in *. clearbody m1.
    destruct (Z.eqb_spec (m_leave m1) 1) as [L1|L1].
    + apply dgoal_here.
      * rewrite E1. apply rel_bits; [exact Rl|exact NB| |rewrite <- E1; exact BB1|rewrite <- E1; exact Q1].
        apply bits_ok_dec. change (decode_mode (m_mode m)). rewrite Hm. unfold decode_mode; orf.
      * intros _. eapply stop_need.
        -- rewrite astep_LENEXT by exact Ha. unfold a_LENEXT. rewrite <- Ee.
           destruct (Z.eqb_spec (i_extra (m_s m)) 0); [contradiction|]. cbn [negb]. reflexivity.
        -- rewrite Q. exact (F1 L1).
        -- rewrite E1. cbn. exact (rl_ret _ _ _ _ _ Rl NB ND).
    + destruct (S1 L1) as (Bt & S2).
      set (f := fun s => set_i_length (set_i_back s (i_back s + i_extra (m_s m)))
                           (u32 (i_length (m_s m1) + bitsn m1 (i_extra (m_s m))))).
      destruct (S2 f) as (BB2 & Q2 & Es2 & Ei2 & Ea2 & Eo2 & Ein2 & Eout2 & Er2 & Et2 & L2).
      set (m2 := dropbits (i_extra (m_s m)) (upd_s m1 f)) in *. clearbody m2.
      set (m3 := set_mode (upd_s m2 (fun s => set_i_was s (i_length s))) DIST).
      set (a1 := AS (set_i_mode (set_i_length (a_s a) (u32 (i_length (a_s a) + sbits src (a_q a) (i_extra (a_s a)))))
                      DIST) (a_q a + i_extra (a_s a)) (a_O a)).
      assert (S: astep lenfix_list distfix_list src a = AGo (a_q a + i_extra (a_s a)) false a1).
      { rewrite astep_LENEXT by exact Ha. unfold a_LENEXT.
        destruct (Z.eqb_spec (i_extra (a_s a)) 0); [lia|]. cbn [negb]. reflexivity. }
      assert (Ms1: m_s m1 = m_s m) by (rewrite E1; reflexivity).
      assert (QI2: a_q a + i_extra (a_s a) <= 8 * (P0 + Zlength (m_inp m)))
        by (rewrite <- Ee, Q, <- Q2, <- Ei2; apply (mq_le src); exact BB2).
      eapply dgoal_go; [exact S|exact QI2|].
      rewrite <- (stepf2_DIST flush lenfix_list distfix_list m3) by reflexivity.
      assert (Ev: u32 (i_length (m_s m1) + bitsn m1 (i_extra (m_s m))) =
                  u32 (i_length (a_s a) + sbits src (a_q a) (i_extra (a_s a))))
        by (rewrite Bt, Ms1, Le, Ee, Q; reflexivity).
      assert (Es3: m_s m3 = set_i_mode (set_i_was (f (m_s m)) (i_length (f (m_s m)))) DIST)
        by (change (m_s m3) with (set_i_mode (set_i_was (m_s m2) (i_length (m_s m2))) DIST); rewrite Es2; reflexivity).
      eapply dcont; [exact HD| |eapply awf_go; eauto|exact L2|reflexivity|rewrite <- Ei2; reflexivity
                    |rewrite <- Ea2; reflexivity].
      eapply rel_dec_next with (m := m) (a := a); try exact Rl.
      * rewrite Hm. unfold decode_mode; orf.
      * apply bitbuf_ext with m2; try reflexivity. exact BB2.
      * exact Ei2.
      * exact Ea2.
      * exact Ein2.
      * exact Eout2.
      * exact Er2.
      * exact Et2.
      * change (m_ow m3) with (m_ow m2). rewrite Eo2. lia.
      * reflexivity.
      * left. change (decode_mode DIST). unfold decode_mode; orf.
      * change (mq P0 m3) with (mq P0 m2). rewrite Q2, <- Q, Ee. reflexivity.
      * change (m_ow m3) with (m_ow m2). rewrite Eo2. exact (rl_O _ _ _ _ _ Rl).
      * rewrite Es3. apply seq_mode; [apply seq_was; unfold f; rewrite Ev; apply seq_length, seq_back; exact Sq| | |];
          intros P; [unfold f; exact Ev|exfalso; dmd|exfalso; dmd].
      * rewrite Es3. reflexivity.
      * reflexivity.
      * reflexivity.
      * rewrite Es3. reflexivity.
      * rewrite Es3. reflexivity.
      * rewrite Es3. unfold win_eq. repeat split.
      * rewrite Es3. exact (rl_head _ _ _ _ _ Rl).
Qed.

Lemma sd_distext : dcase_next DISTEXT (fun md => md = MATCH).
Proof.
  intros [KB KL] AW HD. apply sim_ok_dgoal. intros flush src P0 O0 m a Rl Aw L Hm.
  rewrite stepf2_DISTEXT by exact Hm. unfold c_DISTEXT. cbv zeta.
  assert (Ha: a_mode a = DISTEXT) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Hm).
  assert (NB: m_mode m <> BAD) by (rewrite Hm; discriminate).
  assert (ND: m_mode m <> DONE) by (rewrite Hm; discriminate).
  assert (Sq: seq (m_s m) (a_s a)) by exact (rl_s _ _ _ _ _ Rl NB).
  assert (Q: a_q a = mq P0 m) by exact (rl_q _ _ _ _ _ Rl NB).
  pose proof (rl_bb _ _ _ _ _ Rl) as BB.
  assert (QI: a_q a <= 8 * (P0 + Zlength (m_inp m))) by (rewrite Q; apply (mq_le src), BB).
  assert (Le: i_length (m_s m) = i_length (a_s a))
    by (apply (se_length _ _ Sq); change (len_live (a_mode a)); rewrite Ha; unfold len_live; orf).
  assert (Ee: i_extra (m_s m) = i_extra (a_s a))
    by (apply (se_extra _ _ Sq); change (ext_live (a_mode a)); rewrite Ha; unfold ext_live; orf).
  assert (Eof: i_offset (m_s m) = i_offset (a_s a))
    by (apply (se_offset _ _ Sq); change (off_live (a_mode a)); rewrite Ha; unfold off_live; orf).
  assert (Rx: 0 <= i_extra (a_s a) <= 13).
  { split; [exact (proj1 (sw_extra _ (aw_swf _ _ Aw)))|]. apply (md_distext _ (aw_md _ _ Aw)). exact Ha. }
  pose proof (rl_aout _ _ _ _ _ Rl) as Ao.
  destruct (Z.eqb_spec (i_extra (m_s m)) 0) as [E0|E0]; cbn [negb].
  - set (m3 := set_mode m MATCH).
    set (a1 := AS (set_i_mode (a_s a) MATCH) (a_q a) (a_O a)).
    assert (S: astep lenfix_list distfix_list src a = AGo (a_q a) false a1).
    { rewrite astep_DISTEXT by exact Ha. unfold a_DISTEXT. rewrite <- Ee, E0. reflexivity. }
    eapply dgoal_go; [exact S|exact QI|].
    rewrite <- (stepf2_MATCH flush lenfix_list distfix_list m3) by reflexivity.
    eapply dcont; [exact HD| |eapply awf_go; eauto|exact L|reflexivity|reflexivity|reflexivity].
    eapply rel_dec_next with (m := m) (a := a); try exact Rl; cbn; try reflexivity.
    + rewrite Hm. unfold decode_mode; orf.
    + apply bitbuf_ext with m; try reflexivity. exact BB.
    + lia.
    + left; unfold decode_mode; orf.
    + rewrite Q. reflexivity.
    + exact (rl_O _ _ _ _ _ Rl).
    + apply seq_mode; [exact Sq| | |]; intros P; [exact Le|exact Eof|exfalso; dmd].
    + unfold win_eq; cbn; auto.
    + exact (rl_head _ _ _ _ _ Rl).
  - assert (Hn: 0 <= i_extra (m_s m) <= 32) by lia.
    destruct (needbits_ext src P0 m (i_extra (m_s m)) KB BB L Hn) as (E1 & BB1 & Q1 & F1 & S1).
    set (m1 := needbits (i_extra (m_s m)) m) in *. clearbody m1.
    destruct (Z.eqb_spec (m_leave m1) 1) as [L1|L1].
    + apply dgoal_here.
      * rewrite E1. apply rel_bits; [exact Rl|exact NB| |rewrite <- E1; exact BB1|rewrite <- E1; exact Q1].
        apply bits_ok_dec. change (decode_mode (m_mode m)). rewrite Hm. unfold decode_mode; orf.
      * intros _. eapply stop_need.
        -- rewrite astep_DISTEXT by exact Ha. unfold a_DISTEXT. rewrite <- Ee.
           destruct (Z.eqb_spec (i_extra (m_s m)) 0); [contradiction|]. cbn [negb]. reflexivity.
        -- rewrite Q. exact (F1 L1).
        -- rewrite E1. cbn. exact (rl_ret _ _ _ _ _ Rl NB ND).
    + destruct (S1 L1) as (Bt & S2).
      set (f := fun s => set_i_offset (set_i_back s (i_back s + i_extra (m_s m)))
                           (u32 (i_offset (m_s m1) + bitsn m1 (i_extra (m_s m))))).
      destruct (S2 f) as (BB2 & Q2 & Es2 & Ei2 & Ea2 & Eo2 & Ein2 & Eout2 & Er2 & Et2 & L2).
      set (m2 := dropbits (i_extra (m_s m)) (upd_s m1 f)) in *. clearbody m2.
      set (m3 := set_mode m2 MATCH).
      set (a1 := AS (set_i_mode (set_i_offset (a_s a) (u32 (i_offset (a_s a) + sbits src (a_q a) (i_extra (a_s a)))))
                      MATCH) (a_q a + i_extra (a_s a)) (a_O a)).
      assert (S: astep lenfix_list distfix_list src a = AGo (a_q a + i_extra (a_s a)) false a1).
      { rewrite astep_DISTEXT by exact Ha. unfold a_DISTEXT.
        destruct (Z.eqb_spec (i_extra (a_s a)) 0); [lia|]. cbn [negb]. reflexivity. }
      assert (Ms1: m_s m1 = m_s m) by (rewrite E1; reflexivity).
      assert (QI2: a_q a + i_extra (a_s a) <= 8 * (P0 + Zlength (m_inp m)))
        by (rewrite <- Ee, Q, <- Q2, <- Ei2; apply (mq_le src); exact BB2).
      eapply dgoal_go; [exact S|exact QI2|].
      rewrite <- (stepf2_MATCH flush lenfix_list distfix_list m3) by reflexivity.
      assert (Ev: u32 (i_offset (m_s m1) + bitsn m1 (i_extra (m_s m))) =
                  u32 (i_offset (a_s a) + sbits src (a_q a) (i_extra (a_s a))))
        by (rewrite Bt, Ms1, Eof, Ee, Q; reflexivity).
      assert (Es3: m_s m3 = set_i_mode (f (m_s m)) MATCH)
        by (change (m_s m3) with (set_i_mode (m_s m2) MATCH); rewrite Es2; reflexivity).
      eapply dcont; [exact HD| |eapply awf_go; eauto|exact L2|reflexivity|rewrite <- Ei2; reflexivity
                    |rewrite <- Ea2; reflexivity].
      eapply rel_dec_next with (m := m) (a := a); try exact Rl.
      * rewrite Hm. unfold decode_mode; orf.
      * apply bitbuf_ext with m2; try reflexivity. exact BB2.
      * exact Ei2.
      * exact Ea2.
      * exact Ein2.
      * exact Eout2.
      * exact Er2.
      * exact Et2.
      * change (m_ow m3) with (m_ow m2). rewrite Eo2. lia.
      * reflexivity.
      * left. change (decode_mode MATCH). unfold decode_mode; orf.
      * change (mq P0 m3) with (mq P0 m2). rewrite Q2, <- Q, Ee. reflexivity.
      * change (m_ow m3) with (m_ow m2). rewrite Eo2. exact (rl_O _ _ _ _ _ Rl).
      * rewrite Es3. apply seq_mode; [unfold f; rewrite Ev; apply seq_offset, seq_back; exact Sq| | |];
          intros P; [exact Le|unfold f; exact Ev|exfalso; dmd].
      * rewrite Es3. reflexivity.
      * reflexivity.
      * reflexivity.
      * rewrite Es3. reflexivity.
      * rewrite Es3. reflexivity.
      * rewrite Es3. unfold win_eq. repeat split.
      * rewrite Es3. exact (rl_head _ _ _ _ _ Rl).
Qed.

(* leave = 1 keeps the relation *)
Lemma rel_leave src P0 O0 m a : rel src P0 O0 m a -> rel src P0 O0 (set_leave m) a.
Proof.
  intros [BB Md Q BO O Ao In Out Ret S Ch Tt Tout Win Hd].
  constructor; unfold m_mode, m_left, mq in *; cbn [m_s m_ow m_aout m_in m_inp m_out m_ret m_tout m_nx m_bits
    m_hold set_leave set_m_leave] in *; auto.
  destruct BB; constructor; unfold mq in *; cbn [m_inp m_nx m_bits m_hold set_leave set_m_leave] in *; auto.
Qed.

Lemma sd_lit : kit_stmt -> awf_stmt -> sim_ok (fun md => md = LIT).
Proof.
  intros KIT AW. apply sim_ok_dgoal. intros flush src P0 O0 m a Rl Aw L Hm.
  rewrite stepf2_LIT by exact Hm. unfold c_LIT.
  assert (Ha: a_mode a = LIT) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Hm).
  assert (NB: m_mode m <> BAD) by (rewrite Hm; discriminate).
  assert (ND: m_mode m <> DONE) by (rewrite Hm; discriminate).
  assert (Sq: seq (m_s m) (a_s a)) by exact (rl_s _ _ _ _ _ Rl NB).
  assert (Q: a_q a = mq P0 m) by exact (rl_q _ _ _ _ _ Rl NB).
  assert (QI: a_q a <= 8 * (P0 + Zlength (m_inp m))) by (rewrite Q; apply (mq_le src), (rl_bb _ _ _ _ _ Rl)).
  pose proof (rl_aout _ _ _ _ _ Rl) as Ao. pose proof (rl_O _ _ _ _ _ Rl) as EO.
  assert (S: astep lenfix_list distfix_list src a =
             AGo (a_q a) true (AS (set_i_mode (a_s a) LEN) (a_q a) (a_O a ++ [i_length (a_s a) mod 256])))
    by (rewrite astep_LIT by exact Ha; reflexivity).
  unfold m_left. destruct (Z.eqb_spec (m_aout m - Zlength (m_ow m)) 0) as [E|E].
  - apply dgoal_here; [apply rel_leave; exact Rl|]. intros _.
    eapply stop_full; [exact S| |exact (rl_ret _ _ _ _ _ Rl NB ND)].
    rewrite EO, Zlength_app. lia.
  - eapply dgoal_write; [exact S|exact QI|rewrite EO, Zlength_app; lia|].
    apply dgoal_here; [|cbn; rewrite L; discriminate].
    assert (Le: i_length (m_s m) = i_length (a_s a)) by (apply (se_length _ _ Sq); change (len_live (a_mode a)); rewrite Ha; unfold len_live; orf).
    eapply rel_dec_next with (m := m) (a := a); try exact Rl; cbn; try reflexivity.
    + rewrite Hm. unfold decode_mode; orf.
    + apply bitbuf_ext with m; try reflexivity. exact (rl_bb _ _ _ _ _ Rl).
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + left; unfold decode_mode; orf.
    + rewrite Q. reflexivity.
    + rewrite EO, Le, app_assoc. reflexivity.
    + apply seq_mode; [exact Sq| | |]; intros P; exfalso; dmd.
    + unfold win_eq; cbn; auto.
    + exact (rl_head _ _ _ _ _ Rl).
Qed.
