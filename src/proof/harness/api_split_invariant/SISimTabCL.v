(* CODELENS' while loop: one pass (codelens_iter: one code length symbol, with its repeat count) is one
   abstract step of a_CODELENS, or stops where that step needs more input than the call has. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimTabKit.
Import ListNotations.
Local Open Scope Z_scope.

Section Iter.
Variables (src: list Z) (P0: Z) (O0: list Z).

(* the outcome of one pass of the loop from m (related to a): a step, a stop on the input (the step
   needs bits past the call's input), or a step to BAD *)
Definition sit_clo (m: mst) (a: ast) (o: clout) : Prop :=
  let I := P0 + Zlength (m_inp m) in
  match o with
  | CLnext m' => exists n a', astep lenfix_list distfix_list src a = AGo n false a' /\ n <= 8 * I /\
      rel src P0 O0 m' a' /\ sit_keep m m' /\ m_leave m' = 0 /\ m_mode m' = CODELENS /\
      i_have (m_s m) < i_have (m_s m')
  | CLleave m' => rel src P0 O0 m' a /\ sit_keep m m' /\ m_leave m' = 1 /\
      exists n w a', astep lenfix_list distfix_list src a = AGo n w a' /\ 8 * I < n
  | CLbad m' => exists n a', astep lenfix_list distfix_list src a = AGo n false a' /\ n <= 8 * I /\
      rel src P0 O0 m' a' /\ sit_keep m m' /\ m_leave m' = 0 /\ m_mode m' = BAD
  end.

(* the end of a repeat code: copy the length copy times, or BAD when that overflows *)
Lemma sit_cl_tail m a m5 nx len copy :
  rel src P0 O0 m a -> m_mode m = CODELENS ->
  sit_keep m m5 -> m_s m5 = m_s m -> m_ret m5 = m_ret m -> m_leave m5 = 0 -> bitbuf src P0 m5 ->
  mq P0 m5 = nx -> nx <= 8 * (P0 + Zlength (m_inp m)) -> 0 < copy ->
  astep lenfix_list distfix_list src a =
    (if i_nlen (m_s m) + i_ndist (m_s m) <? i_have (m_s m) + copy then abad a nx
     else ago a nx (lens_fill (Z.to_nat copy) len (a_s a))) ->
  sit_clo m a
    (let s := m_s m5 in
     if i_nlen s + i_ndist s <? i_have s + copy then CLbad (set_bad m5 M_repeat)
     else CLnext (upd_s m5 (lens_fill (Z.to_nat copy) len))).
Proof.
  intros R Md K5 S5 Rt5 L5 B5 Q5 N5 C EA.
  assert (Nb: m_mode m <> BAD) by (rewrite Md; sit_mdg).
  assert (Ma: a_mode a = CODELENS) by (rewrite <- (rl_mode _ _ _ _ _ R); exact Md).
  pose proof (rl_s _ _ _ _ _ R Nb) as S.
  pose proof (sit_teq_of_seq _ _ S) as TQ.
  cbv zeta. rewrite S5.
  destruct (_ <? _) eqn:Ov.
  - exists nx, (AS (set_i_mode (a_s a) BAD) nx (a_O a)). split; [exact EA|]. split; [exact N5|].
    split; [|split; [|split]].
    + apply (sit_rel_bad src P0 O0 m a); [exact R| | | reflexivity | reflexivity | reflexivity |].
      * eapply sit_keep_trans; [exact K5|]. repeat split.
      * apply sit_bb_bad. exact B5.
      * sit_cbn. rewrite S5. exact (rl_head _ _ _ _ _ R).
    + eapply sit_keep_trans; [exact K5|]. repeat split.
    + exact L5.
    + reflexivity.
  - exists nx, (AS (lens_fill (Z.to_nat copy) len (a_s a)) nx (a_O a)). split; [exact EA|]. split; [exact N5|].
    pose proof (sit_fill_facts (Z.to_nat copy) len (m_s m)) as (F1 & F2 & F3 & F4 & F5).
    pose proof (sit_fill_facts (Z.to_nat copy) len (a_s a)) as (G1 & G2 & G3 & G4 & G5).
    cbv zeta in F1, F2, F3, F4, F5, G1, G2, G3, G4, G5.
    assert (Tm: tmode CODELENS) by (right; right; left; reflexivity).
    split; [|split; [|split; [|split]]].
    + apply (sit_rel_tab src P0 O0 m a); [exact R| | | | | | | reflexivity | | | | exact G4 | exact G5].
      * rewrite Md. exact Tm.
      * unfold m_mode in *. sit_cbn. rewrite S5, F3, Md. exact Tm.
      * eapply sit_keep_trans; [exact K5|]. repeat split.
      * apply sit_bb_s. exact B5.
      * unfold m_mode, a_mode. sit_cbn. rewrite S5, F3, G3. exact (rl_mode _ _ _ _ _ R).
      * rewrite <- Q5. reflexivity.
      * sit_cbn. rewrite Rt5. apply (rl_ret _ _ _ _ _ R); [exact Nb|rewrite Md; sit_mdg].
      * sit_cbn. rewrite S5. apply (sit_seq_t _ _ _ _ S F1 G1).
        -- apply sit_teq_fill. exact TQ.
        -- rewrite G3. unfold a_mode in Ma. rewrite Ma. exact Tm.
      * sit_cbn. rewrite S5. exact F2.
    + eapply sit_keep_trans; [exact K5|]. repeat split.
    + exact L5.
    + unfold m_mode. sit_cbn. rewrite S5, F3. exact Md.
    + sit_cbn. rewrite S5, sit_fill_have, Z2Nat.id by lia. lia.
Qed.

Hypothesis K : kit_stmt.

(* the abstract table walk of the code length code: the root entry, no links *)
Lemma sit_adecode_nolink fx dx s t nb q :
  adecode fx dx src s t nb no_link q = (tab_entry fx dx s t (sbits src q nb), e_bits (tab_entry fx dx s t (sbits src q nb))).
Proof. reflexivity. Qed.

(* the repeat code's DROPBITS(here.bits) and DROPBITS(k) after NEEDBITS(here.bits + k) *)
Lemma sit_cl_drop2 m3 eb k :
  bitbuf src P0 m3 -> 0 <= eb -> 0 <= k -> eb + k <= m_bits m3 ->
  let m4 := dropbits eb m3 in let m5 := dropbits k m4 in
  bitbuf src P0 m4 /\ mq P0 m4 = mq P0 m3 + eb /\ bitbuf src P0 m5 /\ mq P0 m5 = mq P0 m3 + eb + k /\
  bitsn m4 k = sbits src (mq P0 m3 + eb) k /\ mq P0 m3 + eb + k <= 8 * (P0 + Zlength (m_inp m3)) /\
  sit_keep m3 m5 /\ m_s m5 = m_s m3 /\ m_s m4 = m_s m3 /\ m_ret m5 = m_ret m3 /\ m_leave m5 = m_leave m3 /\
  m_ret m4 = m_ret m3 /\ m_leave m4 = m_leave m3 /\ sit_keep m3 m4.
Proof.
  intros B3 E Kk Bt. cbv zeta.
  destruct K as [[_ [_ [KD _]]] _].
  pose proof (bb_bits _ _ _ B3) as Bb3.
  destruct (KD src P0 m3 eb B3 ltac:(lia)) as (B4 & Q4 & _).
  assert (Bt4: m_bits (dropbits eb m3) = m_bits m3 - eb) by (apply sit_bits_drop; lia).
  destruct (KD src P0 (dropbits eb m3) k B4 ltac:(lia)) as (B5 & Q5 & Bits4).
  pose proof (sit_bb_end _ _ _ B3) as End3.
  rewrite Q4 in Q5, Bits4.
  split; [exact B4|]. split; [exact Q4|]. split; [exact B5|]. split; [exact Q5|]. split; [exact Bits4|].
  split; [lia|]. repeat split.
Qed.

Lemma sit_cl_iter m a :
  rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> m_mode m = CODELENS ->
  i_have (m_s m) < i_nlen (m_s m) + i_ndist (m_s m) ->
  sit_clo m a (codelens_iter lenfix_list distfix_list m).
Proof.
  intros R W L Md H.
  assert (Nb: m_mode m <> BAD) by (rewrite Md; sit_mdg).
  assert (Ma: a_mode a = CODELENS) by (rewrite <- (rl_mode _ _ _ _ _ R); exact Md).
  pose proof (rl_s _ _ _ _ _ R Nb) as S.
  pose proof (rl_bb _ _ _ _ _ R) as B.
  pose proof (rl_q _ _ _ _ _ R Nb) as Q.
  pose proof (bb_src _ _ _ B) as Bs.
  destruct K as [[KP [KN [KD [KI [KB [KM [KS [KR KY]]]]]]]] KL].
  assert (TV: tvalid CODES lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m))).
  { destruct (md_codelens _ (aw_md _ _ W) Ma) as (_ & _ & _ & _ & TV & _).
    rewrite (se_lencode _ _ S), (se_lenbits _ _ S). unfold tvalid, tvalid_b in *.
    rewrite (sit_tab_entry_ext _ _ _ _ (se_codes _ _ S)). exact TV. }
  assert (TR: trep (tab_entry lenfix_list distfix_list (m_s m) (i_lencode (m_s m))) (i_lenbits (m_s m)) no_link).
  { pose proof (proj2 (aw_tp _ _ W) Ma) as TR.
    rewrite (se_lencode _ _ S), (se_lenbits _ _ S), (sit_tab_entry_ext _ _ _ _ (se_codes _ _ S)). exact TR. }
  pose proof (KL src P0 m CODES (i_lencode (m_s m)) (i_lenbits (m_s m)) no_link B L TV TR
                ltac:(intros op E; discriminate E)) as KL1.
  cbv zeta in KL1. destruct KL1 as [KL1 _].
  assert (EA: astep lenfix_list distfix_list src a = a_CODELENS lenfix_list distfix_list src a)
    by (apply sit_a_CODELENS; exact Ma).
  unfold a_CODELENS in EA.
  rewrite <- (se_nlen _ _ S), <- (se_ndist _ _ S), <- (se_have _ _ S) in EA.
  destruct (Z.ltb_spec (i_have (m_s m)) (i_nlen (m_s m) + i_ndist (m_s m))) as [_|]; [|lia].
  rewrite sit_adecode_nolink in EA.
  rewrite <- (se_lencode _ _ S), <- (se_lenbits _ _ S), <- (sit_tab_entry_ext _ _ _ _ (se_codes _ _ S)), Q in EA.
  set (root := tab_entry lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) (sbits src (mq P0 m) (i_lenbits (m_s m)))) in *.
  unfold codelens_iter.
  destruct (lookup1 lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m) as [[here m1] ok] eqn:E1.
  destruct KL1 as (Em1 & B1 & Q1 & Ok1 & Nok1).
  destruct (sit_keep_bits _ _ Em1) as (K1 & S1 & Rt1).
  pose proof K1 as (Inp1 & _).
  assert (Tm: tmode CODELENS) by (right; right; left; reflexivity).
  assert (Tmm: tmode (m_mode m)) by (rewrite Md; exact Tm).
  assert (Rb: 0 <= e_bits root <= 15).
  { destruct TV as [sz [_ TV]]. apply (sit_root_bits _ _ _ _ _ TV). apply KR; [exact Bs|].
    pose proof (tv_rb _ _ _ _ TV). lia. }
  pose proof (sit_bb_end _ _ _ B1) as End1. rewrite Inp1, Q1 in End1.
  destruct ok.
  2:{ (* the lookup runs out of input *)
    destruct (Nok1 eq_refl) as (L1 & _ & Bl). cbn [negb sit_clo].
    split; [|split; [exact K1|split; [exact L1|]]].
    - apply (sit_rel_bits src P0 O0 m a m1 R K1 S1 Rt1 B1 Q1 Tmm).
    - sit_split_ea EA; (eexists _, _, _; split; [exact EA|]); lia. }
  destruct (Ok1 eq_refl) as (L1 & Eh & Bh1). subst here. cbn [negb].
  pose proof (bb_bits _ _ _ B1) as Bb1.
  pose proof (sit_teq_of_seq _ _ S) as TQ.
  destruct (Z.ltb_spec (e_val root) 16) as [Lt|Ge].
  { (* a code length 0..15 *)
    destruct (KD src P0 m1 (e_bits root) B1 ltac:(lia)) as (B2 & Q2 & _).
    cbn [sit_clo]. unfold ago in EA.
    set (f := fun s : istate => set_i_have (set_i_lens s (upd_Znth (i_have s) (i_lens s) (e_val root))) (i_have s + 1)).
    assert (Ef: f (m_s m) = set_i_have (set_i_lens (m_s m) (upd_Znth (i_have (m_s m)) (i_lens (m_s m)) (e_val root)))
                              (i_have (m_s m) + 1)) by reflexivity.
    pose proof (sit_hl_facts (m_s m) (i_have (m_s m) + 1) (upd_Znth (i_have (m_s m)) (i_lens (m_s m)) (e_val root)))
      as (F1 & F2 & F3 & F4 & F5).
    pose proof (sit_hl_facts (a_s a) (i_have (m_s m) + 1) (upd_Znth (i_have (m_s m)) (i_lens (a_s a)) (e_val root)))
      as (G1 & G2 & G3 & G4 & G5).
    cbv zeta in F1, F2, F3, F4, F5, G1, G2, G3, G4, G5. rewrite <- Ef in F1, F2, F3, F4, F5.
    assert (Sm: m_s (upd_s (dropbits (e_bits root) m1) f) = f (m_s m)) by (sit_cbn; rewrite S1; reflexivity).
    eexists _, _. split; [exact EA|]. split; [lia|].
    split; [|split; [|split; [|split]]].
    - apply (sit_rel_tab src P0 O0 m a); [exact R|exact Tmm| | | | | | reflexivity | | | | exact G4 | exact G5].
      + unfold m_mode in *. rewrite Sm, F3. exact Tmm.
      + eapply sit_keep_trans; [exact K1|]. repeat split.
      + apply sit_bb_s. exact B2.
      + unfold m_mode, a_mode. rewrite Sm, F3. cbn [a_s]. rewrite G3. exact (rl_mode _ _ _ _ _ R).
      + cbn [a_q]. transitivity (mq P0 (dropbits (e_bits root) m1)); [rewrite Q2, Q1; reflexivity|reflexivity].
      + sit_cbn. rewrite Rt1. apply (rl_ret _ _ _ _ _ R); [exact Nb|rewrite Md; sit_mdg].
      + sit_cbn. rewrite Sm. apply (sit_seq_t _ _ _ _ S F1 G1).
        * rewrite Ef, <- (se_lens _ _ S). apply sit_teq_hl. exact TQ.
        * cbn [i_mode set_i_have set_i_lens]. unfold a_mode in Ma. rewrite Ma. exact Tm.
      + rewrite Sm. exact F2.
    - eapply sit_keep_trans; [exact K1|]. repeat split.
    - sit_cbn. exact L1.
    - unfold m_mode in *. rewrite Sm, F3. exact Md.
    - rewrite Sm, Ef. sit_cbn. lia. }
  destruct (Z.eqb_spec (e_val root) 16) as [E16|N16].
  { remember (needbits (e_bits root + 2) m1) as m3 eqn:Em3d.
    pose proof (KN src P0 m1 (e_bits root + 2) B1 L1 ltac:(lia)) as KN3. cbv zeta in KN3. rewrite <- Em3d in KN3.
    destruct KN3 as (B3 & Q3 & Em3 & Ok3 & Nok3).
    destruct (sit_keep_bits _ _ Em3) as (K3 & S3 & Rt3).
    destruct (Z.eqb_spec (m_leave m3) 1) as [L3|L3].
    + destruct (Nok3 ltac:(lia)) as (_ & _ & _ & Bl3). rewrite Inp1, Q1 in Bl3.
      cbn [negb sit_clo]. split; [|split; [eapply sit_keep_trans; eauto|split; [exact L3|]]].
      * apply (sit_rel_bits src P0 O0 m a m3 R); auto.
        -- eapply sit_keep_trans; eauto.
        -- congruence.
        -- congruence.
        -- congruence.
      * sit_split_ea EA; (eexists _, _, _; split; [exact EA|]); lia.
    + assert (L3': m_leave m3 = 0) by (destruct (Z.eq_dec (m_leave m3) 0); [auto|]; destruct (Nok3 n); lia).
      destruct (Ok3 L3') as (Bt3 & _ & _).
      destruct (sit_cl_drop2 m3 (e_bits root) 2 B3 ltac:(lia) ltac:(lia) Bt3)
        as (B4 & Q4 & B5 & Q5 & Bits4 & End5 & K5 & S5 & S4 & Rt5 & L5 & _).
      rewrite Q3, Q1 in Q5, End5, Bits4. rewrite (proj1 K3), Inp1 in End5.
      rewrite S4, S3, S1.
      destruct (Z.eqb_spec (i_have (m_s m)) 0) as [H0|H0].
      { (* no previous length to repeat *)
        assert (Mb: m_mode (set_bad (dropbits (e_bits root) m3) M_repeat) =? BAD = true) by (apply Z.eqb_eq; reflexivity).
        rewrite Mb. cbn [negb sit_clo]. unfold abad in EA.
        assert (Kt: sit_keep m (set_bad (dropbits (e_bits root) m3) M_repeat)).
        { eapply sit_keep_trans; [exact K1|]. eapply sit_keep_trans; [exact K3|]. repeat split. }
        eexists _, _. split; [exact EA|]. split; [lia|].
        split; [|split; [exact Kt|split; [|reflexivity]]].
        - apply (sit_rel_bad src P0 O0 m a); [exact R|exact Kt| |reflexivity|reflexivity|reflexivity|].
          + apply sit_bb_bad. exact B4.
          + cbn [m_s set_bad set_mode upd_s set_m_s set_m_msg dropbits set_m_bits set_m_hold i_head set_i_mode].
            rewrite S3, S1. exact (rl_head _ _ _ _ _ R).
        - cbn [m_leave set_bad set_mode upd_s set_m_s set_m_msg dropbits set_m_bits set_m_hold]. exact L3'. }
      rewrite <- (se_lens _ _ S) in EA.
      rewrite Bits4.
      assert (Mb: m_mode (dropbits 2 (dropbits (e_bits root) m3)) =? BAD = false).
      { apply Z.eqb_neq. unfold m_mode in *. rewrite S5, S3, S1. exact Nb. }
      rewrite Mb. cbn [negb].
      assert (Kt: sit_keep m (dropbits 2 (dropbits (e_bits root) m3))).
      { eapply sit_keep_trans; [exact K1|]. eapply sit_keep_trans; [exact K3|exact K5]. }
      pose proof (KR src (mq P0 m + e_bits root) 2 Bs ltac:(lia)).
      apply (sit_cl_tail m a _ (mq P0 m + e_bits root + 2) (Znth (i_have (m_s m) - 1) (i_lens (m_s m)))); auto; try congruence; lia. }
  destruct (Z.eqb_spec (e_val root) 17) as [E17|N17].
  - remember (needbits (e_bits root + 3) m1) as m3 eqn:Em3d.
    pose proof (KN src P0 m1 (e_bits root + 3) B1 L1 ltac:(lia)) as KN3. cbv zeta in KN3. rewrite <- Em3d in KN3.
    destruct KN3 as (B3 & Q3 & Em3 & Ok3 & Nok3).
    destruct (sit_keep_bits _ _ Em3) as (K3 & S3 & Rt3).
    destruct (Z.eqb_spec (m_leave m3) 1) as [L3|L3].
    + destruct (Nok3 ltac:(lia)) as (_ & _ & _ & Bl3). rewrite Inp1, Q1 in Bl3.
      cbn [negb sit_clo]. split; [|split; [eapply sit_keep_trans; eauto|split; [exact L3|]]].
      * apply (sit_rel_bits src P0 O0 m a m3 R); auto.
        -- eapply sit_keep_trans; eauto.
        -- congruence.
        -- congruence.
        -- congruence.
      * sit_split_ea EA; (eexists _, _, _; split; [exact EA|]); lia.
    + assert (L3': m_leave m3 = 0) by (destruct (Z.eq_dec (m_leave m3) 0); [auto|]; destruct (Nok3 n); lia).
      destruct (Ok3 L3') as (Bt3 & _ & _).
      destruct (sit_cl_drop2 m3 (e_bits root) 3 B3 ltac:(lia) ltac:(lia) Bt3)
        as (B4 & Q4 & B5 & Q5 & Bits4 & End5 & K5 & S5 & S4 & Rt5 & L5 & _).
      rewrite Q3, Q1 in Q5, End5, Bits4. rewrite (proj1 K3), Inp1 in End5.
      rewrite Bits4.
      assert (Mb: m_mode (dropbits 3 (dropbits (e_bits root) m3)) =? BAD = false).
      { apply Z.eqb_neq. unfold m_mode in *. rewrite S5, S3, S1. exact Nb. }
      rewrite Mb. cbn [negb].
      assert (Kt: sit_keep m (dropbits 3 (dropbits (e_bits root) m3))).
      { eapply sit_keep_trans; [exact K1|]. eapply sit_keep_trans; [exact K3|exact K5]. }
      pose proof (KR src (mq P0 m + e_bits root) 3 Bs ltac:(lia)).
      apply (sit_cl_tail m a _ (mq P0 m + e_bits root + 3) 0); auto; try congruence; lia.
  - remember (needbits (e_bits root + 7) m1) as m3 eqn:Em3d.
    pose proof (KN src P0 m1 (e_bits root + 7) B1 L1 ltac:(lia)) as KN3. cbv zeta in KN3. rewrite <- Em3d in KN3.
    destruct KN3 as (B3 & Q3 & Em3 & Ok3 & Nok3).
    destruct (sit_keep_bits _ _ Em3) as (K3 & S3 & Rt3).
    destruct (Z.eqb_spec (m_leave m3) 1) as [L3|L3].
    + destruct (Nok3 ltac:(lia)) as (_ & _ & _ & Bl3). rewrite Inp1, Q1 in Bl3.
      cbn [negb sit_clo]. split; [|split; [eapply sit_keep_trans; eauto|split; [exact L3|]]].
      * apply (sit_rel_bits src P0 O0 m a m3 R); auto.
        -- eapply sit_keep_trans; eauto.
        -- congruence.
        -- congruence.
        -- congruence.
      * sit_split_ea EA; (eexists _, _, _; split; [exact EA|]); lia.
    + assert (L3': m_leave m3 = 0) by (destruct (Z.eq_dec (m_leave m3) 0); [auto|]; destruct (Nok3 n); lia).
      destruct (Ok3 L3') as (Bt3 & _ & _).
      destruct (sit_cl_drop2 m3 (e_bits root) 7 B3 ltac:(lia) ltac:(lia) Bt3)
        as (B4 & Q4 & B5 & Q5 & Bits4 & End5 & K5 & S5 & S4 & Rt5 & L5 & _).
      rewrite Q3, Q1 in Q5, End5, Bits4. rewrite (proj1 K3), Inp1 in End5.
      rewrite Bits4.
      assert (Mb: m_mode (dropbits 7 (dropbits (e_bits root) m3)) =? BAD = false).
      { apply Z.eqb_neq. unfold m_mode in *. rewrite S5, S3, S1. exact Nb. }
      rewrite Mb. cbn [negb].
      assert (Kt: sit_keep m (dropbits 7 (dropbits (e_bits root) m3))).
      { eapply sit_keep_trans; [exact K1|]. eapply sit_keep_trans; [exact K3|exact K5]. }
      pose proof (KR src (mq P0 m + e_bits root) 7 Bs ltac:(lia)).
      apply (sit_cl_tail m a _ (mq P0 m + e_bits root + 7) 0); auto; try congruence; lia.
Qed.

Hypothesis AW : awf_stmt.

(* the abstract state of CODELENS has at most 316 code lengths to read *)
Lemma sit_cl_bound m a : rel src P0 O0 m a -> awf src a -> m_mode m = CODELENS ->
  0 <= i_have (m_s m) <= i_nlen (m_s m) + i_ndist (m_s m) /\ i_nlen (m_s m) + i_ndist (m_s m) <= 316.
Proof.
  intros R W Md.
  assert (Nb: m_mode m <> BAD) by (rewrite Md; sit_mdg).
  assert (Ma: a_mode a = CODELENS) by (rewrite <- (rl_mode _ _ _ _ _ R); exact Md).
  pose proof (rl_s _ _ _ _ _ R Nb) as S.
  destruct (md_codelens _ (aw_md _ _ W) Ma) as (A1 & A2 & A3 & _).
  rewrite (se_have _ _ S), (se_nlen _ _ S), (se_ndist _ _ S). lia.
Qed.

(* the while loop: steps along the trace until all code lengths are read, or a stop on the input, or BAD *)
Definition sit_cll (I Rl: Z) (m: mst) (a: ast) (o: clout) : Prop :=
  match o with
  | CLnext m' => exists a', areach src I Rl a a' /\ rel src P0 O0 m' a' /\ awf src a' /\ sit_keep m m' /\
      m_leave m' = 0 /\ m_mode m' = CODELENS /\ i_nlen (m_s m') + i_ndist (m_s m') <= i_have (m_s m')
  | CLleave m' => exists a', areach src I Rl a a' /\ rel src P0 O0 m' a' /\ sit_keep m m' /\ m_leave m' = 1 /\
      m_mode m' = CODELENS /\ exists n w a'', astep lenfix_list distfix_list src a' = AGo n w a'' /\ 8 * I < n
  | CLbad m' => exists a', areach src I Rl a a' /\ rel src P0 O0 m' a' /\ sit_keep m m' /\ m_leave m' = 0 /\
      m_mode m' = BAD
  end.

Lemma sit_cl_loop k : forall m a, rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> m_mode m = CODELENS ->
  316 - i_have (m_s m) < Z.of_nat k ->
  forall Rl, sit_cll (P0 + Zlength (m_inp m)) Rl m a (codelens_loop lenfix_list distfix_list k m).
Proof.
  induction k as [|k IH]; intros m a R W L Md Hk Rl.
  - pose proof (sit_cl_bound m a R W Md). cbn [codelens_loop sit_cll].
    exists a. split; [apply ar_refl|]. split; [exact R|]. split; [exact W|]. split; [apply sit_keep_refl|].
    split; [exact L|]. split; [exact Md|]. lia.
  - pose proof (sit_cl_bound m a R W Md) as Bd. cbn [codelens_loop].
    destruct (Z.ltb_spec (i_have (m_s m)) (i_nlen (m_s m) + i_ndist (m_s m))) as [Lt|Ge].
    2:{ cbn [sit_cll]. exists a. split; [apply ar_refl|]. split; [exact R|]. split; [exact W|].
        split; [apply sit_keep_refl|]. split; [exact L|]. split; [exact Md|]. lia. }
    pose proof (sit_cl_iter m a R W L Md Lt) as It.
    destruct (codelens_iter lenfix_list distfix_list m) as [m1|m1|m1]; cbn [sit_clo] in It.
    + destruct It as (n & a1 & EA & N1 & R1 & K1 & L1 & M1 & Hh).
      assert (W1: awf src a1) by exact (proj1 (proj2 AW) src a n false a1 W EA).
      specialize (IH m1 a1 R1 W1 L1 M1 ltac:(lia) Rl).
      rewrite (proj1 K1) in IH.
      destruct (codelens_loop lenfix_list distfix_list k m1) as [m2|m2|m2]; cbn [sit_cll] in IH |- *.
      * destruct IH as (a2 & T2 & H2). exists a2. split; [eapply sit_ar_cons; eauto|].
        destruct H2 as (R2 & W2 & K2 & H2). split; [exact R2|]. split; [exact W2|].
        split; [eapply sit_keep_trans; eauto|exact H2].
      * destruct IH as (a2 & T2 & R2 & K2 & H2). exists a2. split; [eapply sit_ar_cons; eauto|].
        split; [exact R2|]. split; [eapply sit_keep_trans; eauto|exact H2].
      * destruct IH as (a2 & T2 & R2 & K2 & H2). exists a2. split; [eapply sit_ar_cons; eauto|].
        split; [exact R2|]. split; [eapply sit_keep_trans; eauto|exact H2].
    + destruct It as (R1 & K1 & L1 & Hb). cbn [sit_cll]. exists a. split; [apply ar_refl|].
      split; [exact R1|]. split; [exact K1|]. split; [exact L1|]. split; [|exact Hb].
      rewrite (rl_mode _ _ _ _ _ R1). rewrite <- (rl_mode _ _ _ _ _ R). exact Md.
    + destruct It as (n & a1 & EA & N1 & R1 & K1 & L1 & M1). cbn [sit_cll]. exists a1.
      split; [eapply sit_ar1; eauto|]. auto.
Qed.

End Iter.
