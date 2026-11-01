(* The case LENLENS: the loop over the code length code lengths (one abstract step per 3-bit item), then
   the zero lengths and the code length code's table (the same inflate_table call in both machines), then
   CODELENS (SISimTabCLCase.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimTabKit.
Require Import Zlib.proof.harness.api_split_invariant.SISimTabCLCase.
Import ListNotations.
Local Open Scope Z_scope.

Section Case.
Variables (src: list Z) (P0: Z) (O0: list Z).
Hypothesis K : kit_stmt.
Hypothesis AW : awf_stmt.
Hypothesis DEC : sim_ok decode_mode.

(* the abstract state of LENLENS has at most 19 lengths to read *)
Lemma sit_ll_bound m a : rel src P0 O0 m a -> awf src a -> m_mode m = LENLENS ->
  0 <= i_have (m_s m) <= i_ncode (m_s m) /\ i_ncode (m_s m) <= 19.
Proof.
  intros R W Md.
  assert (Nb: m_mode m <> BAD) by (rewrite Md; sit_mdg).
  assert (Ma: a_mode a = LENLENS) by (rewrite <- (rl_mode _ _ _ _ _ R); exact Md).
  pose proof (rl_s _ _ _ _ _ R Nb) as S.
  destruct (md_lenlens _ (aw_md _ _ W) Ma) as (A1 & A2 & _).
  rewrite (se_have _ _ S), (se_ncode _ _ S). lia.
Qed.

(* while (have < ncode): NEEDBITS(3), one length, DROPBITS(3): steps along the trace until all are read,
   or a stop on the input *)
Lemma sit_ll_loop k : forall m a, rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> m_mode m = LENLENS ->
  19 - i_have (m_s m) <= Z.of_nat k -> forall Rl,
  let m' := lenlens_loop k m in
  exists a', areach src (P0 + Zlength (m_inp m)) Rl a a' /\ rel src P0 O0 m' a' /\ awf src a' /\
    sit_keep m m' /\ m_mode m' = LENLENS /\
    ((m_leave m' = 0 /\ i_ncode (m_s m') <= i_have (m_s m')) \/
     (m_leave m' = 1 /\ exists n w a'', astep lenfix_list distfix_list src a' = AGo n w a'' /\
                                        8 * (P0 + Zlength (m_inp m)) < n)).
Proof.
  induction k as [|k IH]; intros m a R W L Md Hk Rl; cbv zeta.
  - pose proof (sit_ll_bound m a R W Md). cbn [lenlens_loop].
    exists a. split; [apply ar_refl|]. split; [exact R|]. split; [exact W|]. split; [apply sit_keep_refl|].
    split; [exact Md|]. left. split; [exact L|]. lia.
  - pose proof (sit_ll_bound m a R W Md) as Bd. cbn [lenlens_loop].
    destruct (Z.ltb_spec (i_have (m_s m)) (i_ncode (m_s m))) as [Lt|Ge].
    2:{ exists a. split; [apply ar_refl|]. split; [exact R|]. split; [exact W|].
        split; [apply sit_keep_refl|]. split; [exact Md|]. left. split; [exact L|]. lia. }
    assert (Nb: m_mode m <> BAD) by (rewrite Md; sit_mdg).
    assert (Ma: a_mode a = LENLENS) by (rewrite <- (rl_mode _ _ _ _ _ R); exact Md).
    pose proof (rl_s _ _ _ _ _ R Nb) as S.
    pose proof (rl_bb _ _ _ _ _ R) as B.
    pose proof (rl_q _ _ _ _ _ R Nb) as Q.
    assert (Tmm: tmode (m_mode m)) by (rewrite Md; right; left; reflexivity).
    pose proof K as [[_ [KN [KD _]]] _].
    assert (EA: astep lenfix_list distfix_list src a = a_LENLENS src a) by (apply sit_a_LENLENS; exact Ma).
    unfold a_LENLENS in EA. rewrite <- (se_have _ _ S), <- (se_ncode _ _ S), Q in EA.
    destruct (Z.ltb_spec (i_have (m_s m)) (i_ncode (m_s m))) as [_|]; [|lia].
    unfold ago in EA.
    remember (needbits 3 m) as m1 eqn:Em1d.
    pose proof (KN src P0 m 3 B L ltac:(lia)) as KN1. cbv zeta in KN1. rewrite <- Em1d in KN1.
    destruct KN1 as (B1 & Q1 & Em1 & Ok1 & Nok1).
    destruct (sit_keep_bits _ _ Em1) as (K1 & S1 & Rt1).
    destruct (Z.eqb_spec (m_leave m1) 1) as [L1|L1].
    { (* out of input *)
      destruct (Nok1 ltac:(lia)) as (_ & _ & _ & Bl).
      exists a. split; [apply ar_refl|]. split; [exact (sit_rel_bits src P0 O0 m a m1 R K1 S1 Rt1 B1 Q1 Tmm)|].
      split; [exact W|]. split; [exact K1|]. split; [unfold m_mode; rewrite S1; exact Md|].
      right. split; [exact L1|]. eexists _, _, _. split; [exact EA|]. lia. }
    assert (L1': m_leave m1 = 0) by (destruct (Z.eq_dec (m_leave m1) 0); [auto|]; destruct (Nok1 n); lia).
    destruct (Ok1 L1') as (Bt1 & _ & Hold1).
    assert (Bits1: bitsn m1 3 = sbits src (mq P0 m) 3) by exact Hold1.
    set (f := fun _ : istate =>
          set_i_have (set_i_lens (m_s m1) (upd_Znth (Znth (i_have (m_s m1)) order) (i_lens (m_s m1)) (bitsn m1 3)))
                     (i_have (m_s m1) + 1)).
    set (m2 := upd_s m1 f).
    assert (B2: bitbuf src P0 m2) by (apply sit_bb_s; exact B1).
    pose proof (bb_bits _ _ _ B1) as Bb1.
    destruct (KD src P0 m2 3 B2 ltac:(cbn; lia)) as (B3 & Q3 & _).
    set (s1 := set_i_have (set_i_lens (m_s m) (upd_Znth (Znth (i_have (m_s m)) order) (i_lens (m_s m))
                                                 (sbits src (mq P0 m) 3))) (i_have (m_s m) + 1)).
    assert (Sm3: m_s (dropbits 3 m2) = s1) by (subst s1 m2 f; sit_cbng; rewrite S1, Bits1; reflexivity).
    set (a1 := {| a_s := set_i_have (set_i_lens (a_s a) (upd_Znth (Znth (i_have (m_s m)) order) (i_lens (a_s a))
                                                           (sbits src (mq P0 m) 3))) (i_have (m_s m) + 1);
                  a_q := mq P0 m + 3; a_O := a_O a |}).
    fold a1 in EA.
    pose proof (sit_hl_facts (m_s m) (i_have (m_s m) + 1)
                  (upd_Znth (Znth (i_have (m_s m)) order) (i_lens (m_s m)) (sbits src (mq P0 m) 3)))
      as (F1 & F2 & F3 & F4 & F5).
    pose proof (sit_hl_facts (a_s a) (i_have (m_s m) + 1)
                  (upd_Znth (Znth (i_have (m_s m)) order) (i_lens (a_s a)) (sbits src (mq P0 m) 3)))
      as (G1 & G2 & G3 & G4 & G5).
    cbv zeta in F1, F2, F3, F4, F5, G1, G2, G3, G4, G5. fold s1 in F1, F2, F3, F4, F5.
    assert (K3: sit_keep m (dropbits 3 m2)) by (eapply sit_keep_trans; [exact K1|]; repeat split).
    assert (M3: m_mode (dropbits 3 m2) = LENLENS) by (unfold m_mode in *; rewrite Sm3, F3; exact Md).
    assert (R3: rel src P0 O0 (dropbits 3 m2) a1).
    { apply (sit_rel_tab src P0 O0 m a); [exact R|exact Tmm| |exact K3|exact B3| | |reflexivity| | | |exact G4|exact G5].
      - rewrite M3. right; left; reflexivity.
      - rewrite M3. unfold a_mode, a1. cbn [a_s]. rewrite G3. symmetry. exact Ma.
      - unfold a1. cbn [a_q]. rewrite Q3. transitivity (mq P0 m1 + 3); [rewrite Q1; reflexivity|reflexivity].
      - change (m_ret (dropbits 3 m2)) with (m_ret m1). rewrite Rt1. apply (rl_ret _ _ _ _ _ R); [exact Nb|].
        rewrite Md; sit_mdg.
      - rewrite Sm3. unfold a1. cbn [a_s]. apply (sit_seq_t _ _ _ _ S F1 G1).
        + unfold s1. rewrite <- (se_lens _ _ S). apply sit_teq_hl. apply sit_teq_of_seq. exact S.
        + rewrite G3. unfold a_mode in Ma. rewrite Ma. right; left; reflexivity.
      - rewrite Sm3. exact F2. }
    assert (W1: awf src a1) by exact (proj1 (proj2 AW) src a _ _ a1 W EA).
    assert (L3: m_leave (dropbits 3 m2) = 0) by exact L1'.
    assert (N3: mq P0 m + 3 <= 8 * (P0 + Zlength (m_inp m))).
    { pose proof (sit_bb_end _ _ _ B1). rewrite Q1, (proj1 K1) in *. lia. }
    assert (H3: i_have (m_s (dropbits 3 m2)) = i_have (m_s m) + 1) by (rewrite Sm3; reflexivity).
    specialize (IH (dropbits 3 m2) a1 R3 W1 L3 M3 ltac:(rewrite H3; lia) Rl). cbv zeta in IH.
    rewrite (proj1 K3) in IH.
    destruct IH as (a2 & T2 & R2 & W2 & K2 & M2 & H2).
    exists a2. split; [eapply sit_ar_cons; [exact EA|exact N3|exact T2]|].
    split; [exact R2|]. split; [exact W2|]. split; [eapply sit_keep_trans; eauto|]. split; [exact M2|exact H2].
Qed.

(* the istate after the code length code's table *)
Definition sit_ll_tab (z: istate) (codes: list entry) (nxt lb: Z) : istate :=
  set_i_lenbits (set_i_next (set_i_codes (set_i_lenbits (set_i_distcode (set_i_lencode (set_i_next z 0)
    (TCodes 0)) (TCodes 0)) 7) codes) nxt) lb.

(* the relation in CODELENS after the table, from LENLENS after the zero lengths z, za *)
Lemma sit_ll_rel m a z za codes nxt lb :
  rel src P0 O0 m a -> m_mode m = LENLENS -> sit_tsame (m_s m) z -> sit_skeep (m_s m) z ->
  sit_tsame (a_s a) za -> i_flags za = i_flags (a_s a) -> i_check za = i_check (a_s a) -> sit_teq z za ->
  rel src P0 O0 (set_mode (upd_s (set_m_ret (set_m_s m (sit_ll_tab z codes nxt lb)) 0) (fun s => set_i_have s 0)) CODELENS)
    (AS (set_i_mode (set_i_have (sit_ll_tab za codes nxt lb) 0) CODELENS) (mq P0 m) (a_O a)).
Proof.
  intros R Md F1 F2 G1 G4 G5 TZ.
  assert (Nb: m_mode m <> BAD) by (rewrite Md; sit_mdg).
  pose proof (rl_s _ _ _ _ _ R Nb) as S.
  pose proof TZ as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
  apply (sit_rel_tab src P0 O0 m a); [exact R|rewrite Md; right; left; reflexivity| | | | | | reflexivity | | | | |].
  - right; right; left; reflexivity.
  - repeat split.
  - apply (sit_bb_eq src P0 m); try reflexivity. exact (rl_bb _ _ _ _ _ R).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply (sit_seq_t _ _ _ _ S).
    + eapply sit_tsame_trans; [exact F1|]. unfold sit_ll_tab. sit_cbng. repeat split.
    + eapply sit_tsame_trans; [exact G1|]. unfold sit_ll_tab. sit_cbng. repeat split.
    + unfold sit_ll_tab. sit_cbng. repeat split; auto.
    + right; right; left; reflexivity.
  - eapply sit_skeep_trans; [exact F2|]. unfold sit_ll_tab. sit_cbng. repeat split.
  - unfold sit_ll_tab. sit_cbng. exact G4.
  - unfold sit_ll_tab. sit_cbng. exact G5.
Qed.

(* from LENLENS after the table: the step to CODELENS, then CODELENS (SISimTabCLCase.v) *)
Lemma sit_ll_next flush m a z za codes nxt lb :
  rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> m_mode m = LENLENS ->
  sit_tsame (m_s m) z -> sit_skeep (m_s m) z ->
  sit_tsame (a_s a) za -> i_flags za = i_flags (a_s a) -> i_check za = i_check (a_s a) -> sit_teq z za ->
  astep lenfix_list distfix_list src a =
    AGo (mq P0 m) false (AS (set_i_mode (set_i_have (sit_ll_tab za codes nxt lb) 0) CODELENS) (mq P0 m) (a_O a)) ->
  sit_out flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a
    (c_CODELENS flush lenfix_list distfix_list (fast lenfix_list distfix_list)
       (set_mode (upd_s (set_m_ret (set_m_s m (sit_ll_tab z codes nxt lb)) 0) (fun s => set_i_have s 0)) CODELENS)).
Proof.
  intros R W L Md F1 F2 G1 G4 G5 TZ EA.
  pose proof (sit_ll_rel m a z za codes nxt lb R Md F1 F2 G1 G4 G5 TZ) as R3.
  pose proof (proj1 (proj2 AW) src a _ _ _ W EA) as W3.
  pose proof (sit_mq_end _ _ _ (rl_bb _ _ _ _ _ R)) as Qe.
  apply (sit_out_pre _ _ _ _ _ _ _ _ _ (sit_ar1 _ _ _ _ _ _ EA Qe)).
  exact (sit_cl_case src P0 O0 K AW DEC flush _ _ R3 W3 L eq_refl).
Qed.

Lemma sit_ll_case flush m a :
  rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> m_mode m = LENLENS ->
  sit_out flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a
    (c_LENLENS flush lenfix_list distfix_list (fast lenfix_list distfix_list) m).
Proof.
  intros R W L Md.
  pose proof (sit_ll_bound m a R W Md) as Bd.
  pose proof (sit_ll_loop 19 m a R W L Md ltac:(cbn; lia) (Zlength O0 + m_aout m)) as LP. cbv zeta in LP.
  unfold c_LENLENS.
  destruct LP as (a1 & T1 & R1 & W1 & K1 & M1 & [[L1 Hh]|[L1 (n & w & a2 & EA & Bl)]]).
  2:{ (* out of input *)
    rewrite L1. cbn [Z.eqb Pos.eqb]. cbn [sit_out]. exists a1.
    split; [exact T1|]. split; [exact R1|]. intros _. unfold stop_ok. rewrite EA.
    split; [apply (rl_ret _ _ _ _ _ R1); rewrite M1; sit_mdg|].
    right; right. left. cbn [blocked]. left. exact Bl. }
  rewrite L1. cbn [Z.eqb].
  apply (sit_out_pre _ _ _ _ _ _ _ a1 _ T1).
  pose proof K1 as (Inp1 & Ao1 & _). rewrite <- Inp1, <- Ao1.
  remember (lenlens_loop 19 m) as m1 eqn:Em1. clear Em1.
  clear T1 R W L Md Bd K1 Inp1 Ao1 a m.
  rename m1 into m, a1 into a, R1 into R, W1 into W, L1 into L, M1 into Md.
  assert (Nb: m_mode m <> BAD) by (rewrite Md; sit_mdg).
  assert (Ma: a_mode a = LENLENS) by (rewrite <- (rl_mode _ _ _ _ _ R); exact Md).
  pose proof (rl_s _ _ _ _ _ R Nb) as S.
  pose proof (rl_bb _ _ _ _ _ R) as B.
  pose proof (rl_q _ _ _ _ _ R Nb) as Q.
  pose proof (sit_mq_end _ _ _ B) as Qe.
  assert (Tmm: tmode (m_mode m)) by (rewrite Md; right; left; reflexivity).
  assert (EA: astep lenfix_list distfix_list src a = a_LENLENS src a) by (apply sit_a_LENLENS; exact Ma).
  unfold a_LENLENS in EA. rewrite <- (se_have _ _ S), <- (se_ncode _ _ S), Q in EA.
  destruct (Z.ltb_spec (i_have (m_s m)) (i_ncode (m_s m))) as [|_]; [lia|].
  pose proof (sit_teq_of_seq _ _ S) as TQ.
  pose proof TQ as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
  (* the zero lengths: the same in both machines *)
  pose proof (sit_llz_facts 19 (m_s m)) as (F1 & F2 & F3 & F4 & F5).
  pose proof (sit_llz_facts 19 (a_s a)) as (G1 & G2 & G3 & G4 & G5).
  pose proof (sit_teq_llz 19 _ _ TQ) as TZ.
  cbv zeta in F1, F2, F3, F4, F5, G1, G2, G3, G4, G5.
  remember (lenlens_zero 19 (m_s m)) as z eqn:Ez. remember (lenlens_zero 19 (a_s a)) as za eqn:Eza.
  clear Ez Eza.
  pose proof TZ as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
  (* the code length code's table: the same call in both machines *)
  match goal with |- context [call_table CODES 0 19 7 ?sm] =>
    match type of EA with context [call_table CODES 0 19 7 ?sa] =>
      replace (call_table CODES 0 19 7 sa) with (call_table CODES 0 19 7 sm) in EA
        by (apply sit_call_table_ext; sit_cbng; congruence);
      destruct (call_table CODES 0 19 7 sm) as [[[r codes] nxt] lb]
    end end.
  destruct (Z.eqb_spec r 0) as [Er|Er]; cbn [negb] in EA |- *.
  2:{ (* inflate_table failed *)
    unfold abad in EA. cbn [sit_out]. eexists. split; [eapply sit_ar1; [exact EA|exact Qe]|].
    split; [|intros X; rewrite sit_leave_bad, sit_leave_ret, sit_leave_s, L in X; discriminate X].
    apply (sit_rel_bad src P0 O0 m a); [exact R| | |reflexivity|reflexivity|reflexivity|].
    - repeat split.
    - apply sit_bb_bad, sit_bb_ret, sit_bb_s. exact B.
    - sit_cbng. destruct F2 as (_ & _ & _ & E & _). rewrite E. exact (rl_head _ _ _ _ _ R). }
  subst r. unfold ago in EA.
  exact (sit_ll_next flush m a z za codes nxt lb R W L Md F1 F2 G1 G4 G5 TZ EA).
Qed.

End Case.
