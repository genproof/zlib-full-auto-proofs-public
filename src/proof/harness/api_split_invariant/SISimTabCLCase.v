(* The case CODELENS: the while loop over the code lengths (SISimTabCL.v), then the literal/length and
   distance tables (the same inflate_table calls on equal fields in both machines, so equal results), then
   LEN_, from where the decode modes go on (sim_ok decode_mode). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimTabKit.
Require Import Zlib.proof.harness.api_split_invariant.SISimTabCL.
Import ListNotations.
Local Open Scope Z_scope.

Section Case.
Variables (src: list Z) (P0: Z) (O0: list Z).
Hypothesis K : kit_stmt.
Hypothesis AW : awf_stmt.
Hypothesis DEC : sim_ok decode_mode.

Lemma sit_cl_case flush m a :
  rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> m_mode m = CODELENS ->
  sit_out flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a
    (c_CODELENS flush lenfix_list distfix_list (fast lenfix_list distfix_list) m).
Proof.
  intros R W L Md.
  pose proof (sit_cl_bound src P0 O0 m a R W Md) as Bd.
  pose proof (sit_cl_loop src P0 O0 K AW 320 m a R W L Md ltac:(cbn; lia) (Zlength O0 + m_aout m)) as LP.
  unfold c_CODELENS.
  destruct (codelens_loop lenfix_list distfix_list 320 m) as [m1|m1|m1]; cbn [sit_cll] in LP.
  3:{ destruct LP as (a1 & T1 & R1 & K1 & L1 & M1). cbn [sit_out]. exists a1.
      split; [exact T1|]. split; [exact R1|]. intros X. lia. }
  2:{ destruct LP as (a1 & T1 & R1 & K1 & L1 & M1 & n & w & a2 & EA & Bl). cbn [sit_out]. exists a1.
      split; [exact T1|]. split; [exact R1|]. intros _. unfold stop_ok. rewrite EA.
      split; [apply (rl_ret _ _ _ _ _ R1); rewrite M1; sit_mdg|].
      right; right. left. cbn [blocked]. left. exact Bl. }
  destruct LP as (a1 & T1 & R1 & W1 & K1 & L1 & M1 & Hh).
  apply (sit_out_pre _ _ _ _ _ _ _ a1 _ T1).
  pose proof K1 as (Inp1 & Ao1 & _). rewrite <- Inp1, <- Ao1.
  clear T1 R W L Md Bd K1 Inp1 Ao1 a m.
  rename m1 into m, a1 into a, R1 into R, W1 into W, L1 into L, M1 into Md.
  assert (Nb: m_mode m <> BAD) by (rewrite Md; sit_mdg).
  assert (Ma: a_mode a = CODELENS) by (rewrite <- (rl_mode _ _ _ _ _ R); exact Md).
  pose proof (rl_s _ _ _ _ _ R Nb) as S.
  pose proof (rl_bb _ _ _ _ _ R) as B.
  pose proof (rl_q _ _ _ _ _ R Nb) as Q.
  pose proof (sit_mq_end _ _ _ B) as Qe.
  assert (Tmm: tmode (m_mode m)) by (rewrite Md; right; right; left; reflexivity).
  assert (EA: astep lenfix_list distfix_list src a = a_CODELENS lenfix_list distfix_list src a)
    by (apply sit_a_CODELENS; exact Ma).
  unfold a_CODELENS in EA.
  rewrite <- (se_nlen _ _ S), <- (se_ndist _ _ S), <- (se_have _ _ S) in EA.
  destruct (Z.ltb_spec (i_have (m_s m)) (i_nlen (m_s m) + i_ndist (m_s m))) as [|_]; [lia|].
  rewrite <- (se_lens _ _ S), Q in EA.
  destruct (Z.eqb_spec (Znth 256 (i_lens (m_s m))) 0) as [Z0|Z0].
  { (* no end-of-block code *)
    unfold abad in EA. cbn [sit_out]. eexists. split; [eapply sit_ar1; [exact EA|exact Qe]|].
    split; [|intros X; cbn in X; lia].
    apply (sit_rel_bad src P0 O0 m a); [exact R| | |reflexivity|reflexivity|reflexivity|].
    - repeat split.
    - apply sit_bb_bad. exact B.
    - exact (rl_head _ _ _ _ _ R). }
  pose proof (sit_teq_of_seq _ _ S) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
  (* the literal/length table: the same call in both machines *)
  rewrite (sit_call_table_ext _ _ _ _ (set_i_lenbits (set_i_lencode (set_i_next (a_s a) 0) (TCodes 0)) 9)
             (set_i_lenbits (set_i_lencode (set_i_next (m_s m) 0) (TCodes 0)) 9)) in EA
    by (sit_cbng; congruence).
  replace (i_nlen (set_i_lenbits (set_i_lencode (set_i_next (a_s a) 0) (TCodes 0)) 9))
    with (i_nlen (set_i_lenbits (set_i_lencode (set_i_next (m_s m) 0) (TCodes 0)) 9)) in EA
    by (sit_cbng; congruence).
  destruct (call_table LENS 0 _ 9 (set_i_lenbits (set_i_lencode (set_i_next (m_s m) 0) (TCodes 0)) 9))
    as [[[r codes] nxt] lb].
  destruct (Z.eqb_spec r 0) as [Er|Er]; cbn [negb] in EA |- *.
  2:{ (* inflate_table failed *)
    unfold abad in EA. cbn [sit_out]. eexists. split; [eapply sit_ar1; [exact EA|exact Qe]|].
    split; [|intros X; cbn in X; lia].
    apply (sit_rel_bad src P0 O0 m a); [exact R| | |reflexivity|reflexivity|reflexivity|].
    - repeat split.
    - apply sit_bb_bad, sit_bb_ret, sit_bb_s. exact B.
    - exact (rl_head _ _ _ _ _ R). }
  subst r.
  (* the distance table: the same call in both machines *)
  match goal with |- context [call_table DISTS ?x ?y 6 ?sm] =>
    match type of EA with context [call_table DISTS ?x' ?y' 6 ?sa] =>
      replace (call_table DISTS x' y' 6 sa) with (call_table DISTS x y 6 sm) in EA
        by (unfold call_table; sit_cbng; congruence);
      destruct (call_table DISTS x y 6 sm) as [[[r codes0] nxt0] db]
    end end.
  destruct (Z.eqb_spec r 0) as [Er|Er]; cbn [negb] in EA |- *.
  2:{ (* inflate_table failed *)
    unfold abad in EA. cbn [sit_out]. eexists. split; [eapply sit_ar1; [exact EA|exact Qe]|].
    split; [|intros X; cbn in X; lia].
    apply (sit_rel_bad src P0 O0 m a); [exact R| | |reflexivity|reflexivity|reflexivity|].
    - repeat split.
    - apply sit_bb_bad, sit_bb_ret, sit_bb_s, sit_bb_ret, sit_bb_s. exact B.
    - exact (rl_head _ _ _ _ _ R). }
  subst r. unfold ago in EA.
  match goal with |- context [IBrk (set_leave ?m4)] => set (M4 := m4) end.
  match type of EA with _ = AGo _ _ ?a2 => set (A2 := a2) in EA end.
  assert (R4: rel src P0 O0 M4 A2).
  { apply (sit_rel_tab src P0 O0 m a); [exact R|exact Tmm| | | | | | reflexivity | | | | |]; subst M4 A2.
    - sit_cbng. right; right; right; reflexivity.
    - repeat split.
    - apply (sit_bb_eq src P0 m); try reflexivity. exact B.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - apply (sit_seq_t _ _ _ _ S).
      + sit_cbng. repeat split.
      + sit_cbng. repeat split.
      + sit_cbng. repeat split; auto.
      + sit_cbng. right; right; right; reflexivity.
    - sit_cbng. repeat split.
    - reflexivity.
    - reflexivity. }
  assert (W4: awf src A2) by exact (proj1 (proj2 AW) src a _ _ A2 W EA).
  assert (T4: areach src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a A2) by (eapply sit_ar1; [exact EA|exact Qe]).
  assert (M4L: m_mode M4 = LEN_) by reflexivity.
  destruct (Z.eqb_spec flush Z_TREES) as [Ft|Ft].
  - (* Z_TREES stops before the first code *)
    cbn [sit_out]. exists A2. split; [exact T4|]. split; [apply sit_rel_leave; exact R4|].
    intros _. unfold stop_ok. rewrite (sit_a_LEN_ src A2 ltac:(rewrite <- (rl_mode _ _ _ _ _ R4); exact M4L)).
    unfold a_LEN_, ago. split; [reflexivity|]. right; left; exact Ft.
  - (* LEN_ goes on into the decode modes *)
    rewrite <- (sit_c_LEN_ flush M4 M4L).
    apply (sit_out_pre _ _ _ _ _ _ _ A2 _ T4).
    replace (m_inp m) with (m_inp M4) by reflexivity. replace (m_aout m) with (m_aout M4) by reflexivity.
    apply (sit_sim_ok_out decode_mode flush src P0 O0 M4 A2 DEC R4 W4); [exact L|].
    rewrite M4L. left. reflexivity.
Qed.

End Case.
