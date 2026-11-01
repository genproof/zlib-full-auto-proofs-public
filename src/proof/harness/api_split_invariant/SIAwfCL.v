(* The abstract step of CODELENS keeps the invariant awfx (SIAwfKit.v): one code length (or a repeat)
   read with the code length code's table, and at the end the literal/length and distance tables built
   by inflate_table (valid by the covering facts, replicated and with distances up to 32768 by
   tabrep_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SIAwfKit.
Require Zlib.proof.inflate.Step3Tables Zlib.proof.inflate.Cover2 Zlib.proof.inflate.InvQ5.
Import ListNotations.
Local Open Scope Z_scope.

(* trep of a table read through another accessor that agrees with it on the entries the table uses
   (trep reads the root entries and, through the links of the table's kind, the sub-table entries) *)
Lemma trep_ext: forall kind g1 g2 rb sz lk,
  tvalid_g kind g1 rb sz -> (forall op, lk op = true -> islink kind op = true) ->
  (forall i, 0 <= i < sz -> g1 i = g2 i) -> trep g1 rb lk -> trep g2 rb lk.
Proof.
  intros kind g1 g2 rb sz lk [RB SZ ROOT] LK G [T1 T2].
  pose proof (Z.pow_pos_nonneg 2 rb ltac:(lia)) as P.
  split.
  - intros i j Hi Hj L E.
    assert (Ei: g2 i = g1 i) by (symmetry; apply G; lia).
    assert (Ej: g2 j = g1 j) by (symmetry; apply G; lia).
    rewrite Ei, Ej in *. apply T1; auto.
  - intros i Hi L j k Hj Hk E.
    assert (Ei: g2 i = g1 i) by (symmetry; apply G; lia).
    rewrite Ei in *.
    destruct (ROOT i Hi) as [_ R]. cbv zeta in R. rewrite (LK _ L) in R.
    destruct R as (_ & _ & _ & J).
    destruct (J j Hj) as [Ij _]. destruct (J k Hk) as [Ik _].
    rewrite <- (G _ Ij), <- (G _ Ik) in *. apply T2; auto.
Qed.

(* a CODELENS state with new code lengths L, the first h of them read: still a CODELENS state *)
Lemma awfx_cl_lens: forall src a L h n, awfx src a -> a_mode a = CODELENS ->
  i_have (a_s a) <= h <= i_nlen (a_s a) + i_ndist (a_s a) -> Zlength L = 320 ->
  Forall (fun x => 0 <= x <= 65535) L -> (forall k, 0 <= k < h -> Znth k L <= 15) -> a_q a <= n ->
  awfx src (AS (set_i_have (set_i_lens (a_s a) L) h) n (a_O a)).
Proof.
  intros src [s q O] L h n W Md H ZL FL LE Q. unfold a_mode in *. cbn [a_s a_q a_O] in *.
  destruct W as [W0 BK GZ]. cbn [a_s a_q a_O] in *.
  pose proof (aw_md _ _ W0) as MD. pose proof (aw_swf _ _ W0) as S.
  destruct (md_codelens _ MD Md) as (H0 & Hnl & Hnd & LC & TV & _).
  pose proof (proj2 (aw_tp _ _ W0) Md) as TR.
  pose proof (aw_q _ _ W0) as Q0. cbn [a_s a_q a_O a_mode] in *.
  apply awfx_intro; simpl; auto.
  all: try (intros; md_absurd).
  - apply (aw_src _ _ W0).
  - apply Zlib.proof.inflate.Step3Tables.tb_swf_lens; auto. lia.
  - constructor; simpl; intros; try md_absurd.
    2:{ repeat split; intros; md_absurd. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [auto|]. split; [|auto].
    apply tvalid_codes with s; auto.
  - constructor; simpl; intros; md_absurd.
  - split; simpl; intros; [md_absurd|].
    rewrite (tab_entry_codes _ _ (set_i_have (set_i_lens s L) h) s _ eq_refl). exact TR.
  - apply (aw_wbits _ _ W0).
  - apply (aw_wrap _ _ W0).
  - apply (aw_dict _ _ W0).
  - apply (aw_head _ _ W0).
  - rewrite Md. mdc. lia.
  - lia.
  - apply (aw_O _ _ W0).
  - intros _. apply (aw_chk _ _ W0). cbn [a_mode a_s]. unfold data_mode; tauto.
Qed.

(* a repeat of a code length (16, 17, 18): too many lengths go to BAD, otherwise copy lengths are filled *)
Lemma go_cl_repeat: forall src a nx len copy, awfx src a -> a_mode a = CODELENS ->
  a_q a <= nx -> 0 <= len <= 15 -> 0 <= copy ->
  go_ok src a (if i_nlen (a_s a) + i_ndist (a_s a) <? i_have (a_s a) + copy then abad a nx
               else ago a nx (lens_fill (Z.to_nat copy) len (a_s a))).
Proof.
  intros src a nx len copy W Md Q HL HC.
  destruct (Z.ltb_spec (i_nlen (a_s a) + i_ndist (a_s a)) (i_have (a_s a) + copy)) as [B|B];
    [apply go_abad; auto|].
  pose proof (aw_md _ _ (ax_w _ _ W)) as MD. pose proof (aw_swf _ _ (ax_w _ _ W)) as S.
  destruct (md_codelens _ MD Md) as (H0 & Hnl & Hnd & _ & _ & LE).
  destruct (sw_lens _ S) as [ZL FL].
  destruct (Zlib.proof.inflate.Step3Tables.tb_lens_fill (Z.to_nat copy) len (a_s a)) as (L & E & ZL' & FL' & LE');
    auto; try lia; try (rewrite Z2Nat.id; lia).
  rewrite E. apply go_ago; auto. rewrite Z2Nat.id in * by lia. apply awfx_cl_lens; auto; lia.
Qed.

(* the step to BAD with a new state s that keeps the frame of a *)
Lemma go_abad_s: forall src a s n, awfx src a -> swf s ->
  i_wbits s = i_wbits (a_s a) -> i_wrap s = i_wrap (a_s a) -> i_havedict s = i_havedict (a_s a) ->
  i_head s = i_head (a_s a) -> i_back s = i_back (a_s a) -> a_q a <= n ->
  go_ok src a (abad (AS s n (a_O a)) n).
Proof.
  intros src a s n W S E1 E2 E3 E4 E5 Q. destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  unfold abad, go_ok. cbn [a_s a_O a_q]. split; [|split; [lia | split; [auto | left; auto]]].
  apply awfx_bad; auto; [eapply ax_src; eauto | rewrite E1; auto | rewrite E2; auto | rewrite E3; auto |
    rewrite E4; auto | rewrite E5; auto | lia].
Qed.

Lemma awf_codelens : tabrep_stmt -> case_ok CODELENS.
Proof.
  intros TR src a W Md. rewrite astep_CODELENS by exact Md. unfold a_CODELENS. cbv zeta.
  pose proof (ax_w _ _ W) as W0.
  pose proof (aw_md _ _ W0) as MD. pose proof (aw_swf _ _ W0) as S.
  destruct (md_codelens _ MD Md) as (H0 & Hnl & Hnd & LC & TV & LE).
  destruct (sw_lens _ S) as [ZL FL]. pose proof (sw_lenbits _ S) as LB.
  pose proof (aw_q _ _ W0) as Q0.
  destruct (Z.ltb_spec (i_have (a_s a)) (i_nlen (a_s a) + i_ndist (a_s a))) as [HL|HL].
  - rewrite adecode_nolink.
    set (here := tab_entry lenfix_list distfix_list (a_s a) (i_lencode (a_s a)) (sbits src (a_q a) (i_lenbits (a_s a)))).
    assert (EO: entry_ok here) by (eapply tvalid_root_ok; [exact TV | apply sbits_range; lia]).
    destruct EO as (Op & Bt & Vl).
    cbv beta iota.
    destruct (Z.ltb_spec (e_val here) 16).
    + apply go_ago; [|lia]. apply awfx_cl_lens; auto; try lia.
      * rewrite upd_Znth_Zlength; lia.
      * apply Forall_upd_Znth; auto; lia.
      * intros k Hk. destruct (Z.eq_dec k (i_have (a_s a))).
        -- subst k. rewrite upd_Znth_same by lia. lia.
        -- rewrite upd_Znth_diff by lia. apply LE; lia.
    + destruct (Z.eqb_spec (e_val here) 16).
      * cbv beta iota. destruct (Z.eqb_spec (i_have (a_s a)) 0); [apply go_abad; auto; lia|].
        pose proof (sbits_range src (a_q a + e_bits here) 2 ltac:(lia)).
        assert (IN: In (Znth (i_have (a_s a) - 1) (i_lens (a_s a))) (i_lens (a_s a))) by (apply Znth_In; lia).
        rewrite Forall_forall in FL. specialize (FL _ IN). pose proof (LE (i_have (a_s a) - 1) ltac:(lia)).
        apply go_cl_repeat; auto; lia.
      * destruct (Z.eqb_spec (e_val here) 17); cbv beta iota.
        -- pose proof (sbits_range src (a_q a + e_bits here) 3 ltac:(lia)).
           apply go_cl_repeat; auto; lia.
        -- pose proof (sbits_range src (a_q a + e_bits here) 7 ltac:(lia)).
           apply go_cl_repeat; auto; lia.
  - destruct (Z.eqb_spec (Znth 256 (i_lens (a_s a))) 0) as [Z256|Z256]; [apply go_abad; auto; lia|].
    assert (Hh: i_have (a_s a) = i_nlen (a_s a) + i_ndist (a_s a)) by lia.
    destruct (sw_codes _ S) as [ZC FC].
    set (s1 := set_i_lenbits (set_i_lencode (set_i_next (a_s a) 0) (TCodes 0)) 9).
    assert (S1: swf s1) by (destruct S; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES; lia).
    assert (IN1: inputs_ok LENS (sublist 0 (0 + i_nlen s1) (i_lens s1)) 9).
    { unfold inputs_ok. simpl. rewrite Zlength_sublist by lia. split; [unfold LENS; lia|].
      split; [unfold max_codes; simpl; lia|]. split; [|lia].
      apply Zlib.proof.inflate.Step3Tables.tb_forall_sublist; try lia. intros k Hk. split.
      - rewrite Forall_forall in FL. apply FL. apply Znth_In; lia.
      - apply LE; lia. }
    assert (CAP1: cap_ok LENS (sublist 0 (0 + i_nlen s1) (i_lens s1)) 9 (ENOUGH_CODES - i_next s1)).
    { unfold cap_ok. simpl. unfold LENS, CODES, DISTS, ENOUGH_LENS, ENOUGH_CODES. split; [intros; lia|].
      split; intros; lia. }
    destruct (call_table LENS 0 (i_nlen s1) 9 s1) as [[[r1 c1] n1] b1] eqn:CT1.
    destruct (Zlib.proof.inflate.Step3Tables.tb_call_table LENS 0 (i_nlen s1) 9 s1 r1 c1 n1 b1
                Zlib.proof.inflate.Cover2.cover2_proof S1 ltac:(lia) ltac:(simpl; lia) ltac:(simpl; lia)
                IN1 CAP1 ltac:(unfold LENS, CODES; lia) CT1) as (ZC1 & FC1 & R1 & Rn1 & Ry1).
    destruct (Z.eqb_spec r1 0) as [R10|R10].
    2:{ cbn [negb]. destruct (Rn1 R10) as [-> ->].
        apply go_abad_s; auto; [|lia].
        unfold s1. destruct S; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES in *; lia. }
    subst r1. cbn [negb].
    destruct (Ry1 eq_refl) as (used1 & t1 & M1 & En1 & Ec1 & Zt1 & T1 & U1 & U1L).
    specialize (U1L eq_refl). change (i_next s1) with 0 in *.
    rewrite sublist_nil in Ec1. simpl app in Ec1. subst c1 n1.
    pose proof (tv_rb _ _ _ _ T1) as RB1.
    set (s2 := set_i_lenbits (set_i_next (set_i_codes s1 t1) (0 + used1)) b1).
    set (s3 := set_i_distbits (set_i_distcode s2 (TCodes (i_next s2))) 6).
    assert (S3: swf s3).
    { destruct S; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES, ENOUGH_LENS in *; try lia. }
    assert (IN2: inputs_ok DISTS (sublist (i_nlen s3) (i_nlen s3 + i_ndist s3) (i_lens s3)) 6).
    { unfold inputs_ok. simpl. rewrite Zlength_sublist by lia. split; [unfold DISTS; lia|].
      split; [unfold max_codes; simpl; lia|]. split; [|lia].
      apply Zlib.proof.inflate.Step3Tables.tb_forall_sublist; try lia. intros k Hk. split.
      - rewrite Forall_forall in FL. apply FL. apply Znth_In; lia.
      - apply LE; lia. }
    assert (CAP2: cap_ok DISTS (sublist (i_nlen s3) (i_nlen s3 + i_ndist s3) (i_lens s3)) 6 (ENOUGH_CODES - i_next s3)).
    { unfold cap_ok. simpl. unfold LENS, CODES, DISTS, ENOUGH_LENS, ENOUGH_DISTS, ENOUGH_CODES in *.
      split; [intros; lia|]. split; intros; lia. }
    destruct (call_table DISTS (i_nlen s3) (i_ndist s3) 6 s3) as [[[r2 c2] n2] d2] eqn:CT2.
    destruct (Zlib.proof.inflate.Step3Tables.tb_call_table DISTS (i_nlen s3) (i_ndist s3) 6 s3 r2 c2 n2 d2
                Zlib.proof.inflate.Cover2.cover2_proof S3 ltac:(simpl; lia) ltac:(simpl; lia)
                ltac:(simpl; lia) IN2 CAP2 ltac:(unfold DISTS, CODES; lia) CT2) as (ZC2 & FC2 & R2 & Rn2 & Ry2).
    destruct (Z.eqb_spec r2 0) as [R20|R20].
    2:{ cbn [negb]. destruct (Rn2 R20) as [E2 E3]. subst n2 d2.
        apply go_abad_s; auto; [|lia]. destruct S3; constructor; simpl; auto. }
    subst r2. cbn [negb].
    destruct (Ry2 eq_refl) as (used2 & t2 & M2 & En2 & Ec2 & Zt2 & T2 & U2 & _).
    change (i_next s3) with (0 + used1) in *. change (i_codes s3) with t1 in *. subst c2 n2.
    pose proof (tv_rb _ _ _ _ T2) as RB2.
    unfold ENOUGH_CODES, ENOUGH_LENS in *.
    assert (G1: forall i, 0 <= i < used1 -> Znth (0 + i) (sublist 0 (0 + used1) t1 ++ t2) = Znth i t1).
    { intros i Hi. rewrite Znth_app1 by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia.
      f_equal; lia. }
    assert (G2: forall i, 0 <= i < used2 -> Znth (0 + used1 + i) (sublist 0 (0 + used1) t1 ++ t2) = Znth i t2).
    { intros i Hi. rewrite Znth_app2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
      f_equal; lia. }
    assert (ZO1: Zlength (sublist 0 1444 (i_codes s1)) = 1444 - 0)
      by (rewrite Zlength_sublist; simpl; lia).
    rewrite <- ZO1 in CAP1.
    assert (FO1: Forall entry_ok (sublist 0 1444 (i_codes s1))) by (apply Forall_sublist; exact FC).
    assert (ZO2: Zlength (sublist (0 + used1) 1444 t1) = 1444 - (0 + used1))
      by (rewrite Zlength_sublist; lia).
    rewrite <- ZO2 in CAP2.
    assert (FO2: Forall entry_ok (sublist (0 + used1) 1444 t1)) by (apply Forall_sublist; exact FC1).
    pose proof (proj1 TR LENS _ 9 _ b1 used1 t1 IN1 ltac:(unfold LENS, CODES; lia) CAP1 FO1 M1) as TRL.
    pose proof (proj1 TR DISTS _ 6 _ d2 used2 t2 IN2 ltac:(unfold DISTS, CODES; lia) CAP2 FO2 M2) as TRD.
    pose proof (proj1 (proj2 (proj2 (proj2 TR))) _ 6 _ d2 used2 t2 IN2 CAP2 FO2 M2) as DOK.
    pose proof (InvQ5.cover3_proof LENS _ 9 _ b1 used1 t1 IN1 ltac:(unfold LENS, CODES; lia) CAP1 FO1 M1)
      as (_ & _ & LOK).
    specialize (LOK eq_refl).
    apply go_ago; [|lia].
    apply awfx_decode.
    + apply (aw_src _ _ W0).
    + apply Zlib.proof.inflate.MwfLemmas.swf_set_mode; [|clear; mdc; lia]. destruct S3; constructor; simpl; auto; unfold ENOUGH_CODES; try lia.
    + simpl. unfold decode_mode. tauto.
    + simpl. apply Zlib.proof.inflate.Step3Tables.tb_tvalid_at with used1 t1; simpl; auto; unfold ENOUGH_CODES; lia.
    + simpl. apply Zlib.proof.inflate.Step3Tables.tb_tvalid_at with used2 t2; simpl; auto; unfold ENOUGH_CODES; lia.
    + exists used1. split; [simpl; unfold ENOUGH_CODES; lia|]. split.
      * unfold tvalid_b. apply tvalid_g_ext with (fun i => Znth i t1); [|exact T1].
        intros i Hi. simpl. symmetry. apply G1; auto.
      * intros i Hi. simpl. rewrite G1 by auto. apply LOK; auto.
    + apply (trep_ext LENS (fun i => Znth i t1) _ _ used1); [exact T1 | intros op; rewrite len_islink_eq; auto | |
        exact TRL].
      intros i Hi. simpl. symmetry. apply G1; auto.
    + apply (trep_ext DISTS (fun i => Znth i t2) _ _ used2); [exact T2 | intros op; rewrite dist_islink_eq; auto | |
        exact TRD].
      intros i Hi. simpl. symmetry. apply G2; auto.
    + intros src' q'. change dist_islink with (islink DISTS). apply adecode_prop with used2.
      * unfold tvalid_b. apply tvalid_g_ext with (fun i => Znth i t2); [|exact T2].
        intros i Hi. simpl. symmetry. apply G2; auto.
      * intros i Hi. simpl. rewrite G2 by auto. apply DOK; auto.
    + intros H; exfalso; clear -H; cbn in H; mdc; lia.
    + intros H; exfalso; clear -H; cbn in H; mdc; lia.
    + intros H; exfalso; clear -H; cbn in H; mdc; lia.
    + intros H; exfalso; clear -H; cbn in H; mdc; lia.
    + intros H; exfalso; clear -H; cbn in H; mdc; lia.
    + intros H; exfalso; clear -H; cbn in H; mdc; lia.
    + intros H; exfalso; clear -H; cbn in H; mdc; lia.
    + simpl. apply (aw_wbits _ _ W0).
    + simpl. apply (aw_wrap _ _ W0).
    + simpl. apply (aw_dict _ _ W0).
    + simpl. apply (aw_head _ _ W0).
    + simpl. apply (ax_back _ _ W).
    + simpl. intros NZ. apply (aw_chk _ _ W0); [unfold data_mode; tauto | exact NZ].
    + exact Q0.
    + apply (aw_O _ _ W0).
Qed.
