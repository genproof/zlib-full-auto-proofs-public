(* The table cases TABLE, LENLENS, CODELENS preserve mwf3xW (StepWKit.v): inflate_table's results
   through call_table, with cover2_stmt (Cover2Def.v), cover3_stmt (StepInv.v) and inftrees' fact_result
   (src/proof/inftrees/facts.v, proved: part_result.v fact_result_ok with sorted_ok2, rfc_ok2, bits_ok2,
   subbits_ok2, size_ok2) for the lengths / entries of the tables and used <= ENOUGH_LENS. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.inflate.Step3Tables.
Require Export Zlib.proof.inflate.StepWKit.
Import ListNotations.
Local Open Scope Z_scope.

Require Zlib.proof.inftrees.facts Zlib.proof.inftrees.part_result Zlib.proof.inftrees.part_sorted Zlib.proof.inftrees.part_rfc
  Zlib.proof.inftrees.part_bits Zlib.proof.inftrees.part_subbits Zlib.proof.inftrees.part_size.

(* ---------------------------------------------------------------------------------------------- *)
(* mwf3xW under a new state                                                                        *)

Ltac md_neq := cbv [HEAD TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT LENGTH DONE BAD SYNC
  EXLEN EXTRA] in *; lia.

(* the new mode of a state update is neither EXLEN nor EXTRA *)
Ltac nh_s := simpl; unfold m_mode in *; md_neq.

Lemma tb_set_msg: forall m e, mwf3xW m -> mwf3xW (set_m_msg m e).
Proof.
  intros m e [W X N].
  constructor; [destruct W; constructor; simpl; auto | destruct X; constructor; auto | apply nohdr_ext with m; auto].
Qed.

Lemma tb_set_ret: forall m r, mwf3xW m -> -5 <= r <= 2 -> mwf3xW (set_m_ret m r).
Proof.
  intros m r [W X N] H.
  constructor; [destruct W; constructor; simpl; auto | destruct X; constructor; auto | apply nohdr_ext with m; auto].
Qed.

Lemma tb_bad: forall m e, mwf3xW m -> mwf3xW (set_bad m e).
Proof.
  intros m e W. unfold set_bad. apply mwf3xW_set_mode_plain; try md_neq.
  all: try (apply tb_set_msg; auto).
  unfold decode_mode; md_neq.
Qed.

(* BAD with a new state *)
Lemma tb_bad_s: forall m s' e, mwf3xW m -> swf s' -> (i_mode s' = HEAD -> i_wbits s' = 0 -> i_wrap s' <> 0 -> i_wsize s' = 0 /\ i_win s' = false) ->
  mwf3xW (set_bad (set_m_s m s') e).
Proof.
  intros m s' e [W X] S WB. constructor.
  - destruct W. constructor; simpl; auto.
    all: try (constructor; simpl; intros; try md_neq; unfold decode_mode in *; md_neq).
    all: try (apply swf_set_mode; auto; md_neq).
    all: try (unfold m_mode; simpl; auto).
  - constructor; unfold m_mode; simpl; auto; intros; try md_neq. unfold decode_mode in *; md_neq.
  - unfold nohdr, m_mode; simpl; md_neq.
Qed.

(* a new state, mode facts and xwf3 facts given *)
Lemma tb_new_s: forall m s', mwf3xW m -> swf s' -> modewf s' ->
  (i_mode s' = HEAD -> i_wbits s' = 0 -> i_wrap s' <> 0 -> i_wsize s' = 0 /\ i_win s' = false) -> (i_mode s' = LENEXT -> i_length s' <= 258) ->
  (i_mode s' = DISTEXT -> i_offset s' <= 32768) ->
  (decode_mode (i_mode s') -> lvalid lenfix_list distfix_list s' (i_lencode s') (i_lenbits s')) ->
  m_out m = m_aout m -> i_mode s' <> EXLEN /\ i_mode s' <> EXTRA -> mwf3xW (set_m_s m s').
Proof.
  intros m s' [W X] S M A B C D O N. constructor.
  - destruct W. constructor; simpl; auto.
  - constructor; unfold m_mode; simpl; auto.
  - exact N.
Qed.

Lemma tb_codelens_upd: forall m L h, mwf3xW m -> m_mode m = CODELENS ->
  i_have (m_s m) <= h <= i_nlen (m_s m) + i_ndist (m_s m) -> Zlength L = 320 ->
  Forall (fun x => 0 <= x <= 65535) L -> (forall k, 0 <= k < h -> Znth k L <= 15) ->
  mwf3xW (set_m_s m (set_i_have (set_i_lens (m_s m) L) h)).
Proof.
  intros m L h W Md H ZL FL LE.
  pose proof (mwW_md _ (m3W_w _ W)) as MD. pose proof (mwW_s _ (m3W_w _ W)) as S.
  destruct (md_codelens _ MD Md) as (H0 & Hnl & Hnd & LC & TV & _).
  apply tb_new_s; auto.
  - apply tb_swf_lens; auto. lia.
  - unfold m_mode in Md. constructor; simpl; intros; try md_neq.
    + split; [lia|]. split; [lia|]. split; [lia|]. split; [auto|]. split; [exact TV | auto].
    + unfold decode_mode in *; md_neq.
  - simpl. apply (x3_head _ (m3W_x _ W)).
  - simpl; intros; unfold m_mode in Md; md_neq.
  - simpl; intros; unfold m_mode in Md; md_neq.
  - simpl; intros D; unfold m_mode in Md; unfold decode_mode in D; md_neq.
  - apply mwfW_out_eq; [apply (m3W_w _ W) | md_neq ..].
  - nh_s.
Qed.

Definition cl_ok (h0: Z) (o: clout) : Prop :=
  match o with
  | CLnext m' => mwf3xW m' /\ m_leave m' = 0 /\ m_mode m' = CODELENS /\ h0 < i_have (m_s m')
  | CLleave m' => mwf3xW m'
  | CLbad m' => mwf3xW m'
  end.

Lemma tb_codelens_tail: forall h0 m len copy, mwf3xW m -> m_leave m = 0 -> m_mode m = CODELENS ->
  0 <= len <= 15 -> 1 <= copy -> h0 <= i_have (m_s m) ->
  cl_ok h0
    (if m_mode m =? BAD then CLbad m else
     if i_nlen (m_s m) + i_ndist (m_s m) <? i_have (m_s m) + copy then CLbad (set_bad m M_repeat) else
     CLnext (upd_s m (lens_fill (Z.to_nat copy) len))).
Proof.
  intros h0 m len copy W L Md HL Hc Hh0.
  rewrite Md. replace (CODELENS =? BAD) with false by (symmetry; apply Z.eqb_neq; md_neq).
  destruct (Z.ltb_spec (i_nlen (m_s m) + i_ndist (m_s m)) (i_have (m_s m) + copy)).
  - simpl. apply tb_bad; auto.
  - pose proof (mwW_md _ (m3W_w _ W)) as MD. pose proof (mwW_s _ (m3W_w _ W)) as S.
    destruct (md_codelens _ MD Md) as (H0 & Hnl & Hnd & LC & TV & LE).
    destruct (sw_lens _ S) as [ZL FL].
    destruct (tb_lens_fill (Z.to_nat copy) len (m_s m)) as (L' & E & ZL' & FL' & LE'); auto; try lia.
    unfold upd_s. rewrite E. rewrite Z2Nat.id in * by lia.
    simpl. split; [|split; [exact L | split; [exact Md | lia]]].
    apply tb_codelens_upd; auto. lia.
Qed.

Lemma tb_codelens_iter: forall m, mwf3xW m -> m_leave m = 0 -> m_mode m = CODELENS ->
  i_have (m_s m) < i_nlen (m_s m) + i_ndist (m_s m) ->
  cl_ok (i_have (m_s m)) (codelens_iter lenfix_list distfix_list m).
Proof.
  intros m W L Md Hh.
  pose proof (mwW_md _ (m3W_w _ W)) as MD. pose proof (mwW_s _ (m3W_w _ W)) as S.
  destruct (md_codelens _ MD Md) as (H0 & Hnl & Hnd & LC & TV & LE).
  destruct TV as (sz & _ & TVb).
  pose proof (tv_rb _ _ _ _ TVb) as RB.
  pose proof (lookup1_ok lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m (m3W_w _ W) L
                ltac:(lia) (fun i Hi => proj2 (proj1 (tv_root_bits _ _ _ _ i TVb Hi)))) as LK.
  unfold codelens_iter.
  destruct (lookup1 lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m) as [[here m1] ok].
  destruct LK as (W1 & S1 & LKt & LKf).
  assert (W1': mwf3xW m1) by (apply mwf3xW_intro with m; auto; first [apply (m3W_x _ W) | apply (m3W_n _ W)]).
  destruct ok; [|simpl; auto].
  destruct (LKt eq_refl) as (L1 & B1 & i & Hi & Eh).
  destruct (tv_root_bits _ _ _ _ i TVb Hi) as [Bh Eok]. rewrite <- Eh in Bh, Eok.
  destruct Eok as (Op & Bt & Vl).
  cbn [negb].
  assert (Bb: 0 <= e_bits here <= m_bits m1) by lia.
  destruct (Z.ltb_spec (e_val here) 16).
  - cbn [cl_ok]. set (m2 := dropbits (e_bits here) m1).
    assert (W2: mwf3xW m2) by (apply mwf3xW_dropbits; auto).
    assert (E2: m_s m2 = m_s m) by (unfold m2; rewrite <- S1; reflexivity).
    unfold upd_s. rewrite E2.
    split; [|split; [exact L1 | split; [unfold m_mode; simpl; exact Md | simpl; lia]]].
    replace (m_s m) with (m_s m2) by exact E2.
    apply tb_codelens_upd; auto; rewrite ?E2; auto; try lia.
    + unfold m_mode; rewrite E2; exact Md.
    + rewrite upd_Znth_Zlength; destruct (sw_lens _ S); lia.
    + apply Forall_upd_Znth; [apply (sw_lens _ S) | lia].
    + intros k Hk. destruct (Z.eq_dec k (i_have (m_s m))).
      * subst k. rewrite upd_Znth_same by (destruct (sw_lens _ S); lia). lia.
      * rewrite upd_Znth_diff by (destruct (sw_lens _ S); lia). apply LE; lia.
  - assert (Md1: m_mode m1 = CODELENS) by (unfold m_mode; rewrite S1; exact Md).
    destruct (Z.eqb_spec (e_val here) 16).
    + set (m2 := needbits (e_bits here + 2) m1).
      destruct (Z.eqb_spec (m_leave m2) 1) as [EL|EL].
      { cbv beta iota. apply mwf3xW_needbits; auto; lia. }
      destruct (needbits_ok (e_bits here + 2) m1 W1 L1 ltac:(lia) EL) as [NB NL]. fold m2 in NB, NL.
      assert (W2: mwf3xW m2) by (apply mwf3xW_needbits; auto; lia).
      assert (E2: m_s m2 = m_s m) by (unfold m2; rewrite needbits_s; auto).
      set (m3 := dropbits (e_bits here) m2).
      assert (W3: mwf3xW m3) by (apply mwf3xW_dropbits; auto; lia).
      assert (E3: m_s m3 = m_s m) by exact E2.
      rewrite E3.
      destruct (Z.eqb_spec (i_have (m_s m)) 0).
      { cbv beta iota. change (m_mode (set_bad m3 M_repeat)) with BAD. rewrite Z.eqb_refl. cbn [cl_ok].
        apply tb_bad; auto. }
      cbv beta iota.
      apply tb_codelens_tail.
      * apply mwf3xW_dropbits; auto. pose proof (mwW_bits _ (m3W_w _ W2)). unfold m3, dropbits; simpl; unfold u32; rewrite Z.mod_small; lia.
      * exact NL.
      * unfold m_mode; try change (m_s (dropbits 2 m3)) with (m_s m3); rewrite ?E3; exact Md.
      * rewrite ?E3. destruct (sw_lens _ S) as [ZL FL].
        assert (IN: In (Znth (i_have (m_s m) - 1) (i_lens (m_s m))) (i_lens (m_s m))) by (apply Znth_In; lia).
        rewrite Forall_forall in FL. specialize (FL _ IN). pose proof (LE (i_have (m_s m) - 1) ltac:(lia)). lia.
      * pose proof (bitsn_range m3 2). lia.
      * try change (m_s (dropbits 2 m3)) with (m_s m3); rewrite ?E3; lia.
    + destruct (Z.eqb_spec (e_val here) 17).
      * set (m2 := needbits (e_bits here + 3) m1).
        destruct (Z.eqb_spec (m_leave m2) 1) as [EL|EL].
        { cbv beta iota. apply mwf3xW_needbits; auto; lia. }
        destruct (needbits_ok (e_bits here + 3) m1 W1 L1 ltac:(lia) EL) as [NB NL]. fold m2 in NB, NL.
        assert (W2: mwf3xW m2) by (apply mwf3xW_needbits; auto; lia).
        assert (E2: m_s m2 = m_s m) by (unfold m2; rewrite needbits_s; auto).
        set (m3 := dropbits (e_bits here) m2).
        assert (W3: mwf3xW m3) by (apply mwf3xW_dropbits; auto; lia).
        assert (E3: m_s m3 = m_s m) by exact E2.
        cbv beta iota.
        apply tb_codelens_tail.
        -- apply mwf3xW_dropbits; auto. pose proof (mwW_bits _ (m3W_w _ W2)). unfold m3, dropbits; simpl; unfold u32; rewrite Z.mod_small; lia.
        -- exact NL.
        -- unfold m_mode; try change (m_s (dropbits 3 m3)) with (m_s m3); rewrite ?E3; exact Md.
        -- lia.
        -- pose proof (bitsn_range m3 3). lia.
        -- try change (m_s (dropbits 3 m3)) with (m_s m3); rewrite ?E3; lia.
      * set (m2 := needbits (e_bits here + 7) m1).
        destruct (Z.eqb_spec (m_leave m2) 1) as [EL|EL].
        { cbv beta iota. apply mwf3xW_needbits; auto; lia. }
        destruct (needbits_ok (e_bits here + 7) m1 W1 L1 ltac:(lia) EL) as [NB NL]. fold m2 in NB, NL.
        assert (W2: mwf3xW m2) by (apply mwf3xW_needbits; auto; lia).
        assert (E2: m_s m2 = m_s m) by (unfold m2; rewrite needbits_s; auto).
        set (m3 := dropbits (e_bits here) m2).
        assert (W3: mwf3xW m3) by (apply mwf3xW_dropbits; auto; lia).
        assert (E3: m_s m3 = m_s m) by exact E2.
        cbv beta iota.
        apply tb_codelens_tail.
        -- apply mwf3xW_dropbits; auto. pose proof (mwW_bits _ (m3W_w _ W2)). unfold m3, dropbits; simpl; unfold u32; rewrite Z.mod_small; lia.
        -- exact NL.
        -- unfold m_mode; try change (m_s (dropbits 7 m3)) with (m_s m3); rewrite ?E3; exact Md.
        -- lia.
        -- pose proof (bitsn_range m3 7). lia.
        -- try change (m_s (dropbits 7 m3)) with (m_s m3); rewrite ?E3; lia.
Qed.

Lemma tb_codelens_loop: forall k m, mwf3xW m -> m_leave m = 0 -> m_mode m = CODELENS ->
  316 - i_have (m_s m) < Z.of_nat k ->
  match codelens_loop lenfix_list distfix_list k m with
  | CLnext m' => mwf3xW m' /\ m_leave m' = 0 /\ m_mode m' = CODELENS /\
                 i_nlen (m_s m') + i_ndist (m_s m') <= i_have (m_s m')
  | CLleave m' => mwf3xW m'
  | CLbad m' => mwf3xW m'
  end.
Proof.
  induction k; intros m W L Md K.
  - pose proof (mwW_md _ (m3W_w _ W)) as MD.
    destruct (md_codelens _ MD Md) as (H0 & Hnl & Hnd & _). simpl in K. lia.
  - cbn [codelens_loop].
    destruct (Z.ltb_spec (i_have (m_s m)) (i_nlen (m_s m) + i_ndist (m_s m))) as [Hh|Hh].
    + pose proof (tb_codelens_iter m W L Md Hh) as IT.
      destruct (codelens_iter lenfix_list distfix_list m) as [m'|m'|m']; cbn [cl_ok] in IT; auto.
      destruct IT as (W' & L' & Md' & Hh'). apply IHk; auto. rewrite Nat2Z.inj_succ in K. lia.
    + auto.
Qed.

Lemma tb_bad_s_ret: forall m s' r e, mwf3xW m -> swf s' -> (i_mode s' = HEAD -> i_wbits s' = 0 -> i_wrap s' <> 0 -> i_wsize s' = 0 /\ i_win s' = false) ->
  -5 <= r <= 2 -> mwf3xW (set_bad (set_m_ret (set_m_s m s') r) e).
Proof. intros m s' r e W S WB R. exact (tb_bad_s (set_m_ret m r) s' e (tb_set_ret m r W R) S WB). Qed.

Lemma CODELENS_ok : cover2_stmt -> cover3_stmt -> ok_LEN_ -> ok_CODELENS.
Proof.
  intros C2 C3 OL flush m W L Md.
  pose proof (mwW_s _ (m3W_w _ W)) as S0.
  pose proof (tb_codelens_loop 320 m W L Md ltac:(pose proof (sw_have _ S0); simpl; lia)) as LP.
  unfold c_CODELENS.
  destruct (codelens_loop lenfix_list distfix_list 320 m) as [m1|m1|m1]; cbn [iout_ok]; auto.
  destruct LP as (W1 & L1 & Md1 & Hfull).
  pose proof (mwW_md _ (m3W_w _ W1)) as MD. pose proof (mwW_s _ (m3W_w _ W1)) as S.
  destruct (md_codelens _ MD Md1) as (H0 & Hnl & Hnd & LC & TV & LE).
  destruct (Z.eqb_spec (Znth 256 (i_lens (m_s m1))) 0) as [Z256|Z256].
  { cbn [iout_ok]. apply tb_bad; auto. }
  cbv zeta.
  set (s1 := set_i_lenbits (set_i_lencode (set_i_next (m_s m1) 0) (TCodes 0)) 9).
  assert (Hh: i_have (m_s m1) = i_nlen (m_s m1) + i_ndist (m_s m1)) by lia.
  destruct (sw_lens _ S) as [ZL FL]. destruct (sw_codes _ S) as [ZC FC].
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
  destruct (call_table LENS 0 (i_nlen s1) 9 s1) as [[[r1 c1] n1] b1] eqn:CT1.
  destruct (tb_call_table LENS 0 (i_nlen s1) 9 s1 r1 c1 n1 b1 C2 S1 ltac:(lia) ltac:(simpl; lia) ltac:(simpl; lia)
              IN1 CAP1 ltac:(unfold LENS, CODES; lia) CT1) as (ZC1 & FC1 & R1 & Rn1 & Ry1).
  destruct (Z.eqb_spec r1 0) as [R10|R10].
  2:{ cbn [negb iout_ok]. destruct (Rn1 R10) as [-> ->].
      apply tb_bad_s_ret; auto; [| apply (x3_head _ (m3W_x _ W1)) | lia].
      destruct S; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES in *; lia. }
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
    apply tb_forall_sublist; try lia. intros k Hk. split.
    - rewrite Forall_forall in FL. apply FL. apply Znth_In; lia.
    - apply LE; lia. }
  assert (CAP2: cap_ok DISTS (sublist (i_nlen s3) (i_nlen s3 + i_ndist s3) (i_lens s3)) 6 (ENOUGH_CODES - i_next s3)).
  { unfold cap_ok. simpl. unfold LENS, CODES, DISTS, ENOUGH_LENS, ENOUGH_DISTS, ENOUGH_CODES in *.
    split; [intros; lia|]. split; intros; lia. }
  destruct (call_table DISTS (i_nlen s3) (i_ndist s3) 6 s3) as [[[r2 c2] n2] d2] eqn:CT2.
  destruct (tb_call_table DISTS (i_nlen s3) (i_ndist s3) 6 s3 r2 c2 n2 d2 C2 S3 ltac:(simpl; lia) ltac:(simpl; lia)
              ltac:(simpl; lia) IN2 CAP2 ltac:(unfold DISTS, CODES; lia) CT2) as (ZC2 & FC2 & R2 & Rn2 & Ry2).
  set (s4 := set_i_distbits (set_i_next (set_i_codes s3 c2) n2) d2).
  rewrite !tb_ret_ret.
  destruct (Z.eqb_spec r2 0) as [R20|R20].
  2:{ cbn [negb iout_ok]. destruct (Rn2 R20) as [E2 E3]. subst n2 d2.
      apply tb_bad_s_ret; auto; [| apply (x3_head _ (m3W_x _ W1)) | lia].
      unfold s4. destruct S3; constructor; simpl; auto. }
  subst r2. cbn [negb].
  destruct (Ry2 eq_refl) as (used2 & t2 & M2 & En2 & Ec2 & Zt2 & T2 & U2 & _).
  rewrite tb_mode_ret.
  assert (WM: mwf3xW (set_m_s (set_m_ret m1 0) (set_i_mode s4 LEN_))).
  { change (i_next s3) with (0 + used1) in *. change (i_codes s3) with t1 in *. subst c2 n2.
    pose proof (tv_rb _ _ _ _ T2) as RB2.
    unfold ENOUGH_CODES, ENOUGH_LENS in *.
    assert (G1: forall i, 0 <= i < used1 -> Znth (0 + i) (sublist 0 used1 t1 ++ t2) = Znth i t1).
    { intros i Hi. rewrite Znth_app1 by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia.
      f_equal; lia. }
    assert (G2: forall i, 0 <= i < used2 -> Znth (0 + used1 + i) (sublist 0 (0 + used1) t1 ++ t2) = Znth i t2).
    { intros i Hi. rewrite Znth_app2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
      f_equal; lia. }
    assert (ZO1: Zlength (sublist 0 1444 (i_codes s1)) = 1444 - 0)
      by (rewrite Zlength_sublist; simpl; lia).
    rewrite <- ZO1 in CAP1.
    assert (FO1: Forall entry_ok (sublist 0 1444 (i_codes s1))) by (apply Forall_sublist; exact FC).
    apply tb_new_s.
    - apply tb_set_ret; auto; lia.
    - apply swf_set_mode; [|md_neq]. unfold s4. destruct S3; constructor; simpl; auto; unfold ENOUGH_CODES; try lia.
    - constructor; simpl; intros; try md_neq.
      + split.
        * apply tb_tvalid_at with used1 t1; simpl; auto; unfold ENOUGH_CODES; lia.
        * apply tb_tvalid_at with used2 t2; simpl; auto; unfold ENOUGH_CODES; lia.
    - simpl. first [apply (x3_head _ (m3W_x _ W1)) | (intros ?HH; exfalso; revert HH; md_neq)].
    - simpl; intros; md_neq.
    - simpl; intros; md_neq.
    - simpl; intros _. apply tb_lvalid_at with used1 t1; simpl; auto; unfold ENOUGH_CODES; try lia.
      intros i Hi. apply (C3 _ _ _ _ _ _ IN1 CAP1 FO1 M1 i Hi).
    - apply mwfW_out_eq; [apply (m3W_w _ (tb_set_ret m1 0 W1 ltac:(lia))) | change (m_mode (set_m_ret m1 0)) with (m_mode m1); rewrite Md1; md_neq ..].
    - nh_s. }
  destruct (flush =? Z_TREES); cbn [iout_ok].
  - apply mwf3xW_set_leave; exact WM.
  - apply OL; [exact WM | exact L1 | reflexivity].
Qed.

Lemma tb_lenlens_upd: forall m L h, mwf3xW m -> m_mode m = LENLENS ->
  0 <= h <= i_ncode (m_s m) -> Zlength L = 320 ->
  Forall (fun x => 0 <= x <= 65535) L -> (forall k, 0 <= k < h -> Znth (Znth k order) L <= 7) ->
  mwf3xW (set_m_s m (set_i_have (set_i_lens (m_s m) L) h)).
Proof.
  intros m L h W Md H ZL FL LE.
  pose proof (mwW_md _ (m3W_w _ W)) as MD. pose proof (mwW_s _ (m3W_w _ W)) as S.
  destruct (md_lenlens _ MD Md) as (Hc & H0 & Hnl & Hnd & _).
  apply tb_new_s; auto.
  - apply tb_swf_lens; auto. lia.
  - unfold m_mode in Md. constructor; simpl; intros; try md_neq.
    + split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. auto.
    + unfold decode_mode in *; md_neq.
  - simpl. apply (x3_head _ (m3W_x _ W)).
  - simpl; intros; unfold m_mode in Md; md_neq.
  - simpl; intros; unfold m_mode in Md; md_neq.
  - simpl; intros D; unfold m_mode in Md; unfold decode_mode in D; md_neq.
  - apply mwfW_out_eq; [apply (m3W_w _ W) | md_neq ..].
  - nh_s.
Qed.

Lemma tb_lenlens_loop: forall k m, mwf3xW m -> m_mode m = LENLENS -> m_leave m = 0 ->
  mwf3xW (lenlens_loop k m) /\ m_mode (lenlens_loop k m) = LENLENS.
Proof.
  induction k; intros m W Md L; cbn [lenlens_loop]; auto.
  pose proof (mwW_md _ (m3W_w _ W)) as MD. pose proof (mwW_s _ (m3W_w _ W)) as S.
  destruct (md_lenlens _ MD Md) as (Hc & H0 & Hnl & Hnd & LE).
  destruct (Z.ltb_spec (i_have (m_s m)) (i_ncode (m_s m))) as [Hh|Hh]; auto.
  set (m2 := needbits 3 m).
  assert (W2: mwf3xW m2) by (apply mwf3xW_needbits; auto; lia).
  assert (E2: m_s m2 = m_s m) by (apply needbits_s).
  assert (Md2: m_mode m2 = LENLENS) by (unfold m_mode; rewrite E2; exact Md).
  destruct (Z.eqb_spec (m_leave m2) 1) as [EL|EL]; [auto|].
  destruct (needbits_ok 3 m (m3W_w _ W) L ltac:(lia) EL) as [NB NL]. fold m2 in NB, NL.
  rewrite E2. destruct (sw_lens _ S) as [ZL FL].
  pose proof (tb_order_range (i_have (m_s m)) ltac:(lia)) as OR.
  pose proof (bitsn_range m2 3 ltac:(lia)) as BR.
  apply IHk.
  - apply mwf3xW_dropbits; [|simpl; lia].
    replace (m_s m) with (m_s m2) by exact E2.
    apply tb_lenlens_upd; rewrite ?E2; auto; try lia.
    + rewrite upd_Znth_Zlength; lia.
    + apply Forall_upd_Znth; auto. lia.
    + intros k' Hk'. destruct (Z.eq_dec k' (i_have (m_s m))).
      * subst k'. rewrite upd_Znth_same by lia. lia.
      * pose proof (tb_order_range k' ltac:(lia)).
        rewrite upd_Znth_diff by (try lia; intros E; apply n; apply tb_order_inj; auto; lia).
        apply LE; lia.
  - unfold m_mode; simpl; exact Md.
  - exact NL.
Qed.

Lemma LENLENS_ok : cover2_stmt -> cover3_stmt -> ok_LEN_ -> ok_LENLENS.
Proof.
  intros C2 C3 OL flush m W L Md.
  destruct (tb_lenlens_loop 19 m W Md L) as [W1 Md1].
  unfold c_LENLENS. revert W1 Md1. generalize (lenlens_loop 19 m) as m1. intros m1 W1 Md1.
  destruct (Z.eqb_spec (m_leave m1) 1) as [EL|EL]; [cbn [iout_ok]; auto|].
  assert (L1: m_leave m1 = 0) by (destruct (leave_cases _ (m3W_w _ W1)); auto; contradiction).
  pose proof (mwW_md _ (m3W_w _ W1)) as MD. pose proof (mwW_s _ (m3W_w _ W1)) as S.
  destruct (md_lenlens _ MD Md1) as (Hc & H0 & Hnl & Hnd & LE).
  destruct (sw_lens _ S) as [ZL FL]. destruct (sw_codes _ S) as [ZC FC].
  destruct (tb_lenlens_zero 19 (m_s m1) ltac:(lia) ltac:(simpl; lia) ZL FL LE) as (L0 & EZ & ZL0 & FL0 & LE0).
  rewrite EZ.
  assert (LE7: forall x, 0 <= x < 19 -> 0 <= Znth x L0 <= 7).
  { intros x Hx. destruct (tb_order_surj x Hx) as (k & Hk & <-). split; [|apply LE0; auto].
    rewrite Forall_forall in FL0. apply FL0. apply Znth_In. pose proof (tb_order_range k Hk). lia. }
  set (s0 := set_i_lenbits (set_i_distcode (set_i_lencode (set_i_next (set_i_have (set_i_lens (m_s m1) L0) 19) 0)
                (TCodes 0)) (TCodes 0)) 7).
  assert (S0: swf s0) by (destruct S; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES; lia).
  assert (F07: Forall (fun x => 0 <= x <= 7) (sublist 0 (0 + 19) (i_lens s0))).
  { apply tb_forall_sublist; simpl; try lia. intros k Hk. apply LE7; lia. }
  assert (IN0: inputs_ok CODES (sublist 0 (0 + 19) (i_lens s0)) 7).
  { unfold inputs_ok. simpl. rewrite Zlength_sublist by lia. split; [unfold CODES; lia|].
    split; [unfold max_codes; simpl; lia|]. split; [|lia].
    eapply Forall_impl; [|exact F07]. unfold MAXBITS; simpl; intros; lia. }
  assert (CAP0: cap_ok CODES (sublist 0 (0 + 19) (i_lens s0)) 7 (ENOUGH_CODES - i_next s0)).
  { pose proof (tb_maxlen_le _ F07) as ML. change (i_lens s0) with L0 in *. change (0 + 19) with 19 in *.
    unfold cap_ok. change (i_next s0) with 0. unfold LENS, CODES, DISTS, ENOUGH_CODES. split; [|split; intros; lia].
    intros _. split; [lia|]. split; [lia|]. rewrite Z.shiftl_1_l.
    assert (2 ^ maxlen (sublist 0 19 L0) <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 7) with 128 in *. lia. }
  cbv zeta. fold s0.
  destruct (call_table CODES 0 19 7 s0) as [[[r c] n] b] eqn:CT.
  destruct (tb_call_table CODES 0 19 7 s0 r c n b C2 S0 ltac:(lia) ltac:(lia) ltac:(lia)
              IN0 CAP0 ltac:(intros; lia) CT) as (ZC1 & FC1 & R1 & Rn1 & Ry1).
  destruct (Z.eqb_spec r 0) as [R0|R0].
  2:{ cbn [negb iout_ok]. destruct (Rn1 R0) as [-> ->].
      apply tb_bad_s_ret; auto; [| apply (x3_head _ (m3W_x _ W1)) | lia].
      destruct S0; constructor; simpl; auto. }
  subst r. cbn [negb].
  destruct (Ry1 eq_refl) as (used & t & M & En & Ec & Zt & T & U & _).
  change (i_next s0) with 0 in *. rewrite sublist_nil in Ec. simpl app in Ec. subst c n.
  pose proof (tv_rb _ _ _ _ T) as RB.
  apply CODELENS_ok; auto.
  - change (mwf3xW (set_m_s (set_m_ret m1 0)
      (set_i_mode (set_i_have (set_i_lenbits (set_i_next (set_i_codes s0 t) (0 + used)) b) 0) CODELENS))).
    apply tb_new_s.
    + apply tb_set_ret; auto; lia.
    + apply swf_set_mode; [|md_neq]. destruct S0; constructor; simpl; auto; unfold ENOUGH_CODES in *; try lia.
    + constructor; simpl; intros; try md_neq.
      * split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [|intros; lia].
        apply tb_tvalid_at with used t; simpl; auto; unfold ENOUGH_CODES in *; try lia.
      * unfold decode_mode in *; md_neq.
    + simpl. first [apply (x3_head _ (m3W_x _ W1)) | (intros ?HH; exfalso; revert HH; md_neq)].
    + simpl; intros; md_neq.
    + simpl; intros; md_neq.
    + simpl; intros D; unfold decode_mode in D; md_neq.
    + apply mwfW_out_eq; [apply (m3W_w _ (tb_set_ret m1 0 W1 ltac:(lia))) |
        change (m_mode (set_m_ret m1 0)) with (m_mode m1); rewrite Md1; md_neq ..].
    + nh_s.
Qed.

Lemma TABLE_ok : cover2_stmt -> cover3_stmt -> ok_LEN_ -> ok_TABLE.
Proof.
  intros C2 C3 OL flush m W L Md.
  unfold c_TABLE.
  set (m2 := needbits 14 m).
  destruct (Z.eqb_spec (m_leave m2) 1) as [EL|EL].
  { cbn [iout_ok]. apply mwf3xW_needbits; auto; lia. }
  destruct (needbits_ok 14 m (m3W_w _ W) L ltac:(lia) EL) as [NB NL]. fold m2 in NB, NL.
  assert (W2: mwf3xW m2) by (apply mwf3xW_needbits; auto; lia).
  assert (E2: m_s m2 = m_s m) by (apply needbits_s).
  pose proof (mwW_bits _ (m3W_w _ W2)) as B2.
  cbv zeta.
  set (m3 := dropbits 5 m2). set (m4 := dropbits 5 m3). set (m5 := dropbits 4 m4).
  assert (B3: m_bits m3 = m_bits m2 - 5) by (apply tb_drop_bits; lia).
  assert (B4: m_bits m4 = m_bits m2 - 10) by (unfold m4; rewrite tb_drop_bits; lia).
  assert (W5: mwf3xW m5).
  { apply mwf3xW_dropbits; [|unfold m4 in *; lia]. apply mwf3xW_dropbits; [|lia]. apply mwf3xW_dropbits; auto; lia. }
  assert (E5: m_s m5 = m_s m) by exact E2.
  pose proof (bitsn_range m2 5 ltac:(lia)) as R1.
  pose proof (bitsn_range m3 5 ltac:(lia)) as R2.
  pose proof (bitsn_range m4 4 ltac:(lia)) as R3.
  change (2 ^ 5) with 32 in *. change (2 ^ 4) with 16 in *.
  set (s' := set_i_ncode (set_i_ndist (set_i_nlen (m_s m5) (bitsn m2 5 + 257)) (bitsn m3 5 + 1)) (bitsn m4 4 + 4)).
  pose proof (mwW_s _ (m3W_w _ W5)) as S5.
  assert (S': swf s') by (destruct S5; constructor; simpl; auto; lia).
  unfold upd_s. fold s'.
  destruct (orb (286 <? bitsn m2 5 + 257) (30 <? bitsn m3 5 + 1)) eqn:TM.
  { cbn [iout_ok]. apply tb_bad_s; auto. apply (x3_head _ (m3W_x _ W5)). }
  apply orb_false_iff in TM. destruct TM as [T1 T2]. apply Z.ltb_ge in T1. apply Z.ltb_ge in T2.
  apply LENLENS_ok; auto.
  - change (mwf3xW (set_m_s m5 (set_i_mode (set_i_have s' 0) LENLENS))).
    apply tb_new_s; auto.
    + apply swf_set_mode; [|md_neq]. destruct S'; constructor; simpl; auto; lia.
    + constructor; simpl; intros; try md_neq.
      * split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros; lia.
      * unfold decode_mode in *; md_neq.
    + simpl. first [apply (x3_head _ (m3W_x _ W5)) | (intros ?HH; exfalso; revert HH; md_neq)].
    + simpl; intros; md_neq.
    + simpl; intros; md_neq.
    + simpl; intros D; unfold decode_mode in D; md_neq.
    + apply mwfW_out_eq; [apply (m3W_w _ W5) | unfold m_mode; rewrite E5; fold (m_mode m); rewrite Md; md_neq ..].
    + nh_s.
Qed.

(* all the cases of this file *)
Lemma tables_all : cover2_stmt -> cover3_stmt -> ok_LEN_ -> ok_CODELENS /\ ok_LENLENS /\ ok_TABLE.
Proof.
  intros A B C. split; [apply CODELENS_ok; auto|]. split; [apply LENLENS_ok; auto | apply TABLE_ok; auto].
Qed.
