(* Law inflate_check, theory part: case HEAD keeps Kx. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_check.IKTheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the helpers of inflate_codes' TheoryHead.v (thh_ lemmas), for NEEDBITS(16) in HEAD *)
Lemma ikh_byte src pos inp k :
  ctx_ok src pos inp -> 0 <= k < Zlength inp ->
  Znth k inp = Znth (pos + k) src /\ 0 <= Znth (pos + k) src <= 255.
Proof.
  intros (Hp & Hl & Hb & He) Hk. split; [apply He; auto|].
  unfold bytes_ok in Hb. rewrite Forall_forall in Hb.
  assert (0 <= pos + k < Zlength src) by lia.
  pose proof (Hb (Znth (pos + k) src)) as X. replace Byte.max_unsigned with 255 in X by reflexivity.
  apply X. apply Znth_In; lia.
Qed.

Lemma ikh_pull m src pos :
  ctx_ok src pos (m_inp m) -> 0 <= m_nx m < Zlength (m_inp m) ->
  0 <= pos + m_nx m <= 1 -> m_bits m = 8 * (pos + m_nx m) ->
  m_hold m = le_val (sublist 0 (pos + m_nx m) src) ->
  pull m = set_m_bits (set_m_hold (set_m_nx m (m_nx m + 1)) (le_val (sublist 0 (pos + (m_nx m + 1)) src)))
                      (8 * (pos + (m_nx m + 1))).
Proof.
  intros Hc Hn Hp Hb Hh.
  destruct (ikh_byte src pos (m_inp m) (m_nx m) Hc Hn) as [Eb Rb].
  pose proof Hc as (H0 & Hl & _).
  unfold pull. rewrite Eb, Hb, Hh. f_equal; [f_equal|].
  - assert (pos + m_nx m = 0 \/ pos + m_nx m = 1) as [E|E] by lia.
    + rewrite E in *. replace (pos + (m_nx m + 1)) with 1 by lia.
      rewrite (sublist_one 0 1 src) by lia. rewrite sublist_nil. cbn [le_val].
      change (2 ^ (8 * 0)) with 1. unfold u64. rewrite Z.mod_small; lia.
    + rewrite E in *. replace (pos + (m_nx m + 1)) with 2 by lia.
      rewrite (sublist_one 0 1 src) by lia.
      rewrite (sublist_split 0 1 2 src), (sublist_one 0 1 src), (sublist_one 1 2 src) by lia.
      cbn [le_val app].
      assert (0 <= Znth 0 src <= 255).
      { destruct Hc as (_ & _ & Hbo & _). unfold bytes_ok in Hbo. rewrite Forall_forall in Hbo.
        pose proof (Hbo (Znth 0 src)) as X. replace Byte.max_unsigned with 255 in X by reflexivity. apply X, Znth_In; lia. }
      change (2 ^ (8 * 1)) with 256. unfold u64. rewrite Z.mod_small; lia.
  - unfold u32. rewrite Z.mod_small; lia.
Qed.

Lemma ikh_same m : set_m_bits (set_m_hold (set_m_nx m (m_nx m)) (m_hold m)) (m_bits m) = m.
Proof. destruct m; reflexivity. Qed.

Lemma ikh_nbS k n m :
  needbits_f (S k) n m = if m_bits m <? n then if m_have m =? 0 then set_leave m else needbits_f k n (pull m) else m.
Proof. reflexivity. Qed.

Lemma ikh_nb m src pos :
  ctx_ok src pos (m_inp m) -> 0 <= m_nx m <= Zlength (m_inp m) ->
  hd_head src (pos + m_nx m) (m_hold m) (m_bits m) ->
  exists nx', m_nx m <= nx' <= Zlength (m_inp m) /\
   ((needbits 16 m = set_leave (set_m_bits (set_m_hold (set_m_nx m nx') (le_val (sublist 0 (pos + nx') src)))
                                          (8 * (pos + nx'))) /\ pos + nx' <= 1) \/
    (needbits 16 m = set_m_bits (set_m_hold (set_m_nx m nx') (le_val (sublist 0 2 src))) 16 /\ pos + nx' = 2)).
Proof.
  intros Hc Hn (Hp & Hb & Hh). unfold needbits. rewrite ikh_nbS.
  rewrite Hb. replace (8 * (pos + m_nx m) <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (m_have m =? 0) eqn:E0.
  { exists (m_nx m). split; [lia|]. left. split; [|lia]. rewrite <- Hh, <- Hb, ikh_same. reflexivity. }
  unfold m_have in E0. apply Z.eqb_neq in E0.
  rewrite (ikh_pull m src pos) by (auto; lia).
  set (m1 := set_m_bits _ _).
  assert (Hc1 : ctx_ok src pos (m_inp m1)) by exact Hc.
  change (m_inp m1) with (m_inp m) in Hc1.
  assert (Hnx1 : m_nx m1 = m_nx m + 1) by reflexivity.
  assert (Hb1 : m_bits m1 = 8 * (pos + (m_nx m + 1))) by reflexivity.
  assert (Hh1 : m_hold m1 = le_val (sublist 0 (pos + (m_nx m + 1)) src)) by reflexivity.
  assert (Hi1 : m_inp m1 = m_inp m) by reflexivity.
  assert (pos + m_nx m = 0 \/ pos + m_nx m = 1) as [P|P] by lia.
  - rewrite ikh_nbS, Hb1. replace (8 * (pos + (m_nx m + 1)) <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (m_have m1 =? 0) eqn:E1.
    { exists (m_nx m + 1). split; [lia|]. left. split; [|lia].
      reflexivity. }
    unfold m_have in E1. apply Z.eqb_neq in E1. rewrite Hi1, Hnx1 in E1.
    rewrite (ikh_pull m1 src pos) by (rewrite ?Hi1, ?Hnx1; auto; lia).
    rewrite ikh_nbS. cbn [m_bits set_m_bits]. rewrite Hnx1.
    replace (8 * (pos + (m_nx m + 1 + 1)) <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
    exists (m_nx m + 1 + 1). split; [lia|]. right. split; [|lia].
    replace (pos + (m_nx m + 1 + 1)) with 2 by lia. unfold m1.
    destruct m; reflexivity.
  - rewrite ikh_nbS, Hb1. replace (8 * (pos + (m_nx m + 1)) <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
    exists (m_nx m + 1). split; [lia|]. right. split; [|lia].
    unfold m1. replace (pos + (m_nx m + 1)) with 2 by lia. reflexivity.
Qed.

Ltac ikh_unf G :=
  unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, Zlib.proof.inflate.Model.TYPE,
    TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT,
    MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM in G.

Ltac ikh_dis G F HM :=
  match type of G with
  | _ \/ _ => let G1 := fresh "G" in let G2 := fresh "G" in
      destruct G as [G1|G2]; [ikh_dis G1 F HM | ikh_dis G2 F HM]
  | _ => first [apply F; exact G | apply HM in G; ikh_unf G; lia]
  end.

(* Kx after a pass of HEAD on a wrapped stream: nothing produced, the modes HEAD, BAD, FLAGS, TYPE, DICTID *)
Lemma ikh_Kx wrap src pos out a0 m m' :
  Kx wrap src pos out a0 m -> m_mode m = HEAD -> wrap <> 0 ->
  m_ow m' = m_ow m -> m_out m' = m_out m -> m_aout m' = m_aout m ->
  i_total (m_s m') = i_total (m_s m) -> m_tout m' = m_tout m ->
  ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') ->
  (m_mode m' = HEAD \/ m_mode m' = BAD \/ m_mode m' = FLAGS \/
   m_mode m' = Zlib.proof.inflate.Model.TYPE \/ m_mode m' = DICTID) ->
  (m_mode m' = FLAGS -> ik_gzhdr_ok wrap src (pos + m_nx m') (m_bits m') FLAGS (i_flags (m_s m'))) ->
  (m_mode m' = DICTID -> ik_zh_ok wrap src (pos + m_nx m') (m_bits m') (i_flags (m_s m'))) ->
  (m_mode m' = Zlib.proof.inflate.Model.TYPE -> ik_post wrap src pos out m') ->
  Kx wrap src pos out a0 m'.
Proof.
  intros K Hmd W0 How Hout Haout Htot Htout Hbuf Hm Hfl Hdi Hty.
  assert (Pre : ik_pre out m).
  { apply (kx_pre _ _ _ _ _ _ K W0). left; exact Hmd. }
  assert (Pre' : ik_pre out m').
  { destruct Pre as (P1 & P2 & P3). split; [exact P1|]. rewrite How, Hout, Haout. auto. }
  assert (HM : forall md, m_mode m' = md -> md = HEAD \/ md = BAD \/ md = FLAGS \/
                 md = Zlib.proof.inflate.Model.TYPE \/ md = DICTID) by (intros md <-; exact Hm).
  unfold HEAD, BAD, FLAGS, Zlib.proof.inflate.Model.TYPE, DICTID in HM.
  constructor.
  - apply (kx_wrap _ _ _ _ _ _ K).
  - exact Hbuf.
  - split.
    + intros D. exfalso. destruct D as [D|[D|[D|[D|D]]]]; apply HM in D;
        unfold EXTRA, NAME, COMMENT, COPY_, COPY in D; lia.
    + intros D. exfalso. apply HM in D. unfold EXLEN in D. lia.
  - left. exact (proj2 (proj2 Pre')).
  - rewrite Htot, Hout, Haout. apply (kx_total _ _ _ _ _ _ K).
  - rewrite Htout, Hout, Haout. apply (kx_tout _ _ _ _ _ _ K).
  - intros; contradiction.
  - intros _ _. exact Pre'.
  - intros _ G. destruct (Z.eq_dec (m_mode m') FLAGS) as [F|F].
    + rewrite F. apply Hfl; exact F.
    + exfalso. destruct G as [D|[D|[D|[D|[D|[D|[D|D]]]]]]];
        try (apply F; exact D); apply HM in D;
        unfold TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC in D; lia.
  - intros _ [D|D].
    + apply Hdi; exact D.
    + exfalso. apply HM in D. unfold DICT in D. lia.
  - intros _ G. destruct (Z.eq_dec (m_mode m') Zlib.proof.inflate.Model.TYPE) as [F|F].
    + apply Hty; exact F.
    + exfalso. unfold ik_post_mode, decode_mode in G.
      ikh_dis G F HM.
  - intros _ [D|D].
    + left; exact Pre'.
    + exfalso. apply HM in D. unfold MEM in D. lia.
  - intros _. unfold ik_trail. cbv zeta.
    split; [|split]; intros D; exfalso; apply HM in D; unfold CHECK, LENGTH, DONE in D; lia.
Qed.

(* the two header bytes as the 16-bit hold *)
Lemma ikh_h2 b0 b1 : 0 <= b0 <= 255 -> 0 <= b1 <= 255 ->
  let h := b0 + 256 * (b1 + 256 * 0) in
  h mod 256 = b0 /\ Z.shiftr h 8 = b1 /\ h mod 16 = b0 mod 16 /\ Z.shiftr h 4 mod 16 = b0 / 16 /\
  0 <= h < 2 ^ 16.
Proof.
  intros H0 H1 h. subst h. rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 8) with 256. change (2 ^ 4) with 16. change (2 ^ 16) with 65536.
  repeat split; Z.to_euclidean_division_equations; lia.
Qed.

Lemma ikh_lv1 x : (m_leave (set_leave x) =? 1) = true.
Proof. reflexivity. Qed.

Ltac ikh_red :=
  unfold m_mode; cbn [m_nx m_bits m_hold m_msg m_s m_inp m_aout m_out m_ret m_leave m_adler m_ow m_tout
       set_mode upd_s set_m_s set_m_h upd_h set_m_nx set_m_hold set_m_bits set_m_msg set_m_adler
       set_leave set_m_leave set_bad initbits dropbits
       i_mode i_wrap i_head i_total i_flags i_check set_i_mode set_i_check set_i_wbits set_i_flags set_i_dmax].

Ltac ikh_nomode Hmd' :=
  ikh_red; intros ?D; exfalso; try rewrite Hmd' in *;
  unfold HEAD, FLAGS, DICTID, TYPEDO, BAD, Zlib.proof.inflate.Model.TYPE in *; lia.

Lemma ikx_head : headx_stmt.
Proof.
  intros KK wrap src pos out a0 inp aout flush m Hc K X Hw Hl Hmd. unfold md_head in Hmd.
  pose proof (Inv.mw_nx _ (proj1 Hw)) as Hnx.
  pose proof (kc_inp _ _ _ _ _ _ K) as Hinp. subst inp.
  pose proof Hc as (Hpos & Hsrc & Hbytes & _).
  assert (Hmd' : i_mode (m_s m) = HEAD) by exact Hmd.
  unfold stepf2, step2. cbv beta zeta. rewrite Hmd, Z.eqb_refl.
  unfold c_HEAD2. cbv beta zeta. rewrite (kc_wrap _ _ _ _ _ _ K).
  destruct (Z.eqb_spec wrap 0) as [W0|W0].
  { cbn [stepx_post]. subst wrap. destruct X. constructor; ikh_red; auto; try rewrite Hmd'; try (intros; congruence).
    - split; intros D; exfalso; [destruct D as [D|[D|[D|[D|D]]]]|]; ikh_unf D; lia.
    - intros _. split; [exact (proj1 (kx_raw eq_refl))|].
      unfold ik_gzhdr_mode, TYPEDO, DICTID, DICT, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC; lia. }
  pose proof (kc_hd _ _ _ _ _ _ K W0 Hmd) as Hhd.
  destruct (ikh_nb m src pos Hc Hnx Hhd) as (nx' & Hn' & [[E Hp]|[E Hp]]); rewrite E.
  { rewrite ikh_lv1. cbn [stepx_post].
    apply (ikh_Kx wrap src pos out a0 m); auto; try ikh_nomode Hmd'.
    ikh_red. unfold ik_bitbuf. split; [lia|]. rewrite Z.sub_diag, Z.shiftr_0_r. reflexivity. }
  set (H2 := le_val (sublist 0 2 src)).
  set (m2 := set_m_bits (set_m_hold (set_m_nx m nx') H2) 16).
  assert (E1 : (m_leave m2 =? 1) = false) by (cbn; rewrite Hl; reflexivity).
  assert (E2 : m_s m2 = m_s m) by reflexivity.
  assert (E3 : m_hold m2 = H2) by reflexivity.
  rewrite E1, E2, E3, (kc_wrap _ _ _ _ _ _ K), (kc_head _ _ _ _ _ _ K).
  cbv iota. subst m2.
  cbn [m_hold m_s set_m_bits set_m_hold set_m_nx dropbits upd_s set_m_s i_wbits set_i_wbits].
  assert (L2 : 2 <= Zlength src) by lia.
  assert (Bk : forall k, 0 <= k < 2 -> 0 <= Znth k src <= 255).
  { intros k Hk. unfold bytes_ok in Hbytes. rewrite Forall_forall in Hbytes.
    pose proof (Hbytes (Znth k src)) as Y. replace Byte.max_unsigned with 255 in Y by reflexivity.
    apply Y, Znth_In; lia. }
  assert (EH : H2 = Znth 0 src + 256 * (Znth 1 src + 256 * 0)).
  { unfold H2. rewrite (sublist_split 0 1 2 src), (sublist_one 0 1 src), (sublist_one 1 2 src) by lia.
    reflexivity. }
  destruct (ikh_h2 (Znth 0 src) (Znth 1 src) (Bk 0 ltac:(lia)) (Bk 1 ltac:(lia))) as (h1 & h2 & h3 & h4 & h5).
  cbv zeta in h1, h2, h3, h4, h5. rewrite <- EH in h1, h2, h3, h4, h5.
  assert (Hbuf2 : ik_bitbuf src (pos + nx') H2 16).
  { unfold ik_bitbuf. split; [lia|]. rewrite Hp. change (8 * 2 - 16) with 0. rewrite Z.shiftr_0_r. reflexivity. }
  assert (Wv := kx_wrap _ _ _ _ _ _ X).
  assert (Pre : ik_pre out m) by (apply (kx_pre _ _ _ _ _ _ X W0); left; exact Hmd).
  destruct (negb (Z.land wrap 2 =? 0) && (H2 =? 35615))%bool eqn:G.
  { apply andb_true_iff in G. destruct G as [G G']. apply negb_true_iff, Z.eqb_neq in G. apply Z.eqb_eq in G'.
    rewrite G' in h1, h2. change (35615 mod 256) with 31 in h1. change (Z.shiftr 35615 8) with 139 in h2.
    cbn [stepx_post]. apply (ikh_Kx wrap src pos out a0 m); auto; try ikh_nomode Hmd'.
    - ikh_red. apply (kk_bb_init KK); auto; lia.
    - ikh_red. intros _. unfold ik_gzhdr_ok.
      assert (Gz : ik_gzw wrap src = true).
      { unfold ik_gzw. destruct Wv as [W|[W|[W|[W|[W|[W|W]]]]]]; subst wrap;
          try congruence; try reflexivity; try (exfalso; apply G; reflexivity).
        all: rewrite <- h1, <- h2; replace (2 <=? Zlength src) with true by (symmetry; apply Z.leb_le; lia);
          reflexivity. }
      split; [exact G|]. split; [exact Gz|]. split; [exact L2|]. split; [auto|]. split; [auto|].
      split; [intros _; lia|]. split; [intros D; contradiction|].
      split; intros D; exfalso; [|destruct D as [D|[D|[D|[D|D]]]]]; ikh_unf D; lia. }
  destruct (orb (Z.land wrap 1 =? 0) _) eqn:G1.
  { cbn [stepx_post]. apply (ikh_Kx wrap src pos out a0 m); auto; try ikh_nomode Hmd'. }
  apply orb_false_iff in G1. destruct G1 as [G1 G1']. apply Z.eqb_neq in G1. apply negb_false_iff, Z.eqb_eq in G1'.
  rewrite h1, h2 in G1'.
  destruct (negb (H2 mod 16 =? 8)) eqn:G2.
  { cbn [stepx_post]. apply (ikh_Kx wrap src pos out a0 m); auto; try ikh_nomode Hmd'. }
  apply negb_false_iff, Z.eqb_eq in G2. rewrite h3 in G2.
  destruct (orb (15 <? _) _) eqn:G4.
  { cbn [stepx_post]. apply (ikh_Kx wrap src pos out a0 m); auto; try ikh_nomode Hmd'.
    ikh_red. change (u32 (16 - 4)) with 12. apply (kk_bb_drop KK src (pos + nx') H2 16 4); [lia|exact Hbuf2]. }
  apply orb_false_iff in G4. destruct G4 as [G4 _]. apply Z.ltb_ge in G4. rewrite h4 in G4.
  assert (Zh : ik_zhdr src).
  { unfold ik_zhdr. split; [lia|]. split.
    { change 15 with (Z.ones 4). rewrite Z.land_ones by lia. exact G2. }
    split; [|exact G1']. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. lia. }
  assert (Gz : ik_gzw wrap src = false).
  { assert (G' : Z.land wrap 2 <> 0 -> H2 <> 35615).
    { intros W2 E'. apply Z.eqb_neq in W2. rewrite W2, E', Z.eqb_refl in G. discriminate G. }
    unfold ik_gzw. destruct Wv as [W|[W|[W|[W|[W|[W|W]]]]]]; subst wrap;
      try congruence; try reflexivity; try (exfalso; apply G1; reflexivity).
    all: specialize (G' ltac:(compute; discriminate));
      destruct (Z.eqb_spec (Znth 0 src) 31) as [Z0|Z0]; destruct (Z.eqb_spec (Znth 1 src) 139) as [Z1|Z1];
      rewrite ?andb_true_r, ?andb_false_r; try reflexivity;
      exfalso; apply G'; rewrite EH, Z0, Z1; reflexivity. }
  cbn [stepx_post]. destruct (Z.land (Z.shiftr H2 4) 512 =? 0) eqn:G5.
  - apply (ikh_Kx wrap src pos out a0 m); auto; try ikh_nomode Hmd'.
    + ikh_red. apply (kk_bb_init KK); auto; lia.
    + intros _. unfold ik_post. cbv zeta. ikh_red. destruct Pre as (P1 & P2 & P3). rewrite P1, P2.
      split; [left; split; [reflexivity|]; split; [exact Zh|]; split; [exact Gz|lia]|].
      split; [|reflexivity].
      rewrite sublist_of_nil. cbn [app negb Z.eqb ik_chk]. symmetry. apply (kk_adler_nil KK).
  - apply (ikh_Kx wrap src pos out a0 m); auto; try ikh_nomode Hmd'.
    + ikh_red. apply (kk_bb_init KK); auto; lia.
    + intros _. ikh_red. unfold ik_zh_ok.
      split; [exact G1|]. split; [exact Gz|]. split; [exact Zh|]. split; [reflexivity|lia].
Qed.
