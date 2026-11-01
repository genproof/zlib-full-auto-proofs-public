(* The simulation of the modes STORED, COPY_ and COPY: a stored block's header (the padding to a byte
   boundary, LEN and NLEN), then its bytes, copied from the input k at a time (k abstract steps). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimBlockKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma sib_set_length_same s : set_i_length s (i_length s) = s.
Proof. destruct s; reflexivity. Qed.

(* k bytes of a stored block are k abstract steps: each reads the byte at the (byte-aligned) bit position
   and writes it *)
Lemma sib_copy_steps src I R : forall n a,
  let k := Z.of_nat n in
  a_mode a = COPY -> a_q a mod 8 = 0 -> 0 <= a_q a -> k <= i_length (a_s a) -> a_q a + 8 * k <= 8 * I ->
  Zlength (a_O a) + k <= R -> a_q a / 8 + k <= Zlength src ->
  exists a', areach src I R a a' /\ a_s a' = set_i_length (a_s a) (i_length (a_s a) - k) /\
             a_q a' = a_q a + 8 * k /\ a_O a' = a_O a ++ sublist (a_q a / 8) (a_q a / 8 + k) src.
Proof.
  induction n as [|n IH]; intros a k M Q8 Q0 Kl Ki Kr Ks; subst k.
  - exists a. split; [apply ar_refl|]. cbn [Z.of_nat]. rewrite Z.sub_0_r, sib_set_length_same.
    rewrite sublist_nil' by lia. rewrite app_nil_r. split; [reflexivity|]. split; [lia|reflexivity].
  - rewrite Nat2Z.inj_succ in *.
    set (s := a_s a) in *. set (q := a_q a) in *.
    set (a1 := AS (set_i_length s (i_length s - 1)) (q + 8) (a_O a ++ [sbyte src q])).
    assert (A: astep lenfix_list distfix_list src a = AGo (q + 8) true a1).
    { rewrite sib_a_COPY by exact M. unfold a_COPY. fold s q.
      destruct (Z.eqb_spec (i_length s) 0) as [E|E]; [lia|reflexivity]. }
    assert (Hq: (q + 8) / 8 = q / 8 + 1).
    { replace (q + 8) with (q + 1 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (M1: a_mode a1 = COPY) by exact M.
    assert (Q81: a_q a1 mod 8 = 0) by (unfold a1; cbn [a_q]; rewrite Z.add_mod, Q8 by lia; reflexivity).
    destruct (IH a1) as (a' & T & Es & Eq & EO); unfold a1 in *; cbn [a_s a_q a_O a_mode i_length set_i_length] in *;
      try (rewrite Hq); try (rewrite Zlength_app, Zlength_cons, Zlength_nil); try lia; try assumption.
    exists a'. split; [|split; [|split]].
    + eapply ar_step; [exact A| |exact T]. unfold blocked. intros [B|[_ B]]; lia.
    + rewrite Es. replace (i_length s - Z.succ (Z.of_nat n)) with (i_length s - 1 - Z.of_nat n) by lia.
      reflexivity.
    + rewrite Eq. lia.
    + rewrite EO, Hq, <- app_assoc. f_equal. unfold sbyte.
        rewrite (sublist_split (q / 8) (q / 8 + 1) (q / 8 + Z.succ (Z.of_nat n))) by
          (pose proof (Z.div_pos q 8 Q0 ltac:(lia)); lia).
        rewrite sublist_len_1 by (pose proof (Z.div_pos q 8 Q0 ltac:(lia)); lia). cbn [app]. f_equal. f_equal. lia.
Qed.

Lemma sib_sbits0 src q : sbits src q 0 = 0.
Proof. unfold sbits. rewrite Z.pow_0_r, Z.mod_1_r. reflexivity. Qed.

(* the bytes inflate copies are the input's at the bit position (an empty bit buffer) *)
Lemma sib_inbytes src P0 m k :
  bitbuf src P0 m -> 0 <= k -> m_nx m + k <= Zlength (m_inp m) ->
  inbytes m k = sublist (P0 + m_nx m) (P0 + m_nx m + k) src.
Proof.
  intros [_ H0 [_ Hi] [N0 _] _ _] K N. unfold inbytes. rewrite Hi at 1.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* the machine after copying k bytes of a stored block, and the abstract state after k steps *)
Lemma sib_rel_copy src P0 O0 m a k a' :
  rel src P0 O0 m a -> m_mode m = COPY -> m_bits m = 0 -> 0 <= k -> m_nx m + k <= Zlength (m_inp m) ->
  Zlength (m_ow m) + k <= m_aout m ->
  a_s a' = set_i_length (a_s a) (i_length (a_s a) - k) -> a_q a' = a_q a + 8 * k ->
  a_O a' = a_O a ++ sublist (a_q a / 8) (a_q a / 8 + k) src ->
  rel src P0 O0 (upd_s (set_m_nx (set_m_ow m (m_ow m ++ inbytes m k)) (m_nx m + k))
                       (fun s => set_i_length s (i_length s - k))) a'.
Proof.
  intros R M B0 K N W Es Eq EO.
  assert (D: data_mode (m_mode m)) by (rewrite M; sib_mdg).
  assert (NB: m_mode m <> BAD) by (rewrite M; sib_mdg).
  pose proof (rl_bb _ _ _ _ _ R) as BB.
  assert (Q8: a_q a / 8 = P0 + m_nx m).
  { rewrite (rl_q _ _ _ _ _ R NB). unfold mq. rewrite B0, Z.sub_0_r.
    replace (8 * (P0 + m_nx m)) with ((P0 + m_nx m) * 8) by lia. apply Z.div_mul. lia. }
  rewrite Q8 in EO. rewrite <- sib_inbytes in EO by (auto; lia).
  assert (Sq: seq (m_s m) (a_s a)) by exact (rl_s _ _ _ _ _ R NB).
  assert (Ma: a_mode a = COPY) by (rewrite <- (rl_mode _ _ _ _ _ R); exact M).
  assert (Le: i_length (m_s m) = i_length (a_s a))
    by (apply (se_length _ _ Sq); unfold a_mode in Ma; rewrite Ma; unfold len_live; tauto).
  destruct R. unfold m_left, m_mode in *. pose proof (Zlength_nonneg (m_ow m)).
  assert (Lb: Zlength (inbytes m k) = k).
  { unfold inbytes. destruct rl_bb as [_ _ _ Nx _ _]. rewrite Zlength_sublist; lia. }
  unfold a_mode in Ma.
  constructor; unfold a_mode, m_left; sib_cbn; rewrite ?Zlength_app, ?Lb, ?M, ?Es; sib_cbn; rewrite ?M, ?Ma.
  - destruct BB as [S1 S2 S3 S4 S5 S6]. constructor; sib_cbn; auto; [lia|lia|].
    rewrite S6, B0, !sib_sbits0. reflexivity.
  - reflexivity.
  - intros _. rewrite Eq. unfold mq in *. sib_cbn. rewrite B0 in *. lia.
  - unfold bits_ok. cbv zeta. sib_cbn. rewrite M. split; [intros X; exfalso; revert X; sib_mdg|].
    split; intros _; [exact B0|rewrite B0; reflexivity].
  - rewrite EO, rl_O, app_assoc. reflexivity.
  - lia.
  - exact rl_in.
  - destruct rl_out as (O1 & _ & O3). rewrite M in O3. rewrite O3 by (right; left; sib_mdg).
    rewrite ?Zlength_app, ?Lb. split; [lia|]. split; [intros X; exfalso; revert X; sib_mdg|intros _; reflexivity].
  - intros _ _. apply rl_ret; rewrite M; sib_mdg.
  - intros _. rewrite Le. apply sib_seq_length. exact Sq.
  - destruct rl_chk as [_ C]. rewrite M in C. split; [intros X; exfalso; revert X; sib_mdg|].
    intros _ Wr. apply C; [sib_mdg|exact Wr].
  - destruct rl_tot as [T1 _]. rewrite M in T1. split; [intros _; apply T1; right; left; sib_mdg|].
    intros X; exfalso; revert X; sib_mdg.
  - destruct rl_out as (_ & _ & O3). rewrite M in O3. rewrite O3 in * by (right; left; sib_mdg).
    rewrite rl_tout. f_equal. lia.
  - intros _. eapply sib_swin_ext; [..|apply rl_win; rewrite M; sib_mdg]; reflexivity.
  - exact rl_head.
Qed.

(* COPY: up to min(length, have, left) bytes of the input to the output, or the end of the block *)
Lemma sib_copy flush src P0 O0 m a :
  rel src P0 O0 m a -> 0 <= i_length (a_s a) -> m_leave m = 0 -> m_mode m = COPY ->
  sib_out flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a (c_COPY m).
Proof.
  intros R Lr L M.
  assert (NB: m_mode m <> BAD) by (rewrite M; sib_mdg).
  assert (Ma: a_mode a = COPY) by (rewrite <- (rl_mode _ _ _ _ _ R); exact M).
  assert (Q: a_q a = mq P0 m) by exact (rl_q _ _ _ _ _ R NB).
  pose proof (rl_bits _ _ _ _ _ R) as Bk. unfold bits_ok in Bk. cbv zeta in Bk.
  destruct Bk as (_ & Bc & _). pose proof (Bc (or_intror M)) as B0. clear Bc.
  assert (Sq: seq (m_s m) (a_s a)) by exact (rl_s _ _ _ _ _ R NB).
  assert (Le: i_length (m_s m) = i_length (a_s a))
    by (apply (se_length _ _ Sq); unfold a_mode in Ma; rewrite Ma; unfold len_live; tauto).
  pose proof (rl_bb _ _ _ _ _ R) as BB. destruct BB as [_ BP [Bi _] Bn _ _].
  pose proof (rl_aout _ _ _ _ _ R) as Ao. pose proof (Zlength_nonneg (m_ow m)).
  pose proof (rl_O _ _ _ _ _ R) as EO0.
  assert (Ret: m_ret m = Z_OK) by (apply (rl_ret _ _ _ _ _ R); rewrite M; sib_mdg).
  unfold mq in Q. rewrite B0, Z.sub_0_r in Q.
  unfold c_COPY. destruct (Z.eqb_spec (i_length (m_s m)) 0) as [L0|L0]; cbn [negb].
  - (* the block is done *)
    eapply sib_out_go; [eapply sib_ar1f|..].
    + rewrite sib_a_COPY by exact Ma. unfold a_COPY. rewrite <- Le, L0. reflexivity.
    + rewrite Q. lia.
    + eapply sib_rel_dstep; [exact R|rewrite M; sib_mdg|rewrite M; sib_mdg|..]; sib_cbn; try reflexivity.
      * eapply sib_bb_ext; [..|exact (rl_bb _ _ _ _ _ R)]; reflexivity.
      * apply sib_bits_free; sib_cbn; sib_mdg.
      * right. sib_mdg.
      * intros _. rewrite Q. unfold mq. sib_cbn. rewrite B0. lia.
      * intros _. apply sib_seq_mode0; [exact Sq|sib_mdg..].
    + sib_cbn. exact L.
  - cbv zeta. set (k := Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m)).
    assert (Kr: 0 <= k <= i_length (m_s m) /\ k <= m_have m /\ k <= m_left m).
    { unfold k, m_have, m_left. lia. }
    destruct (Z.eqb_spec k 0) as [K0|K0].
    + (* no input or no output space: the call stops *)
      apply sib_out_stay; [apply sib_rel_leave; exact R|]. intros _.
      unfold stop_ok. rewrite sib_a_COPY by exact Ma. unfold a_COPY. rewrite <- Le.
      destruct (Z.eqb_spec (i_length (m_s m)) 0) as [E|E]; [contradiction|]. cbn [negb].
      split; [exact Ret|]. right. right. left. unfold blocked.
      destruct (Z.eq_dec (m_have m) 0) as [H0|H0].
      * left. unfold m_have in H0. rewrite Q. lia.
      * right. split; [reflexivity|]. rewrite EO0, Zlength_app.
        assert (m_left m = 0) by (unfold k in K0; unfold m_have, m_left in *; lia). unfold m_left in *. lia.
    + (* k bytes *)
      assert (Kp: 0 < k) by lia.
      destruct (sib_copy_steps src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) (Z.to_nat k) a)
        as (a' & T & Es & Eq & EO); rewrite ?Z2Nat.id by lia; try exact Ma.
      { rewrite Q. rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
      { rewrite Q. lia. }
      { rewrite <- Le. lia. }
      { rewrite Q. unfold m_have in Kr. lia. }
      { rewrite EO0, Zlength_app. unfold m_left in Kr. lia. }
      { rewrite Q. rewrite Z.mul_comm, Z_div_mult by lia. unfold m_have in Kr. lia. }
      rewrite Z2Nat.id in Es, Eq, EO by lia.
      eapply sib_out_go; [exact T| |sib_cbn; exact L].
      apply (sib_rel_copy src P0 O0 m a k a'); auto; unfold m_have, m_left in Kr; lia.
Qed.

Lemma sib_COPY : kit_stmt -> sib_case COPY.
Proof.
  intros _ flush src P0 O0 m a R W L M. rewrite sib_c_COPY by exact M. apply sib_copy; auto.
  apply (sw_length _ (aw_swf _ _ W)).
Qed.

(* COPY_: the free step to COPY, then COPY *)
Lemma sib_copy_ flush src P0 O0 m a :
  rel src P0 O0 m a -> 0 <= i_length (a_s a) -> m_leave m = 0 -> m_mode m = COPY_ ->
  sib_out flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a (c_COPY_ m).
Proof.
  intros R Lr L M. unfold c_COPY_.
  assert (NB: m_mode m <> BAD) by (rewrite M; sib_mdg).
  assert (Ma: a_mode a = COPY_) by (rewrite <- (rl_mode _ _ _ _ _ R); exact M).
  assert (Q: a_q a = mq P0 m) by exact (rl_q _ _ _ _ _ R NB).
  pose proof (rl_bits _ _ _ _ _ R) as Bk. unfold bits_ok in Bk. cbv zeta in Bk.
  destruct Bk as (_ & Bc & _). pose proof (Bc (or_introl M)) as B0. clear Bc.
  assert (Sq: seq (m_s m) (a_s a)) by exact (rl_s _ _ _ _ _ R NB).
  set (a1 := AS (set_i_mode (a_s a) COPY) (a_q a) (a_O a)).
  apply (sib_out_pre _ _ _ _ _ _ _ a1).
  { eapply sib_ar1f; [rewrite sib_a_COPY_ by exact Ma; reflexivity|].
    rewrite Q. apply (sib_mq_le src), (rl_bb _ _ _ _ _ R). }
  refine (sib_copy flush src P0 O0 (set_mode m COPY) a1 _ Lr L eq_refl).
  unfold a1. eapply sib_rel_dstep; [exact R|rewrite M; sib_mdg|rewrite M; sib_mdg|..]; sib_cbn; try reflexivity.
  - eapply sib_bb_ext; [..|exact (rl_bb _ _ _ _ _ R)]; reflexivity.
  - unfold bits_ok. cbv zeta. sib_cbn. split; [sib_mdg|]. split; intros _; [exact B0|rewrite B0; reflexivity].
  - right. sib_mdg.
  - intros _. rewrite Q. apply sib_mq_ext; reflexivity.
  - intros _. apply sib_seq_mode; [exact Sq| |sib_mdg|sib_mdg]. intros _.
    apply (se_length _ _ Sq). unfold a_mode in Ma. rewrite Ma. unfold len_live. tauto.
Qed.

Lemma sib_COPY_ : kit_stmt -> sib_case COPY_.
Proof.
  intros _ flush src P0 O0 m a R W L M. rewrite sib_c_COPY_ by exact M. apply sib_copy_; auto.
  apply (sw_length _ (aw_swf _ _ W)).
Qed.

(* STORED: BYTEBITS (the abstract machine's alignment step), NEEDBITS(32), LEN and NLEN; then COPY_ *)
Lemma sib_STORED : kit_stmt -> sib_case STORED.
Proof.
  intros [K _] flush src P0 O0 m a R W L M.
  destruct K as (Kpull & Knb & Kdrop & Kinit & Kbyte & Kmod & Kshr & Krange & Kbyte8).
  rewrite sib_c_STORED by exact M. unfold c_STORED.
  set (I := P0 + Zlength (m_inp m)). set (Rr := Zlength O0 + m_aout m).
  assert (NB: m_mode m <> BAD) by (rewrite M; sib_mdg).
  assert (Ma: a_mode a = STORED) by (rewrite <- (rl_mode _ _ _ _ _ R); exact M).
  assert (Q: a_q a = mq P0 m) by exact (rl_q _ _ _ _ _ R NB).
  assert (Sq: seq (m_s m) (a_s a)) by exact (rl_s _ _ _ _ _ R NB).
  assert (Ret: m_ret m = Z_OK) by (apply (rl_ret _ _ _ _ _ R); rewrite M; sib_mdg).
  pose proof (rl_bb _ _ _ _ _ R) as BB.
  assert (Iq: mq P0 m <= 8 * I) by (apply (sib_mq_le src), BB).
  (* the alignment *)
  set (q1 := align8 (a_q a)). set (a1 := AS (a_s a) q1 (a_O a)).
  assert (T1: areach src I Rr a a1).
  { destruct (Z.eqb_spec (a_q a mod 8) 0) as [E|E].
    - unfold a1, q1. rewrite sib_align8_id by exact E. destruct a. apply ar_refl.
    - eapply sib_ar1f.
      + rewrite sib_a_STORED by exact Ma. unfold a_STORED.
        destruct (Z.eqb_spec (a_q a mod 8) 0) as [E'|E']; [contradiction|reflexivity].
      + unfold q1. rewrite Q. unfold mq. pose proof (bb_bits _ _ _ BB). pose proof (bb_nx _ _ _ BB).
        pose proof (sib_align8_le (P0 + m_nx m) (m_bits m) ltac:(lia)). unfold I. lia. }
  assert (Q18: q1 mod 8 = 0) by apply sib_align8_mod.
  assert (A1: astep lenfix_list distfix_list src a1 =
              let h := sbits src q1 32 in
              if negb (Z.land h 65535 =? Z.lxor (Z.shiftr h 16) 65535) then abad a1 (q1 + 32)
              else ago a1 (q1 + 32) (set_i_mode (set_i_length (a_s a) (h mod 65536)) COPY_)).
  { rewrite sib_a_STORED by exact Ma. unfold a_STORED. unfold a1 at 1 2. cbn [a_s a_q].
    rewrite Q18. reflexivity. }
  cbv zeta in A1.
  (* the concrete machine *)
  destruct (Kbyte src P0 m BB) as [BBb Qb].
  rewrite <- Q in Qb. fold q1 in Qb.
  pose proof (sib_bytebits_bits m ltac:(pose proof (bb_bits _ _ _ BB); lia)) as [Bb8 Bb].
  assert (Lb: m_leave (bytebits m) = 0) by exact L.
  destruct (Knb src P0 (bytebits m) 32 BBb Lb ltac:(lia)) as (BB1 & Qn & E1 & OK1 & LV1).
  set (m1 := needbits 32 (bytebits m)) in *.
  assert (Em1: m_s m1 = m_s m /\ m_ret m1 = m_ret m /\ m_inp m1 = m_inp m /\ m_aout m1 = m_aout m /\
               m_ow m1 = m_ow m /\ m_in m1 = m_in m /\ m_out m1 = m_out m /\ m_tout m1 = m_tout m)
    by (rewrite E1; unfold bytebits; sib_cbn; repeat split).
  destruct Em1 as (Es1 & Er1 & Ei1 & Ea1 & Eo1 & Ein1 & Eout1 & Et1).
  rewrite Qb in Qn.
  assert (Bk1: bits_ok (m_s m) (m_bits m1)).
  { assert (Mi: i_mode (m_s m) = STORED) by exact M. apply sib_bits_free; rewrite Mi; sib_mdg. }
  assert (R1: rel src P0 O0 m1 a1).
  { unfold a1. rewrite <- Qn. apply (sib_rel_bq src P0 O0 m a m1); auto. }
  destruct (Z.eqb_spec (m_leave m1) 1) as [Lv|Lv].
  - (* the input ends before LEN and NLEN *)
    exists a1. split; [exact T1|]. split; [exact R1|]. intros _.
    unfold stop_ok. rewrite A1. destruct (LV1 ltac:(lia)) as (_ & _ & _ & X). rewrite Qb in X.
    destruct (negb _); (split; [rewrite Er1; exact Ret|]); right; right; left; cbn; left; exact X.
  - assert (L1: m_leave m1 = 0) by (destruct (Z.eq_dec (m_leave m1) 0) as [X|X]; [exact X|];
                                     destruct (LV1 X) as [X1 _]; contradiction).
    destruct (OK1 L1) as (B32 & _ & _).
    assert (B1: m_bits m1 = 32).
    { apply sib_needbits32_bits; [|exact Bb8|exact L1].
      pose proof (bb_bits _ _ _ BB). pose proof (Z.div_mod (m_bits (bytebits m)) 8 ltac:(lia)).
      rewrite Bb8 in *. lia. }
    assert (Hh: m_hold m1 = sbits src q1 32) by (rewrite (bb_hold _ _ _ BB1), B1; f_equal; exact Qn).
    assert (Iq1: q1 + 32 <= 8 * I).
    { rewrite <- Qn. unfold mq, I. pose proof (bb_nx _ _ _ BB1). pose proof (bb_bits _ _ _ BB1). rewrite Ei1 in *. lia. }
    rewrite Hh. set (h := sbits src q1 32) in *.
    destruct (Z.eqb_spec (Z.land h 65535) (Z.lxor (Z.shiftr h 16) 65535)) as [Hc|Hc]; cbn [negb] in A1 |- *.
    + (* LEN and NLEN agree: COPY_ *)
      set (s2 := set_i_mode (set_i_length (a_s a) (h mod 65536)) COPY_).
      set (a2 := AS s2 (q1 + 32) (a_O a)).
      assert (T2: areach src I Rr a a2) by (eapply sib_ar_trans; [exact T1|]; eapply sib_ar1f; [exact A1|exact Iq1]).
      set (m2 := set_mode (initbits (upd_s m1 (fun s => set_i_length s (h mod 65536)))) COPY_).
      assert (R2: rel src P0 O0 m2 a2).
      { destruct (Kinit src P0 (upd_s m1 (fun s => set_i_length s (h mod 65536)))) as [BBi Qi];
          [eapply sib_bb_ext; [..|exact BB1]; reflexivity|].
        unfold m2, a2, s2. eapply sib_rel_dstep; [exact R|rewrite M; sib_mdg|rewrite M; sib_mdg|..];
          unfold initbits; sib_cbn; rewrite ?Es1, ?Ei1, ?Ea1, ?Eo1, ?Ein1, ?Eout1, ?Et1, ?Er1; sib_cbn; try reflexivity.
        - eapply sib_bb_ext; [..|exact BBi]; reflexivity.
        - unfold bits_ok. cbv zeta. sib_cbn. split; [sib_mdg|]. split; intros _; reflexivity.
        - right. sib_mdg.
        - intros _. rewrite (sib_mq_ext P0 (initbits (upd_s m1 (fun s => set_i_length s (h mod 65536)))))
            by reflexivity. rewrite Qi. sib_cbn. rewrite B1, (sib_mq_ext P0 m1) by reflexivity. rewrite Qn. reflexivity.
        - intros _. apply sib_seq_mode; [apply sib_seq_length; exact Sq|reflexivity|sib_mdg|sib_mdg]. }
      assert (Lm2: m_leave m2 = 0) by (unfold m2, initbits; sib_cbn; exact L1).
      destruct (Z.eqb_spec flush Z_TREES) as [Ft|Ft]; cbn [negb].
      * (* Z_TREES: stop after the stored block's header *)
        exists a2. split; [exact T2|]. split; [unfold set_leave; apply sib_rel_leave; exact R2|]. intros _.
        unfold stop_ok. rewrite sib_a_COPY_ by reflexivity. unfold a_COPY_, ago. cbv iota.
        split; [unfold set_leave, m2, initbits; sib_cbn; rewrite Er1; exact Ret|]. right. left. exact Ft.
      * pose proof (sib_copy_ flush src P0 O0 m2 a2 R2) as X.
        change (m_inp m2) with (m_inp m1) in X. change (m_aout m2) with (m_aout m1) in X.
        rewrite Ei1, Ea1 in X.
        eapply sib_out_pre; [exact T2|]. apply X; [|exact Lm2|reflexivity].
        unfold a2, s2. sib_cbn. apply Z.mod_pos_bound. lia.
    + (* LEN and NLEN disagree *)
      eapply sib_out_go; [eapply sib_ar_trans; [exact T1|]; eapply sib_ar1f; [exact A1|exact Iq1]| |].
      * unfold abad. eapply sib_rel_dstep; [exact R|rewrite M; sib_mdg|rewrite M; sib_mdg|..];
          unfold set_bad; sib_cbn; rewrite ?Es1, ?Ei1, ?Ea1, ?Eo1, ?Ein1, ?Eout1, ?Et1, ?Er1; sib_cbn; try reflexivity.
        -- eapply sib_bb_ext; [..|exact BB1]; reflexivity.
        -- apply sib_bits_free; sib_cbn; sib_mdg.
        -- left. reflexivity.
        -- intros X. contradiction.
        -- intros X. contradiction.
      * unfold set_bad; sib_cbn. exact L1.
Qed.
