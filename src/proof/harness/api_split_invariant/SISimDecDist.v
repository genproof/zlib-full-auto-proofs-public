(* DIST: the distance code (lookup1, lookup2 after a link: the entry of the abstract table walk), an invalid
   code, or the distance's extra bits (falling through into DISTEXT). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimDecKit.
Import ListNotations.
Local Open Scope Z_scope.

(* a disjunction of equations, one of which holds by reflexivity *)
Ltac orf := repeat (first [reflexivity | left; reflexivity | right]).

(* the link test of the abstract walk is inflate_table's for a distance table *)
Lemma islink_DISTS op : islink DISTS op = dist_islink op.
Proof. reflexivity. Qed.

(* the tables of two states that agree on the codes *)
Lemma tvalid_seq kind fx dx s t tr nb : seq s t -> tvalid kind fx dx t tr nb -> tvalid kind fx dx s tr nb.
Proof. intros H. unfold tvalid, tvalid_b, tab_entry. rewrite (se_codes _ _ H). auto. Qed.

Lemma trep_seq fx dx s t tr nb lk :
  seq s t -> trep (tab_entry fx dx t tr) nb lk -> trep (tab_entry fx dx s tr) nb lk.
Proof. intros H. unfold tab_entry. rewrite (se_codes _ _ H). auto. Qed.

(* a distance code is at least as long as its root entry's bits, which are >= 0 (so are a sub-table
   entry's) *)
Lemma adecode_dist_ge src s q :
  bytes_ok src ->
  (forall src q n, bytes_ok src -> 0 <= n -> 0 <= sbits src q n < 2 ^ n) ->
  tvalid DISTS lenfix_list distfix_list s (i_distcode s) (i_distbits s) ->
  0 <= e_bits (tab_entry lenfix_list distfix_list s (i_distcode s) (sbits src q (i_distbits s))) <=
  snd (adecode lenfix_list distfix_list src s (i_distcode s) (i_distbits s) dist_islink q).
Proof.
  intros Bs KR (sz & _ & [Rb _ T]).
  assert (Hi := KR src q (i_distbits s) Bs ltac:(lia)).
  destruct (T _ Hi) as [(_ & B1 & _) Hl]. cbv zeta in Hl. rewrite islink_DISTS in Hl.
  unfold adecode. destruct (dist_islink _); cbn [snd]; [|lia].
  destruct Hl as (_ & Op & _ & J).
  assert (Hj := KR src (q + e_bits (tab_entry lenfix_list distfix_list s (i_distcode s)
                                     (sbits src q (i_distbits s))))
                  (e_op (tab_entry lenfix_list distfix_list s (i_distcode s) (sbits src q (i_distbits s))))
                  Bs ltac:(lia)).
  destruct (J _ Hj) as (_ & (_ & B2 & _) & _). lia.
Qed.

(* the bit buffer updates of lookup1 then lookup2 are one update *)
Lemma set4_twice m nx h b lv nx' h' b' lv' :
  set_m_leave (set_m_bits (set_m_hold (set_m_nx
    (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv) nx') h') b') lv' =
  set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx') h') b') lv'.
Proof. destruct m; reflexivity. Qed.

Lemma set_i_back_twice s x y : set_i_back (set_i_back s x) y = set_i_back s y.
Proof. destruct s; reflexivity. Qed.

(* the fields a lookup does not change *)
Lemma set4_fields m m' nx h b lv :
  m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv ->
  m_s m' = m_s m /\ m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_in m' = m_in m /\
  m_out m' = m_out m /\ m_ret m' = m_ret m /\ m_tout m' = m_tout m.
Proof. intros ->. repeat split. Qed.

(* the walk's result when the root entry is a link, and when it is not *)
Lemma adecode_dist_link fx dx src s t nb q :
  dist_islink (e_op (tab_entry fx dx s t (sbits src q nb))) = true ->
  adecode fx dx src s t nb dist_islink q =
  (tab_entry fx dx s t (e_val (tab_entry fx dx s t (sbits src q nb)) +
     sbits src (q + e_bits (tab_entry fx dx s t (sbits src q nb))) (e_op (tab_entry fx dx s t (sbits src q nb)))),
   e_bits (tab_entry fx dx s t (sbits src q nb)) +
   e_bits (tab_entry fx dx s t (e_val (tab_entry fx dx s t (sbits src q nb)) +
     sbits src (q + e_bits (tab_entry fx dx s t (sbits src q nb))) (e_op (tab_entry fx dx s t (sbits src q nb)))))).
Proof. intros E. unfold adecode. cbv zeta. rewrite E. reflexivity. Qed.

Lemma adecode_dist_final fx dx src s t nb q :
  dist_islink (e_op (tab_entry fx dx s t (sbits src q nb))) = false ->
  adecode fx dx src s t nb dist_islink q =
  (tab_entry fx dx s t (sbits src q nb), e_bits (tab_entry fx dx s t (sbits src q nb))).
Proof. intros E. unfold adecode. cbv zeta. rewrite E. reflexivity. Qed.

(* DIST's abstract step reads the whole code *)
Lemma astep_DIST_go src a :
  a_mode a = DIST ->
  exists a1, astep lenfix_list distfix_list src a =
    AGo (a_q a + snd (adecode lenfix_list distfix_list src (a_s a) (i_distcode (a_s a)) (i_distbits (a_s a))
                        dist_islink (a_q a))) false a1.
Proof.
  intros Ha. rewrite astep_DIST by exact Ha. unfold a_DIST.
  destruct (adecode _ _ _ _ _ _ _ _) as [h l]. cbn [snd].
  destruct (negb _); eexists; reflexivity.
Qed.

(* DROPBITS after an update of the istate: the fields it keeps *)
Lemma drop_upd_fields k m f P0 :
  m_s (dropbits k (upd_s m f)) = f (m_s m) /\ m_inp (dropbits k (upd_s m f)) = m_inp m /\
  m_aout (dropbits k (upd_s m f)) = m_aout m /\ m_ow (dropbits k (upd_s m f)) = m_ow m /\
  m_in (dropbits k (upd_s m f)) = m_in m /\ m_out (dropbits k (upd_s m f)) = m_out m /\
  m_ret (dropbits k (upd_s m f)) = m_ret m /\ m_tout (dropbits k (upd_s m f)) = m_tout m /\
  m_leave (dropbits k (upd_s m f)) = m_leave m /\ mq P0 (upd_s m f) = mq P0 m.
Proof. repeat split. Qed.

(* the bit count after DROPBITS(k), k <= bits *)
Lemma dropbits_bits k m : 0 <= k <= m_bits m -> m_bits m <= 39 -> m_bits (dropbits k m) = m_bits m - k.
Proof. intros H B. unfold dropbits, u32. cbn. apply Z.mod_small. lia. Qed.

(* the end of the pass, after the code (l bits) has been dropped: an invalid code goes to BAD, a
   distance base sets offset and extra and falls through into DISTEXT *)
Lemma dist_tail flush src P0 O0 m a m4 here l b :
  awf_stmt -> sim_ok (fun md => md = DISTEXT) ->
  rel src P0 O0 m a -> awf src a -> m_mode m = DIST ->
  adecode lenfix_list distfix_list src (a_s a) (i_distcode (a_s a)) (i_distbits (a_s a)) dist_islink (a_q a)
    = (here, l) ->
  bitbuf src P0 m4 -> mq P0 m4 = mq P0 m + l -> m_leave m4 = 0 -> m_s m4 = set_i_back (m_s m) b ->
  m_inp m4 = m_inp m -> m_aout m4 = m_aout m -> m_ow m4 = m_ow m -> m_in m4 = m_in m ->
  m_out m4 = m_out m -> m_ret m4 = m_ret m -> m_tout m4 = m_tout m ->
  dgoal flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a
    (if negb (Z.land (e_op here) 64 =? 0) then IBrk (set_bad m4 M_d_code) else
     c_DISTEXT (set_mode (upd_s m4 (fun s => set_i_extra (set_i_offset s (e_val here)) (Z.land (e_op here) 15)))
                  DISTEXT)).
Proof.
  intros AW HX Rl Aw Hm Ad BB4 Q4 L4 Es4 Ei Ea Eo Ein Eout Er Et.
  assert (Ha: a_mode a = DIST) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Hm).
  assert (NB: m_mode m <> BAD) by (rewrite Hm; discriminate).
  assert (Sq: seq (m_s m) (a_s a)) by exact (rl_s _ _ _ _ _ Rl NB).
  assert (Q: a_q a = mq P0 m) by exact (rl_q _ _ _ _ _ Rl NB).
  assert (Le: i_length (m_s m) = i_length (a_s a))
    by (apply (se_length _ _ Sq); change (len_live (a_mode a)); rewrite Ha; unfold len_live; orf).
  assert (QI: a_q a + l <= 8 * (P0 + Zlength (m_inp m)))
    by (rewrite Q, <- Q4, <- Ei; apply (mq_le src); exact BB4).
  pose proof (rl_aout _ _ _ _ _ Rl) as Ao.
  destruct (Z.land (e_op here) 64 =? 0) eqn:E64; cbn [negb].
  - set (a1 := AS (set_i_mode (set_i_extra (set_i_offset (a_s a) (e_val here)) (Z.land (e_op here) 15)) DISTEXT)
                  (a_q a + l) (a_O a)).
    assert (S: astep lenfix_list distfix_list src a = AGo (a_q a + l) false a1)
      by (rewrite astep_DIST by exact Ha; unfold a_DIST; rewrite Ad, E64; reflexivity).
    eapply dgoal_go; [exact S|exact QI|].
    set (m5 := set_mode (upd_s m4 (fun s => set_i_extra (set_i_offset s (e_val here)) (Z.land (e_op here) 15)))
                 DISTEXT).
    rewrite <- (stepf2_DISTEXT flush lenfix_list distfix_list m5) by reflexivity.
    assert (Es5: m_s m5 = set_i_mode (set_i_extra (set_i_offset (set_i_back (m_s m) b) (e_val here))
                                        (Z.land (e_op here) 15)) DISTEXT)
      by (change (m_s m5) with (set_i_mode (set_i_extra (set_i_offset (m_s m4) (e_val here))
                                              (Z.land (e_op here) 15)) DISTEXT); rewrite Es4; reflexivity).
    eapply dcont; [exact HX| |eapply awf_go; eauto|exact L4|reflexivity|rewrite <- Ei; reflexivity
                  |rewrite <- Ea; reflexivity].
    eapply rel_dec_next with (m := m) (a := a); try exact Rl.
    + rewrite Hm. unfold decode_mode; orf.
    + apply bitbuf_ext with m4; try reflexivity. exact BB4.
    + exact Ei.
    + exact Ea.
    + exact Ein.
    + exact Eout.
    + exact Er.
    + exact Et.
    + change (m_ow m5) with (m_ow m4). rewrite Eo. lia.
    + reflexivity.
    + left. change (decode_mode DISTEXT). unfold decode_mode; orf.
    + change (mq P0 m5) with (mq P0 m4). rewrite Q4, <- Q. reflexivity.
    + change (m_ow m5) with (m_ow m4). rewrite Eo. exact (rl_O _ _ _ _ _ Rl).
    + rewrite Es5. apply seq_mode; [apply seq_extra, seq_offset, seq_back; exact Sq| | |];
        intros P; [exact Le|reflexivity|reflexivity].
    + rewrite Es5. reflexivity.
    + reflexivity.
    + reflexivity.
    + rewrite Es5. reflexivity.
    + rewrite Es5. reflexivity.
    + rewrite Es5. unfold win_eq. repeat split.
    + rewrite Es5. exact (rl_head _ _ _ _ _ Rl).
  - assert (S: astep lenfix_list distfix_list src a = abad a (a_q a + l))
      by (rewrite astep_DIST by exact Ha; unfold a_DIST; rewrite Ad, E64; reflexivity).
    unfold abad in S.
    eapply dgoal_go; [exact S|exact QI|].
    apply dgoal_here; [|cbn; rewrite L4; discriminate].
    assert (Es6: m_s (set_bad m4 M_d_code) = set_i_mode (set_i_back (m_s m) b) BAD)
      by (cbn; rewrite Es4; reflexivity).
    eapply rel_dec_bad with (m := m) (a := a); try exact Rl.
    + apply bitbuf_ext with m4; try reflexivity. exact BB4.
    + exact Ei.
    + exact Ea.
    + exact Eo.
    + exact Ein.
    + exact Eout.
    + exact Et.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + rewrite Es6. exact (rl_head _ _ _ _ _ Rl).
Qed.

Lemma sd_dist : dcase_next DIST (fun md => md = DISTEXT).
Proof.
  intros [KB KL] AW HX. apply sim_ok_dgoal. intros flush src P0 O0 m a Rl Aw L Hm.
  rewrite stepf2_DIST by exact Hm. unfold c_DIST. cbv zeta.
  assert (Ha: a_mode a = DIST) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Hm).
  assert (NB: m_mode m <> BAD) by (rewrite Hm; discriminate).
  assert (ND: m_mode m <> DONE) by (rewrite Hm; discriminate).
  assert (Sq: seq (m_s m) (a_s a)) by exact (rl_s _ _ _ _ _ Rl NB).
  assert (Q: a_q a = mq P0 m) by exact (rl_q _ _ _ _ _ Rl NB).
  pose proof (rl_bb _ _ _ _ _ Rl) as BB.
  assert (Dm: decode_mode (a_mode a)) by (rewrite Ha; unfold decode_mode; orf).
  assert (TV: tvalid DISTS lenfix_list distfix_list (m_s m) (i_distcode (m_s m)) (i_distbits (m_s m))).
  { rewrite (se_distcode _ _ Sq), (se_distbits _ _ Sq). apply tvalid_seq with (a_s a); [exact Sq|].
    exact (proj2 (md_tables _ (aw_md _ _ Aw) Dm)). }
  assert (TR: trep (tab_entry lenfix_list distfix_list (m_s m) (i_distcode (m_s m))) (i_distbits (m_s m))
                dist_islink).
  { rewrite (se_distcode _ _ Sq), (se_distbits _ _ Sq). apply trep_seq with (a_s a); [exact Sq|].
    exact (proj2 (proj1 (aw_tp _ _ Aw) Dm)). }
  assert (Ad: adecode lenfix_list distfix_list src (a_s a) (i_distcode (a_s a)) (i_distbits (a_s a)) dist_islink (a_q a)
            = adecode lenfix_list distfix_list src (m_s m) (i_distcode (m_s m)) (i_distbits (m_s m)) dist_islink (mq P0 m))
    by (rewrite (adecode_seq _ _ _ (m_s m) (a_s a) _ _ _ _ Sq), (se_distcode _ _ Sq), (se_distbits _ _ Sq), Q; reflexivity).
  pose proof (KL src P0 m DISTS (i_distcode (m_s m)) (i_distbits (m_s m)) dist_islink BB L TV TR
                (fun op E => eq_trans (islink_DISTS op) E)) as K.
  cbv zeta in K. destruct K as [K1 K2].
  destruct KB as (_ & _ & KD & _ & _ & _ & _ & KR & _).
  pose proof (adecode_dist_ge src (m_s m) (mq P0 m) (aw_src _ _ Aw) KR TV) as Ge.
  destruct (astep_DIST_go src a Ha) as (a0 & S0). rewrite Ad, Q in S0.
  pose proof (rl_ret _ _ _ _ _ Rl NB ND) as Ret.
  assert (Bk: forall b, bits_ok (m_s m) b)
    by (intros b; apply bits_ok_dec; change (decode_mode (m_mode m)); rewrite Hm; unfold decode_mode; orf).
  remember (tab_entry lenfix_list distfix_list (m_s m) (i_distcode (m_s m)) (sbits src (mq P0 m) (i_distbits (m_s m))))
    as root eqn:Er in *.
  destruct (lookup1 lenfix_list distfix_list (i_distcode (m_s m)) (i_distbits (m_s m)) m) as [[h1 m1] ok1] eqn:E1.
  destruct K1 as (E1s & BB1 & Q1 & T1 & F1).
  destruct (set4_fields _ _ _ _ _ _ E1s) as (Fs1 & Fi1 & Fa1 & Fo1 & Fin1 & Fout1 & Fr1 & Ft1).
  cbv beta iota.
  destruct ok1; cbn [negb].
  2:{ destruct (F1 eq_refl) as (L1 & _ & X).
      apply dgoal_here.
      - rewrite E1s. apply rel_bits; [exact Rl|exact NB|apply Bk|rewrite <- E1s; exact BB1|rewrite <- E1s; exact Q1].
      - intros _. eapply stop_need; [exact S0| |rewrite Fr1; exact Ret]. lia. }
  destruct (T1 eq_refl) as (L1 & Eh1 & Bits1). subst h1.
  assert (BBu: forall (m': mst) f, bitbuf src P0 m' -> bitbuf src P0 (upd_s m' f))
    by (intros m' f B; apply bitbuf_ext with m'; reflexivity || exact B).
  destruct (Z.land (e_op root) 240 =? 0) eqn:E240.
  - (* a link: the sub-table entry of lookup2 *)
    assert (Lk: dist_islink (e_op root) = true) by exact E240.
    specialize (K2 Lk m1 BB1 L1 Fs1 Fi1 Q1 (proj1 Bits1)).
    destruct (lookup2 lenfix_list distfix_list (i_distcode (m_s m)) root m1) as [[h2 m2] ok2] eqn:E2.
    destruct K2 as (E2s & BB2 & Q2 & T2 & F2).
    destruct (set4_fields _ _ _ _ _ _ E2s) as (Fs2 & Fi2 & Fa2 & Fo2 & Fin2 & Fout2 & Fr2 & Ft2).
    assert (E21: m2 = set_m_leave (set_m_bits (set_m_hold (set_m_nx m (m_nx m2)) (m_hold m2)) (m_bits m2))
                        (m_leave m2))
      by (rewrite E2s at 1; rewrite E1s at 1; apply set4_twice).
    pose proof (adecode_dist_link lenfix_list distfix_list src (m_s m) (i_distcode (m_s m)) (i_distbits (m_s m))
                  (mq P0 m)) as AL.
    rewrite <- Er in AL. specialize (AL Lk).
    cbv beta iota.
    destruct ok2; cbn [negb].
    2:{ destruct (F2 eq_refl) as (L2 & _ & X).
        apply dgoal_here.
        - rewrite E21. apply rel_bits; [exact Rl|exact NB|apply Bk|rewrite <- E21; exact BB2|rewrite <- E21; exact Q2].
        - intros _. eapply stop_need; [exact S0| |rewrite Fr2, Fr1; exact Ret]. rewrite AL. cbn [snd]. lia. }
    destruct (T2 eq_refl) as (L2 & Eh2 & Bits2).
    rewrite <- Eh2 in AL. rewrite AL in Ge. cbn [snd] in Ge.
    pose proof (bb_bits _ _ _ BB2) as Rb2.
    destruct (KD src P0 (upd_s m2 (fun s => set_i_back s (i_back s + e_bits root))) (e_bits root) (BBu _ _ BB2)
                ltac:(cbn; lia)) as (BB3 & Q3 & _).
    set (m3 := dropbits (e_bits root) (upd_s m2 (fun s => set_i_back s (i_back s + e_bits root)))) in *.
    destruct (drop_upd_fields (e_bits root) m2 (fun s => set_i_back s (i_back s + e_bits root)) P0)
      as (Gs3 & Gi3 & Ga3 & Go3 & Gin3 & Gout3 & Gr3 & Gt3 & Gl3 & Gq3).
    fold m3 in Gs3, Gi3, Ga3, Go3, Gin3, Gout3, Gr3, Gt3, Gl3.
    assert (Mb3: m_bits m3 = m_bits m2 - e_bits root)
      by (transitivity (m_bits (upd_s m2 (fun s => set_i_back s (i_back s + e_bits root))) - e_bits root);
          [apply dropbits_bits; cbn; lia|reflexivity]).
    destruct (KD src P0 (upd_s m3 (fun s => set_i_back s (i_back s + e_bits h2))) (e_bits h2) (BBu _ _ BB3)
                ltac:(change (m_bits (upd_s m3 (fun s => set_i_back s (i_back s + e_bits h2)))) with (m_bits m3); lia)) as (BB4 & Q4 & _).
    destruct (drop_upd_fields (e_bits h2) m3 (fun s => set_i_back s (i_back s + e_bits h2)) P0)
      as (Gs4 & Gi4 & Ga4 & Go4 & Gin4 & Gout4 & Gr4 & Gt4 & Gl4 & Gq4).
    apply (dist_tail flush src P0 O0 m a _ h2 (e_bits root + e_bits h2) (i_back (m_s m) + e_bits root + e_bits h2)
             AW HX Rl Aw Hm).
    + rewrite Ad, AL. reflexivity.
    + exact BB4.
    + rewrite Q4, Gq4, Q3, Gq3, Q2. lia.
    + rewrite Gl4, Gl3. exact L2.
    + rewrite Gs4, Gs3, Fs2, Fs1. cbv beta. rewrite set_i_back_twice. f_equal; cbn; lia.
    + rewrite Gi4, Gi3, Fi2, Fi1. reflexivity.
    + rewrite Ga4, Ga3, Fa2, Fa1. reflexivity.
    + rewrite Go4, Go3, Fo2, Fo1. reflexivity.
    + rewrite Gin4, Gin3, Fin2, Fin1. reflexivity.
    + rewrite Gout4, Gout3, Fout2, Fout1. reflexivity.
    + rewrite Gr4, Gr3, Fr2, Fr1. reflexivity.
    + rewrite Gt4, Gt3, Ft2, Ft1. reflexivity.
  - (* a final entry in the root table *)
    assert (Lk: dist_islink (e_op root) = false) by exact E240.
    pose proof (adecode_dist_final lenfix_list distfix_list src (m_s m) (i_distcode (m_s m)) (i_distbits (m_s m))
                  (mq P0 m)) as AF.
    rewrite <- Er in AF. specialize (AF Lk).
    cbv beta iota. cbn [negb].
    pose proof (bb_bits _ _ _ BB1) as Rb1.
    destruct (KD src P0 (upd_s m1 (fun s => set_i_back s (i_back s + e_bits root))) (e_bits root) (BBu _ _ BB1)
                ltac:(cbn; lia)) as (BB4 & Q4 & _).
    destruct (drop_upd_fields (e_bits root) m1 (fun s => set_i_back s (i_back s + e_bits root)) P0)
      as (Gs4 & Gi4 & Ga4 & Go4 & Gin4 & Gout4 & Gr4 & Gt4 & Gl4 & Gq4).
    apply (dist_tail flush src P0 O0 m a _ root (e_bits root) (i_back (m_s m) + e_bits root) AW HX Rl Aw Hm).
    + rewrite Ad, AF. reflexivity.
    + exact BB4.
    + rewrite Q4, Gq4, Q1. reflexivity.
    + rewrite Gl4. exact L1.
    + rewrite Gs4, Fs1. reflexivity.
    + rewrite Gi4, Fi1. reflexivity.
    + rewrite Ga4, Fa1. reflexivity.
    + rewrite Go4, Fo1. reflexivity.
    + rewrite Gin4, Fin1. reflexivity.
    + rewrite Gout4, Fout1. reflexivity.
    + rewrite Gr4, Fr1. reflexivity.
    + rewrite Gt4, Ft1. reflexivity.
Qed.
