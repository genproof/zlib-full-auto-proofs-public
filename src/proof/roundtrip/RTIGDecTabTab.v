(* RT-I: copy of rfc1951/DecTabTab.v over the generalized definitions RTIGDefs.v. *)
(* Part of DecTab: TABLE (NEEDBITS(14), HLIT/HDIST/HCLEN).  Kit and statements: DecTabKit.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDefs Zlib.proof.roundtrip.RTIGDecTabKit.
Import ListNotations.
Local Open Scope Z_scope.

(* the TABLE disjunct of at_mode *)
Lemma ttb_at_table G s c hold bits out :
  at_mode G s c hold bits out -> i_mode s = TABLE ->
  hold_ok G c hold bits /\ at_table G s (8 * c - bits) bits out.
Proof.
  unfold at_mode. cbv zeta. intros [Hh D] E. split; [exact Hh|].
  unfold HEAD, FLAGS, TIME, OS, Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE,
    LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE in *.
  repeat match type of D with
  | (_ /\ _) \/ _ => destruct D as [[E' A]|D]; [first [exact A | exfalso; lia] |]
  end.
  destruct D as [E' _]. exfalso. lia.
Qed.

(* block_ok of block k *)
Lemma ttb_blocks_nth wmax : forall bs out k, blocks_ok wmax out bs -> (k < length bs)%nat ->
  exists out', block_ok wmax out' (nth k bs (Stored [])).
Proof.
  induction bs as [|b bs IH]; intros out k H Hk; simpl in Hk; [lia|].
  destruct H as [H1 H2]. destruct k as [|k]; simpl.
  - exists out. exact H1.
  - apply (IH _ k H2). lia.
Qed.

Lemma ttb_dyn_ranges G k nlen ndist cls toks syms :
  dctx_ok G -> 0 <= k < nblk G -> blk G k = Dynamic nlen ndist cls toks syms ->
  257 <= nlen <= 286 /\ 1 <= ndist <= 30 /\ 4 <= Zlength cls <= 19.
Proof.
  intros (SO & _) Hk B. destruct SO as (_ & _ & _ & _ & _ & BO).
  unfold nblk in Hk. rewrite Zlength_correct in Hk.
  destruct (ttb_blocks_nth _ _ _ (Z.to_nat k) BO ltac:(lia)) as [out' OKb].
  unfold blk in B. rewrite B in OKb. simpl in OKb. lia.
Qed.

(* the 14 header bits, piece by piece *)
Lemma ttb_hdr_piece (K: dkit_stmt) G k nlen ndist cls toks syms a n v :
  dctx_ok G -> 0 <= k < nblk G -> blk G k = Dynamic nlen ndist cls toks syms ->
  0 <= a -> 0 <= n -> a + n <= 14 -> sublist a (a + n) (dyn_hdr14 nlen ndist cls) = bits_le v n ->
  0 <= v < 2 ^ n ->
  bval (sublist (bpos G k + 3 + a) (bpos G k + 3 + a + n) (sbits G)) = v.
Proof.
  intros OK Hk B Ha Hn Han E Hv.
  pose proof (dyn_sub_hdr K G k nlen ndist cls toks syms OK Hk B) as D.
  pose proof (bpos_ge_D0 G k). pose proof (D0_nonneg G).
  replace (sublist (bpos G k + 3 + a) (bpos G k + 3 + a + n) (sbits G))
    with (sublist a (a + n) (sublist (bpos G k + 3) (bpos G k + 17) (sbits G))).
  2:{ rewrite sublist_sublist by lia. f_equal; lia. }
  rewrite D, E, bval_bits_le by lia. apply Z.mod_small. exact Hv.
Qed.

Lemma ttb_hdr_split nlen ndist cls :
  sublist 0 (0 + 5) (dyn_hdr14 nlen ndist cls) = bits_le (nlen - 257) 5 /\
  sublist 5 (5 + 5) (dyn_hdr14 nlen ndist cls) = bits_le (ndist - 1) 5 /\
  sublist 10 (10 + 4) (dyn_hdr14 nlen ndist cls) = bits_le (Zlength cls - 4) 4.
Proof.
  unfold dyn_hdr14.
  assert (L5: forall v, Zlength (bits_le v 5) = 5) by (intros; apply Zlength_bits_le; lia).
  assert (L4: forall v, Zlength (bits_le v 4) = 4) by (intros; apply Zlength_bits_le; lia).
  split; [|split].
  - rewrite sublist_app1 by (rewrite ?L5; lia). apply sublist_same; rewrite ?L5; lia.
  - rewrite sublist_app2 by (rewrite ?L5; lia). rewrite L5.
    rewrite sublist_app1 by (rewrite ?L5; lia). apply sublist_same; rewrite ?L5; lia.
  - rewrite sublist_app2 by (rewrite ?L5; lia). rewrite L5.
    rewrite sublist_app2 by (rewrite ?L5; lia). rewrite L5.
    apply sublist_same; rewrite ?L4; lia.
Qed.

(* after the 14 bits: the state at LENLENS *)
Lemma ttb_post G pos inp ob m m4 k nlen ndist cls toks syms :
  dkit_stmt -> ictx G pos inp -> Kd G pos inp ob m -> m_mode m = TABLE -> tabs_ok (m_s m) ->
  bop m m4 -> m_leave m = 0 -> hb G pos inp m4 -> qp pos m4 = bpos G k + 17 -> m_bits m4 < 8 ->
  in_blk G (m_s m) k -> blk G k = Dynamic nlen ndist cls toks syms -> ob ++ m_ow m = outk G k ->
  (forall m', tin G pos inp ob m' -> m_mode m' = LENLENS -> m_ow m' = m_ow m ->
     tt_ok G pos inp ob (m_ow m) (ttab_ll m')) ->
  tt_ok G pos inp ob (m_ow m)
    (ttab_ll (set_mode (upd_s (upd_s m4 (fun s => set_i_ncode (set_i_ndist (set_i_nlen s nlen) ndist) (Zlength cls)))
                              (fun s => set_i_have s 0)) LENLENS)).
Proof.
  intros K C Kd0 M TB (S4 & R4 & L4 & F4) L0 H4 Q4 B4 IB BK O HL.
  set (m6 := set_mode _ LENLENS).
  assert (F6: tfr m4 m6) by (constructor; reflexivity).
  assert (S6: m_s m6 = set_i_mode (set_i_have (set_i_ncode (set_i_ndist (set_i_nlen (m_s m) nlen) ndist)
                         (Zlength cls)) 0) LENLENS) by (unfold m6, set_mode, upd_s; cbn [m_s set_m_s]; rewrite S4; reflexivity).
  assert (Md6: m_mode m6 = LENLENS) by (unfold m_mode; rewrite S6; reflexivity).
  assert (Ow6: m_ow m6 = m_ow m) by (rewrite (tf_ow _ _ F6); apply (tf_ow _ _ F4)).
  destruct H4 as (I4 & N4 & B64 & HO4).
  apply HL; [|exact Md6|exact Ow6].
  split; [|split; [|split]].
  - apply (kd_tfr G pos inp ob m m6 Kd0).
    + left. exact M.
    + exact (tfr_trans _ _ _ F4 F6).
    + right; left. exact Md6.
    + change (m_ret m6) with (m_ret m4). rewrite R4. rewrite (kd_ret _ _ _ _ _ Kd0), M. reflexivity.
    + change (m_nx m6) with (m_nx m4). change (m_hold m6) with (m_hold m4). change (m_bits m6) with (m_bits m4).
      rewrite Ow6, O, S6. unfold at_mode. cbv zeta. split; [exact HO4|].
      do 6 right. left. split; [reflexivity|].
      exists k, nlen, ndist, cls, toks, syms. cbn [i_mode set_i_mode i_last set_i_last i_nlen set_i_nlen
        i_ndist set_i_ndist i_ncode set_i_ncode i_have set_i_have i_lens set_i_mode].
      destruct IB as [IB1 IB2].
      split; [split; [exact IB1|]; cbn; exact IB2|].
      split; [exact BK|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [pose proof (Zlength_nonneg cls); lia|].
      split; [intros; lia|]. unfold qp in Q4. split; lia.
  - change (m_leave m6) with (m_leave m4). congruence.
  - change (m_nx m6) with (m_nx m4). exact N4.
  - unfold tabs_ok in *. rewrite S6. cbn. exact TB.
Qed.

Lemma part_tab : part_tab_stmt.
Proof.
  intros G pos inp ob m K C SL (Kd0 & L0 & NX & TB) M HL.
  pose proof C as C'. destruct C' as (OK & P0 & PL & E).
  destruct (ttb_at_table _ _ _ _ _ _ (kd_at _ _ _ _ _ Kd0) M)
    as [HO (k & nlen & ndist & cls & toks & syms & IB & BK & O & Q & B14)].
  pose proof IB as [Hk Lf].
  destruct (ttb_dyn_ranges G k nlen ndist cls toks syms OK Hk BK) as (Rn & Rd & Rc).
  pose proof (proj1 HO) as Bnn.
  assert (H0: hb G pos inp m) by (split; [exact (kd_inp _ _ _ _ _ Kd0)|split; [exact NX|split; [lia|exact HO]]]).
  assert (Q0: qp pos m = bpos G k + 3) by (unfold qp; lia).
  assert (R0: m_ret m = Z_OK) by (rewrite (kd_ret _ _ _ _ _ Kd0), M; reflexivity).
  pose proof (dyn_len G k nlen ndist cls toks syms BK) as DL.
  pose proof (bpos_succ K G k OK Hk) as BS.
  pose proof (bpos_endpos K G (k + 1) OK ltac:(lia)) as BE.
  pose proof (Zlength_nonneg (dyn_tkb cls toks)) as Z1.
  pose proof (Zlength_nonneg (send_syms (dyn_ll nlen toks) (dyn_dl nlen ndist toks) syms)) as Z2.
  destruct (hb_needbits K G pos inp C 4 14 m H0 ltac:(lia) ltac:(simpl; lia))
    as (H1 & Q1 & S1 & R1 & F1 & Bb1 & Cs).
  change (needbits_f 4 14 m) with (needbits 14 m) in *.
  unfold ttab_tab. cbv zeta.
  set (m1 := needbits 14 m) in *.
  destruct Cs as [(L1 & N1 & B1) | (L1 & B1)].
  - rewrite L1. change (1 =? 1) with true. cbv beta iota.
    unfold tt_ok. split; [|split; [exact (tf_ow _ _ F1)|split; [exact L1|split; [exact N1|]]]].
    + apply (kd_tfr G pos inp ob m m1 Kd0).
      * left. exact M.
      * exact F1.
      * unfold md_tabl, m_mode. rewrite S1. left. exact M.
      * congruence.
      * rewrite S1, (tf_ow _ _ F1). unfold at_mode. cbv zeta. split; [exact (proj2 (proj2 (proj2 H1)))|].
        do 5 right. left. split; [exact M|].
        exists k, nlen, ndist, cls, toks, syms. split; [exact IB|]. split; [exact BK|]. split; [exact O|].
        unfold qp in Q1, Q0. split; lia.
    + apply (leave_slen G pos inp m1 14 SL N1 B1). lia.
  - rewrite L1, L0. change (0 =? 1) with false. cbv beta iota.
    pose proof (ttb_hdr_split nlen ndist cls) as (E1 & E2 & E3).
    assert (V1: bitsn m1 5 = nlen - 257).
    { rewrite (hb_bitsn K G pos inp m1 5 H1 ltac:(lia)), Q1, Q0.
      rewrite <- (ttb_hdr_piece K G k nlen ndist cls toks syms 0 5 (nlen - 257) OK Hk BK ltac:(lia) ltac:(lia)
                    ltac:(lia) E1 ltac:(simpl; lia)).
      all: (f_equal; f_equal; lia). }
    destruct (hb_drop K G pos inp m1 5 H1 ltac:(lia)) as (H2 & Q2 & B2).
    assert (V2: bitsn (dropbits 5 m1) 5 = ndist - 1).
    { rewrite (hb_bitsn K G pos inp _ 5 H2 ltac:(lia)), Q2, Q1, Q0.
      rewrite <- (ttb_hdr_piece K G k nlen ndist cls toks syms 5 5 (ndist - 1) OK Hk BK ltac:(lia) ltac:(lia)
                    ltac:(lia) E2 ltac:(simpl; lia)).
      all: (f_equal; f_equal; lia). }
    destruct (hb_drop K G pos inp _ 5 H2 ltac:(lia)) as (H3 & Q3 & B3).
    assert (V3: bitsn (dropbits 5 (dropbits 5 m1)) 4 = Zlength cls - 4).
    { rewrite (hb_bitsn K G pos inp _ 4 H3 ltac:(lia)), Q3, Q2, Q1, Q0.
      rewrite <- (ttb_hdr_piece K G k nlen ndist cls toks syms 10 4 (Zlength cls - 4) OK Hk BK ltac:(lia) ltac:(lia)
                    ltac:(lia) E3 ltac:(simpl; lia)).
      all: (f_equal; f_equal; lia). }
    destruct (hb_drop K G pos inp _ 4 H3 ltac:(lia)) as (H4 & Q4 & B4).
    rewrite V1, V2, V3.
    replace (nlen - 257 + 257) with nlen by lia. replace (ndist - 1 + 1) with ndist by lia.
    replace (Zlength cls - 4 + 4) with (Zlength cls) by lia.
    replace ((286 <? nlen) || (30 <? ndist))%bool with false
      by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia).
    cbv beta iota.
    apply (ttb_post G pos inp ob m _ k nlen ndist cls toks syms K C Kd0 M TB); try assumption.
    + eapply bop_trans; [|apply bop_drop]. eapply bop_trans; [|apply bop_drop].
      eapply bop_trans; [|apply bop_drop]. split; [exact S1|split; [exact R1|split; [exact L1|exact F1]]].
    + lia.
    + lia.
Qed.
