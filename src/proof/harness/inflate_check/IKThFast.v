(* Law inflate_check, theory part: LEN's fast path (inflate_fast) keeps Kx.
   The bit buffer: Step3Fast.v's segment analysis of fast_iter (each pull has its byte, each drop has
   its bits), redone with ik_bitbuf carried along (ikf_bb); the rest of Kx is untouched by the fast
   path (only nx, hold, bits, ow, the mode and the message change; m_out = m_aout). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.inflate.Step3Fast.
Require Import Zlib.proof.harness.inflate_check.IKTheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ikf_len_ok_iff: forall e, Inv2.len_ok e <-> StepInv.len_ok e.
Proof. intros e. unfold Inv2.len_ok, StepInv.len_ok. split; intros H R; specialize (H R); lia. Qed.

Lemma ikf_mwf3x: forall m, Inv3.mwf3 m -> mwf3x m.
Proof.
  intros m [W [A B C D]]. constructor; auto. constructor; auto.
  intros E. destruct (B E) as (sz & S1 & S2 & S3). exists sz. split; auto. split; auto.
  intros i Hi. apply ikf_len_ok_iff. auto.
Qed.

Section BB.
Variables (src: list Z) (pos: Z) (inp: list Z).
Hypotheses (KK: ik_kit) (CX: ctx_ok src pos inp).

Definition ikf_bb (m: mst) : Prop :=
  m_inp m = inp /\ ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m).

Lemma ikf_bb_pull m : ikf_bb m -> 0 <= m_nx m < Zlength (m_inp m) -> m_bits m <= 56 -> ikf_bb (pull m).
Proof.
  intros [I B] N L. rewrite I in N.
  destruct (kk_pull KK src pos inp m CX I N L B) as (B' & _).
  split; [|exact B']. unfold pull; simpl. exact I.
Qed.

Lemma ikf_bb_drop m k : ikf_bb m -> 0 <= k <= m_bits m -> m_bits m <= 39 -> ikf_bb (dropbits k m).
Proof.
  intros [I B] K L. split; [unfold dropbits; simpl; exact I|].
  unfold dropbits; simpl.
  replace (u32 (m_bits m - k)) with (m_bits m - k) by (unfold u32; rewrite Z.mod_small; lia).
  apply (kk_bb_drop KK); auto.
Qed.

Lemma ikf_bb_ow m o : ikf_bb m -> ikf_bb (set_m_ow m o).
Proof. unfold ikf_bb; simpl; auto. Qed.

Lemma ikf_fill2 m : mwf m -> 0 <= m_bits m <= 31 ->
  (m_bits m < 15 -> 16 <= 8 * (Zlength (m_inp m) - m_nx m)) -> ikf_bb m -> ikf_bb (s_fill2 m).
Proof.
  intros W B N H. unfold s_fill2, fpull. destruct (Z.ltb_spec (m_bits m) 15) as [L|L]; [|exact H].
  specialize (N L). pose proof (mw_nx _ W).
  destruct (pull_facts m W ltac:(lia) B) as (W1 & _ & B1 & _ & _ & _ & N1).
  apply ikf_bb_pull.
  - apply ikf_bb_pull; auto; lia.
  - rewrite N1. replace (m_inp (pull m)) with (m_inp m) by reflexivity. lia.
  - lia.
Qed.

Lemma ikf_fwalk: forall kind lf t rb sz s m here m',
  tvalid_g kind (tab_entry lenfix_list distfix_list s t) rb sz ->
  (forall op, 1 <= op <= 14 -> lf op = true) ->
  (forall e, final_ok kind e -> lf (e_op e) = false) ->
  mwf m -> m_s m = s -> 15 <= m_bits m -> ikf_bb m ->
  fwalk_f lenfix_list distfix_list 2 lf t (tab_entry lenfix_list distfix_list s t (m_hold m mod 2 ^ rb)) m = (here, m') ->
  ikf_bb m'.
Proof.
  intros kind lf t rb sz s m here m' TV LT LF W Es Bm BB E.
  pose proof (tv_rb _ _ _ _ TV) as RB. pose proof (tv_size _ _ _ _ TV) as SZ.
  assert (Hi: 0 <= m_hold m mod 2 ^ rb < 2 ^ rb) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  set (i := m_hold m mod 2 ^ rb) in *.
  pose proof (tv_root _ _ _ _ TV i Hi) as R. cbv zeta in R. destruct R as [Eok R].
  set (e := tab_entry lenfix_list distfix_list s t i) in *.
  rewrite fwalk_S in E. cbv zeta in E.
  pose proof (mw_bits _ W) as WB.
  destruct (islink kind (e_op e)) eqn:IL.
  - destruct R as (R1 & R2 & R3 & R4).
    rewrite (LT (e_op e) ltac:(lia)) in E.
    destruct (drop_facts m (e_bits e) W ltac:(lia)) as (W1 & F1 & B1 & A1 & Q1 & O1 & N1).
    pose proof (ikf_bb_drop m (e_bits e) BB ltac:(lia) ltac:(lia)) as BB1.
    set (m1 := dropbits (e_bits e) m) in *.
    assert (Hj: 0 <= m_hold m1 mod 2 ^ e_op e < 2 ^ e_op e) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
    destruct (R4 _ Hj) as (S1 & S2 & S3 & S4 & S5). cbv zeta in S1, S2, S3, S4, S5.
    assert (Es1: m_s m1 = s) by (unfold m1, dropbits; simpl; auto).
    rewrite Es1 in E.
    set (e2 := tab_entry lenfix_list distfix_list s t (e_val e + m_hold m1 mod 2 ^ e_op e)) in *.
    rewrite fwalk_S in E. cbv zeta in E. rewrite (LF _ S5) in E.
    inversion E; subst here m'. destruct S2 as (_ & S2 & _).
    pose proof (mw_bits _ W1).
    apply ikf_bb_drop; auto; lia.
  - destruct R as [R1 R2]. rewrite (LF _ R2) in E. inversion E; subst here m'.
    destruct Eok as (_ & Eb & _).
    apply ikf_bb_drop; auto; lia.
Qed.

Lemma ikf_lext: forall here m len m',
  mwf m -> 0 <= m_bits m <= 31 -> 16 <= e_op here <= 21 ->
  (m_bits m < 5 -> m_nx m < Zlength (m_inp m)) -> ikf_bb m ->
  s_lext here m = (len, m') -> ikf_bb m'.
Proof.
  intros here m len m' W B Op N BB E. unfold s_lext in E. cbv zeta in E.
  destruct (land16_cases (e_op here) ltac:(lia)) as [_ Lx].
  set (opx := Z.land (e_op here) 15) in *.
  pose proof (mw_nx _ W).
  destruct (Z.eqb_spec opx 0) as [Z0|Z0].
  - simpl in E. inversion E; subst len m'. exact BB.
  - simpl in E.
    assert (P: exists m1, (if m_bits m <? opx then fpull m else m) = m1 /\ mwf m1 /\ ikf_bb m1 /\
               opx <= m_bits m1 <= 31).
    { destruct (Z.ltb_spec (m_bits m) opx).
      - destruct (pull_facts m W ltac:(apply N; lia) B) as (W1 & F1 & B1 & A1 & Q1 & O1 & N1).
        exists (pull m). split; [reflexivity|]. split; [auto|]. split; [|lia].
        apply ikf_bb_pull; auto; [specialize (N ltac:(lia)); lia | lia].
      - exists m. split; [reflexivity|]. split; [auto|]. split; [auto|]. lia. }
    destruct P as (m1 & E1 & W1 & BB1 & B1). rewrite E1 in E.
    inversion E; subst len m'. fold (dropbits opx m1).
    apply ikf_bb_drop; auto; lia.
Qed.

Lemma ikf_dext: forall opx m, mwf m -> 0 <= opx <= 13 -> 0 <= m_bits m <= 31 -> 13 <= avail m ->
  ikf_bb m -> ikf_bb (s_dext opx m).
Proof.
  intros opx m W X B A BB. pose proof (mw_nx _ W). unfold s_dext, fpull, avail in *.
  destruct (Z.ltb_spec (m_bits m) opx).
  - destruct (pull_facts m W ltac:(lia) B) as (W1 & F1 & B1 & A1 & Q1 & O1 & N1).
    pose proof (ikf_bb_pull m BB ltac:(lia) ltac:(lia)) as BB1.
    rewrite B1.
    destruct (Z.ltb_spec (m_bits m + 8) opx).
    + apply ikf_bb_pull; auto.
      * rewrite N1. replace (m_inp (pull m)) with (m_inp m) by reflexivity. lia.
      * lia.
    + exact BB1.
  - exact BB.
Qed.

(* one iteration (Step3Fast.iter_ok with the bit buffer) *)
Lemma ikf_iter: forall m, mwf3x m -> m_mode m = LEN -> m_nx m + 6 <= Zlength (m_inp m) ->
  Zlength (m_ow m) + 258 <= m_aout m -> m_bits m <= 31 -> ikf_bb m ->
  let '(go, m') := fast_iter' m in
  exists mb, Step3Fast.frame m mb /\ mwf mb /\ qv m <= qv mb /\ 0 <= m_bits mb <= 31 /\ ikf_bb mb /\
    ((go = true /\ m' = mb) \/
     (go = false /\ (m' = set_mode mb Model.TYPE \/ exists e, m' = set_bad mb e))).
Proof.
  intros m [W X] Hmd Hnx How Hb BB0.
  assert (DM: decode_mode (m_mode m)) by (unfold decode_mode; right; left; exact Hmd).
  destruct (x3_lens _ X DM) as (lsz & Lsz & LV & LOK).
  destruct (md_tables _ (mw_md _ W) DM) as [_ (dsz & Dsz & DV)].
  pose proof (mw_bits _ W) as B0.
  pose proof (sw_wdata _ (mw_s _ W)) as [_ BW].
  pose proof (sw_wnext _ (mw_s _ W)) as [[WN _] _].
  pose proof (mw_ow _ W) as [_ BO].
  pose proof (mw_nx _ W) as NX0.
  assert (A0: 48 <= avail m) by (unfold avail; lia).
  unfold fast_iter'. cbv zeta.
  destruct (fill2_ok m W ltac:(lia) ltac:(intros; lia)) as (W1 & F1 & B1 & A1 & Q1 & O1).
  pose proof (ikf_fill2 m W ltac:(lia) ltac:(intros; lia) BB0) as BB1.
  destruct (frame_s _ _ F1) as (S1 & I1 & AO1 & SO1 & _).
  match goal with |- context [fwalk_f ?a ?b ?c ?d ?e ?f ?g] => destruct (fwalk_f a b c d e f g) as [h1 m2] eqn:E2 end.
  pose proof (ikf_fwalk LENS len_link _ _ _ _ _ h1 m2 LV len_link_true len_link_final W1 S1 ltac:(lia) BB1 E2) as BB2.
  destruct (fwalk_ok LENS len_link _ _ _ _ _ h1 m2 LV len_link_true len_link_final W1 S1 ltac:(lia) E2)
    as (W2 & F2 & B2 & A2 & Q2 & O2 & FO2 & (i2 & I2 & H2)).
  destruct (frame_s _ _ F2) as (S2 & I2' & AO2 & SO2 & _).
  cbv beta iota.
  destruct (e_op h1 =? 0) eqn:Op0; cbv beta iota.
  - (* literal *)
    exists (set_m_ow m2 (m_ow m2 ++ [e_val h1 mod 256])).
    pose proof (Z.mod_pos_bound (e_val h1) 256 ltac:(lia)).
    split; [eapply frame_trans; [exact F1|]; eapply frame_trans; [exact F2|]; apply frame_ow|].
    split.
    { apply mwf_set_ow; auto.
      - rewrite Zlength_app, Zlength_cons, Zlength_nil. rewrite O2, O1, AO2, AO1. lia.
      - apply bytes_ok_app1; [congruence|lia].
      - pose proof (mw_sow _ W2). rewrite Zlength_app. pose proof (Zlength_nonneg [e_val h1 mod 256]). lia. }
    split; [unfold qv in *; simpl; lia|]. split; [simpl; lia|]. split; [apply ikf_bb_ow; exact BB2|].
    left; auto.
  - destruct (Z.land (e_op h1) 16 =? 0) eqn:L16; cbv beta iota.
    + destruct (Z.land (e_op h1) 32 =? 0); cbv beta iota;
      exists m2; (split; [eapply frame_trans; eauto|]); (split; [auto|]); (split; [lia|]); (split; [lia|]);
      (split; [exact BB2|]);
      right; (split; [reflexivity|]); [right; eexists; reflexivity | left; reflexivity].
    + apply Z.eqb_neq in L16. pose proof (final_len16 _ FO2 L16) as OpR.
      assert (LO: StepInv.len_ok h1) by (rewrite H2; apply LOK; auto).
      destruct (s_lext h1 m2) as [len m3] eqn:E3.
      unfold avail in A0, A1, A2.
      pose proof (mw_nx _ W2) as NX2.
      pose proof (ikf_lext h1 m2 len m3 W2 ltac:(lia) OpR ltac:(intros; lia) BB2 E3) as BB3.
      destruct (lext_ok h1 m2 len m3 W2 ltac:(lia) OpR FO2 LO ltac:(intros; lia) E3)
        as (W3 & F3 & B3 & A3 & Q3 & O3 & Len).
      destruct (frame_s _ _ F3) as (S3 & I3 & AO3 & SO3 & _).
      unfold avail in A3.
      cbv beta iota.
      pose proof (ikf_fill2 m3 W3 ltac:(lia) ltac:(intros; lia) BB3) as BB4.
      destruct (fill2_ok m3 W3 ltac:(lia) ltac:(intros; lia)) as (W4 & F4 & B4 & A4 & Q4 & O4).
      destruct (frame_s _ _ F4) as (S4 & I4 & AO4 & SO4 & _).
      match goal with |- context [fwalk_f ?a ?b ?c ?d ?e ?f ?g] => destruct (fwalk_f a b c d e f g) as [h5 m5] eqn:E5 end.
      pose proof (ikf_fwalk DISTS dist_link _ _ _ _ _ h5 m5 DV dist_link_true dist_link_final W4
                  ltac:(congruence) ltac:(lia) BB4 E5) as BB5.
      destruct (fwalk_ok DISTS dist_link _ _ _ _ _ h5 m5 DV dist_link_true dist_link_final W4
                  ltac:(congruence) ltac:(lia) E5)
        as (W5 & F5 & B5 & A5 & Q5 & O5 & FO5 & _).
      destruct (frame_s _ _ F5) as (S5 & I5 & AO5 & SO5 & _).
      cbv beta iota.
      destruct (Z.land (e_op h5) 16 =? 0) eqn:D16; cbv beta iota.
      * exists m5.
        split; [repeat (eapply frame_trans; [eassumption|]); apply frame_refl|].
        split; [auto|]. split; [lia|]. split; [lia|]. split; [exact BB5|].
        right. split; [reflexivity|]. right; eexists; reflexivity.
      * apply Z.eqb_neq in D16. pose proof (final_dist16 _ FO5 D16) as DR.
        destruct (land16_cases (e_op h5) DR) as [_ DX].
        unfold avail in A4, A5.
        pose proof (ikf_dext (Z.land (e_op h5) 15) m5 W5 ltac:(lia) ltac:(lia) ltac:(unfold avail; lia) BB5) as BB6.
        destruct (dext_ok (Z.land (e_op h5) 15) m5 W5 ltac:(lia) ltac:(lia) ltac:(unfold avail; lia))
          as (W6 & F6 & B6 & Q6 & O6).
        pose proof (ikf_bb_drop _ (Z.land (e_op h5) 15) BB6 ltac:(lia) ltac:(lia)) as BB7.
        destruct (drop_facts _ (Z.land (e_op h5) 15) W6 ltac:(lia)) as (W7 & F7 & B7 & A7 & Q7 & O7 & N7).
        destruct (frame_s _ _ F6) as (S6 & I6 & AO6 & SO6 & _).
        destruct (frame_s _ _ F7) as (S7 & I7 & AO7 & SO7 & _).
        match goal with |- context [s_copy ?a ?b ?c ?d] => destruct (s_copy a b c d) as [go m8] eqn:E8 end.
        assert (OW7: m_ow (dropbits (Z.land (e_op h5) 15) (s_dext (Z.land (e_op h5) 15) m5)) = m_ow m) by congruence.
        apply copy_ok in E8; [| auto | rewrite OW7; auto | lia | auto].
        destruct E8 as [(G & o & E8 & Lo & Bo8) | (G & E8)]; subst go m8.
        -- exists (set_m_ow (dropbits (Z.land (e_op h5) 15) (s_dext (Z.land (e_op h5) 15) m5)) o).
           split; [repeat (eapply frame_trans; [eassumption|]); apply frame_ow|].
           split.
           { apply mwf_set_ow; auto; rewrite ?AO7, ?AO6, ?AO5, ?AO4, ?AO3, ?AO2.
             - rewrite AO1. rewrite OW7 in Lo. lia.
             - pose proof (mw_sow _ W7). lia. }
           rewrite qv_ow, bits_ow. split; [lia|]. split; [lia|]. split; [apply ikf_bb_ow; exact BB7|].
           left; auto.
        -- exists (dropbits (Z.land (e_op h5) 15) (s_dext (Z.land (e_op h5) 15) m5)).
           split; [repeat (eapply frame_trans; [eassumption|]); apply frame_refl|].
           split; [auto|]. split; [lia|]. split; [lia|]. split; [exact BB7|].
           right. split; [reflexivity|]. right; eexists; reflexivity.
Qed.

Lemma ikf_loop: forall k m, mwf3x m -> m_mode m = LEN -> m_nx m + 6 <= Zlength (m_inp m) ->
  Zlength (m_ow m) + 258 <= m_aout m -> 0 <= m_bits m <= 31 -> ikf_bb m ->
  exists mb, Step3Fast.frame m mb /\ mwf3x mb /\ qv m <= qv mb /\ 0 <= m_bits mb <= 31 /\ ikf_bb mb /\
    (fast_loop lenfix_list distfix_list k m = mb \/
     fast_loop lenfix_list distfix_list k m = set_mode mb Model.TYPE \/
     exists e, fast_loop lenfix_list distfix_list k m = set_bad mb e).
Proof.
  induction k; intros m W Hmd Hnx How Hb BB.
  - exists m. split; [apply frame_refl|]. split; [auto|]. split; [lia|]. split; [lia|]. split; [auto|].
    left; reflexivity.
  - rewrite fast_loop_S, fast_iter_eq.
    pose proof (ikf_iter m W Hmd Hnx How ltac:(lia) BB) as IT.
    destruct (fast_iter' m) as [go m1]. destruct IT as (mb & F & Wb & Q & B & BBb & C).
    assert (W2: mwf3x mb) by (eapply mwf3x_of_frame; eauto).
    destruct (frame_s _ _ F) as (S & I & AO & _).
    destruct C as [(G & E) | (G & E)]; subst go.
    + subst m1. simpl andb.
      destruct (andb (m_nx mb <? Zlength (m_inp mb) - 5) (Zlength (m_ow mb) <? m_aout mb - 257)) eqn:Cnd.
      * apply andb_prop in Cnd. destruct Cnd as [C1 C2]. apply Z.ltb_lt in C1. apply Z.ltb_lt in C2.
        assert (Md: m_mode mb = LEN) by (unfold m_mode; rewrite S; exact Hmd).
        destruct (IHk mb W2 Md ltac:(lia) ltac:(lia) B BBb) as (mb' & F' & W' & Q' & B' & BB' & C').
        exists mb'. split; [eapply frame_trans; eauto|]. split; [auto|]. split; [lia|]. split; [lia|].
        split; [auto|]. exact C'.
      * exists mb. split; [auto|]. split; [auto|]. split; [lia|]. split; [lia|]. split; [auto|].
        left; reflexivity.
    + simpl andb. exists mb. split; [auto|]. split; [auto|]. split; [lia|]. split; [lia|]. split; [auto|].
      right. destruct E as [E|[e E]]; [left; exact E | right; exists e; exact E].
Qed.

(* the unused whole bytes given back *)
Lemma ikf_post m : mwf m -> 0 <= m_bits m <= 31 -> ikf_bb m -> ikf_bb (Step3Fast.post m).
Proof.
  intros W B [I BB]. pose proof (mw_nx _ W) as NX.
  destruct CX as (C1 & C2 & C3 & C4).
  assert (S: Z.shiftr (m_bits m) 3 = m_bits m / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  pose proof (Z.div_mod (m_bits m) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (m_bits m) 8 ltac:(lia)).
  unfold Step3Fast.post, ikf_bb. rewrite S. set (q := m_bits m / 8) in *.
  cbn [m_nx m_hold m_bits m_inp set_m_bits set_m_hold set_m_nx]. split; [exact I|].
  replace (pos + (m_nx m - q)) with (pos + m_nx m - q) by lia.
  replace (m_bits m - q * 8) with (m_bits m - 8 * q) by lia.
  apply (kk_bb_giveback KK); auto.
  - rewrite I in NX. lia.
  - apply Z.div_pos; lia.
  - lia.
Qed.

End BB.

(* ---------------------------------------------------------------------------------------------- *)
(* Kx of the result                                                                              *)

Lemma ikf_kx wrap src pos out a0 m mf :
  Kx wrap src pos out a0 m -> m_mode m = LEN -> m_out m = m_aout m ->
  i_total (m_s mf) = i_total (m_s m) -> i_check (m_s mf) = i_check (m_s m) ->
  i_flags (m_s mf) = i_flags (m_s m) ->
  m_adler mf = m_adler m -> m_out mf = m_out m -> m_aout mf = m_aout m -> m_tout mf = m_tout m ->
  (m_mode mf = LEN \/ m_mode mf = Zlib.proof.inflate.Model.TYPE \/ m_mode mf = BAD) ->
  ik_bitbuf src (pos + m_nx mf) (m_hold mf) (m_bits mf) ->
  8 * m_nx m - m_bits m <= 8 * m_nx mf - m_bits mf ->
  Kx wrap src pos out a0 mf.
Proof.
  intros K Md Om Et Ec Ef Ea Eo Eao Eto Mf Bf Q.
  assert (Pm: ik_post_mode (m_mode m)).
  { unfold ik_post_mode, decode_mode. right; right; right; right; right; right; right; right; left.
    right; left; exact Md. }
  assert (NP: ~ ik_pre_mode (m_mode mf)).
  { unfold ik_pre_mode, ik_gzhdr_mode. unfold LEN, Zlib.proof.inflate.Model.TYPE, BAD, HEAD, FLAGS, TIME, OS,
      EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT in *. lia. }
  assert (Post: wrap <> 0 -> ik_post wrap src pos out mf).
  { intros Wr. pose proof (kx_post _ _ _ _ _ _ K Wr Pm) as P. unfold ik_post in *. cbv zeta in *.
    rewrite Ef, Ec, Ea, Eo, Eao. rewrite Om, Z.sub_diag in *. rewrite !sublist_nil in *.
    destruct P as [H1 [H2 H3]]. split; [|split; auto].
    destruct H1 as [H1|H1]; [left|right]; destruct H1 as (A1 & A2 & A3 & A4);
      (split; [exact A1|split; [exact A2|split; [exact A3|lia]]]). }
  constructor.
  - exact (kx_wrap _ _ _ _ _ _ K).
  - exact Bf.
  - split; intros H; exfalso;
      unfold LEN, Zlib.proof.inflate.Model.TYPE, BAD, EXTRA, NAME, COMMENT, COPY_, COPY, EXLEN in *; lia.
  - left; congruence.
  - rewrite Et, Eao, Eo. exact (kx_total _ _ _ _ _ _ K).
  - rewrite Eto, Eao, Eo. exact (kx_tout _ _ _ _ _ _ K).
  - intros Wr. destruct (kx_raw _ _ _ _ _ _ K Wr) as [A _]. rewrite Ea. split; [exact A|].
    unfold ik_gzhdr_mode, LEN, Zlib.proof.inflate.Model.TYPE, BAD, FLAGS, TIME, OS,
      EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT in *. lia.
  - intros _ H. exfalso; apply NP; exact H.
  - intros _ H. exfalso; apply NP; unfold ik_pre_mode; right; left; exact H.
  - intros _ H. exfalso; apply NP; unfold ik_pre_mode; right; right; exact H.
  - intros Wr _. exact (Post Wr).
  - intros Wr _. right. exact (Post Wr).
  - intros _. unfold ik_trail. cbv zeta.
    split; [|split]; intros Hx; exfalso;
      unfold LEN, Zlib.proof.inflate.Model.TYPE, BAD, CHECK, LENGTH, DONE in *; lia.
Qed.

Ltac ikf_qv :=
  match goal with Q: qv _ <= qv _ |- _ =>
    unfold qv in Q; unfold Step3Fast.post; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8;
    cbn [restore upd_s set_mode set_bad m_nx m_bits set_m_bits set_m_hold set_m_nx set_m_s set_m_sow
         set_m_snx set_m_msg];
    cbn in Q; lia
  end.

Lemma ikx_fast : fastx_part_stmt.
Proof.
  intros KK wrap src pos out a0 inp aout m CX HK HX W L Md Om Hh Hl Hb. cbv zeta.
  pose proof (ikf_mwf3x m W) as W3.
  pose proof (mwf3x_restore m W3) as W0.
  set (m0 := restore m) in *.
  assert (Md0: m_mode m0 = LEN) by exact Md.
  assert (N0: m_nx m0 + 6 <= Zlength (m_inp m0)) by (unfold m_have in Hh; exact (ltac:(simpl; lia))).
  assert (O0: Zlength (m_ow m0) + 258 <= m_aout m0) by (unfold m_left in Hl; exact (ltac:(simpl; lia))).
  assert (B0: 0 <= m_bits m0 <= 31) by (pose proof (mw_bits _ (m3_w _ W3)); exact (ltac:(simpl; lia))).
  assert (BB0: ikf_bb src pos inp m0) by (split; [exact (kc_inp _ _ _ _ _ _ HK) | exact (kx_buf _ _ _ _ _ _ HX)]).
  destruct (ikf_loop src pos inp KK CX (Z.to_nat (m_aout m0) + 1) m0 W0 Md0 N0 O0 B0 BB0)
    as (mb & F & Wb & Q & B & BBb & C).
  destruct (frame_s _ _ F) as (S & I & AO & SO & OO).
  pose proof (ikf_post src pos inp KK CX mb (m3_w _ Wb) B BBb) as [_ BBp].
  assert (Mb: m_mode mb = LEN) by (unfold m_mode; rewrite S; exact Md0).
  destruct mode_neq as (N1 & N2 & N3 & N4 & N5).
  rewrite fast_eq. destruct C as [E | [E | [e E]]]; rewrite E.
  - rewrite mode_restore_post, Mb. apply Z.eqb_neq in N1. rewrite N1.
    apply ikf_kx with m; auto.
    all: first [ exact BBp | (rewrite F; reflexivity) | ikf_qv ].
  - rewrite post_set_mode.
    replace (m_mode (set_mode (restore (post mb)) Model.TYPE) =? Model.TYPE) with true
      by (symmetry; apply Z.eqb_eq; reflexivity).
    apply ikf_kx with m; auto.
    all: first [ exact BBp | (rewrite F; reflexivity) | (right; left; reflexivity) | ikf_qv ].
  - rewrite post_set_bad.
    replace (m_mode (set_bad (restore (post mb)) e) =? Model.TYPE) with false
      by (symmetry; apply Z.eqb_neq; exact N2).
    apply ikf_kx with m; auto.
    all: first [ exact BBp | (rewrite F; reflexivity) | (right; right; reflexivity) | ikf_qv ].
Qed.
