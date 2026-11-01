(* LEN: the fast path (inflate_fast, by fast_sim_stmt) and the slow path (lookup1, lookup2 after a link: the
   entry of the abstract table walk), then the literal, the end of block, an invalid code, or the length's
   extra bits (falling through into LENEXT). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimDecKit.
Import ListNotations.
Local Open Scope Z_scope.

(* a disjunction of equations, one of which holds by reflexivity *)
Ltac orf := repeat (first [reflexivity | left; reflexivity | right]).

(* the entries of a table read in two states with the same codes[] are the same *)
Lemma tab_entry_fun fx dx s t : i_codes s = i_codes t -> tab_entry fx dx s = tab_entry fx dx t.
Proof. intros E. unfold tab_entry. rewrite E. reflexivity. Qed.

Lemma tvalid_seq kind s t tr rb : seq s t ->
  tvalid kind lenfix_list distfix_list t tr rb -> tvalid kind lenfix_list distfix_list s tr rb.
Proof. intros H. unfold tvalid, tvalid_b. rewrite (tab_entry_fun _ _ s t (se_codes _ _ H)). auto. Qed.

(* the abstract walk of a valid length/literal table: the root entry, and after a link the sub-table entry;
   the code lengths are not negative *)
Lemma adecode_len src s q :
  kit_bits_stmt -> bytes_ok src -> tvalid LENS lenfix_list distfix_list s (i_lencode s) (i_lenbits s) ->
  let root := tab_entry lenfix_list distfix_list s (i_lencode s) (sbits src q (i_lenbits s)) in
  0 <= e_bits root /\
  (len_islink (e_op root) = false ->
     adecode lenfix_list distfix_list src s (i_lencode s) (i_lenbits s) len_islink q = (root, e_bits root)) /\
  (len_islink (e_op root) = true ->
     let h2 := tab_entry lenfix_list distfix_list s (i_lencode s)
                 (e_val root + sbits src (q + e_bits root) (e_op root)) in
     0 <= e_bits h2 /\
     adecode lenfix_list distfix_list src s (i_lencode s) (i_lenbits s) len_islink q = (h2, e_bits root + e_bits h2)).
Proof.
  intros KB Bs TV root. destruct TV as (sz & _ & [Rb _ Root]).
  destruct KB as (_ & _ & _ & _ & _ & _ & _ & KR & _).
  assert (Hi: 0 <= sbits src q (i_lenbits s) < 2 ^ i_lenbits s) by (apply KR; auto; lia).
  specialize (Root _ Hi). cbv zeta in Root. fold root in Root. destruct Root as [Eo Rt].
  unfold adecode. cbv zeta. fold root.
  split; [unfold entry_ok in Eo; lia|]. split.
  - intros F. rewrite F. reflexivity.
  - intros T. rewrite T.
    assert (Lr: islink LENS (e_op root) = true) by (change (len_islink (e_op root) = true); exact T).
    rewrite Lr in Rt. destruct Rt as (_ & Hop & _ & Sub).
    assert (Hj: 0 <= sbits src (q + e_bits root) (e_op root) < 2 ^ e_op root) by (apply KR; auto; lia).
    destruct (Sub _ Hj) as (_ & Eo2 & _). split; [unfold entry_ok in Eo2; lia|reflexivity].
Qed.

(* a step of a_LEN reads the code (l bits) and writes nothing *)
Lemma a_LEN_go src a :
  exists a1, a_LEN lenfix_list distfix_list src a =
    AGo (a_q a + snd (adecode lenfix_list distfix_list src (a_s a) (i_lencode (a_s a)) (i_lenbits (a_s a))
                        len_islink (a_q a))) false a1.
Proof.
  unfold a_LEN. destruct (adecode _ _ _ _ _ _ _ _) as [h l]. cbn [snd].
  destruct (e_op h =? 0); [eexists; reflexivity|].
  destruct (negb (Z.land (e_op h) 32 =? 0)); [eexists; reflexivity|].
  destruct (negb (Z.land (e_op h) 64 =? 0)); eexists; reflexivity.
Qed.

(* a lookup only pulls bytes: the rest of the machine is unchanged *)
Lemma bits_frame m m' :
  m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m (m_nx m')) (m_hold m')) (m_bits m')) (m_leave m') ->
  m_s m' = m_s m /\ m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_in m' = m_in m /\
  m_out m' = m_out m /\ m_ret m' = m_ret m /\ m_tout m' = m_tout m.
Proof. intros E. rewrite E. cbn. auto 10. Qed.

(* the end of LEN's slow path, once the code's entry `here` is found: DROPBITS of its bits, then the literal,
   the end of the block, an invalid code, or the length's extra bits (falling through into LENEXT) *)
Definition len_tail (here: entry) (m: mst) : iout :=
  let m := dropbits (e_bits here) (upd_s m (fun s => set_i_back s (i_back s + e_bits here))) in
  let m := upd_s m (fun s => set_i_length s (e_val here)) in
  if e_op here =? 0 then IBrk (set_mode m LIT) else
  if negb (Z.land (e_op here) 32 =? 0) then
    IBrk (set_mode (upd_s m (fun s => set_i_back s (-1))) Zlib.proof.inflate.Model.TYPE) else
  if negb (Z.land (e_op here) 64 =? 0) then IBrk (set_bad m M_ll_code) else
  c_LENEXT lenfix_list distfix_list (set_mode (upd_s m (fun s => set_i_extra s (Z.land (e_op here) 15))) LENEXT).

(* the relation after the step *)
Ltac tail_rel m4 BB4 Q4 Sq4 Es4 Ei4 Ea4 Eo4 Ein4 Eout4 Er4 Et4 Hm Rl :=
  try (apply bitbuf_ext with m4; try reflexivity; exact BB4);
  try (rewrite (mq_ext _ m4) by reflexivity; rewrite Q4; reflexivity);
  try (apply seq_mode; [first [exact Sq4 | apply seq_back; exact Sq4 | apply seq_extra; exact Sq4]| | |]; let P := fresh in intros P; first [reflexivity | exfalso; dmd]);
  cbn; rewrite ?Ei4, ?Ea4, ?Eo4, ?Ein4, ?Eout4, ?Er4, ?Et4; try reflexivity; try lia;
  try (rewrite Hm; unfold decode_mode; orf);
  try (left; unfold decode_mode; orf);
  try exact (rl_O _ _ _ _ _ Rl);
  try (rewrite Es4; reflexivity);
  try (rewrite Es4; exact (rl_head _ _ _ _ _ Rl));
  try (rewrite Es4; unfold win_eq; repeat split).

(* the tail is one abstract step a_LEN: the machine m3 after the lookups differs from the loop head m only in
   the bit buffer and state->back, and the entry found is the abstract table walk's, of length l *)
Lemma len_tail_ok flush src P0 O0 m a m3 b here l :
  kit_stmt -> awf_stmt -> sim_ok (fun md => md = LENEXT) ->
  rel src P0 O0 m a -> awf src a -> m_mode m = LEN ->
  bitbuf src P0 m3 -> m_leave m3 = 0 -> m_s m3 = set_i_back (m_s m) b ->
  m_inp m3 = m_inp m -> m_aout m3 = m_aout m -> m_ow m3 = m_ow m -> m_in m3 = m_in m ->
  m_out m3 = m_out m -> m_ret m3 = m_ret m -> m_tout m3 = m_tout m ->
  0 <= e_bits here <= m_bits m3 -> mq P0 m3 + e_bits here = a_q a + l ->
  adecode lenfix_list distfix_list src (a_s a) (i_lencode (a_s a)) (i_lenbits (a_s a)) len_islink (a_q a) =
    (here, l) ->
  dgoal flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a (len_tail here m3).
Proof.
  intros [KB KL] AW HL Rl Aw Hm BB3 L3 Es3 Ei3 Ea3 Eo3 Ein3 Eout3 Er3 Et3 Hb Hq Hd.
  assert (Ha: a_mode a = LEN) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Hm).
  assert (NB: m_mode m <> BAD) by (rewrite Hm; discriminate).
  assert (Sq: seq (m_s m) (a_s a)) by exact (rl_s _ _ _ _ _ Rl NB).
  pose proof (rl_aout _ _ _ _ _ Rl) as Ao.
  unfold len_tail. cbv zeta.
  set (f := fun s => set_i_back s (i_back s + e_bits here)).
  destruct KB as (_ & _ & KD & _).
  assert (BBu: bitbuf src P0 (upd_s m3 f)) by (apply bitbuf_ext with m3; reflexivity || exact BB3).
  destruct (KD src P0 (upd_s m3 f) (e_bits here) BBu Hb) as (BB4 & Q4 & _).
  set (m4 := dropbits (e_bits here) (upd_s m3 f)) in *.
  assert (E4: m_s m4 = set_i_back (set_i_back (m_s m) b) (b + e_bits here) /\ m_inp m4 = m_inp m /\
              m_aout m4 = m_aout m /\ m_ow m4 = m_ow m /\ m_in m4 = m_in m /\ m_out m4 = m_out m /\
              m_ret m4 = m_ret m /\ m_tout m4 = m_tout m /\ m_leave m4 = 0)
    by (unfold m4, f, dropbits, upd_s; cbn; rewrite Es3; cbn; auto 10).
  destruct E4 as (Es4 & Ei4 & Ea4 & Eo4 & Ein4 & Eout4 & Er4 & Et4 & L4).
  change (mq P0 (upd_s m3 f)) with (mq P0 m3) in Q4. rewrite Hq in Q4.
  clearbody m4. clear f BBu.
  assert (QI: a_q a + l <= 8 * (P0 + Zlength (m_inp m)))
    by (rewrite <- Q4, <- Ei4; apply (mq_le src); exact BB4).
  assert (S: astep lenfix_list distfix_list src a = a_LEN lenfix_list distfix_list src a)
    by (apply astep_LEN; exact Ha).
  unfold a_LEN in S. rewrite Hd in S.
  assert (Sq4: seq (set_i_length (m_s m4) (e_val here)) (set_i_length (a_s a) (e_val here)))
    by (rewrite Es4; apply seq_length, seq_back, seq_back; exact Sq).
  revert S.
  destruct (Z.eqb_spec (e_op here) 0) as [Op0|Op0]; intros S.
  - (* a literal *)
    eapply dgoal_go; [exact S|exact QI|].
    apply dgoal_here; [|cbn; rewrite L4; discriminate].
    eapply rel_dec_next with (m := m) (a := a); try exact Rl.
    all: tail_rel m4 BB4 Q4 Sq4 Es4 Ei4 Ea4 Eo4 Ein4 Eout4 Er4 Et4 Hm Rl.
  - revert S. destruct (Z.eqb_spec (Z.land (e_op here) 32) 0) as [Op32|Op32]; cbn [negb]; intros S.
    2: { (* the end of the block *)
      eapply dgoal_go; [exact S|exact QI|].
      apply dgoal_here; [|cbn; rewrite L4; discriminate].
      eapply rel_dec_next with (m := m) (a := a); try exact Rl.
      all: tail_rel m4 BB4 Q4 Sq4 Es4 Ei4 Ea4 Eo4 Ein4 Eout4 Er4 Et4 Hm Rl. }
    revert S. destruct (Z.eqb_spec (Z.land (e_op here) 64) 0) as [Op64|Op64]; cbn [negb]; intros S.
    2: { (* an invalid code *)
      eapply dgoal_go; [exact S|exact QI|].
      apply dgoal_here; [|cbn; rewrite L4; discriminate].
      eapply rel_dec_bad with (m := m) (a := a); try exact Rl.
      all: tail_rel m4 BB4 Q4 Sq4 Es4 Ei4 Ea4 Eo4 Ein4 Eout4 Er4 Et4 Hm Rl. }
    (* the length's extra bits *)
    eapply dgoal_go; [exact S|exact QI|].
    set (m6 := set_mode (upd_s (upd_s m4 (fun s : istate => set_i_length s (e_val here)))
                 (fun s : istate => set_i_extra s (Z.land (e_op here) 15))) LENEXT).
    rewrite <- (stepf2_LENEXT flush lenfix_list distfix_list m6) by reflexivity.
    eapply dcont; [exact HL| |eapply awf_go; eauto|exact L4|reflexivity|rewrite <- Ei4; reflexivity
                  |rewrite <- Ea4; reflexivity].
    eapply rel_dec_next with (m := m) (a := a); try exact Rl.
    all: tail_rel m4 BB4 Q4 Sq4 Es4 Ei4 Ea4 Eo4 Ein4 Eout4 Er4 Et4 Hm Rl.
Qed.

Lemma sd_len : kit_stmt -> awf_stmt -> fast_sim_stmt -> sim_ok (fun md => md = LENEXT) -> sim_ok (fun md => md = LEN).
Proof.
  intros KIT AW FS HL. apply sim_ok_dgoal. intros flush src P0 O0 m a Rl Aw L Hm.
  rewrite stepf2_LEN by exact Hm. unfold c_LEN.
  destruct (andb (andb (6 <=? m_have m) (258 <=? m_left m)) (m_bits m <? 8)) eqn:F.
  - (* inflate_fast *)
    apply andb_prop in F. destruct F as [F F3]. apply andb_prop in F. destruct F as [F1 F2].
    apply Z.leb_le in F1. apply Z.leb_le in F2. apply Z.ltb_lt in F3.
    destruct (FS src P0 O0 m a Rl Aw L Hm F1 F2 F3) as (a' & A & R' & L').
    exists a'. split; [exact A|]. split; [exact R'|]. intros L1. rewrite L' in L1. discriminate.
  - (* the slow path *)
    destruct KIT as [KB KL].
    assert (Ha: a_mode a = LEN) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Hm).
    assert (NB: m_mode m <> BAD) by (rewrite Hm; discriminate).
    assert (ND: m_mode m <> DONE) by (rewrite Hm; discriminate).
    assert (Sq: seq (m_s m) (a_s a)) by exact (rl_s _ _ _ _ _ Rl NB).
    assert (Q: a_q a = mq P0 m) by exact (rl_q _ _ _ _ _ Rl NB).
    pose proof (rl_bb _ _ _ _ _ Rl) as BB.
    pose proof (rl_aout _ _ _ _ _ Rl) as Ao.
    assert (DM: decode_mode (i_mode (a_s a))) by (change (decode_mode (a_mode a)); rewrite Ha; unfold decode_mode; orf).
    assert (TVa: tvalid LENS lenfix_list distfix_list (a_s a) (i_lencode (a_s a)) (i_lenbits (a_s a)))
      by exact (proj1 (md_tables _ (aw_md _ _ Aw) DM)).
    assert (TRa: trep (tab_entry lenfix_list distfix_list (a_s a) (i_lencode (a_s a))) (i_lenbits (a_s a)) len_islink)
      by exact (proj1 (proj1 (aw_tp _ _ Aw) DM)).
    set (m0 := upd_s m (fun s => set_i_back s 0)).
    assert (Sq0: seq (m_s m0) (a_s a)) by (apply seq_back; exact Sq).
    assert (BB0: bitbuf src P0 m0) by (apply bitbuf_ext with m; reflexivity || exact BB).
    assert (Q0: mq P0 m0 = a_q a) by (rewrite Q; reflexivity).
    assert (Rl0: rel src P0 O0 m0 a).
    { eapply rel_dec_next with (m := m) (a := a); try exact Rl; cbn; try reflexivity.
      all: first [exact BB0 | exact (eq_sym Q0) | exact Sq0 | exact (rl_O _ _ _ _ _ Rl) | lia
                 | exact (rl_head _ _ _ _ _ Rl) | exact (rl_mode _ _ _ _ _ Rl)
                 | solve [unfold win_eq; cbn; auto] | (rewrite Hm; unfold decode_mode; orf)
                 | (left; change (decode_mode (m_mode m)); rewrite Hm; unfold decode_mode; orf)]. }
    assert (TV0: tvalid LENS lenfix_list distfix_list (m_s m0) (i_lencode (m_s m0)) (i_lenbits (m_s m0))).
    { rewrite (se_lencode _ _ Sq0), (se_lenbits _ _ Sq0). eapply tvalid_seq; [exact Sq0|exact TVa]. }
    assert (TR0: trep (tab_entry lenfix_list distfix_list (m_s m0) (i_lencode (m_s m0))) (i_lenbits (m_s m0)) len_islink).
    { rewrite (se_lencode _ _ Sq0), (se_lenbits _ _ Sq0), (tab_entry_fun _ _ _ _ (se_codes _ _ Sq0)). exact TRa. }
    assert (LK: forall op, len_islink op = true -> islink LENS op = true) by (intros op H; exact H).
    pose proof (KL src P0 m0 LENS (i_lencode (m_s m0)) (i_lenbits (m_s m0)) len_islink BB0 L TV0 TR0 LK) as K.
    cbv zeta in K |- *.
    rewrite (se_lencode _ _ Sq0), (se_lenbits _ _ Sq0), (tab_entry_fun _ _ _ _ (se_codes _ _ Sq0)), Q0 in K.
    rewrite (se_lencode _ _ Sq0), (se_lenbits _ _ Sq0).
    destruct (adecode_len src (a_s a) (a_q a) KB (aw_src _ _ Aw) TVa) as (Br & Dn & Dl).
    destruct (a_LEN_go src a) as (a1 & S1).
    rewrite <- (astep_LEN lenfix_list distfix_list src a Ha) in S1.
    set (root := tab_entry lenfix_list distfix_list (a_s a) (i_lencode (a_s a)) (sbits src (a_q a) (i_lenbits (a_s a))))
      in *.
    change (m_inp m0) with (m_inp m) in K.
    assert (Rt: m_ret m = Z_OK) by exact (rl_ret _ _ _ _ _ Rl NB ND).
    assert (BO: forall b, bits_ok (m_s m0) b)
      by (intros b; apply bits_ok_dec; change (decode_mode (m_mode m)); rewrite Hm; unfold decode_mode; orf).
    destruct K as [K1 K2].
    revert K1. destruct (lookup1 lenfix_list distfix_list (i_lencode (a_s a)) (i_lenbits (a_s a)) m0)
      as [[h1 m1] ok1] eqn:E1. intros K1.
    destruct K1 as (E1' & BB1 & Q1 & Ok1 & Nok1).
    destruct (bits_frame _ _ E1') as (Ms1 & Ei1 & Ea1 & Eo1 & Ein1 & Eout1 & Er1 & Et1).
    assert (Rl1: rel src P0 O0 m1 a).
    { rewrite E1'. apply rel_bits; [exact Rl0|exact NB|apply BO|rewrite <- E1'; exact BB1|].
      rewrite <- E1', Q1. exact (eq_sym Q0). }
    destruct ok1; cbn [negb].
    + destruct (Ok1 eq_refl) as (L1 & Eh1 & Hb1). subst h1.
      change (negb (e_op root =? 0) && (Z.land (e_op root) 240 =? 0))%bool with (len_islink (e_op root)).
      destruct (len_islink (e_op root)) eqn:LKr.
      * (* a link: the sub-table *)
        destruct (Dl eq_refl) as (Bh2 & Hd2).
        set (h2 := tab_entry lenfix_list distfix_list (a_s a) (i_lencode (a_s a))
                     (e_val root + sbits src (a_q a + e_bits root) (e_op root))) in *.
        pose proof (K2 eq_refl m1 BB1 L1 Ms1 Ei1 Q1 (proj1 Hb1)) as K3. clear K2.
        revert K3. destruct (lookup2 lenfix_list distfix_list (i_lencode (a_s a)) root m1)
          as [[h2' m2] ok2] eqn:E2. intros K3.
        destruct K3 as (E2' & BB2 & Q2 & Ok2 & Nok2).
        destruct (bits_frame _ _ E2') as (Ms2 & Ei2 & Ea2 & Eo2 & Ein2 & Eout2 & Er2 & Et2).
        destruct ok2; cbn [negb].
        -- destruct (Ok2 eq_refl) as (L2 & Eh2 & Hb2). subst h2'.
           destruct KB as (KP & KN & KD & KR).
           set (f := fun s => set_i_back s (i_back s + e_bits root)).
           assert (BBu: bitbuf src P0 (upd_s m2 f)) by (apply bitbuf_ext with m2; reflexivity || exact BB2).
           assert (Hk: 0 <= e_bits root <= m_bits (upd_s m2 f)) by (change (m_bits (upd_s m2 f)) with (m_bits m2); lia).
           destruct (KD src P0 (upd_s m2 f) (e_bits root) BBu Hk) as (BB3 & Q3 & _).
           pose proof (bb_bits _ _ _ BB2) as Bt2.
           refine (len_tail_ok flush src P0 O0 m a (dropbits (e_bits root) (upd_s m2 f)) (e_bits root) h2
                     (e_bits root + e_bits h2) (conj (conj KP (conj KN (conj KD KR))) KL) AW HL Rl Aw Hm BB3 _ _ _ _ _ _ _ _ _ _ _ Hd2).
           ++ exact L2.
           ++ cbn. rewrite Ms2, Ms1. reflexivity.
           ++ cbn. rewrite Ei2, Ei1. reflexivity.
           ++ cbn. rewrite Ea2, Ea1. reflexivity.
           ++ cbn. rewrite Eo2, Eo1. reflexivity.
           ++ cbn. rewrite Ein2, Ein1. reflexivity.
           ++ cbn. rewrite Eout2, Eout1. reflexivity.
           ++ cbn. rewrite Er2, Er1. reflexivity.
           ++ cbn. rewrite Et2, Et1. reflexivity.
           ++ cbn. unfold u32. rewrite Z.mod_small; lia.
           ++ rewrite Q3. change (mq P0 (upd_s m2 f)) with (mq P0 m2). rewrite Q2. lia.
        -- destruct (Nok2 eq_refl) as (L2 & _ & Hlt).
           apply dgoal_here.
           ++ rewrite E2'. apply rel_bits; [exact Rl1|unfold m_mode; rewrite Ms1; exact NB|rewrite Ms1; apply BO|rewrite <- E2'; exact BB2|].
              rewrite <- E2', Q2. exact (eq_sym Q1).
           ++ intros _. eapply stop_need; [exact S1| |rewrite Er2, Er1; exact Rt].
              rewrite Hd2. cbn [snd]. lia.
      * (* the root entry is the code's *)
        refine (len_tail_ok flush src P0 O0 m a m1 0 root (e_bits root) (conj KB KL) AW HL Rl Aw Hm BB1 L1 Ms1
                  Ei1 Ea1 Eo1 Ein1 Eout1 Er1 Et1 _ _ (Dn eq_refl)); lia.
    + destruct (Nok1 eq_refl) as (L1 & _ & Hlt).
      apply dgoal_here; [exact Rl1|]. intros _.
      eapply stop_need; [exact S1| |rewrite Er1; exact Rt].
      destruct (len_islink (e_op root)) eqn:LKr.
      * destruct (Dl eq_refl) as (Bh2 & Hd2). rewrite Hd2. cbn [snd]. lia.
      * rewrite (Dn eq_refl). cbn [snd]. lia.
Qed.
