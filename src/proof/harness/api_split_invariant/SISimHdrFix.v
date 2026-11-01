(* The header simulation, the fixed-width gzip fields FLAGS, TIME, OS, EXLEN: NEEDBITS of the field, then
   the field's update and the fall-through into the next mode. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdrKit.
Import ListNotations.
Local Open Scope Z_scope.

(* NEEDBITS of a whole field: when the input ends in it, the call stops before the abstract step that
   reads the field; otherwise the pass goes on (K) with the field's bits in hold *)
Lemma sh_field n flush src P0 O0 R m a w a1 (K: mst -> iout) :
  kit_bits_stmt -> rel src P0 O0 m a -> hbits m -> m_leave m = 0 -> hdr_mode (m_mode m) ->
  ~ (m_mode m = EXTRA \/ m_mode m = NAME \/ m_mode m = COMMENT \/
     (m_mode m = EXLEN /\ Z.land (i_flags (m_s m)) 1024 = 0)) ->
  n = (if orb (m_mode m =? TIME) (m_mode m =? DICTID) then 32 else 16) ->
  astep lenfix_list distfix_list src a = AGo (a_q a + n) w a1 ->
  (forall nx1 h1,
     bitbuf src P0 (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h1) n) 0) ->
     mq P0 (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h1) n) 0) = mq P0 m ->
     h1 = sbits src (a_q a) n -> a_q a = mq P0 m -> a_q a + n <= 8 * (P0 + Zlength (m_inp m)) ->
     hgoal flush src P0 O0 (P0 + Zlength (m_inp m)) R a
       (K (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h1) n) 0))) ->
  hgoal flush src P0 O0 (P0 + Zlength (m_inp m)) R a
    (if m_leave (needbits n m) =? 1 then IBrk (needbits n m) else K (needbits n m)).
Proof.
  intros KB Rl Hb L0 Hh NS En ST HK.
  destruct (Hb Hh) as (B8 & Bn & _). rewrite <- En in Bn.
  assert (Hn: n = 16 \/ n = 32) by (rewrite En; destruct (orb _ _); auto).
  destruct (hdr_not_bad _ Hh) as [NB _].
  pose proof (rl_bb _ _ _ _ _ Rl) as BB.
  destruct (needbits_hdr src P0 m n KB BB L0 Hn B8 Bn) as (E1 & BB1 & Q1 & S1 & F1).
  set (m1 := needbits n m) in *.
  set (nx1 := m_nx m1) in *. set (h1 := m_hold m1) in *. set (b1 := m_bits m1) in *. set (l1 := m_leave m1) in *.
  clearbody m1 nx1 h1 b1 l1. subst m1.
  pose proof (rl_q _ _ _ _ _ Rl NB) as Q.
  cbn [m_leave set_m_leave].
  destruct (Z.eqb_spec l1 1) as [Lv|Lv].
  - (* the input ends in the field *)
    destruct (F1 ltac:(cbn; lia)) as (_ & B8' & Bn' & Blk). cbn in B8', Bn'. subst l1.
    exists a. split; [apply ar_refl|]. split; [apply hrel_mk|].
    + intros BO. apply rel_bits; auto.
    + intros _. unfold m_mode in *. cbn. rewrite <- En. split; [exact B8'|]. split; [exact Bn'|].
      intros N; exfalso; exact (NS N).
    + unfold m_mode. cbn. exact (hdr_not_copy _ Hh).
    + intros _. eapply stop_need; [exact ST| |].
      * rewrite Q. exact Blk.
      * cbn. apply (rl_ret _ _ _ _ _ Rl NB). destruct (hdr_not_bad _ Hh); auto.
  - assert (l1 = 0) by (destruct (Z.eq_dec l1 0) as [?|N]; [auto | destruct (F1 N); lia]). subst l1.
    destruct (S1 eq_refl) as (Eb & Eh & Lim). subst b1.
    apply HK; auto; rewrite Q; auto.
Qed.

(* apply sh_field to a goal ... (if m_leave (needbits n m) =? 1 then IBrk .. else B) *)
Ltac sh_apply n :=
  lazymatch goal with |- context [if m_leave (needbits n ?m) =? 1 then IBrk (needbits n ?m) else ?B] =>
    let B' := eval pattern (needbits n m) in B in
    lazymatch B' with ?F _ => eapply (sh_field n) with (K := F) end end.

Lemma sh_time : hcase_next TIME (fun md => md = OS).
Proof.
  intros KIT AW CONT flush src P0 O0 m a [Rl Hb] Aw L0 Md.
  rewrite stepf2_TIME by exact Md. unfold c_TIME2.
  assert (Hh: hdr_mode (m_mode m)) by (rewrite Md; unfold hdr_mode; auto 20).
  destruct (hdr_not_bad _ Hh) as [NB _].
  assert (MdA: a_mode a = TIME) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Md).
  set (h := sbits src (a_q a) 32).
  assert (ST: astep lenfix_list distfix_list src a =
              AGo (a_q a + 32) false (AS (set_i_mode (acrc (a_s a) (hbytes4 h)) OS) (a_q a + 32) (a_O a))).
  { rewrite astep_TIME by exact MdA. reflexivity. }
  cbv zeta. sh_apply 32; [exact (proj1 KIT) | exact Rl | exact Hb | exact L0 | exact Hh
    | rewrite Md; intros [E|[E|[E|[E _]]]]; discriminate | rewrite Md; reflexivity | exact ST | ].
  intros nx1 h1 BB1 Q1 Eh Q Lim.
  cbn [m_s set_m_leave set_m_bits set_m_hold set_m_nx]. rewrite (rl_head _ _ _ _ _ Rl). cbv iota.
  rewrite crc_if_acrc.
  set (M := set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h1) 32) 0) in *.
  assert (HM: m_hold M = h) by (cbn; exact Eh). rewrite HM.
  destruct (proj1 (proj2 (proj2 (proj2 (proj1 KIT)))) src P0 M BB1) as (BBi & Qi).
  eapply hgoal_go; [exact ST | exact Lim | ].
  pose proof (rl_s _ _ _ _ _ Rl NB) as SQ.
  destruct (rl_chk _ _ _ _ _ Rl) as (CK & _).
  destruct (acrc_fields (m_s m) (hbytes4 h)) as (F1m & F2m & F3m & F4m & F5m & F6m & F7m & F8m).
  match goal with |- context [c_OS2 ?X] =>
    rewrite <- (stepf2_OS flush lenfix_list distfix_list X) by reflexivity end.
  eapply hcont; [exact CONT | apply hrel_mk; [intros BO | | hrel_md] | eapply awf_go; eauto | reflexivity | reflexivity | reflexivity | reflexivity].
  + eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                         | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
    * eapply bitbuf_ext; [exact BBi | reflexivity ..].
    * cbn [a_q]. unfold mq in *. cbn in *. lia.
    * cbn. apply seq_mode_hdr; [apply seq_acrc; exact SQ | unfold hdr_mode; auto 20 | discriminate].
    * intros _. cbn. apply acrc_check; [apply CK; exact Hh | apply (se_flags _ _ SQ) | apply (se_wrap _ _ SQ)].
    * intros D. exfalso. revert D. unfold data_mode, decode_mode. vm_compute. lia.
    * left. unfold hdr_mode. cbn. auto 20.
    * cbn. exact F4m.
    * cbn. unfold win_eq in *. cbn. exact F8m.
    * cbn. rewrite F5m. exact (rl_head _ _ _ _ _ Rl).
  + intros _. cbn. split; [reflexivity|]. split; [lia|]. intros _. reflexivity.
Qed.

(* a header pass that ends in BAD after one abstract step *)
Lemma sh_bad flush src P0 O0 I R m a n a1 M :
  rel src P0 O0 m a -> hdr_mode (m_mode m) ->
  astep lenfix_list distfix_list src a = AGo n false a1 -> n <= 8 * I -> a_mode a1 = BAD -> a_O a1 = a_O a ->
  bitbuf src P0 M -> m_inp M = m_inp m -> m_aout M = m_aout m -> m_ow M = m_ow m -> m_in M = m_in m ->
  m_out M = m_out m -> m_tout M = m_tout m -> m_mode M = BAD -> i_head (m_s M) = false -> m_leave M = 0 ->
  hgoal flush src P0 O0 I R a (IBrk M).
Proof.
  intros Rl Hh ST Lim Ma Oa BB Ei Ea Eo Ein Eout Et Md Hd L.
  eapply hgoal_go; [exact ST | exact Lim | ].
  exists a1. split; [apply ar_refl|]. split; [split|].
  - eapply rel_hdr_bad; eauto.
  - intros H. exfalso. rewrite Md in H. exact (proj1 bad_modes H).
  - intros E. rewrite L in E. discriminate.
Qed.

Lemma sh_os : hcase_next OS (fun md => md = EXLEN).
Proof.
  intros KIT AW CONT flush src P0 O0 m a [Rl Hb] Aw L0 Md.
  rewrite stepf2_OS by exact Md. unfold c_OS2.
  assert (Hh: hdr_mode (m_mode m)) by (rewrite Md; unfold hdr_mode; auto 20).
  destruct (hdr_not_bad _ Hh) as [NB _].
  assert (MdA: a_mode a = OS) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Md).
  set (h := sbits src (a_q a) 16).
  assert (ST: astep lenfix_list distfix_list src a =
              AGo (a_q a + 16) false (AS (set_i_mode (acrc (a_s a) (hbytes2 h)) EXLEN) (a_q a + 16) (a_O a))).
  { rewrite astep_OS by exact MdA. reflexivity. }
  cbv zeta. sh_apply 16; [exact (proj1 KIT) | exact Rl | exact Hb | exact L0 | exact Hh
    | rewrite Md; intros [E|[E|[E|[E _]]]]; discriminate | rewrite Md; reflexivity | exact ST | ].
  intros nx1 h1 BB1 Q1 Eh Q Lim.
  cbn [m_s set_m_leave set_m_bits set_m_hold set_m_nx]. rewrite (rl_head _ _ _ _ _ Rl). cbv iota.
  rewrite crc_if_acrc.
  set (M := set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h1) 16) 0) in *.
  assert (HM: m_hold M = h) by (cbn; exact Eh). rewrite HM.
  destruct (proj1 (proj2 (proj2 (proj2 (proj1 KIT)))) src P0 M BB1) as (BBi & Qi).
  eapply hgoal_go; [exact ST | exact Lim | ].
  pose proof (rl_s _ _ _ _ _ Rl NB) as SQ.
  destruct (rl_chk _ _ _ _ _ Rl) as (CK & _).
  destruct (acrc_fields (m_s m) (hbytes2 h)) as (F1m & F2m & F3m & F4m & F5m & F6m & F7m & F8m).
  match goal with |- context [c_EXLEN2 ?X] =>
    rewrite <- (stepf2_EXLEN flush lenfix_list distfix_list X) by reflexivity end.
  eapply hcont; [exact CONT | apply hrel_mk; [intros BO | | hrel_md] | eapply awf_go; eauto | reflexivity | reflexivity | reflexivity | reflexivity].
  + eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                         | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
    * eapply bitbuf_ext; [exact BBi | reflexivity ..].
    * cbn [a_q]. unfold mq in *. cbn in *. lia.
    * cbn. apply seq_mode_hdr; [apply seq_acrc; exact SQ | unfold hdr_mode; auto 20 | discriminate].
    * intros _. cbn. apply acrc_check; [apply CK; exact Hh | apply (se_flags _ _ SQ) | apply (se_wrap _ _ SQ)].
    * intros D. exfalso. revert D. unfold data_mode, decode_mode. vm_compute. lia.
    * left. unfold hdr_mode. cbn. auto 20.
    * cbn. exact F4m.
    * cbn. unfold win_eq in *. cbn. exact F8m.
    * cbn. rewrite F5m. exact (rl_head _ _ _ _ _ Rl).
  + intros _. cbn. split; [reflexivity|]. split; [lia|]. intros _. reflexivity.
Qed.

Lemma sh_flags : hcase_next FLAGS (fun md => md = TIME).
Proof.
  intros KIT AW CONT flush src P0 O0 m a [Rl Hb] Aw L0 Md.
  rewrite stepf2_FLAGS by exact Md. unfold c_FLAGS2.
  assert (Hh: hdr_mode (m_mode m)) by (rewrite Md; unfold hdr_mode; auto 20).
  destruct (hdr_not_bad _ Hh) as [NB _].
  assert (MdA: a_mode a = FLAGS) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Md).
  set (h := sbits src (a_q a) 16).
  assert (STg: astep lenfix_list distfix_list src a =
     if negb (Z.land (s32 h) 255 =? 8) then abad a (a_q a + 16) else
     if negb (Z.land (s32 h) 57344 =? 0) then abad a (a_q a + 16) else
     ago a (a_q a + 16) (set_i_mode (acrc (set_i_flags (a_s a) (s32 h)) (hbytes2 h)) TIME)).
  { rewrite astep_FLAGS by exact MdA. reflexivity. }
  pose proof (rl_s _ _ _ _ _ Rl NB) as SQ.
  destruct (rl_chk _ _ _ _ _ Rl) as (CK & _).
  cbv zeta.
  destruct (negb (Z.land (s32 h) 255 =? 8)) eqn:C1;
    [|destruct (negb (Z.land (s32 h) 57344 =? 0)) eqn:C2]; unfold abad, ago in STg;
    (sh_apply 16; [exact (proj1 KIT) | exact Rl | exact Hb | exact L0 | exact Hh
      | rewrite Md; intros [E|[E|[E|[E _]]]]; discriminate | rewrite Md; reflexivity | exact STg | ]);
    intros nx1 h1 BB1 Q1 Eh Q Lim;
    cbn [m_hold m_s set_m_leave set_m_bits set_m_hold set_m_nx upd_s set_m_s i_flags set_i_flags];
    subst h1; fold h in BB1, Q1; fold h; rewrite ?C1, ?C2; cbv iota.
  - eapply sh_bad; [exact Rl | exact Hh | exact STg | exact Lim | reflexivity | reflexivity
                   | eapply bitbuf_ext; [exact BB1 | reflexivity ..] | reflexivity | reflexivity | reflexivity
                   | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity ].
    cbn. exact (rl_head _ _ _ _ _ Rl).
  - eapply sh_bad; [exact Rl | exact Hh | exact STg | exact Lim | reflexivity | reflexivity
                   | eapply bitbuf_ext; [exact BB1 | reflexivity ..] | reflexivity | reflexivity | reflexivity
                   | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity ].
    cbn. exact (rl_head _ _ _ _ _ Rl).
  - replace (i_head (set_i_flags (m_s m) (s32 h))) with false
      by (cbn; symmetry; exact (rl_head _ _ _ _ _ Rl)). cbv iota.
    rewrite crc_if_acrc.
    set (M := set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h) 16) 0) in *.
    destruct (proj1 (proj2 (proj2 (proj2 (proj1 KIT)))) src P0 M BB1) as (BBi & Qi).
    eapply hgoal_go; [exact STg | exact Lim | ].
    destruct (acrc_fields (set_i_flags (m_s m) (s32 h)) (hbytes2 h)) as (F1m & F2m & F3m & F4m & F5m & F6m & F7m & F8m).
    cbn [i_total i_head i_flags set_i_flags] in F4m, F5m, F8m. unfold win_eq in F8m. cbn in F8m.
    match goal with |- context [c_TIME2 ?X] =>
      rewrite <- (stepf2_TIME flush lenfix_list distfix_list X) by reflexivity end.
    eapply hcont; [exact CONT | apply hrel_mk; [intros BO | | hrel_md] | eapply awf_go; eauto | reflexivity | reflexivity | reflexivity | reflexivity].
    + eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                           | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
      * eapply bitbuf_ext; [exact BBi | reflexivity ..].
      * cbn [a_q]. unfold mq in *. cbn in *. lia.
      * cbn. apply seq_mode_hdr; [apply seq_acrc, seq_flags; exact SQ | unfold hdr_mode; auto 20 | discriminate].
      * intros _. cbn. apply acrc_check; cbn; [apply CK; exact Hh | reflexivity | apply (se_wrap _ _ SQ)].
      * intros D. exfalso. revert D. unfold data_mode, decode_mode. vm_compute. lia.
      * left. unfold hdr_mode. cbn. auto 20.
      * cbn. exact F4m.
      * unfold win_eq. cbn. exact F8m.
      * cbn. rewrite F5m. exact (rl_head _ _ _ _ _ Rl).
    + intros _. cbn. split; [reflexivity|]. split; [lia|]. intros _. reflexivity.
Qed.

(* EXLEN without an extra field: EXTRA is passed through with the length 0, into NAME *)
Lemma seq_mode_len_mode s t X v Y : seq s t -> hdr_mode Y -> Y <> EXTRA ->
  seq (set_i_mode (set_i_length (set_i_mode s X) v) Y) (set_i_mode (set_i_length (set_i_mode t X) v) Y).
Proof. intros H Hy Ne. destruct H; constructor; cbn; auto; intros; exfalso; hmd. Qed.

Lemma sh_exlen : hcase_next EXLEN (fun md => md = EXTRA \/ md = NAME).
Proof.
  intros KIT AW CONT flush src P0 O0 m a [Rl Hb] Aw L0 Md.
  rewrite stepf2_EXLEN by exact Md. unfold c_EXLEN2.
  assert (Hh: hdr_mode (m_mode m)) by (rewrite Md; unfold hdr_mode; auto 20).
  destruct (hdr_not_bad _ Hh) as [NB _].
  assert (MdA: a_mode a = EXLEN) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Md).
  pose proof (rl_s _ _ _ _ _ Rl NB) as SQ.
  destruct (rl_chk _ _ _ _ _ Rl) as (CK & _).
  pose proof (rl_bb _ _ _ _ _ Rl) as BB.
  pose proof (rl_q _ _ _ _ _ Rl NB) as Q.
  assert (FE: i_flags (m_s m) = i_flags (a_s a)) by apply (se_flags _ _ SQ).
  cbv zeta.
  destruct (Z.eqb_spec (Z.land (i_flags (m_s m)) 1024) 0) as [Fl|Fl]; cbn [negb].
  - (* no extra field: through EXTRA into NAME, without input *)
    rewrite (rl_head _ _ _ _ _ Rl). cbv iota.
    unfold c_EXTRA2. cbn [m_s set_mode upd_s set_m_s i_flags set_i_mode]. rewrite Fl.
    change (negb (0 =? 0)) with false. cbv iota zeta.
    destruct (Hb Hh) as (_ & _ & B0). specialize (B0 (or_intror (or_intror (or_intror (conj Md Fl))))).
    assert (Lq: a_q a <= 8 * (P0 + Zlength (m_inp m))).
    { rewrite Q. unfold mq. pose proof (bb_nx _ _ _ BB). pose proof (bb_bits _ _ _ BB). lia. }
    set (a1 := AS (set_i_mode (a_s a) EXTRA) (a_q a) (a_O a)).
    assert (ST1: astep lenfix_list distfix_list src a = AGo (a_q a) false a1).
    { rewrite astep_EXLEN by exact MdA. unfold a_EXLEN. rewrite <- FE, Fl. reflexivity. }
    set (a2 := AS (set_i_mode (set_i_length (set_i_mode (a_s a) EXTRA) 0) NAME) (a_q a) (a_O a)).
    assert (ST2: astep lenfix_list distfix_list src a1 = AGo (a_q a1) false a2).
    { rewrite astep_EXTRA by reflexivity. unfold a_EXTRA. cbn. rewrite <- FE, Fl. reflexivity. }
    eapply hgoal_go; [exact ST1 | exact Lq | ].
    eapply hgoal_go; [exact ST2 | exact Lq | ].
    match goal with |- context [c_NAME2 ?X] =>
      rewrite <- (stepf2_NAME flush lenfix_list distfix_list X) by reflexivity end.
    eapply hcont; [exact CONT | apply hrel_mk; [intros BO | | hrel_md] | eapply (awf_go src a1); [exact AW | eapply (awf_go src a); eauto | exact ST2] | exact L0 | right; reflexivity
                  | reflexivity | reflexivity].
    + eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                           | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
      * eapply bitbuf_ext; [exact BB | reflexivity ..].
      * exact Q.
      * cbn. apply seq_mode_len_mode; [exact SQ | unfold hdr_mode; auto 20 | discriminate].
      * intros _. cbn. apply CK; exact Hh.
      * intros D. exfalso. revert D. unfold data_mode, decode_mode. vm_compute. lia.
      * left. unfold hdr_mode. cbn. auto 20.
      * reflexivity.
      * unfold win_eq. cbn. repeat split; reflexivity.
      * exact (rl_head _ _ _ _ _ Rl).
    + intros _. cbn. unfold m_mode in *. split; [rewrite B0; reflexivity|]. split; [lia|]. intros _. exact B0.
  - (* the extra field's length *)
    set (h := sbits src (a_q a) 16).
    assert (ST: astep lenfix_list distfix_list src a =
                AGo (a_q a + 16) false
                  (AS (set_i_mode (acrc (set_i_length (a_s a) (u32 h)) (hbytes2 h)) EXTRA) (a_q a + 16) (a_O a))).
    { rewrite astep_EXLEN by exact MdA. unfold a_EXLEN. rewrite <- FE.
      destruct (Z.eqb_spec (Z.land (i_flags (m_s m)) 1024) 0) as [E|E]; [contradiction|]. reflexivity. }
    sh_apply 16; [exact (proj1 KIT) | exact Rl | exact Hb | exact L0 | exact Hh
      | rewrite Md; intros [E|[E|[E|[_ E]]]]; [discriminate .. | exact (Fl E)] | rewrite Md; reflexivity
      | exact ST | ].
    intros nx1 h1 BB1 Q1 Eh Q' Lim.
    cbn [m_hold m_s set_m_leave set_m_bits set_m_hold set_m_nx upd_s set_m_s i_head set_i_length].
    subst h1. fold h in BB1, Q1. fold h.
    rewrite (rl_head _ _ _ _ _ Rl). cbv iota.
    rewrite crc_if_acrc.
    set (M := set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h) 16) 0) in *.
    destruct (proj1 (proj2 (proj2 (proj2 (proj1 KIT)))) src P0 M BB1) as (BBi & Qi).
    eapply hgoal_go; [exact ST | exact Lim | ].
    destruct (acrc_fields (set_i_length (m_s m) (u32 h)) (hbytes2 h)) as (F1m & F2m & F3m & F4m & F5m & F6m & F7m & F8m).
    destruct (acrc_fields (set_i_length (a_s a) (u32 h)) (hbytes2 h)) as (F1a & F2a & F3a & F4a & F5a & F6a & F7a & F8a).
    cbn [i_total i_head i_flags i_length set_i_length] in F4m, F5m, F6m, F6a. unfold win_eq in F8m. cbn in F8m.
    match goal with |- context [c_EXTRA2 ?X] =>
      rewrite <- (stepf2_EXTRA flush lenfix_list distfix_list X) by reflexivity end.
    eapply hcont; [exact CONT | apply hrel_mk; [intros BO | | hrel_md] | eapply awf_go; eauto | reflexivity | left; reflexivity
                  | reflexivity | reflexivity].
    + eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                           | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
      * eapply bitbuf_ext; [exact BBi | reflexivity ..].
      * cbn [a_q]. unfold mq in *. cbn in *. lia.
      * cbn. apply seq_mode; [apply seq_acrc, seq_length; exact SQ | | |].
        -- intros _. cbn. rewrite F6m, F6a. reflexivity.
        -- intros D. exfalso. revert D. unfold off_live. vm_compute. lia.
        -- intros D. exfalso. revert D. unfold ext_live. vm_compute. lia.
      * intros _. cbn. apply acrc_check; cbn; [apply CK; exact Hh | exact FE | apply (se_wrap _ _ SQ)].
      * intros D. exfalso. revert D. unfold data_mode, decode_mode. vm_compute. lia.
      * left. unfold hdr_mode. cbn. auto 20.
      * cbn. exact F4m.
      * unfold win_eq. cbn. exact F8m.
      * cbn. rewrite F5m. exact (rl_head _ _ _ _ _ Rl).
    + intros _. cbn. split; [reflexivity|]. split; [lia|]. intros _. reflexivity.
Qed.
