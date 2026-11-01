(* The header simulation, the end of the header: HCRC (the gzip header's CRC, then the data phase),
   DICTID (the zlib dictionary id) and DICT (no dictionary was given: inflate() returns Z_NEED_DICT). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdrKit.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdrFix.
Import ListNotations.
Local Open Scope Z_scope.

(* a pass that ends (without leaving) after one abstract step *)
Lemma hgoal_final flush src P0 O0 I R a n a1 M :
  astep lenfix_list distfix_list src a = AGo n false a1 -> n <= 8 * I ->
  hrel src P0 O0 M a1 -> m_leave M = 0 -> hgoal flush src P0 O0 I R a (IBrk M).
Proof.
  intros ST Lim Rl L. eapply hgoal_go; [exact ST | exact Lim | ].
  exists a1. split; [apply ar_refl|]. split; [exact Rl|]. intros E. rewrite L in E. discriminate.
Qed.

(* a mode that reads none of length, offset, extra *)
Lemma seq_mode_nolive s t v : seq s t -> ~ len_live v -> ~ off_live v -> ~ ext_live v ->
  seq (set_i_mode s v) (set_i_mode t v).
Proof. intros H L O E. apply seq_mode; auto; intros X; exfalso; auto. Qed.

Lemma nolive_TYPE : ~ len_live Zlib.proof.inflate.Model.TYPE /\ ~ off_live Zlib.proof.inflate.Model.TYPE /\
                    ~ ext_live Zlib.proof.inflate.Model.TYPE.
Proof. unfold len_live, off_live, ext_live. vm_compute. lia. Qed.

Lemma nolive_DICT : ~ len_live DICT /\ ~ off_live DICT /\ ~ ext_live DICT.
Proof. unfold len_live, off_live, ext_live. vm_compute. lia. Qed.

Lemma type_data : data_mode Zlib.proof.inflate.Model.TYPE /\ ~ hdr_mode Zlib.proof.inflate.Model.TYPE.
Proof. unfold data_mode, hdr_mode. vm_compute. lia. Qed.

(* nothing is written in the header *)
Lemma hdr_O0 src P0 O0 m a : rel src P0 O0 m a -> awf src a -> hdr_mode (m_mode m) -> O0 = [].
Proof.
  intros Rl Aw Hh. pose proof (aw_hdrO _ _ Aw) as H.
  rewrite <- (rl_mode _ _ _ _ _ Rl) in H. specialize (H Hh).
  rewrite (rl_O _ _ _ _ _ Rl) in H. destruct O0; [reflexivity|discriminate].
Qed.

(* the bit position is within the input *)
Lemma q_in src P0 O0 m a : rel src P0 O0 m a -> m_mode m <> BAD -> a_q a <= 8 * (P0 + Zlength (m_inp m)).
Proof.
  intros Rl NB. rewrite (rl_q _ _ _ _ _ Rl NB). pose proof (rl_bb _ _ _ _ _ Rl) as BB.
  unfold mq. pose proof (bb_nx _ _ _ BB). pose proof (bb_bits _ _ _ BB). lia.
Qed.

(* the end of the gzip header: the check of the data phase is crc32's initial 0 *)
Lemma sh_hcrc_fin src P0 O0 m a M q :
  rel src P0 O0 m a -> hdr_mode (m_mode m) -> O0 = [] ->
  bitbuf src P0 M -> m_inp M = m_inp m -> m_aout M = m_aout m -> m_ow M = m_ow m -> m_in M = m_in m ->
  m_out M = m_out m -> m_ret M = m_ret m -> m_tout M = m_tout m -> m_s M = m_s m -> q = mq P0 M ->
  hrel src P0 O0 (set_mode (set_m_adler (upd_s M (fun s => set_i_check s 0)) 0) Zlib.proof.inflate.Model.TYPE)
       (AS (set_i_mode (set_i_check (a_s a) 0) Zlib.proof.inflate.Model.TYPE) q (a_O a)).
Proof.
  intros Rl Hh O0n BB Ei Ea Eo Ein Eout Er Et Es Eq.
  destruct (hdr_not_bad _ Hh) as [NB _].
  pose proof (rl_s _ _ _ _ _ Rl NB) as SQ.
  destruct nolive_TYPE as (N1 & N2 & N3). destruct type_data as (D1 & D2).
  apply hrel_mk; [intros BO | | hrel_md].
  - eapply rel_hdr_next; [exact Rl | exact Hh | | cbn; assumption | cbn; assumption | cbn; assumption
                         | cbn; assumption | cbn; assumption | cbn; assumption | cbn; assumption
                         | | | | | | | | | | | exact BO].
    + eapply bitbuf_ext; [exact BB | reflexivity ..].
    + reflexivity.
    + cbn. rewrite Eq. reflexivity.
    + reflexivity.
    + cbn. rewrite Es. apply seq_mode_nolive; auto. apply seq_check. exact SQ.
    + intros H. exfalso. exact (D2 H).
    + intros _ _. cbn. rewrite O0n. symmetry. apply update_check_nil01. auto.
    + right. exact D1.
    + cbn. rewrite Es. reflexivity.
    + unfold win_eq. cbn. rewrite Es. repeat split; reflexivity.
    + cbn. rewrite Es. exact (rl_head _ _ _ _ _ Rl).
  - intros H. exfalso. exact (D2 H).
Qed.

Lemma sh_hcrc : kit_stmt -> awf_stmt -> hcase_ok (fun md => md = HCRC).
Proof.
  intros KIT AW flush src P0 O0 m a [Rl Hb] Aw L0 Md.
  rewrite stepf2_HCRC by exact Md. unfold c_HCRC.
  assert (Hh: hdr_mode (m_mode m)) by (rewrite Md; unfold hdr_mode; auto 20).
  destruct (hdr_not_bad _ Hh) as [NB _].
  assert (MdA: a_mode a = HCRC) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Md).
  pose proof (rl_s _ _ _ _ _ Rl NB) as SQ.
  destruct (rl_chk _ _ _ _ _ Rl) as (CK & _).
  pose proof (rl_bb _ _ _ _ _ Rl) as BB.
  pose proof (rl_q _ _ _ _ _ Rl NB) as Q.
  pose proof (hdr_O0 _ _ _ _ _ Rl Aw Hh) as O0n.
  assert (FE: i_flags (m_s m) = i_flags (a_s a)) by apply (se_flags _ _ SQ).
  assert (WE: i_wrap (m_s m) = i_wrap (a_s a)) by apply (se_wrap _ _ SQ).
  assert (CE: i_check (m_s m) = i_check (a_s a)) by (apply CK; exact Hh).
  cbv zeta.
  destruct (Z.eqb_spec (Z.land (i_flags (m_s m)) 512) 0) as [Fl|Fl].
  - (* no header CRC *)
    cbn [negb]. cbv iota.
    rewrite (rl_head _ _ _ _ _ Rl). cbv iota.
    assert (ST: astep lenfix_list distfix_list src a =
                AGo (a_q a) false (AS (set_i_mode (set_i_check (a_s a) 0) Zlib.proof.inflate.Model.TYPE)
                                      (a_q a) (a_O a))).
    { rewrite astep_HCRC by exact MdA. unfold a_HCRC. rewrite <- FE, Fl. reflexivity. }
    eapply hgoal_final; [exact ST | exact (q_in _ _ _ _ _ Rl NB) | | exact L0].
    eapply sh_hcrc_fin; eauto.
  - set (h := sbits src (a_q a) 16).
    assert (STg: astep lenfix_list distfix_list src a =
       if (negb (Z.land (i_wrap (a_s a)) 4 =? 0) && negb (h =? Z.land (i_check (a_s a)) 65535))%bool
       then abad a (a_q a + 16)
       else ago a (a_q a + 16) (set_i_mode (set_i_check (a_s a) 0) Zlib.proof.inflate.Model.TYPE)).
    { rewrite astep_HCRC by exact MdA. unfold a_HCRC. rewrite <- FE.
      destruct (Z.eqb_spec (Z.land (i_flags (m_s m)) 512) 0) as [E|E]; [contradiction|]. reflexivity. }
    cbn [negb]. cbv iota.
    destruct (negb (Z.land (i_wrap (a_s a)) 4 =? 0) && negb (h =? Z.land (i_check (a_s a)) 65535))%bool eqn:C;
      unfold abad, ago in STg;
      (sh_apply 16; [exact (proj1 KIT) | exact Rl | exact Hb | exact L0 | exact Hh
        | rewrite Md; intros [E|[E|[E|[E _]]]]; discriminate | rewrite Md; reflexivity | exact STg | ]);
      intros nx1 h1 BB1 Q1 Eh Q' Lim;
      cbn [m_hold m_s set_m_leave set_m_bits set_m_hold set_m_nx];
      subst h1; fold h in BB1, Q1; fold h; rewrite WE, CE, C; cbv iota.
    + eapply sh_bad; [exact Rl | exact Hh | exact STg | exact Lim | reflexivity | reflexivity
                     | eapply bitbuf_ext; [exact BB1 | reflexivity ..] | reflexivity | reflexivity | reflexivity
                     | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity ].
      cbn. exact (rl_head _ _ _ _ _ Rl).
    + set (M := set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h) 16) 0) in *.
      replace (i_head (m_s (initbits M))) with false by (symmetry; exact (rl_head _ _ _ _ _ Rl)). cbv iota.
      destruct (proj1 (proj2 (proj2 (proj2 (proj1 KIT)))) src P0 M BB1) as (BBi & Qi).
      eapply hgoal_final; [exact STg | exact Lim | | reflexivity].
      eapply sh_hcrc_fin; eauto; try reflexivity.
      rewrite Qi, Q1, <- Q. reflexivity.
Qed.

(* DICT without a dictionary: inflate() returns Z_NEED_DICT, the state stays at DICT *)
Lemma sh_dict_ret flush src P0 O0 I R m a :
  hrel src P0 O0 m a -> awf src a -> m_mode m = DICT ->
  hgoal flush src P0 O0 I R a (c_DICT flush m).
Proof.
  intros [Rl Hb] Aw Md.
  assert (Hh: hdr_mode (m_mode m)) by (rewrite Md; unfold hdr_mode; auto 20).
  destruct (hdr_not_bad _ Hh) as [NB _].
  assert (MdA: a_mode a = DICT) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Md).
  pose proof (rl_s _ _ _ _ _ Rl NB) as SQ.
  destruct (rl_chk _ _ _ _ _ Rl) as (CK & _).
  assert (HD: i_havedict (m_s m) = 0) by (rewrite (se_havedict _ _ SQ); exact (aw_dict _ _ Aw)).
  unfold c_DICT. rewrite HD. cbv iota.
  split; [reflexivity|]. exists a. split; [apply ar_refl|]. split; [apply hrel_mk; [intros BO | | ]|].
  - eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                         | reflexivity | reflexivity | reflexivity | transitivity (m_mode m); [reflexivity | rewrite Md, MdA; reflexivity]
                         | | reflexivity | | | | | | | | exact BO].
    + eapply bitbuf_ext; [exact (rl_bb _ _ _ _ _ Rl) | reflexivity ..].
    + cbn. rewrite (rl_q _ _ _ _ _ Rl NB). reflexivity.
    + destruct SQ; constructor; cbn; auto.
    + intros _. cbn. exact (CK Hh).
    + intros D. exfalso. revert D. unfold data_mode, decode_mode. cbn. change (i_mode (m_s m)) with (m_mode m). rewrite Md. vm_compute. lia.
    + left. exact Hh.
    + reflexivity.
    + unfold win_eq. cbn. repeat split; reflexivity.
    + cbn. exact (rl_head _ _ _ _ _ Rl).
  - intros H. cbn. unfold m_mode in *. cbn. apply Hb. exact H.
  - apply hdr_not_copy. exact Hh.
  - rewrite astep_DICT by exact MdA. unfold a_DICT. rewrite (aw_dict _ _ Aw). reflexivity.
Qed.

Lemma sh_dict : kit_stmt -> awf_stmt -> hcase_ok (fun md => md = DICT).
Proof.
  intros KIT AW flush src P0 O0 m a Rl Aw L0 Md.
  rewrite stepf2_DICT by exact Md. apply sh_dict_ret; auto.
Qed.

Lemma sh_dictid : kit_stmt -> awf_stmt -> hcase_ok (fun md => md = DICTID).
Proof.
  intros KIT AW flush src P0 O0 m a [Rl Hb] Aw L0 Md.
  rewrite stepf2_DICTID by exact Md. unfold c_DICTID.
  assert (Hh: hdr_mode (m_mode m)) by (rewrite Md; unfold hdr_mode; auto 20).
  destruct (hdr_not_bad _ Hh) as [NB _].
  assert (MdA: a_mode a = DICTID) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Md).
  pose proof (rl_s _ _ _ _ _ Rl NB) as SQ.
  set (h := sbits src (a_q a) 32).
  assert (ST: astep lenfix_list distfix_list src a =
              AGo (a_q a + 32) false (AS (set_i_mode (set_i_check (a_s a) (swap32 h)) DICT) (a_q a + 32) (a_O a))).
  { rewrite astep_DICTID by exact MdA. reflexivity. }
  cbv zeta.
  sh_apply 32; [exact (proj1 KIT) | exact Rl | exact Hb | exact L0 | exact Hh
    | rewrite Md; intros [E|[E|[E|[E _]]]]; discriminate | rewrite Md; reflexivity | exact ST | ].
  intros nx1 h1 BB1 Q1 Eh Q Lim.
  cbn [m_hold set_m_leave set_m_bits set_m_hold set_m_nx]. subst h1. fold h in BB1, Q1. fold h.
  set (M := set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h) 32) 0) in *.
  destruct (proj1 (proj2 (proj2 (proj2 (proj1 KIT)))) src P0 M BB1) as (BBi & Qi).
  eapply hgoal_go; [exact ST | exact Lim | ].
  destruct nolive_DICT as (N1 & N2 & N3).
  apply sh_dict_ret; [apply hrel_mk; [intros BO | | hrel_md] | eapply awf_go; eauto | reflexivity].
  - eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                         | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
    + eapply bitbuf_ext; [exact BBi | reflexivity ..].
    + cbn [a_q]. unfold mq in *. cbn in *. lia.
    + cbn. apply seq_mode_nolive; auto. apply seq_check. exact SQ.
    + intros _. reflexivity.
    + intros D. exfalso. revert D. unfold data_mode, decode_mode. vm_compute. lia.
    + left. unfold hdr_mode. cbn. auto 20.
    + reflexivity.
    + unfold win_eq. cbn. repeat split; reflexivity.
    + cbn. exact (rl_head _ _ _ _ _ Rl).
  - intros _. cbn. split; [reflexivity|]. split; [lia|]. intros [E|[E|[E|[E _]]]]; discriminate.
Qed.
