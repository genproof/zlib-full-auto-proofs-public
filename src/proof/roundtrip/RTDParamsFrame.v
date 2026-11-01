(* RT-D part PARAMS: params_tail keeps the functional invariant (KF, KF2).
   [pframe s s']: every field the invariant reads except the level, the strategy, matches, head and prev. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV2.
Require Import Zlib.proof.roundtrip.RTDLTCMisc.
Import ListNotations.
Local Open Scope Z_scope.

Definition pframe (s s' : dstate) : Prop :=
  d_status s' = d_status s /\ d_po s' = d_po s /\ d_wrap s' = d_wrap s /\ d_gzhead s' = d_gzhead s /\
  d_w_size s' = d_w_size s /\ d_w_bits s' = d_w_bits s /\ d_w_mask s' = d_w_mask s /\ d_window s' = d_window s /\
  d_ins_h s' = d_ins_h s /\ d_hash_size s' = d_hash_size s /\ d_hash_mask s' = d_hash_mask s /\
  d_hash_shift s' = d_hash_shift s /\ d_block_start s' = d_block_start s /\
  d_match_length s' = d_match_length s /\ d_match_available s' = d_match_available s /\
  d_strstart s' = d_strstart s /\ d_match_start s' = d_match_start s /\ d_lookahead s' = d_lookahead s /\
  d_insert s' = d_insert s /\ d_pbm s' = d_pbm s /\
  tr_ltree (d_tr s') = tr_ltree (d_tr s) /\ tr_dtree (d_tr s') = tr_dtree (d_tr s) /\
  tr_bltree (d_tr s') = tr_bltree (d_tr s) /\ tr_wk (d_tr s') = tr_wk (d_tr s) /\
  tr_out (d_tr s') = tr_out (d_tr s) /\ tr_sym_next (d_tr s') = tr_sym_next (d_tr s) /\
  tr_lit_bufsize (d_tr s') = tr_lit_bufsize (d_tr s).

Ltac pf_destruct P :=
  destruct P as (Pst & Ppo & Pwr & Pgz & Pws & Pwb & Pwm & Pwin & Pih & Phs & Phm & Phsh & Pbs & Pml & Pma & Pss &
                 Pms & Pla & Pins & Ppbm & Plt & Pdt & Pblt & Pwk & Pout & Psn & Plb).

Ltac pf_rw :=
  repeat match goal with
  | E : ?f ?s' = ?f ?s |- context [?f ?s'] => rewrite E
  | E : ?f (d_tr ?s') = ?f (d_tr ?s) |- context [?f (d_tr ?s')] => rewrite E
  end.

Lemma pframe_trans : forall s1 s2 s3, pframe s1 s2 -> pframe s2 s3 -> pframe s1 s3.
Proof.
  intros s1 s2 s3 P Q. unfold pframe in *. decompose [and] P. decompose [and] Q.
  repeat split; congruence.
Qed.

Lemma pframe_slide : forall s s', pframe s s' -> pframe (slide_hc s) s'.
Proof. intros s s' P. exact P. Qed.

(** ** The level classes of config_table *)
Lemma cfg_f_class : forall l, 0 <= l <= 9 ->
  (cfg_f l = 0 <-> l = 0) /\ (cfg_f l = 2 <-> 4 <= l) /\ (cfg_f l = 0 \/ cfg_f l = 1 \/ cfg_f l = 2).
Proof.
  intros l Hl.
  assert (l = 0 \/ l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7 \/ l = 8 \/ l = 9) as H by lia.
  repeat destruct H as [H|H]; subst; unfold cfg_f; simpl; lia.
Qed.

(** ** Pieces of the invariant *)
Lemma kwin_frame : forall H s s', pframe s s' -> kwin H s -> kwin H s'.
Proof. intros H s s' P K. pf_destruct P. unfold kwin in *. pf_rw. exact K. Qed.

Lemma kmatch_frame : forall s s', pframe s s' -> kmatch s -> kmatch s'.
Proof. intros s s' P K. pf_destruct P. unfold kmatch in *. pf_rw. exact K. Qed.

Lemma tree_ok_frame : forall s s' syms, pframe s s' -> tree_ok (d_tr s) (d_pbm s) syms ->
  tree_ok (d_tr s') (d_pbm s') syms.
Proof. intros s s' syms P K. pf_destruct P. unfold tree_ok in *. pf_rw. exact K. Qed.

Lemma wtrees_frame : forall s s' syms, pframe s s' -> wtrees s syms ->
  Forall (sym_ok s') syms -> (d_level s' = 0 -> syms = []) ->
  (d_level s' <> 0 -> blk_len syms = d_strstart s - d_block_start s - d_match_available s) ->
  wtrees s' syms.
Proof.
  intros s s' syms P (T1 & T2 & _ & _ & _) F L0 L1.
  pose proof (tree_ok_frame s s' syms P T1) as T1'. pf_destruct P.
  unfold wtrees, d_L in *. pf_rw. rewrite Ppbm in T1'. auto 10.
Qed.

Lemma chain_hok_frame : forall s s', pframe s s' -> d_head s' = d_head s -> d_prev s' = d_prev s ->
  chain_hok s -> chain_hok s'.
Proof.
  intros s s' P Eh Ep K. pf_destruct P. unfold chain_hok, h3, update_hash, lim, MAX_DIST in *. pf_rw. exact K.
Qed.

Lemma primed_frame : forall s s' p, pframe s s' -> primed s p -> primed s' p.
Proof. intros s s' p P K. pf_destruct P. unfold primed, update_hash in *. pf_rw. exact K. Qed.

Lemma chain_hok_clear : forall s, (forall b, 0 <= b < d_hash_size s -> Znth b (d_head s) = 0) -> chain_hok s.
Proof.
  intros s H b Hb. exists (fun q => q = 0). split; [apply H; exact Hb|].
  intros q Hq Hq0. lia.
Qed.

(** ** What params_tail changes *)
Lemma params_tail_shape : forall s lv st s2,
  params_tail s lv st = Some s2 ->
  pframe s s2 /\ d_level s2 = lv /\ d_strategy s2 = st /\
  ((d_matches s2 = d_matches s /\ d_head s2 = d_head s /\ d_prev s2 = d_prev s /\
    (d_level s = lv \/ d_level s <> 0 \/ d_matches s = 0)) \/
   (d_level s = 0 /\ lv <> 0 /\ d_matches s = 1 /\ d_matches s2 = 0 /\
    d_head s2 = d_head (slide_hc s) /\ d_prev s2 = d_prev (slide_hc s)) \/
   (d_level s = 0 /\ lv <> 0 /\ d_matches s <> 0 /\ d_matches s <> 1 /\ d_matches s2 = 0 /\
    d_head s2 = repeat 0 (Z.to_nat (d_hash_size s)))).
Proof.
  intros s lv st s2 E. unfold params_tail in E.
  destruct (negb (d_level s =? lv)) eqn:El.
  - apply negb_true_iff, Z.eqb_neq in El.
    destruct ((d_level s =? 0) && negb (d_matches s =? 0)) eqn:Em.
    + apply andb_true_iff in Em. destruct Em as [Em1 Em2].
      apply Z.eqb_eq in Em1. apply negb_true_iff, Z.eqb_neq in Em2.
      destruct (d_matches s =? 1) eqn:E1.
      * apply Z.eqb_eq in E1. unfold c_slide_hash in E.
        destruct (guard _); cbn [bind] in E; [|discriminate].
        destruct (Znth lv config_table) as [[[[? ?] ?] ?] ?]. cbn [bind] in E.
        injection E as <-. split; [repeat split; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        right; left. repeat split; auto; congruence.
      * apply Z.eqb_neq in E1. unfold c_clear_hash in E.
        destruct (wr _ _ _); cbn [bind] in E; [|discriminate].
        destruct (guard _); cbn [bind] in E; [|discriminate].
        destruct (Znth lv config_table) as [[[[? ?] ?] ?] ?]. cbn [bind] in E.
        injection E as <-. split; [repeat split; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        right; right. repeat split; auto; congruence.
    + cbn [bind] in E. destruct (Znth lv config_table) as [[[[? ?] ?] ?] ?]. cbn [bind] in E.
      injection E as <-. split; [repeat split; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      apply andb_false_iff in Em. destruct Em as [Em|Em].
      * right; left. apply Z.eqb_neq in Em. exact Em.
      * right; right. apply negb_false_iff, Z.eqb_eq in Em. exact Em.
  - apply negb_false_iff, Z.eqb_eq in El. cbn [bind] in E. injection E as <-.
    split; [repeat split; reflexivity|]. split; [exact El|]. split; [reflexivity|].
    left. repeat split; auto.
Qed.

Lemma khdr_frame : forall dict wrap s s' HDR, pframe s s' -> khdr dict wrap s HDR -> khdr dict wrap s' HDR.
Proof. intros dict wrap s s' HDR P K. pf_destruct P. unfold khdr in *. pf_rw. exact K. Qed.

Lemma allbits_frame : forall O s s', pframe s s' -> allbits O s' = allbits O s.
Proof. intros O s s' P. pf_destruct P. unfold allbits, pend, bibits, d_pending, d_bi_valid. pf_rw. reflexivity. Qed.

Lemma bi_valid_frame : forall s s', pframe s s' -> d_bi_valid s' = d_bi_valid s.
Proof. intros s s' P. pf_destruct P. unfold d_bi_valid. pf_rw. reflexivity. Qed.

Lemma prm_level : forall s, W s -> 0 <= d_level s <= 9.
Proof.
  intros s HW. pose proof (W_prm s HW) as Hp.
  destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _). exact L.
Qed.

(** the case of params_tail: same function and strategy, or everything read is in blocks *)
Definition pcase (s : dstate) (lv st : Z) : Prop :=
  (cfg_f lv = cfg_f (d_level s) /\ st = d_strategy s) \/ (d_lookahead s = 0 /\ d_strstart s = d_block_start s).

Lemma kdata2_params : forall dict D BS syms s lv st s2,
  W s -> kdata2 dict D BS syms s -> 0 <= lv <= 9 -> pcase s lv st ->
  params_tail s lv st = Some s2 -> kdata2 dict D BS syms s2.
Proof.
  intros dict D BS syms s lv st s2 HW Kd Hlv Hc E.
  destruct (params_tail_shape s lv st s2 E) as (P & Hl2 & Hs2 & _).
  pose proof (prm_level s HW) as Hls.
  unfold kdata2 in *. destruct Kd as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  pose proof (kwin_frame _ _ _ P K1) as K1'. pose proof (kmatch_frame _ _ P K2) as K2'.
  destruct Hc as [(Hf & Hst) | (Hla & Hss)].
  - destruct (cfg_f_class lv Hlv) as (A1 & A2 & _). destruct (cfg_f_class (d_level s) Hls) as (B1 & B2 & _).
    assert (C0 : d_level s2 = 0 <-> d_level s = 0) by (rewrite Hl2, <- A1, Hf, B1; tauto).
    assert (C4 : 4 <= d_level s2 <-> 4 <= d_level s) by (rewrite Hl2, <- A2, Hf, B2; tauto).
    assert (K3' : wtrees s2 syms).
    { apply (wtrees_frame s s2 syms P K3).
      - destruct K3 as (_ & _ & F & _). eapply Forall_impl; [|exact F].
        intros x (V1 & V2 & V3). pose proof P as P'. pf_destruct P'. unfold sym_ok, MAX_DIST in *.
        rewrite Pws, Hs2, Hst. split; [exact V1|]. split; [exact V2|].
        intros H4. apply V3. apply C4. exact H4.
      - intros L0. apply K3. apply C0. exact L0.
      - intros L0. apply K3. intros L1. apply L0. apply C0. exact L1. }
    pf_destruct P. pf_rw. cbv zeta in *.
    split; [exact K1'|]. split; [exact K2'|]. split; [exact K3'|].
    split; [exact K4|]. split; [exact K5|]. split; [exact K6|].
    replace (d_level s2 =? 0) with (d_level s =? 0); [exact K7|].
    destruct (Z.eqb_spec (d_level s) 0), (Z.eqb_spec (d_level s2) 0); tauto.
  - destruct (W_empty s syms HW K3 Hla Hss) as [Hma ->].
    assert (K3' : wtrees s2 []).
    { apply (wtrees_frame s s2 [] P K3); [constructor|reflexivity|]. intros _. rewrite Hma, Hss. unfold blk_len. cbn. lia. }
    pf_destruct P. pf_rw. cbv zeta in *.
    split; [exact K1'|]. split; [exact K2'|]. split; [exact K3'|].
    split; [exact K4|]. split; [exact K5|]. split; [exact K6|].
    rewrite K7. f_equal. rewrite Hma, Hss. destruct (d_level s =? 0), (d_level s2 =? 0); lia.
Qed.

Lemma W_matches : forall s, W s -> d_level s <> 0 -> d_matches s = 0.
Proof.
  intros s (_ & _ & _ & _ & Hh & _) Hl. unfold whash in Hh.
  rewrite (proj2 (Z.eqb_neq _ _) Hl) in Hh. apply Hh.
Qed.

Lemma khash_params : forall s lv st s2,
  W s -> khash s -> 0 <= lv <= 9 -> pcase s lv st ->
  params_tail s lv st = Some s2 -> khash s2.
Proof.
  intros s lv st s2 HW [Kh1 Kh2] Hlv Hc E.
  destruct (params_tail_shape s lv st s2 E) as (P & Hl2 & Hs2 & Hcase).
  pose proof (prm_level s HW) as Hls.
  split.
  - destruct Hcase as [(Em & Eh & Ep & Hor) | [(L0 & Lv & M1 & M2 & Eh & Ep) | (L0 & Lv & M1 & M2 & M3 & Eh)]].
    + destruct (Z.eq_dec (d_level s) lv) as [Eq|Ne].
      * rewrite Hl2, <- Eq. rewrite Em.
        destruct (d_level s =? 0).
        -- destruct Kh1 as [(A & B) | [(A & B) | A]].
           ++ left. split; [exact A|]. exact (chain_hok_frame s s2 P Eh Ep B).
           ++ right; left. split; [exact A|].
              refine (chain_hok_frame (slide_hc s) (slide_hc s2) P _ _ B);
                unfold slide_hc; cbn; pose proof P as P'; pf_destruct P'; congruence.
           ++ right; right. exact A.
        -- exact (chain_hok_frame s s2 P Eh Ep Kh1).
      * assert (Hm0 : d_matches s = 0).
        { destruct Hor as [Hor|[Hor|Hor]]; [contradiction|apply W_matches; assumption|exact Hor]. }
        assert (Hch : chain_hok s).
        { destruct (d_level s =? 0); [|exact Kh1].
          destruct Kh1 as [(_ & B) | [(A & _) | A]]; [exact B|lia|lia]. }
        pose proof (chain_hok_frame s s2 P Eh Ep Hch) as Hch2.
        rewrite Hl2. destruct (lv =? 0); [left; split; [congruence|exact Hch2]|exact Hch2].
    + rewrite Hl2, (proj2 (Z.eqb_neq _ _) Lv).
      rewrite L0, Z.eqb_refl in Kh1. destruct Kh1 as [(A & _) | [(_ & B) | A]]; [lia| |lia].
      exact (chain_hok_frame (slide_hc s) s2 (pframe_slide s s2 P) Eh Ep B).
    + rewrite Hl2, (proj2 (Z.eqb_neq _ _) Lv).
      apply chain_hok_clear. intros b Hb. rewrite Eh.
      pose proof P as P'. pf_destruct P'. rewrite Phs in Hb.
      apply Znth_repeat_inrange. lia.
  - intros Hfn Hla.
    destruct Hc as [(Hf & Hst) | (Hla0 & _)].
    + destruct (cfg_f_class lv Hlv) as (A1 & _). destruct (cfg_f_class (d_level s) Hls) as (B1 & _).
      assert (Efn : fn_of s2 = fn_of s).
      { unfold fn_of. rewrite Hl2, Hs2, Hst, Hf.
        destruct (Z.eqb_spec lv 0), (Z.eqb_spec (d_level s) 0); try reflexivity; exfalso; rewrite Hf in A1; tauto. }
      pose proof P as P'. pf_destruct P'.
      rewrite Efn, Pla in *. destruct (Kh2 Hfn Hla) as (I & Pr).
      split; [rewrite Pins; exact I|]. rewrite Pss. exact (primed_frame s s2 _ P Pr).
    + pose proof P as P'. pf_destruct P'. rewrite Pla, Hla0 in Hla. unfold MIN_MATCH in Hla. lia.
Qed.

Lemma kf2_params : forall dict wrap D O fin s tin tout adler lv st s2,
  W s -> KF2 dict wrap D O fin s tin tout adler -> 0 <= lv <= 9 -> pcase s lv st ->
  params_tail s lv st = Some s2 -> KF2 dict wrap D O fin s2 tin tout adler.
Proof.
  intros dict wrap D O fin s tin tout adler lv st s2 HW (Hgz & BS & syms & (Kd & Kh) & Hst) Hlv Hc E.
  destruct (params_tail_shape s lv st s2 E) as (P & _).
  pose proof (kdata2_params dict D BS syms s lv st s2 HW Kd Hlv Hc E) as Kd'.
  pose proof (khash_params s lv st s2 HW Kh Hlv Hc E) as Kh'.
  pose proof (allbits_frame O s s2 P) as Eab. pose proof (bi_valid_frame s s2 P) as Ebv.
  pose proof (fun HDR => khdr_frame dict wrap s s2 HDR P) as Hkh.
  pose proof P as P'. pf_destruct P'.
  split; [rewrite Pgz; exact Hgz|]. exists BS, syms. split; [split; assumption|].
  rewrite Pst, Eab, Ebv, Pwr. unfold pend, d_pending. rewrite Ppo, Pout. fold (pend s).
  destruct Hst as [H0 | [(H1 & HDR & K1 & K2) | (H1 & H2 & H3 & HDR & K1 & K2)]].
  - left. exact H0.
  - right; left. split; [exact H1|]. exists HDR. split; [apply Hkh; exact K1|exact K2].
  - right; right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    exists HDR. split; [apply Hkh; exact K1|exact K2].
Qed.

(** ** The same for interface v1 (KF, kdata) *)
Lemma kdata_params : forall dict D BS syms s lv st s2,
  W s -> kdata dict D BS syms s -> 0 <= lv <= 9 -> pcase s lv st ->
  params_tail s lv st = Some s2 -> kdata dict D BS syms s2.
Proof.
  intros dict D BS syms s lv st s2 HW Kd Hlv Hc E.
  destruct (params_tail_shape s lv st s2 E) as (P & Hl2 & Hs2 & _).
  pose proof (prm_level s HW) as Hls.
  unfold kdata in *. destruct Kd as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  pose proof (kwin_frame _ _ _ P K1) as K1'. pose proof (kmatch_frame _ _ P K2) as K2'.
  destruct Hc as [(Hf & Hst) | (Hla & Hss)].
  - destruct (cfg_f_class lv Hlv) as (A1 & A2 & _). destruct (cfg_f_class (d_level s) Hls) as (B1 & B2 & _).
    assert (C0 : d_level s2 = 0 <-> d_level s = 0) by (rewrite Hl2, <- A1, Hf, B1; tauto).
    assert (C4 : 4 <= d_level s2 <-> 4 <= d_level s) by (rewrite Hl2, <- A2, Hf, B2; tauto).
    assert (K3' : wtrees s2 syms).
    { apply (wtrees_frame s s2 syms P K3).
      - destruct K3 as (_ & _ & F & _). eapply Forall_impl; [|exact F].
        intros x (V1 & V2 & V3). pose proof P as P'. pf_destruct P'. unfold sym_ok, MAX_DIST in *.
        rewrite Pws, Hs2, Hst. split; [exact V1|]. split; [exact V2|].
        intros H4. apply V3. apply C4. exact H4.
      - intros L0. apply K3. apply C0. exact L0.
      - intros L0. apply K3. intros L1. apply L0. apply C0. exact L1. }
    pf_destruct P. pf_rw. cbv zeta in *.
    split; [exact K1'|]. split; [exact K2'|]. split; [exact K3'|].
    split; [exact K4|]. split; [exact K5|]. split; [exact K6|].
    exact K7.
  - destruct (W_empty s syms HW K3 Hla Hss) as [Hma ->].
    assert (K3' : wtrees s2 []).
    { apply (wtrees_frame s s2 [] P K3); [constructor|reflexivity|]. intros _. rewrite Hma, Hss. unfold blk_len. cbn. lia. }
    pf_destruct P. pf_rw. cbv zeta in *.
    split; [exact K1'|]. split; [exact K2'|]. split; [exact K3'|].
    split; [exact K4|]. split; [exact K5|]. split; [exact K6|].
    exact K7.
Qed.

Lemma kf_params : forall dict wrap D O fin s tin tout adler lv st s2,
  W s -> KF dict wrap D O fin s tin tout adler -> 0 <= lv <= 9 -> pcase s lv st ->
  params_tail s lv st = Some s2 -> KF dict wrap D O fin s2 tin tout adler.
Proof.
  intros dict wrap D O fin s tin tout adler lv st s2 HW (Hgz & BS & syms & (Kd & Kh) & Hst) Hlv Hc E.
  destruct (params_tail_shape s lv st s2 E) as (P & _).
  pose proof (kdata_params dict D BS syms s lv st s2 HW Kd Hlv Hc E) as Kd'.
  pose proof (khash_params s lv st s2 HW Kh Hlv Hc E) as Kh'.
  pose proof (allbits_frame O s s2 P) as Eab. pose proof (bi_valid_frame s s2 P) as Ebv.
  pose proof (fun HDR => khdr_frame dict wrap s s2 HDR P) as Hkh.
  pose proof P as P'. pf_destruct P'.
  split; [rewrite Pgz; exact Hgz|]. exists BS, syms. split; [split; assumption|].
  rewrite Pst, Eab, Ebv, Pwr. unfold pend, d_pending. rewrite Ppo, Pout. fold (pend s).
  destruct Hst as [H0 | [(H1 & HDR & K1 & K2) | (H1 & H2 & H3 & HDR & K1 & K2)]].
  - left. exact H0.
  - right; left. split; [exact H1|]. exists HDR. split; [apply Hkh; exact K1|exact K2].
  - right; right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    exists HDR. split; [apply Hkh; exact K1|exact K2].
Qed.
