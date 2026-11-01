(** * deflate_slow for wide streams, part Fbo: FLUSH_BLOCK_ONLY as an event

    Port of LTCSlowFbo.v to the invariant [SIw] / [EIw] of DetCoreSlowInv.v; the helpers that do not mention
    the invariant are LTCSlowFbo's. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetCoreSlowInv.
Require Import Zlib.proof.deflate.LTCSlowFbo.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem fboev_okw : fbo_spec -> fboev_partw.
Proof.
  intros Hfbo s0 z0 flush s z evs syms last HE Hpre Hsy Hl1 Hl0 Hbsn.
  pose proof Hpre as (Hprm & Hws & Hlev & Htr & HsL & Hblk & Hbss & Hb16 & Hwin & Ho & Hq & Hlast & Hzo).
  destruct (Hfbo s z syms last Hpre) as (s' & z' & x & buf & Hc & Hbuf1 & Hbuf0 & Hzx & Hbx & HG & Hk & Hbs' &
    Htr' & Hcfg & Hm & Ho' & Hbv & Hbv1 & Hpd).
  destruct HE as (Hc0 & Hfn & Hos & Hsp & Hapi & Hza & Had & (k & x0 & Hst & Hbx0 & Hk0) & Hch & Hev).
  pose proof Hc0 as (_ & _ & _ & _ & Hz0 & _ & Ha0).
  assert (Hz0a : zall z0) by (apply zwide_zall; exact Hz0).
  assert (Kss : d_strstart s' = d_strstart s) by exact (f_equal d_strstart Hk).
  assert (Kla : d_lookahead s' = d_lookahead s) by exact (f_equal d_lookahead Hk).
  assert (Kwb : d_w_bits s' = d_w_bits s) by exact (f_equal d_w_bits Hk).
  assert (Kws : d_w_size s' = d_w_size s) by exact (f_equal d_w_size Hk).
  assert (Khb : d_hash_bits s' = d_hash_bits s) by exact (f_equal d_hash_bits Hk).
  assert (Kpb : d_pending_buf_size s' = d_pending_buf_size s) by exact (f_equal d_pending_buf_size Hk).
  assert (Kst : d_status s' = d_status s) by exact (f_equal d_status Hk).
  assert (Kwr : d_wrap s' = d_wrap s) by exact (f_equal d_wrap Hk).
  assert (Kgh : d_gzhead s' = d_gzhead s) by exact (f_equal d_gzhead Hk).
  assert (Kgi : d_gzindex s' = d_gzindex s) by exact (f_equal d_gzindex Hk).
  assert (Klf : d_last_flush s' = d_last_flush s) by exact (f_equal d_last_flush Hk).
  assert (Kme : d_method s' = d_method s) by exact (f_equal d_method Hk).
  unfold tr_cfg in Hcfg. injection Hcfg as KL Kse Klv Ksg.
  destruct Hsp as (Swb & Sws & Shb & SL & Spb & Slv & Ssg).
  destruct Hapi as (Ast & Awr & Agh & Agi & Alf & Ame).
  destruct Hzx as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9).
  assert (Hao : 0 <= z_avail_out z').
  { destruct Hzo as (Hzo1 & _).
    destruct (fbo_out _ _ _ _ _ Hc Hzo1) as (y & Ey & Ly).
    rewrite Z7 in Ey. apply app_inv_head in Ey. subst y. lia. }
  set (e := DFlush (Gb s (z_total_out z)) (d_tr s) syms buf (d_strstart s - d_block_start s) last).
  assert (Hevok : ev_ok s0 flush e).
  { unfold e, ev_ok.
    split; [rewrite <- Slv; exact Hlev|].
    split; [exact (flush_pre_of s syms Hprm Htr HsL Ho Hq)|].
    split.
    { exists (z_total_out z). destruct Hzo as (_ & Ht & _).
      split; [exact Ht|]. destruct Hq as (Q1 & _).
      unfold Gb, bitpos, d_bi_valid. unfold d_pending in *. lia. }
    split; [exact SL|]. split; [exact Slv|]. split; [exact Ssg|]. split; [exact Hlast|].
    split; [exact Hl1|].
    split; [intros H0; rewrite <- SL; exact (Hl0 H0)|].
    split; [symmetry; exact Hblk|].
    split.
    { destruct (Z.leb_spec 0 (d_block_start s)) as [P|P].
      - destruct (Hbuf1 P) as (b & -> & Lb & Bb). destruct (Hwin P) as (W1 & _).
        split; [exact Lb|]. split; [exact Bb|]. exact W1.
      - rewrite (Hbuf0 P). specialize (Hbsn P). unfold MAX_DIST in Hbsn. rewrite <- Sws. exact Hbsn. }
    split.
    { intros y Hy Hne. rewrite Forall_forall in Hsy. destruct (Hsy y Hy) as (_ & D & _).
      specialize (D Hne). unfold MAX_DIST in D. rewrite <- Sws. exact D. }
    { intros H4 HF y Hy Hne Hs0. rewrite Forall_forall in Hsy. destruct (Hsy y Hy) as (_ & _ & D).
      apply D; [rewrite Slv; exact H4|rewrite Ssg; exact HF|exact Hne|exact Hs0]. } }
  assert (Hst' : zstep (d_wrap s0) z0 z' (k + 0) (x0 ++ x)).
  { apply (zstep_trans _ z0 z z'); [exact (proj1 Hz0a)|exact Ha0|exact Hst|].
    apply zout_only_zstep; [exact Hza|exact Had| |exact Hao].
    unfold zout_only. repeat split; assumption. }
  exists s', z', e.
  split; [exact Hc|]. split; [reflexivity|].
  split.
  { split; [exact Hc0|]. split; [exact Hfn|]. split; [exact Ho'|].
    split; [unfold same_prm; unfold d_L, d_level, d_strategy in *; rewrite Kwb, Kws, Khb, KL, Kpb, Klv, Ksg;
            split; [exact Swb|]; split; [exact Sws|]; split; [exact Shb|]; split; [exact SL|];
            split; [exact Spb|]; split; [exact Slv|exact Ssg]|].
    split; [unfold api_eq; rewrite Kst, Kwr, Kgh, Kgi, Klf, Kme;
            split; [exact Ast|]; split; [exact Awr|]; split; [exact Agh|]; split; [exact Agi|];
            split; [exact Alf|exact Ame]|].
    split; [exact (zall_zstep _ _ _ _ _ Hz0a Hst' Hao)|].
    split; [rewrite Z5; exact Had|].
    split.
    { exists (k + 0), (x0 ++ x). split; [exact Hst'|]. split; [apply Forall_app; split; assumption|].
      rewrite sum_len_app. unfold ub in *. rewrite Kss, Kla, Hbs'. cbn [ev_len e]. lia. }
    split.
    { rewrite HG. apply (ev_chain_app _ _ (Gb s (z_total_out z))); [exact Hch|reflexivity]. }
    apply Forall_app. split; [exact Hev|]. constructor; [exact Hevok|constructor]. }
  split; [exact Hk|]. split; [exact Hbs'|]. split; [exact Htr'|].
  split; [unfold tr_cfg; rewrite KL, Kse, Klv, Ksg; reflexivity|].
  split; [exact Hm|]. split; [exact Hbv|]. split; [exact Hbv1|]. split; [exact Hpd|]. exact Z3.
Qed.
