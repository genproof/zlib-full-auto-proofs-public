(** * deflate_huff part: see LTCHuffKit.v for the statement and the design. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCHuffKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** A field kept by FLUSH_BLOCK_ONLY. *)
Ltac hfbw_fk K f E :=
  pose proof (f_equal f K) as E; unfold fbo_keep in E; autorewrite with hproj in E.

Lemma hfbw_chain_ok s s' :
  d_strstart s' = d_strstart s -> d_w_size s' = d_w_size s -> d_hash_size s' = d_hash_size s ->
  d_head s' = d_head s -> d_prev s' = d_prev s -> d_w_mask s' = d_w_mask s ->
  chain_ok s -> chain_ok s'.
Proof.
  intros E1 E2 E3 E4 E5 E6. unfold chain_ok, chain_with, lim, MAX_DIST.
  rewrite E1, E2, E3, E4, E5, E6. exact (fun H => H).
Qed.

Theorem hfbw_ok : fbo_spec -> hfbw_stmt.
Proof.
  intros Hfbo s z flush syms last H0 Hz Had Hfl Hlast Hl1 Hl0.
  destruct H0 as (Hp & Hs & Hpos & Hw & Hh & Hm & Ht & HL & Hf & Hb & Hlit & Ho & Hq & Hfn).
  destruct (fn_of_huff s Hp Hfn) as [Hlev Hstr].
  assert (Ha : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  pose proof Hp as Hp'.
  destruct Hp' as (Hwb & Hws & Hwm & Hhb & Hhs & Hhm & Hsh & HLe & Hpbs & Hob & Hpbm & Hse & Hlv & Hst & Hme).
  assert (HLb : 128 <= d_L s <= 32768).
  { rewrite HLe. split.
    - replace 128 with (2 ^ 7) by reflexivity. apply Z.pow_le_mono_r; lia.
    - replace 32768 with (2 ^ 15) by reflexivity. apply Z.pow_le_mono_r; lia. }
  pose proof Hpos as Hpos'.
  destruct Hpos' as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  pose proof Hs as Hs'.
  destruct Hs' as (S1 & S2 & S3 & S4 & S5).
  pose proof Hz as Hz'. destruct Hz' as [Hzi Hzo].
  assert (Hpre : fbo_pre s z syms last).
  { unfold fbo_pre. split; [exact Hp|]. split; [exact Hs|]. split; [lia|]. split; [exact Ht|].
    split; [exact HL|]. split; [exact Hb|]. split; [lia|]. split; [lia|].
    split.
    { intros Hbs. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia. }
    split; [exact Ho|]. split; [exact Hq|]. split; [lia|]. exact Hzo. }
  destruct (Hfbo s z syms last Hpre) as (s' & z' & x & buf & Hc & Hbuf1 & Hbuf0 & Hzx & Hbx & HG & Hk & Hbs' &
    Ht' & Hcfg & Hmat & Ho' & Hbv & Hbv1 & Hpz).
  exists s', z', (DFlush (Gb s (z_total_out z)) (d_tr s) syms buf (d_strstart s - d_block_start s) last).
  hfbw_fk Hk d_status Est. hfbw_fk Hk d_wrap Ewr. hfbw_fk Hk d_gzhead Egh. hfbw_fk Hk d_gzindex Egi.
  hfbw_fk Hk d_last_flush Elf. hfbw_fk Hk d_method Eme. hfbw_fk Hk d_w_size Ews. hfbw_fk Hk d_w_bits Ewb.
  hfbw_fk Hk d_w_mask Ewm. hfbw_fk Hk d_window Ewi. hfbw_fk Hk d_window_size Ewz. hfbw_fk Hk d_prev Epr.
  hfbw_fk Hk d_head Ehe. hfbw_fk Hk d_hash_size Ehs. hfbw_fk Hk d_hash_bits Ehb. hfbw_fk Hk d_hash_mask Ehm.
  hfbw_fk Hk d_hash_shift Ehx. hfbw_fk Hk d_match_length Eml. hfbw_fk Hk d_match_available Ema.
  hfbw_fk Hk d_strstart Ess. hfbw_fk Hk d_match_start Emst. hfbw_fk Hk d_lookahead Ela.
  hfbw_fk Hk d_prev_length Epl. hfbw_fk Hk d_insert Ein. hfbw_fk Hk d_high_water Ehw.
  hfbw_fk Hk d_pending_buf_size Epb.
  assert (Elv : d_level s' = d_level s) by (unfold d_level; unfold tr_cfg in Hcfg; congruence).
  assert (Esg : d_strategy s' = d_strategy s) by (unfold d_strategy; unfold tr_cfg in Hcfg; congruence).
  assert (EL : d_L s' = d_L s) by (unfold d_L; unfold tr_cfg in Hcfg; congruence).
  assert (Ese : tr_sym_end (d_tr s') = tr_sym_end (d_tr s)) by (unfold tr_cfg in Hcfg; congruence).
  assert (Hav : 0 <= z_avail_out z').
  { apply (flush_block_only_avail s z last s' z' Hc). destruct Hzo as (Z1 & _). exact Z1. }
  assert (Hzs : zstep (d_wrap s) z z' 0 x) by exact (zout_only_zstep _ _ _ _ Hz Had Hzx Hav).
  assert (Hz2 : zall z') by exact (zall_zstep _ _ _ _ _ Hz Hzs Hav).
  pose proof Ht' as Ht2. destruct Ht2 as (T1 & T2 & T3 & _).
  change (tr_lit_bufsize (d_tr s')) with (d_L s') in T1, T2.
  assert (Hsp : same_prm s s').
  { unfold same_prm. rewrite Ewb, Ews, Ehb, EL, Epb, Elv, Esg. repeat split. }
  assert (Hp2 : prm s').
  { unfold prm. rewrite Ewb, Ews, Ewm, Ehb, Ehs, Ehm, Ehx, Epb, Elv, Esg, Eme, EL, Ese.
    split; [lia|]. split; [exact Hws|]. split; [exact Hwm|]. split; [lia|]. split; [exact Hhs|].
    split; [exact Hhm|]. split; [exact Hsh|]. split; [exact HLe|]. split; [exact Hpbs|].
    split; [rewrite T1, EL; reflexivity|]. split; [rewrite T2, EL; reflexivity|]. split; [exact Hse|].
    split; [lia|]. split; [lia|]. exact Hme. }
  assert (HW : W s').
  { unfold W. split; [exact Hp2|].
    split. { unfold wstruct. rewrite Ewi, Ews, Ewz, Epr, Ehe, Ehs. exact Hs. }
    split. { unfold wpos, MAX_DIST. rewrite Ela, Ess, Ewz, Hbs', Ein, Ews, Ehw. repeat split; try lia. }
    split. { unfold wwin. rewrite Ess, Ela, Ehw, Ewi. exact Hw. }
    split.
    { unfold whash in Hh |- *. rewrite Elv. rewrite (proj2 (Z.eqb_neq _ _) Hlev) in Hh |- *.
      destruct Hh as [_ Hco]. split; [exact Hmat|].
      exact (hfbw_chain_ok s s' Ess Ews Ehs Ehe Epr Ewm Hco). }
    split.
    { unfold wmatch, MAX_DIST in Hm |- *.
      rewrite (fn_of_same_prm' s s' Hsp), Eml, Epl, Ema, Ess, Ela, Emst, Ews, Esg. exact Hm. }
    split; [intros E; lia|].
    exists []. unfold wtrees. split; [exact Ht'|]. split; [rewrite Zlength_nil, EL; lia|].
    split; [constructor|]. split; [intros _; reflexivity|].
    intros _. rewrite blk_len_nil, Hbs', Ess, Ema, Ha. lia. }
  pose proof Hzx as Hzx2. destruct Hzx2 as (X1 & X2 & X3 & X4 & X5 & _).
  split; [exact Hc|].
  split.
  { unfold hcrel. split; [exact HW|].
    split. { intros _. unfold d_sym_next. rewrite T3, Hbs', Ess, Zlength_nil. lia. }
    split; [exact Ho'|]. split; [exact Hsp|].
    split. { unfold api_eq. rewrite Est, Ewr, Egh, Egi, Elf, Eme. repeat split. }
    split.
    { exists 0, x. split; [exact Hzs|]. split; [exact Hbx|].
      unfold sum_len. cbn [fold_right ev_len]. unfold ub. rewrite Hbs', Ess, Ela. lia. }
    split.
    { cbn [ev_chain ev_g]. split; [reflexivity|]. exact HG. }
    constructor; [|constructor].
    cbv beta iota delta [ev_ok].
    split; [lia|].
    split; [exact (flush_pre_of s syms Hp Ht HL Ho Hq)|].
    split.
    { exists (z_total_out z). destruct Hzo as (Z1 & Z2 & _). split; [exact Z2|].
      unfold Gb, bitpos. destruct Hq as (Q1 & Q2 & Q3). unfold d_pending, d_bi_valid in *. lia. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact Hlast|]. split; [exact Hl1|]. split; [exact Hl0|]. split; [symmetry; exact Hb|].
    split.
    { destruct (Z_lt_le_dec (d_block_start s) 0) as [N|N].
      - rewrite (Hbuf0 N). specialize (P6 N). unfold MAX_DIST in P6. lia.
      - destruct (Hbuf1 N) as (b & -> & B1 & B2). split; [exact B1|]. split; [exact B2|]. lia. }
    split.
    { intros y Hy Hy0. destruct (proj1 (Forall_forall _ _) Hf y Hy) as (_ & F2 & _).
      unfold MAX_DIST in F2. exact (F2 Hy0). }
    intros H4 H5 y Hy Hy0 Hy1. destruct (proj1 (Forall_forall _ _) Hf y Hy) as (_ & _ & F3).
    exact (F3 H4 H5 Hy0 Hy1). }
  split; [reflexivity|]. split; [exact Hz2|]. split; [exact X5|]. split; [exact X3|].
  split; [exact Ela|]. split; [exact Ess|]. split; [exact Hbs'|].
  split. { unfold d_sym_next. rewrite T3, Zlength_nil. reflexivity. }
  split; [exact Hbv|]. split; [exact Hbv1|]. exact Hpz.
Qed.
