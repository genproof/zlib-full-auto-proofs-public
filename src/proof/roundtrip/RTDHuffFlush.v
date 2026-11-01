(* RT-D part HUFF: FLUSH_BLOCK_ONLY at a huff state (model on RTDLTCHuffFbw.hfbw_ok).  Statement: RTDHuffKit.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDHuffKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** A field kept by FLUSH_BLOCK_ONLY (as RTDLTCHuffFbw.hfbw_fk). *)
Ltac hff_fk K f E :=
  pose proof (f_equal f K) as E; unfold fbo_keep in E; autorewrite with hproj in E.

Theorem hfflush_ok : fbo_spec -> fbo_fspec -> hfflush_stmt.
Proof.
  intros Hfbo Hff s z syms last s' z' dict D BS p H0 Hz Hlast Hk Hp0 Hpm Hc.
  pose proof H0 as H0'.
  destruct H0' as (Hp & Hs & Hpos & Hw & Hh & Hm & Ht & HL & Hf & Hb & Hlit & Ho & Hq & Hfn).
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
  pose proof Hk as Hk'. destruct Hk' as (Kw & Kb & Ke & Kr & Kd & Kc).
  destruct (Hff s z s' z' syms last dict D BS p Hpre Kw Kb Ke Kr) as (x & blk & Hzx & Hbo & Hexp & Hbits);
    [exact Kd|exact Hp0|exact Hpm|exact Hc|].
  destruct (Hfbo s z syms last Hpre) as (s2 & z2 & x2 & buf & Hc2 & _ & _ & _ & _ & _ & Hk2 & Hbs' &
    Ht' & Hcfg & _).
  rewrite Hc in Hc2. injection Hc2 as <- <-.
  hff_fk Hk2 d_w_size Ews. hff_fk Hk2 d_w_bits Ewb.
  hff_fk Hk2 d_w_mask Ewm. hff_fk Hk2 d_window Ewi. hff_fk Hk2 d_prev Epr.
  hff_fk Hk2 d_head Ehe. hff_fk Hk2 d_hash_size Ehs. hff_fk Hk2 d_hash_mask Ehm.
  hff_fk Hk2 d_hash_shift Ehx. hff_fk Hk2 d_match_available Ema.
  hff_fk Hk2 d_strstart Ess. hff_fk Hk2 d_lookahead Ela.
  assert (EL : d_L s' = d_L s) by (unfold d_L; unfold tr_cfg in Hcfg; congruence).
  exists x, blk.
  split; [exact Hzx|].
  split.
  { unfold wtrees. split; [exact Ht'|]. split; [rewrite Zlength_nil, EL; lia|].
    split; [constructor|]. split; [intros _; reflexivity|].
    intros _. rewrite blk_len_nil, Hbs', Ess, Ema, Ha. lia. }
  split; [|exact Hbits].
  unfold hk3 in Hk |- *. cbv zeta in Hk |- *.
  rewrite Ess, Ela, Hbs', Ewb.
  split. { unfold kwin in Kw |- *. rewrite Ess, Ela, Ewi. exact Kw. }
  split; [exact Hbo|]. split; [exact Hexp|].
  split; [exact I|].
  split. { unfold F.syms_data. cbn [map fold_left]. exact Hexp. }
  unfold chain_hok, lim, MAX_DIST, h3, update_hash in Kc |- *.
  rewrite Ess, Ela, Ews, Ewi, Ewm, Ehe, Epr, Ehs, Ehm, Ehx. exact Kc.
Qed.
