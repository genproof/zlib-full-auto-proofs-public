(** * deflate_rle, part: FLUSH_BLOCK_ONLY on an RTS0 state
    Statement: LTCRleKit.v ([rfbw_stmt]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCRleKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.
(** flush_pending never makes avail_out negative. *)
Lemma rfbw_fp_avail s z s' z' :
  c_flush_pending s z = Some (s', z') -> 0 <= z_avail_out z -> 0 <= z_avail_out z'.
Proof.
  intros H Hz. unfold c_flush_pending in H.
  destruct (c_tr_flush_bits (d_out s)) as [o|]; [|discriminate]. cbn [bind] in H.
  destruct (d_pending (set_d_out s o) >? z_avail_out z) eqn:Ep.
  - destruct (z_avail_out z =? 0) eqn:E0.
    + inversion H; subst; lia.
    + destruct (mb_read _ _ _) as [b|]; [|discriminate]. cbn [bind] in H.
      unfold out_put in H.
      destruct (Zlength b <=? z_avail_out z); [|discriminate]. cbn [bind] in H.
      inversion H; subst. cbn. lia.
  - destruct (u32 (d_pending (set_d_out s o)) =? 0) eqn:E0.
    + inversion H; subst; lia.
    + destruct (mb_read _ _ _) as [b|] eqn:Er; [|discriminate]. cbn [bind] in H.
      unfold out_put in H.
      destruct (Zlength b <=? z_avail_out z) eqn:El; [|discriminate]. cbn [bind] in H.
      inversion H; subst. cbn.
      unfold mb_read in Er.
      destruct ((0 <=? u32 (d_pending (set_d_out s o))) &&
                mb_definedb _ _ _) eqn:Ed; [|discriminate].
      inversion Er; subst. clear Er.
      apply andb_true_iff in Ed. destruct Ed as [Ed1 Ed2].
      unfold mb_definedb in Ed2. apply andb_true_iff in Ed2. destruct Ed2 as [Ed2 _].
      apply andb_true_iff in Ed2. destruct Ed2 as [Ed2 Ed3].
      apply Z.leb_le in Ed1. apply Z.leb_le in Ed2. apply Z.leb_le in Ed3. apply Z.leb_le in El.
      cbn [mb_val] in *.
      clear H. cbn in Ed2, Ed3. rewrite Zlength_sublist in El by lia. lia.
Qed.

Lemma rfbw_fbo_avail s z last s' z' :
  c_flush_block_only s z last = Some (s', z') -> 0 <= z_avail_out z -> 0 <= z_avail_out z'.
Proof.
  intros H Hz. unfold c_flush_block_only in H.
  destruct (guard _); [|discriminate]. cbn [bind] in H.
  destruct (if d_block_start s >=? 0 then _ else _) as [buf|]; [|discriminate]. cbn [bind] in H.
  destruct (c_tr_flush_block _ _ _ _) as [[t u0]|]; [|discriminate]. cbn [bind] in H.
  eapply rfbw_fp_avail; eauto.
Qed.

Theorem rfbw_ok : fbo_spec -> rfbw_stmt.
Proof.
  intros Hfbo s z flush syms last HT Hz Ha Hfl Hl Hl1 Hl0.
  pose proof HT as (Hp & Hs & Hpos & Hw & Hh & Hm & Ht & HL & Hf & Hb & Ho & Hq & Hfn & Hss).
  assert (Hlev := fn_of_rle s Hp Hfn).
  assert (Hma := wmatch_avail0 s Hm Hfn).
  pose proof Hp as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15).
  pose proof Hs as (S1 & S2 & S3 & S4 & S5).
  pose proof Hpos as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  assert (Hws : d_w_size s <= 32768).
  { rewrite P2. assert (2 ^ d_w_bits s <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 15) with 32768 in H. lia. }
  assert (HL2 : 128 <= d_L s).
  { rewrite P8. assert (2 ^ 7 <= 2 ^ (d_hash_bits s - 1)) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 7) with 128 in H. lia. }
  pose proof Hz as [Hzi Hzo0]. pose proof Hzo0 as (Z1 & Z2 & Z3).
  assert (Hpre : fbo_pre s z syms last).
  { unfold fbo_pre. split; [exact Hp|]. split; [exact Hs|]. split; [lia|]. split; [exact Ht|].
    split; [exact HL|]. split; [exact Hb|]. split; [lia|]. split; [lia|].
    split; [intros Hbs; split; [lia|split; [lia|]]; intros i Hi; apply Hw; lia|].
    split; [exact Ho|]. split; [exact Hq|]. split; [exact Hl|]. exact Hzo0. }
  destruct (Hfbo s z syms last Hpre) as (s' & z' & x & buf & Hc & Hbuf1 & Hbuf0 & Hzo & Hx & HG & Hk & Hbs'
    & Ht' & Hcfg & Hmat & Ho' & Hbv & Hbv1 & Hpz).
  assert (Hav : 0 <= z_avail_out z') by (eapply rfbw_fbo_avail; [exact Hc|exact Z1]).
  assert (Hzs : zstep (d_wrap s) z z' 0 x) by (apply zout_only_zstep; auto).
  assert (E_wb : d_w_bits s' = d_w_bits s) by exact (f_equal d_w_bits Hk).
  assert (E_ws : d_w_size s' = d_w_size s) by exact (f_equal d_w_size Hk).
  assert (E_wm : d_w_mask s' = d_w_mask s) by exact (f_equal d_w_mask Hk).
  assert (E_hb : d_hash_bits s' = d_hash_bits s) by exact (f_equal d_hash_bits Hk).
  assert (E_hs : d_hash_size s' = d_hash_size s) by exact (f_equal d_hash_size Hk).
  assert (E_hm : d_hash_mask s' = d_hash_mask s) by exact (f_equal d_hash_mask Hk).
  assert (E_hsh : d_hash_shift s' = d_hash_shift s) by exact (f_equal d_hash_shift Hk).
  assert (E_pbs : d_pending_buf_size s' = d_pending_buf_size s) by exact (f_equal d_pending_buf_size Hk).
  assert (E_me : d_method s' = d_method s) by exact (f_equal d_method Hk).
  assert (E_win : d_window s' = d_window s) by exact (f_equal d_window Hk).
  assert (E_wsz : d_window_size s' = d_window_size s) by exact (f_equal d_window_size Hk).
  assert (E_prev : d_prev s' = d_prev s) by exact (f_equal d_prev Hk).
  assert (E_head : d_head s' = d_head s) by exact (f_equal d_head Hk).
  assert (E_la : d_lookahead s' = d_lookahead s) by exact (f_equal d_lookahead Hk).
  assert (E_ss : d_strstart s' = d_strstart s) by exact (f_equal d_strstart Hk).
  assert (E_ins : d_insert s' = d_insert s) by exact (f_equal d_insert Hk).
  assert (E_hw : d_high_water s' = d_high_water s) by exact (f_equal d_high_water Hk).
  assert (E_ml : d_match_length s' = d_match_length s) by exact (f_equal d_match_length Hk).
  assert (E_pl : d_prev_length s' = d_prev_length s) by exact (f_equal d_prev_length Hk).
  assert (E_ma : d_match_available s' = d_match_available s) by exact (f_equal d_match_available Hk).
  assert (E_ms : d_match_start s' = d_match_start s) by exact (f_equal d_match_start Hk).
  assert (E_st : d_status s' = d_status s) by exact (f_equal d_status Hk).
  assert (E_wr : d_wrap s' = d_wrap s) by exact (f_equal d_wrap Hk).
  assert (E_gh : d_gzhead s' = d_gzhead s) by exact (f_equal d_gzhead Hk).
  assert (E_gi : d_gzindex s' = d_gzindex s) by exact (f_equal d_gzindex Hk).
  assert (E_lf : d_last_flush s' = d_last_flush s) by exact (f_equal d_last_flush Hk).
  assert (E_L : d_L s' = d_L s) by exact (f_equal (fun c => fst (fst (fst c))) Hcfg).
  assert (E_se : tr_sym_end (d_tr s') = tr_sym_end (d_tr s)) by exact (f_equal (fun c => snd (fst (fst c))) Hcfg).
  assert (E_lev : d_level s' = d_level s) by exact (f_equal (fun c => snd (fst c)) Hcfg).
  assert (E_str : d_strategy s' = d_strategy s) by exact (f_equal (fun c => snd c) Hcfg).
  assert (Efn : fn_of s' = fn_of s) by (unfold fn_of; rewrite E_lev, E_str; reflexivity).
  pose proof Ht' as (T1 & T2 & T3 & _).
  set (e := DFlush (Gb s (z_total_out z)) (d_tr s) syms buf (d_strstart s - d_block_start s) last).
  exists s', z', e.
  split; [exact Hc|].
  split.
  { unfold crel.
    split.
    { (* W s' *)
      unfold W. split.
      { unfold prm. rewrite E_wb, E_ws, E_wm, E_hb, E_hs, E_hm, E_hsh, E_L, E_pbs, E_se, E_lev, E_str, E_me.
        unfold d_L in T1, T2. rewrite <- E_L in *. unfold d_L in *.
        destruct P1, P4, P13, P14. repeat split; assumption. }
      split.
      { unfold wstruct. rewrite E_win, E_wsz, E_ws, E_prev, E_head, E_hs. exact Hs. }
      split.
      { unfold wpos. rewrite E_la, E_ss, E_wsz, Hbs', E_ins, E_ws, E_hw. unfold MAX_DIST. rewrite E_ws.
        repeat split; lia. }
      split.
      { unfold wwin. rewrite E_win, E_ss, E_la, E_hw. exact Hw. }
      split.
      { unfold whash in *. rewrite E_lev. destruct (Z.eqb_spec (d_level s) 0) as [E0|N0]; [lia|].
        split; [exact Hmat|]. destruct Hh as [_ Hco].
        unfold chain_ok, chain_with, lim, MAX_DIST in *.
        rewrite E_ss, E_ws, E_head, E_prev, E_hs, E_wm. exact Hco. }
      split.
      { unfold wmatch. rewrite Efn, E_ml, E_pl, E_ma, E_ss, E_la, E_ms, E_str. unfold MAX_DIST. rewrite E_ws.
        exact Hm. }
      split; [intros E0; rewrite E_lev in E0; clear - E0 Hlev; lia|].
      exists []. unfold wtrees. split; [exact Ht'|]. split; [rewrite Zlength_nil, E_L; clear - HL2; lia|].
      split; [constructor|]. split; [intros; reflexivity|].
      intros _. rewrite Hbs', E_ss, E_ma, Hma. unfold blk_len. cbn. lia. }
    split; [exact Ho'|].
    split.
    { unfold same_prm. split; [exact E_wb|]. split; [exact E_ws|]. split; [exact E_hb|].
      split; [exact E_L|]. split; [exact E_pbs|]. split; [exact E_lev|]. exact E_str. }
    split.
    { unfold api_eq. split; [exact E_st|]. split; [exact E_wr|]. split; [exact E_gh|].
      split; [exact E_gi|]. split; [exact E_lf|]. exact E_me. }
    split.
    { exists 0, x. split; [exact Hzs|]. split; [exact Hx|].
      unfold ub, sum_len, e. cbn [fold_right ev_len]. rewrite Hbs', E_ss, E_la. lia. }
    split.
    { unfold e. cbn [ev_chain ev_g]. split; [reflexivity|]. exact HG. }
    constructor; [|constructor].
    unfold e, ev_ok.
    split; [lia|].
    split; [apply flush_pre_of; auto|].
    split.
    { exists (z_total_out z). split; [lia|].
      destruct Hq as (Hq1 & Hq2 & Hq3). unfold Gb, bitpos, d_bi_valid, d_pending in *. lia. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact Hl|]. split; [exact Hl1|]. split; [exact Hl0|].
    split; [symmetry; exact Hb|].
    split.
    { destruct (Z_lt_le_dec (d_block_start s) 0) as [Hn|Hn].
      - rewrite (Hbuf0 Hn). unfold MAX_DIST in Q6. lia.
      - destruct (Hbuf1 Hn) as (b & -> & Hlb & Hbb). split; [exact Hlb|]. split; [exact Hbb|]. clear - Hn Hss S3 Hws. lia. }
    split.
    { intros y Hy Hne. rewrite Forall_forall in Hf. destruct (Hf y Hy) as (_ & D & _).
      unfold MAX_DIST in D. auto. }
    intros H4 HF y Hy Hne H0. rewrite Forall_forall in Hf. destruct (Hf y Hy) as (_ & _ & D).
    exact (D H4 HF Hne H0). }
  split; [reflexivity|].
  split; [eapply zall_zstep; eauto|].
  destruct Hzo as (_ & _ & A3 & _ & A5 & _).
  split; [exact A5|]. split; [exact A3|].
  split; [exact E_la|]. split; [exact E_ss|]. split; [exact Hbs'|].
  split; [unfold d_sym_next; rewrite T3; reflexivity|].
  split; [exact Hbv|]. split; [exact Hbv1|]. exact Hpz.
Qed.
