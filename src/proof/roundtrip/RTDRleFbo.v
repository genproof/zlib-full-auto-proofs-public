(* RT-D part RLE: FLUSH_BLOCK_ONLY at an rle state (statement: RTDRleKit.v; model on RTDLTCRleFbw.rfbw_ok). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDRleKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem rffbo_ok : fbo_spec -> fbo_fspec -> rffbo_stmt.
Proof.
  intros Hfbo Hff s z syms last s' z' dict D BS p HT Hz Hl Hd HD HR Hp0 Hpm Hc.
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
  pose proof Hz as [Hzi Hzo0].
  assert (Hpre : fbo_pre s z syms last).
  { unfold fbo_pre. split; [exact Hp|]. split; [exact Hs|]. split; [lia|]. split; [exact Ht|].
    split; [exact HL|]. split; [exact Hb|]. split; [lia|]. split; [lia|].
    split; [intros Hbs; split; [lia|split; [lia|]]; intros i Hi; apply Hw; lia|].
    split; [exact Ho|]. split; [exact Hq|]. split; [exact Hl|]. exact Hzo0. }
  destruct (Hfbo s z syms last Hpre) as (s2 & z2 & x2 & buf & Hc2 & _ & _ & _ & _ & _ & Hk & Hbs'
    & Ht' & Hcfg & _ & _ & _ & _ & _).
  rewrite Hc in Hc2. injection Hc2 as <- <-.
  pose proof HR as (Rw & Rb & Re & Rs & Rd & Rc).
  destruct (Hff s z s' z' syms last dict D BS p Hpre Rw Rb Re Rs Rd Hp0 Hpm Hc)
    as (x & blk & Hzo & Hbok & Hexp & Hbits).
  assert (E_wb : d_w_bits s' = d_w_bits s) by exact (f_equal d_w_bits Hk).
  assert (E_ws : d_w_size s' = d_w_size s) by exact (f_equal d_w_size Hk).
  assert (E_wm : d_w_mask s' = d_w_mask s) by exact (f_equal d_w_mask Hk).
  assert (E_hs : d_hash_size s' = d_hash_size s) by exact (f_equal d_hash_size Hk).
  assert (E_hm : d_hash_mask s' = d_hash_mask s) by exact (f_equal d_hash_mask Hk).
  assert (E_hsh : d_hash_shift s' = d_hash_shift s) by exact (f_equal d_hash_shift Hk).
  assert (E_win : d_window s' = d_window s) by exact (f_equal d_window Hk).
  assert (E_prev : d_prev s' = d_prev s) by exact (f_equal d_prev Hk).
  assert (E_head : d_head s' = d_head s) by exact (f_equal d_head Hk).
  assert (E_la : d_lookahead s' = d_lookahead s) by exact (f_equal d_lookahead Hk).
  assert (E_ss : d_strstart s' = d_strstart s) by exact (f_equal d_strstart Hk).
  assert (E_ma : d_match_available s' = d_match_available s) by exact (f_equal d_match_available Hk).
  assert (E_L : d_L s' = d_L s) by exact (f_equal (fun c => fst (fst (fst c))) Hcfg).
  assert (E_lev : d_level s' = d_level s) by exact (f_equal (fun c => snd (fst c)) Hcfg).
  exists x, blk.
  split; [exact Hzo|].
  split.
  { unfold wtrees. split; [exact Ht'|]. split; [rewrite Zlength_nil, E_L; lia|].
    split; [constructor|]. split; [intros; reflexivity|].
    intros _. rewrite Hbs', E_ss, E_ma, Hma. unfold blk_len. cbn. lia. }
  split; [|exact Hbits].
  unfold rkt in *. cbv zeta in *. rewrite E_ss, E_la, E_wb, Hbs'.
  split.
  { unfold kwin in *. rewrite E_ss, E_la, E_win. exact Rw. }
  split; [exact Hbok|]. split; [exact Hexp|]. split; [exact I|].
  split; [exact Hexp|].
  unfold chain_hok, lim, h3, update_hash, MAX_DIST in *.
  rewrite E_hs, E_head, E_ss, E_la, E_ws, E_win, E_wm, E_prev, E_hsh, E_hm. exact Rc.
Qed.
