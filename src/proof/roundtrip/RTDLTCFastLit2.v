(** * deflate_fast, part lit, against the CORRECTED tally specification [tally_spec2] (RTDLTCSpecs2.v:
    tally_spec is false without a bound on lit_bufsize; tally_spec2 adds [tr_lit_bufsize t <= 32768], which follows
    from prm: L = 2^(hash_bits - 1) <= 2^15).  With RTDLTCSpecs2.tally_spec_2, [lit_stmt]
    also follows from the original [tally_spec]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCFastKit.
Require Export Zlib.proof.roundtrip.RTDLTCSpecs2.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma lit_chain_mono s n l l' G : chain_with s n l G -> l <= l' -> chain_with s n l' G.
Proof.
  intros (A & B & C) Hl. split; [exact A|]. split; [exact B|].
  intros q Hq Hq0 Hql. apply C; auto; lia.
Qed.

Lemma lit_u32_id x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

Ltac sr_field Hk f E := assert (E := f_equal f Hk); unfold sr_keep, hc_keep in E; autorewrite with fproj in E.

Theorem lit_ok2 : tally_spec2 -> lit_stmt.
Proof.
  intros [Htl _] s s2 HW Ho Hq Hfn Hrd Hla HSR Hml.
  destruct HSR as (Hk & Hws2 & [G HG] & Hml2 & _).
  destruct HW as (Hp & Hws & Hpos & Hwin & Hh & Hm & _ & syms & Ht).
  sr_field Hk d_window Ewin. sr_field Hk d_window_size Ewsz. sr_field Hk d_strstart Ess.
  sr_field Hk d_lookahead Ela. sr_field Hk d_tr Etr. sr_field Hk d_pbm Epbm.
  assert (Hp0 := Hp). assert (Hlev := fn_of_fast s Hp Hfn).
  assert (Ha : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  destruct Hp as (Hwb & Hwsz & Hwm & Hhb & Hhs & Hhm & Hhsh & HL & Hpbs & Hob & Hpbm & Hse & Hlv & Hstr & Hmeth).
  destruct Hws as (Hwl & Hwok & Hwss & Hpl & Hhl).
  destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  destruct Ht as (Ht1 & HL2 & Hf & _ & Hb).
  assert (Hb' : blk_len syms = d_strstart s - d_block_start s) by (rewrite Hb by lia; lia).
  assert (HL15 : d_L s <= 32768).
  { rewrite HL. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hrdc : mb_rd (d_window s) (d_strstart s) = Some (Znth (d_strstart s) (mb_val (d_window s)))).
  { unfold mb_rd. rewrite (Hwin (d_strstart s)) by lia. unfold in_range.
    replace ((0 <=? d_strstart s) && (d_strstart s <? Zlength (mb_val (d_window s)))) with true by lia.
    reflexivity. }
  set (c := Znth (d_strstart s) (mb_val (d_window s))) in *.
  assert (Hc : 0 <= c < 256).
  { destruct Hwok as [_ Hok]. apply Hok; [lia|]. apply Hwin. lia. }
  destruct (Htl (d_tr s) (d_pbm s) syms c Ht1 HL2 HL15 Hc) as (t' & m' & Etl & Ht' & Hfr).
  unfold flit. rewrite Ewin, Ess, Hrdc. cbn [bind]. unfold c_dtally_lit, d_trm. rewrite Etr, Epbm, Etl.
  cbn [bind].
  assert (Hws15 : d_w_size s <= 32768).
  { rewrite Hwsz. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hss1 : d_strstart s + 1 < d_window_size s).
  { assert (E : MIN_LOOKAHEAD = 262) by reflexivity. unfold ready, MAX_DIST in Hrd. rewrite E in Hrd.
    destruct Hrd as [R|[R _]]; lia. }
  eexists _, _, (syms ++ [(0, c)]). split; [reflexivity|].
  unfold set_d_trm. cbn [fst snd]. autorewrite with fproj. rewrite Ela, Ess.
  rewrite (lit_u32_id (d_lookahead s - 1)) by lia. rewrite (lit_u32_id (d_strstart s + 1)) by lia.
  sr_field Hk d_w_size Ewsize. sr_field Hk d_w_bits Ewbits. sr_field Hk d_w_mask Ewmask.
  sr_field Hk d_hash_size Ehsize. sr_field Hk d_hash_bits Ehbits. sr_field Hk d_hash_mask Ehmask.
  sr_field Hk d_hash_shift Ehshift. sr_field Hk d_block_start Ebs. sr_field Hk d_insert Eins.
  sr_field Hk d_high_water Ehw. sr_field Hk d_prev_length Epl. sr_field Hk d_match_available Ema.
  sr_field Hk d_po Epo. sr_field Hk d_status Estatus. sr_field Hk d_wrap Ewrap. sr_field Hk d_gzhead Egzh.
  sr_field Hk d_gzindex Egzi. sr_field Hk d_last_flush Elf. sr_field Hk d_method Emeth.
  sr_field Hk d_pending_buf_size Epbs.
  set (s3 := set_d_strstart (set_d_lookahead (set_d_pbm (set_d_tr s2 t') m') (d_lookahead s - 1)) (d_strstart s + 1)).
  assert (S_win : d_window s3 = d_window s) by (unfold s3; autorewrite with fproj; exact Ewin).
  assert (S_wsz : d_window_size s3 = d_window_size s) by (unfold s3; autorewrite with fproj; exact Ewsz).
  assert (S_ss : d_strstart s3 = d_strstart s + 1) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_la : d_lookahead s3 = d_lookahead s - 1) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_wsize : d_w_size s3 = d_w_size s) by (unfold s3; autorewrite with fproj; exact Ewsize).
  assert (S_wbits : d_w_bits s3 = d_w_bits s) by (unfold s3; autorewrite with fproj; exact Ewbits).
  assert (S_wmask : d_w_mask s3 = d_w_mask s2) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_hsize : d_hash_size s3 = d_hash_size s2) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_hbits : d_hash_bits s3 = d_hash_bits s) by (unfold s3; autorewrite with fproj; exact Ehbits).
  assert (S_hmask : d_hash_mask s3 = d_hash_mask s) by (unfold s3; autorewrite with fproj; exact Ehmask).
  assert (S_hshift : d_hash_shift s3 = d_hash_shift s) by (unfold s3; autorewrite with fproj; exact Ehshift).
  assert (S_bs : d_block_start s3 = d_block_start s) by (unfold s3; autorewrite with fproj; exact Ebs).
  assert (S_ins : d_insert s3 = d_insert s) by (unfold s3; autorewrite with fproj; exact Eins).
  assert (S_hw : d_high_water s3 = d_high_water s) by (unfold s3; autorewrite with fproj; exact Ehw).
  assert (S_pl : d_prev_length s3 = d_prev_length s) by (unfold s3; autorewrite with fproj; exact Epl).
  assert (S_ma : d_match_available s3 = d_match_available s) by (unfold s3; autorewrite with fproj; exact Ema).
  assert (S_ml : d_match_length s3 = d_match_length s2) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_po : d_po s3 = d_po s) by (unfold s3; autorewrite with fproj; exact Epo).
  assert (S_status : d_status s3 = d_status s) by (unfold s3; autorewrite with fproj; exact Estatus).
  assert (S_wrap : d_wrap s3 = d_wrap s) by (unfold s3; autorewrite with fproj; exact Ewrap).
  assert (S_gzh : d_gzhead s3 = d_gzhead s) by (unfold s3; autorewrite with fproj; exact Egzh).
  assert (S_gzi : d_gzindex s3 = d_gzindex s) by (unfold s3; autorewrite with fproj; exact Egzi).
  assert (S_lf : d_last_flush s3 = d_last_flush s) by (unfold s3; autorewrite with fproj; exact Elf).
  assert (S_meth : d_method s3 = d_method s) by (unfold s3; autorewrite with fproj; exact Emeth).
  assert (S_pbs : d_pending_buf_size s3 = d_pending_buf_size s) by (unfold s3; autorewrite with fproj; exact Epbs).
  assert (S_tr : d_tr s3 = t') by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_pbm : d_pbm s3 = m') by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_prev : d_prev s3 = d_prev s2) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_head : d_head s3 = d_head s2) by (unfold s3; autorewrite with fproj; reflexivity).
  clearbody s3.
  destruct Hfr as (Fcfg & Fmat & Fpend & Fbuf & Fbv & Fbu & Fgrow).
  unfold tr_cfg in Fcfg. injection Fcfg as F1 F2 F3 F4.
  assert (S_L : d_L s3 = d_L s) by (unfold d_L; rewrite S_tr; exact F1).
  assert (S_level : d_level s3 = d_level s) by (unfold d_level; rewrite S_tr; exact F3).
  assert (S_strat : d_strategy s3 = d_strategy s) by (unfold d_strategy; rewrite S_tr; exact F4).
  assert (S_pend : d_pending s3 = d_pending s) by (unfold d_pending; rewrite S_tr; exact Fpend).
  assert (S_bv : d_bi_valid s3 = d_bi_valid s) by (unfold d_bi_valid; rewrite S_tr; exact Fbv).
  assert (S_mat : d_matches s3 = d_matches s) by (unfold d_matches; rewrite S_tr; exact Fmat).
  assert (S_md : MAX_DIST s3 = MAX_DIST s) by (unfold MAX_DIST; rewrite S_wsize; reflexivity).
  assert (S_fn : fn_of s3 = fn_of s) by (unfold fn_of; rewrite S_level, S_strat; reflexivity).
  assert (Esym : sym_ok s3 = sym_ok s) by (unfold sym_ok; rewrite S_md, S_level, S_strat; reflexivity).
  destruct Fgrow as (G1 & G2 & G3 & G4).
  assert (Hlen3 : Zlength (syms ++ [(0, c)]) = Zlength syms + 1) by (rewrite Zlength_app; reflexivity).
  assert (Hblk3 : blk_len (syms ++ [(0, c)]) = blk_len syms + 1) by (rewrite blk_len_app; reflexivity).
  assert (Hbl := blk_len_bound syms (proj1 (proj2 (proj2 (proj2 Ht1))))).
  assert (Hch : chain_ok s3).
  { exists G. assert (HG3 : chain_with s3 (d_strstart s + 1) (lim s) G).
    { destruct HG as (A & B & C). split; [exact A|]. split; [rewrite S_hsize, S_head; exact B|].
      rewrite S_wmask, S_prev. exact C. }
    rewrite S_ss. apply (lit_chain_mono _ _ _ _ _ HG3). unfold lim. rewrite S_ss, S_md.
    destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); destruct (Z.gtb_spec (d_strstart s + 1) (MAX_DIST s)); lia. }
  rewrite Ewmask in S_wmask. rewrite Ehsize in S_hsize.
  split; [|split].
  - unfold TS. split.
    2:{ rewrite Hse, Hlen3, S_L.
        destruct (Z.eqb_spec (3 * Zlength syms + 3) (3 * (d_L s - 1))), (Z.eqb_spec (Zlength syms + 1) (d_L s - 1));
          auto; lia. }
    unfold TS0.
    split.
    { unfold prm. rewrite S_wbits, S_wsize, S_wmask, S_hbits, S_hsize, S_hmask, S_hshift, S_L, S_pbs, S_pbm,
        S_level, S_strat, S_meth, S_tr, G1, G2, F2. exact Hp0. }
    split.
    { destruct Hws2 as (W1 & W2 & W3 & W4 & W5). rewrite Ewin, Ewsz, Ewsize, Ehsize in *.
      unfold wstruct. rewrite S_win, S_wsz, S_wsize, S_prev, S_head, S_hsize.
      exact (conj W1 (conj W2 (conj W3 (conj W4 W5)))). }
    split.
    { unfold wpos. rewrite S_la, S_ss, S_wsz, S_bs, S_ins, S_wsize, S_hw, S_md.
      repeat split; lia. }
    split.
    { unfold wwin in *. rewrite S_ss, S_la, S_hw, S_win. intros i Hi. apply Hwin. lia. }
    split.
    { unfold whash in *. rewrite S_level. destruct (Z.eqb_spec (d_level s) 0) as [E|E]; [lia|].
      split; [|exact Hch]. rewrite S_mat. destruct Hh as [Hh _]. exact Hh. }
    split.
    { unfold wmatch in *. rewrite S_ml, S_pl, S_ma, Ha, S_ss, S_la, S_fn. rewrite Ha in Hm.
      destruct Hm as (M1 & M2 & _ & M4 & _).
      split; [exact Hml2|]. split; [exact M2|]. split; [left; reflexivity|].
      split; [intros _; split; [exact Hml|exact (proj2 (M4 eq_refl))]|]. intros E; discriminate E. }
    split; [rewrite S_tr, S_pbm; exact Ht'|].
    split; [rewrite Hlen3, S_L; lia|].
    split.
    { rewrite Esym. apply Forall_app. split; [exact Hf|]. constructor; [|constructor].
      unfold sym_ok, valid_sym. cbn [fst snd].
      split; [split; lia|]. split; [intros H; congruence|intros _ _ H; congruence]. }
    split; [rewrite Hblk3, S_ss, S_bs; lia|].
    split.
    { apply (outok_grow s s3 Ho).
      - rewrite S_tr, S_pbm. exact (conj G1 (conj G2 (conj G3 G4))).
      - exact S_po.
      - exact S_pend.
      - exact S_pbs.
      - destruct Ho as (_ & Hbo & _). unfold bits_ok in *. rewrite S_tr, Fbv, Fbuf, Fpend. exact Hbo. }
    split; [unfold quiet in *; rewrite S_pend, S_po, S_bv; exact Hq|].
    split; [rewrite S_fn; exact Hfn|].
    rewrite S_ss, S_wsz. lia.
  - unfold fr. split.
    { unfold same_prm. rewrite S_wbits, S_wsize, S_hbits, S_L, S_pbs, S_level, S_strat.
      repeat (split; [reflexivity|]); reflexivity. }
    split.
    { unfold api_eq. rewrite S_status, S_wrap, S_gzh, S_gzi, S_lf, S_meth.
      repeat (split; [reflexivity|]); reflexivity. }
    split; [unfold ub; rewrite S_ss, S_bs, S_la; lia|].
    intros tout. unfold Gb. rewrite S_pend, S_bv. reflexivity.
  - lia.
Qed.
