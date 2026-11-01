(** * deflate_huff part: see RTDLTCHuffKit.v for the statement and the design. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCHuffKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma hlit_chain_mono s n l l' G : chain_with s n l G -> l <= l' -> chain_with s n l' G.
Proof.
  intros (A & B & C) Hl. split; [exact A|]. split; [exact B|].
  intros q Hq Hq0 Hql. apply C; auto; lia.
Qed.

Lemma hlit_u32_id x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

Lemma hlit_sumZ_app a b : HuffAbs.sumZ (a ++ b) = HuffAbs.sumZ a + HuffAbs.sumZ b.
Proof. induction a as [|x a IH]; cbn [app HuffAbs.sumZ]; [lia|]. rewrite IH. lia. Qed.

Lemma hlit_blk_len_app syms x : blk_len (syms ++ [x]) = blk_len syms + sym_len x.
Proof. unfold blk_len. rewrite map_app, hlit_sumZ_app. cbn [map HuffAbs.sumZ]. lia. Qed.

(** Port of rlit_ok (RTDLTCRleLit.v) to deflate_huff: match_length = 0. *)
Theorem hlit_ok : tally_spec2 -> hlit_stmt.
Proof.
  intros [Htl _] s HW He Ho Hq Hfn Hla.
  destruct HW as (Hp & Hws & Hpos & Hwin & Hh & Hm & _ & syms & Ht).
  set (s2 := set_d_match_length s 0).
  assert (Ewin : d_window s2 = d_window s) by (unfold s2; autorewrite with hproj; reflexivity).
  assert (Ess : d_strstart s2 = d_strstart s) by (unfold s2; autorewrite with hproj; reflexivity).
  assert (Etr : d_tr s2 = d_tr s) by (unfold s2; autorewrite with hproj; reflexivity).
  assert (Epbm : d_pbm s2 = d_pbm s) by (unfold s2; autorewrite with hproj; reflexivity).
  assert (Ela : d_lookahead s2 = d_lookahead s) by (unfold s2; autorewrite with hproj; reflexivity).
  assert (Hp0 := Hp). assert (Hlev := fn_of_huff s Hp Hfn).
  assert (Ha : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  assert (Hh' : d_matches s = 0 /\ chain_ok s).
  { unfold whash in Hh. destruct (Z.eqb_spec (d_level s) 0); [lia|exact Hh]. }
  destruct Hh' as [Hmat0 [G HG0]].
  destruct Hp as (Hwb & Hwsz & Hwm & Hhb & Hhs & Hhm & Hhsh & HL & Hpbs & Hob & Hpbm & Hse & Hlv & Hstr & Hmeth).
  destruct Hws as (Hwl & Hwok & Hwss & Hpl & Hhl).
  destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  destruct Ht as (Ht1 & HL2 & Hf & _ & Hb).
  assert (Hb' : blk_len syms = d_strstart s - d_block_start s) by (rewrite Hb by lia; lia).
  assert (He' : d_strstart s - d_block_start s <= Zlength syms).
  { specialize (He Hfn). destruct Ht1 as (_ & _ & T3 & _). unfold d_sym_next in He. rewrite T3 in He. lia. }
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
  unfold hlit. fold s2. rewrite Ewin, Ess, Hrdc. cbn [bind]. unfold c_dtally_lit, d_trm. rewrite Etr, Epbm, Etl.
  cbn [bind].
  assert (Hws15 : d_w_size s <= 32768).
  { rewrite Hwsz. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  eexists _, _, (syms ++ [(0, c)]). split; [reflexivity|].
  unfold set_d_trm. cbn [fst snd]. autorewrite with hproj. rewrite Ela, Ess.
  rewrite (hlit_u32_id (d_lookahead s - 1)) by lia. rewrite (hlit_u32_id (d_strstart s + 1)) by lia.
  set (s3 := set_d_strstart (set_d_lookahead (set_d_pbm (set_d_tr s2 t') m') (d_lookahead s - 1)) (d_strstart s + 1)).
  assert (S_win : d_window s3 = d_window s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_wsz : d_window_size s3 = d_window_size s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_ss : d_strstart s3 = d_strstart s + 1) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_la : d_lookahead s3 = d_lookahead s - 1) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_wsize : d_w_size s3 = d_w_size s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_wbits : d_w_bits s3 = d_w_bits s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_wmask : d_w_mask s3 = d_w_mask s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_hsize : d_hash_size s3 = d_hash_size s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_hbits : d_hash_bits s3 = d_hash_bits s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_hmask : d_hash_mask s3 = d_hash_mask s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_hshift : d_hash_shift s3 = d_hash_shift s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_bs : d_block_start s3 = d_block_start s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_ins : d_insert s3 = d_insert s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_hw : d_high_water s3 = d_high_water s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_pl : d_prev_length s3 = d_prev_length s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_ma : d_match_available s3 = d_match_available s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_ml : d_match_length s3 = 0) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_po : d_po s3 = d_po s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_status : d_status s3 = d_status s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_wrap : d_wrap s3 = d_wrap s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_gzh : d_gzhead s3 = d_gzhead s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_gzi : d_gzindex s3 = d_gzindex s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_lf : d_last_flush s3 = d_last_flush s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_meth : d_method s3 = d_method s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_pbs : d_pending_buf_size s3 = d_pending_buf_size s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_tr : d_tr s3 = t') by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_pbm : d_pbm s3 = m') by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_prev : d_prev s3 = d_prev s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
  assert (S_head : d_head s3 = d_head s) by (unfold s3, s2; autorewrite with hproj; reflexivity).
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
  assert (Hblk3 : blk_len (syms ++ [(0, c)]) = blk_len syms + 1) by (rewrite hlit_blk_len_app; reflexivity).
  assert (Hch : chain_ok s3).
  { exists G. assert (HG3 : chain_with s3 (d_strstart s + 1) (lim s) G).
    { destruct HG0 as (A & B & C). split; [intros v Hv; destruct (A v Hv); lia|].
      split; [rewrite S_hsize, S_head; exact B|].
      rewrite S_wmask, S_prev. exact C. }
    rewrite S_ss. apply (hlit_chain_mono _ _ _ _ _ HG3). unfold lim. rewrite S_ss, S_md.
    destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); destruct (Z.gtb_spec (d_strstart s + 1) (MAX_DIST s)); lia. }
  split; [|split; [|split]].
  - unfold HS0.
    split.
    { unfold prm. rewrite S_wbits, S_wsize, S_wmask, S_hbits, S_hsize, S_hmask, S_hshift, S_L, S_pbs, S_pbm,
        S_level, S_strat, S_meth, S_tr, G1, G2, F2. exact Hp0. }
    split.
    { unfold wstruct. rewrite S_win, S_wsz, S_wsize, S_prev, S_head, S_hsize.
      exact (conj Hwl (conj Hwok (conj Hwss (conj Hpl Hhl)))). }
    split.
    { unfold wpos. rewrite S_la, S_ss, S_wsz, S_bs, S_ins, S_wsize, S_hw, S_md.
      repeat split; lia. }
    split.
    { unfold wwin in *. rewrite S_ss, S_la, S_hw, S_win. intros i Hi. apply Hwin. lia. }
    split.
    { unfold whash in *. rewrite S_level. destruct (Z.eqb_spec (d_level s) 0) as [E|E]; [lia|].
      split; [|exact Hch]. rewrite S_mat. exact Hmat0. }
    split.
    { unfold wmatch in *. rewrite S_ml, S_pl, S_ma, Ha, S_ss, S_la, S_fn. rewrite Ha in Hm.
      destruct Hm as (M1 & M2 & _ & M4 & _).
      assert (E1 : MAX_MATCH = 258) by reflexivity; assert (E2 : MIN_MATCH = 3) by reflexivity.
      rewrite ?E1, ?E2 in *. split; [lia|]. split; [exact M2|]. split; [left; reflexivity|].
      split; [intros _; split; [lia|exact (proj2 (M4 eq_refl))]|]. intros E; discriminate E. }
    split; [rewrite S_tr, S_pbm; exact Ht'|].
    split; [rewrite Hlen3, S_L; lia|].
    split.
    { rewrite Esym. apply Forall_app. split; [exact Hf|]. constructor; [|constructor].
      unfold sym_ok, valid_sym. cbn [fst snd].
      split; [split; lia|]. split; [intros H; congruence|intros _ _ H; congruence]. }
    split; [rewrite Hblk3, S_ss, S_bs; lia|].
    split; [rewrite Hlen3, S_ss, S_bs; lia|].
    split.
    { apply (outok_grow s s3 Ho).
      - rewrite S_tr, S_pbm. exact (conj G1 (conj G2 (conj G3 G4))).
      - exact S_po.
      - exact S_pend.
      - exact S_pbs.
      - destruct Ho as (_ & Hbo & _). unfold bits_ok in *. rewrite S_tr, Fbv, Fbuf, Fpend. exact Hbo. }
    split; [unfold quiet in *; rewrite S_pend, S_po, S_bv; exact Hq|].
    rewrite S_fn; exact Hfn.
  - rewrite Hse, Hlen3, S_L.
    destruct (Z.eqb_spec (3 * Zlength syms + 3) (3 * (d_L s - 1))), (Z.eqb_spec (Zlength syms + 1) (d_L s - 1));
      auto; lia.
  - unfold hfr. split.
    { unfold same_prm. rewrite S_wbits, S_wsize, S_hbits, S_L, S_pbs, S_level, S_strat.
      repeat (split; [reflexivity|]); reflexivity. }
    split.
    { unfold api_eq. rewrite S_status, S_wrap, S_gzh, S_gzi, S_lf, S_meth.
      repeat (split; [reflexivity|]); reflexivity. }
    split; [unfold ub; rewrite S_ss, S_bs, S_la; lia|].
    intros tout. unfold Gb. rewrite S_pend, S_bv. reflexivity.
  - reflexivity.
Qed.
