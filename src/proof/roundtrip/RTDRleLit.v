(* RT-D part RLE: the literal branch (flit) (statement: RTDRleKit.v; model on RTDLTCRleLit.rlit_ok). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDRleKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma rflit_sublist_snoc (H : list Z) n : 0 <= n < Zlength H ->
  sublist 0 (n + 1) H = sublist 0 n H ++ [Znth n H].
Proof.
  intros Hn. rewrite (sublist_split 0 n (n + 1)) by lia. f_equal. apply sublist_len_1. lia.
Qed.

Lemma rflit_rkt dict D BS syms s s3 c :
  rkt dict D BS syms s ->
  d_window s3 = d_window s -> d_strstart s3 = d_strstart s + 1 -> d_lookahead s3 = d_lookahead s - 1 ->
  d_w_bits s3 = d_w_bits s -> d_block_start s3 = d_block_start s -> d_hash_size s3 = d_hash_size s ->
  d_head s3 = d_head s -> d_w_mask s3 = d_w_mask s -> d_prev s3 = d_prev s ->
  d_hash_shift s3 = d_hash_shift s -> d_hash_mask s3 = d_hash_mask s -> MAX_DIST s3 = MAX_DIST s ->
  c = Znth (d_strstart s) (mb_val (d_window s)) -> 0 <= c < 256 -> 1 <= d_lookahead s -> 0 <= d_strstart s ->
  rkt dict D BS (syms ++ [(0, c)]) s3.
Proof.
  intros (K1 & K2 & K3 & K4 & K5 & K6) S_win S_ss S_la S_wbits S_bs S_hsize S_head S_wmask S_prev
    S_hshift S_hmask S_md Ec Hc Hla Hss.
  unfold rkt in *. cbv zeta in *.
  assert (Ewl : d_strstart s3 + d_lookahead s3 = d_strstart s + d_lookahead s) by lia.
  rewrite Ewl, S_wbits, S_bs, S_ss.
  set (H := dict ++ D) in *.
  set (off := Zlength H - (d_strstart s + d_lookahead s)) in *.
  destruct K1 as [Kl Kw].
  assert (Ec' : c = Znth (off + d_strstart s) H).
  { rewrite Ec, Kw by lia. f_equal; unfold off; lia. }
  split; [|split; [exact K2|split; [exact K3|split; [|split]]]].
  - unfold kwin. rewrite Ewl, S_win. split; [exact Kl|]. exact Kw.
  - apply rk_syms_rok_app. split; [exact K4|]. rewrite K5. cbn [syms_rok fst snd]. split; [|exact I].
    cbn. lia.
  - rewrite rk_syms_data_app, K5. cbn [map]. unfold F.syms_data. cbn [fold_left].
    unfold fsym. cbn [fst snd Z.eqb]. unfold F.sym_data. rewrite Ec'.
    replace (off + (d_strstart s + 1)) with (off + d_strstart s + 1) by lia.
    rewrite rflit_sublist_snoc by (unfold off; lia). reflexivity.
  - unfold chain_hok in *. intros b Hb. rewrite S_hsize in Hb. destruct (K6 b Hb) as (Gc & G0 & GC).
    exists Gc. rewrite S_head. split; [exact G0|]. intros q Gq q0 ql.
    assert (Hlim : lim s <= lim s3).
    { unfold lim. rewrite S_ss, S_md.
      destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); destruct (Z.gtb_spec (d_strstart s + 1) (MAX_DIST s)); lia. }
    destruct (GC q Gq q0 ltac:(lia)) as (A & B & C).
    rewrite Ewl, S_wmask, S_prev. split; [exact A|]. split; [|exact C].
    rewrite <- B. unfold h3, update_hash. rewrite S_win, S_hshift, S_hmask. reflexivity.
Qed.

Theorem rflit_ok : tally_spec2 -> rflit_stmt.
Proof.
  intros Htally s ml s3 bf dict D BS syms HW Ho Hq Hfn Hrd Hla Hml Hdict HD Hwt Hk Hrun.
  destruct (rlit_ok Htally s ml HW Ho Hq Hfn Hrd Hla Hml) as (s3' & bf' & syms3 & E & HR & _ & _).
  rewrite Hrun in E. injection E as <- <-.
  destruct Htally as [Htl _].
  destruct HW as (Hp & Hws & Hpos & Hwin & _ & _ & _ & _).
  destruct Hp as (Hwb & Hwsz & Hwm & Hhb & Hhs & Hhm & Hhsh & HL & Hpbs & Hob & Hpbm & Hse & Hlv & Hstr & Hmeth).
  destruct Hws as (Hwl & Hwok & Hwss & Hpl & Hhl).
  destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  destruct Hwt as (Ht1 & HL2 & _).
  set (s2 := set_d_match_length s ml) in *.
  assert (Ewin : d_window s2 = d_window s) by (unfold s2; autorewrite with fproj; reflexivity).
  assert (Ess : d_strstart s2 = d_strstart s) by (unfold s2; autorewrite with fproj; reflexivity).
  assert (Etr : d_tr s2 = d_tr s) by (unfold s2; autorewrite with fproj; reflexivity).
  assert (Epbm : d_pbm s2 = d_pbm s) by (unfold s2; autorewrite with fproj; reflexivity).
  assert (Ela : d_lookahead s2 = d_lookahead s) by (unfold s2; autorewrite with fproj; reflexivity).
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
  assert (Hss1 : d_strstart s + 1 < d_window_size s).
  { assert (E : MIN_LOOKAHEAD = 262) by reflexivity. unfold rready, MAX_DIST in Hrd. rewrite E in Hrd.
    assert (E2 : MAX_MATCH = 258) by reflexivity. rewrite E2 in Hrd.
    destruct Hrd as [R|[R _]]; lia. }
  assert (Hws15 : d_w_size s <= 32768).
  { rewrite Hwsz. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  unfold flit in Hrun. rewrite Ewin, Ess, Hrdc in Hrun. cbn [bind] in Hrun.
  unfold c_dtally_lit, d_trm in Hrun. rewrite Etr, Epbm, Etl in Hrun. cbn [bind] in Hrun.
  unfold set_d_trm in Hrun. cbn [fst snd] in Hrun. autorewrite with fproj in Hrun. rewrite Ela, Ess in Hrun.
  rewrite (rlit_u32_id (d_lookahead s - 1)) in Hrun by lia.
  rewrite (rlit_u32_id (d_strstart s + 1)) in Hrun by lia.
  injection Hrun as Es3 _.
  assert (S_win : d_window s3 = d_window s) by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_ss : d_strstart s3 = d_strstart s + 1) by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_la : d_lookahead s3 = d_lookahead s - 1) by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_wsize : d_w_size s3 = d_w_size s) by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_wbits : d_w_bits s3 = d_w_bits s) by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_wmask : d_w_mask s3 = d_w_mask s) by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_hsize : d_hash_size s3 = d_hash_size s) by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_hmask : d_hash_mask s3 = d_hash_mask s) by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_hshift : d_hash_shift s3 = d_hash_shift s) by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_bs : d_block_start s3 = d_block_start s) by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_tr : d_tr s3 = t') by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_pbm : d_pbm s3 = m') by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_prev : d_prev s3 = d_prev s) by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_head : d_head s3 = d_head s) by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_po : d_po s3 = d_po s) by (rewrite <- Es3; unfold s2; autorewrite with fproj; reflexivity).
  assert (S_md : MAX_DIST s3 = MAX_DIST s) by (unfold MAX_DIST; rewrite S_wsize; reflexivity).
  destruct Hfr as (Fcfg & Fmat & Fpend & Fbuf & Fbv & Fbu & Fgrow).
  assert (S_pend : d_pending s3 = d_pending s) by (unfold d_pending; rewrite S_tr; exact Fpend).
  assert (S_bv : d_bi_valid s3 = d_bi_valid s) by (unfold d_bi_valid; rewrite S_tr; exact Fbv).
  assert (Esy : syms3 = syms ++ [(0, c)]).
  { destruct HR as ((_ & _ & _ & _ & _ & _ & T3 & _) & _). rewrite S_tr, S_pbm in T3.
    exact (rk_tree_ok_uniq _ _ _ _ T3 Ht'). }
  subst syms3. exists (syms ++ [(0, c)]). split; [exact HR|]. split; [|split].
  - exact (rflit_rkt dict D BS syms s s3 c Hk S_win S_ss S_la S_wbits S_bs S_hsize S_head S_wmask S_prev
      S_hshift S_hmask S_md ltac:(reflexivity) Hc ltac:(lia) ltac:(lia)).
  - unfold bibits. rewrite S_tr, Fbuf, S_bv. reflexivity.
  - destruct Hq as (Hq1 & _). unfold pend. rewrite S_pend, Hq1, !Z.add_0_r, !sublist_nil. reflexivity.
Qed.
