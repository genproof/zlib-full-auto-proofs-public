(** * RT-D part FAST, piece: flit_stmt (statement and definitions: RTDFastKit.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFastKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma flit_syms_data_snoc out l x : F.syms_data out (l ++ [x]) = F.sym_data (F.syms_data out l) x.
Proof. unfold F.syms_data. apply fold_left_app. Qed.

Lemma flit_syms_rok_lit w out l c : syms_rok w out l -> 0 <= c < 256 -> syms_rok w out (l ++ [(0, c)]).
Proof.
  revert out. induction l as [|a l IH]; intros out H1 H2; cbn [app syms_rok] in *.
  - split; [exact H2|exact I].
  - destruct H1 as [Ha Hr]. split; [exact Ha|]. apply IH; assumption.
Qed.

Lemma flit_lim_mono s2 s3 :
  MAX_DIST s3 = MAX_DIST s2 -> d_strstart s3 = d_strstart s2 + 1 -> lim s2 <= lim s3.
Proof.
  intros E1 E2. unfold lim. rewrite E1, E2.
  destruct (Z.gtb_spec (d_strstart s2) (MAX_DIST s2)); destruct (Z.gtb_spec (d_strstart s2 + 1) (MAX_DIST s2)); lia.
Qed.

Lemma flit_chain_hok s2 s3 :
  d_hash_size s3 = d_hash_size s2 -> d_head s3 = d_head s2 -> d_prev s3 = d_prev s2 -> d_w_mask s3 = d_w_mask s2 ->
  d_window s3 = d_window s2 -> d_hash_shift s3 = d_hash_shift s2 -> d_hash_mask s3 = d_hash_mask s2 ->
  d_strstart s3 + d_lookahead s3 = d_strstart s2 + d_lookahead s2 -> lim s2 <= lim s3 ->
  chain_hok s2 -> chain_hok s3.
Proof.
  intros E1 E2 E3 E4 E5 E6 E7 E8 Hl H b Hb. rewrite E1 in Hb. destruct (H b Hb) as (Gb & G0 & G1).
  exists Gb. rewrite E2. split; [exact G0|]. intros q Gq Hq Hlq.
  destruct (G1 q Gq Hq ltac:(lia)) as (A & B & C). rewrite E8, E4, E3. split; [exact A|]. split; [|exact C].
  rewrite <- B. unfold h3, update_hash. rewrite E5, E6, E7. reflexivity.
Qed.

Lemma flit_primed s2 s3 p :
  d_ins_h s3 = d_ins_h s2 -> d_window s3 = d_window s2 -> d_hash_shift s3 = d_hash_shift s2 ->
  d_hash_mask s3 = d_hash_mask s2 -> primed s2 p -> primed s3 p.
Proof.
  intros E1 E2 E3 E4 [h0 H]. exists h0. unfold update_hash in *. rewrite E1, E2, E3, E4. exact H.
Qed.

Ltac flit_field Hk f E := assert (E := f_equal f Hk); unfold sr_keep, hc_keep in E; autorewrite with fproj in E.

Theorem flit_ok : flit_stmt.
Proof.
  intros s s2 s3 bf dict D BS syms Htl2 HW Ho Hq Hfn Hrd Hla HSR Hml Hdict HD Hk0 Hch2 Hpr2 Hflit.
  destruct (lit_ok2 Htl2 s s2 HW Ho Hq Hfn Hrd Hla HSR Hml) as (s3' & bf' & syms3 & Ef & HTS & _ & _).
  rewrite Hflit in Ef. injection Ef as E1 E2. subst s3' bf'.
  destruct Htl2 as [Htl _].
  destruct HSR as (Hk & Hws2 & _ & _ & _).
  destruct Hk0 as ((Kw & Km & (Kt & KL & _) & Kb & Ke & Kr & Kd) & (Kh1 & Kh2)).
  destruct HW as (Hp & Hws & Hpos & Hwin & Hh & Hm & _ & _ & _).
  flit_field Hk d_window Ewin. flit_field Hk d_window_size Ewsz. flit_field Hk d_strstart Ess.
  flit_field Hk d_lookahead Ela. flit_field Hk d_tr Etr. flit_field Hk d_pbm Epbm.
  assert (Hlev := fn_of_fast s Hp Hfn).
  destruct Hp as (Hwb & Hwsz & Hwm & Hhb & Hhs & Hhm & Hhsh & HL & Hpbs & Hob & Hpbm & Hse & Hlv & Hstr & Hmeth).
  destruct Hws as (Hwl & Hwok & Hwss & Hpl & Hhl).
  destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  assert (HL15 : d_L s <= 32768).
  { rewrite HL. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hrdc : mb_rd (d_window s) (d_strstart s) = Some (Znth (d_strstart s) (mb_val (d_window s)))).
  { unfold mb_rd. rewrite (Hwin (d_strstart s)) by lia. unfold in_range.
    replace ((0 <=? d_strstart s) && (d_strstart s <? Zlength (mb_val (d_window s)))) with true by lia.
    reflexivity. }
  set (c := Znth (d_strstart s) (mb_val (d_window s))) in *.
  assert (Hc : 0 <= c < 256).
  { destruct Hwok as [_ Hok]. apply Hok; [lia|]. apply Hwin. lia. }
  destruct (Htl (d_tr s) (d_pbm s) syms c Kt KL HL15 Hc) as (t' & m' & Etl & Ht' & Hfr).
  unfold flit in Hflit. rewrite Ewin, Ess, Hrdc in Hflit. cbn [bind] in Hflit.
  unfold c_dtally_lit, d_trm in Hflit. rewrite Etr, Epbm, Etl in Hflit. cbn [bind] in Hflit.
  unfold set_d_trm in Hflit. cbn [fst snd] in Hflit. injection Hflit as Es3 Ebf.
  assert (Hws15 : d_w_size s <= 32768).
  { rewrite Hwsz. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  autorewrite with fproj in Es3. rewrite Ela, Ess in Es3.
  rewrite (lit_u32_id (d_lookahead s - 1)) in Es3 by lia. rewrite (lit_u32_id (d_strstart s + 1)) in Es3 by lia.
  flit_field Hk d_w_size Ewsize. flit_field Hk d_w_bits Ewbits.
  flit_field Hk d_block_start Ebs. flit_field Hk d_insert Eins.
  subst s3.
  set (s3 := set_d_strstart (set_d_lookahead (set_d_pbm (set_d_tr s2 t') m') (d_lookahead s - 1)) (d_strstart s + 1)) in *.
  assert (S_win : d_window s3 = d_window s2) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_ss : d_strstart s3 = d_strstart s + 1) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_la : d_lookahead s3 = d_lookahead s - 1) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_wsize : d_w_size s3 = d_w_size s) by (unfold s3; autorewrite with fproj; exact Ewsize).
  assert (S_wbits : d_w_bits s3 = d_w_bits s) by (unfold s3; autorewrite with fproj; exact Ewbits).
  assert (S_wmask : d_w_mask s3 = d_w_mask s2) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_hsize : d_hash_size s3 = d_hash_size s2) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_hmask : d_hash_mask s3 = d_hash_mask s2) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_hshift : d_hash_shift s3 = d_hash_shift s2) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_bs : d_block_start s3 = d_block_start s) by (unfold s3; autorewrite with fproj; exact Ebs).
  assert (S_ins : d_insert s3 = d_insert s) by (unfold s3; autorewrite with fproj; exact Eins).
  assert (S_insh : d_ins_h s3 = d_ins_h s2) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_tr : d_tr s3 = t') by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_pbm : d_pbm s3 = m') by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_prev : d_prev s3 = d_prev s2) by (unfold s3; autorewrite with fproj; reflexivity).
  assert (S_head : d_head s3 = d_head s2) by (unfold s3; autorewrite with fproj; reflexivity).
  clearbody s3.
  destruct Hfr as (Fcfg & Fmat & Fpend & Fbuf & Fbv & Fbu & Fgrow).
  unfold tr_cfg in Fcfg. injection Fcfg as F1 F2 F3 F4.
  assert (S_level : d_level s3 = d_level s) by (unfold d_level; rewrite S_tr; exact F3).
  assert (S_strat : d_strategy s3 = d_strategy s) by (unfold d_strategy; rewrite S_tr; exact F4).
  assert (S_fn : fn_of s3 = fn_of s) by (unfold fn_of; rewrite S_level, S_strat; reflexivity).
  assert (S_md : MAX_DIST s3 = MAX_DIST s2) by (unfold MAX_DIST; rewrite S_wsize, Ewsize; reflexivity).
  assert (Esyms : syms3 = syms ++ [(0, c)]).
  { destruct HTS as ((_ & _ & _ & _ & _ & _ & Tt & _) & _). rewrite S_tr, S_pbm in Tt.
    exact (tree_ok_uniq _ _ _ _ Tt Ht'). }
  subst syms3. exists (syms ++ [(0, c)]). split; [exact HTS|]. split.
  - destruct Kw as [Kw1 Kw2].
    assert (Hsum : d_strstart s3 + d_lookahead s3 = d_strstart s + d_lookahead s) by lia.
    unfold kt. cbv zeta. rewrite Hsum, S_bs, S_wbits, S_ss.
    split; [unfold kwin; rewrite Hsum, S_win, Ewin; exact (conj Kw1 Kw2)|].
    split; [exact Kb|]. split; [exact Ke|]. split; [exact (flit_syms_rok_lit _ _ _ _ Kr Hc)|].
    split.
    + rewrite map_app. cbn [map]. rewrite flit_syms_data_snoc, Kd.
      assert (Ha : d_match_available s = 0).
      { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
      rewrite Ha, Z.sub_0_r. unfold fsym. cbn [fst snd Z.eqb]. unfold F.sym_data.
      set (H := dict ++ D) in *.
      assert (Ec : c = Znth (Zlength H - (d_strstart s + d_lookahead s) + d_strstart s) H).
      { unfold c. rewrite Kw2 by lia. reflexivity. }
      rewrite Ec. rewrite <- (sublist_last_1 0 _ H) by lia. f_equal. lia.
    + split.
      * rewrite S_level. destruct (Z.eqb_spec (d_level s) 0) as [E|E]; [lia|].
        apply (flit_chain_hok s2 s3); try assumption.
        -- rewrite Ess, Ela. lia.
        -- apply flit_lim_mono; [exact S_md|rewrite S_ss, Ess; reflexivity].
      * intros _ H3. rewrite S_la in H3. rewrite S_ins.
        destruct (Kh2 (or_introl Hfn) ltac:(lia)) as [I0 _]. split; [exact I0|].
        rewrite S_ss. apply (flit_primed s2 s3); try assumption. apply Hpr2. lia.
  - unfold bibits, d_bi_valid. rewrite S_tr, Fbuf, Fbv. reflexivity.
Qed.
