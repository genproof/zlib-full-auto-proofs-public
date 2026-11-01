(* RT-D part SLOW: the functional part fmatch_part of deflate_slow (statement: RTDSlowKit.v).
   The proof follows the safety proof RTDLTCSlowMatch.match_ok step by step and adds the functional facts:
   the symbol Ref prev_length dist expands (overlapping copy) to the bytes kmatch3 vouches for, the insertion
   loop keeps the chains hash-consistent and ins_h primed (RTDSlMatchLoop.v), FLUSH_BLOCK (RTDSlMatchFbo.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSlowKit.
Require Import Zlib.proof.roundtrip.RTDSlMatchLoop Zlib.proof.roundtrip.RTDSlMatchFbo.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Lists *)

(* the overlapping copy of n bytes at distance d after the first q bytes of H *)
Lemma fm_lz_copy (H : list Z) d : forall n q,
  1 <= d <= q -> q + Z.of_nat n <= Zlength H ->
  (forall i, 0 <= i < Z.of_nat n -> Znth (q - d + i) H = Znth (q + i) H) ->
  F.lz_copy n d (sublist 0 q H) = sublist 0 (q + Z.of_nat n) H.
Proof.
  induction n as [|n IH]; intros q Hd Hl Hi.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - cbn [F.lz_copy].
    rewrite Nat2Z.inj_succ in Hl, Hi.
    assert (Hz : Zlength (sublist 0 q H) = q) by (rewrite Zlength_sublist by lia; lia).
    rewrite Hz, Znth_sublist by lia. rewrite Z.add_0_r.
    rewrite <- (Z.add_0_r (q - d)), Hi, Z.add_0_r by lia.
    rewrite <- sublist_last_1 by lia.
    rewrite IH by (try lia; intros i Hi'; replace (q + 1 - d + i) with (q - d + (i + 1)) by lia;
                   replace (q + 1 + i) with (q + (i + 1)) by lia; apply Hi; lia).
    f_equal. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma fm_sym_bytes_inj : forall l1 l2, Zlength l1 = Zlength l2 -> sym_bytes l1 = sym_bytes l2 -> l1 = l2.
Proof.
  induction l1 as [|[a b] l1 IH]; intros [|[c d] l2] L E.
  - reflexivity.
  - rewrite Zlength_nil, Zlength_cons in L. pose proof (Zlength_nonneg l2). lia.
  - rewrite Zlength_nil, Zlength_cons in L. pose proof (Zlength_nonneg l1). lia.
  - rewrite !sym_bytes_cons in E. cbn [fst snd] in E. injection E as E1 E2 E3 E4.
    rewrite !Zlength_cons in L.
    rewrite (IH l2) by (auto; lia).
    assert (a = c).
    { change (a / 256 = c / 256) in E2. rewrite (Z_div_mod_eq_full a 256), (Z_div_mod_eq_full c 256), E1, E2. reflexivity. }
    subst. reflexivity.
Qed.

Lemma fm_tree_ok_uniq t m s1 s2 : tree_ok t m s1 -> tree_ok t m s2 -> s1 = s2.
Proof.
  intros (_ & _ & N1 & _ & B1 & _) (_ & _ & N2 & _ & B2 & _).
  assert (L : Zlength s1 = Zlength s2) by lia.
  apply fm_sym_bytes_inj; [exact L|]. rewrite <- B1, <- B2, L. reflexivity.
Qed.

Lemma fm_syms_data_app out a b :
  F.syms_data out (map fsym (a ++ b)) = F.syms_data (F.syms_data out (map fsym a)) (map fsym b).
Proof. unfold F.syms_data. rewrite map_app, fold_left_app. reflexivity. Qed.

Lemma fm_syms_rok_app wmax : forall a out b,
  syms_rok wmax out (a ++ b) <-> syms_rok wmax out a /\ syms_rok wmax (F.syms_data out (map fsym a)) b.
Proof.
  induction a as [|x a IH]; intros out b.
  - cbn. tauto.
  - cbn [app syms_rok map]. rewrite IH. unfold F.syms_data. cbn [fold_left]. tauto.
Qed.

(** ** Chains *)
Lemma fm_chain_hokS_mono x y S :
  d_hash_size y = d_hash_size x -> d_head y = d_head x -> d_w_mask y = d_w_mask x -> d_prev y = d_prev x ->
  d_window y = d_window x -> d_hash_shift y = d_hash_shift x -> d_hash_mask y = d_hash_mask x ->
  lim x <= lim y -> chain_hokS x S -> chain_hokS y S.
Proof.
  intros E1 E2 E3 E4 E5 E6 E7 Hl H b Hb. rewrite E1 in Hb. destruct (H b Hb) as (G & G0 & GS).
  exists G. rewrite E2. split; [exact G0|]. intros q Gq q0 ql.
  destruct (GS q Gq q0 ltac:(lia)) as (A & B & C). split; [exact A|]. split.
  - unfold h3, update_hash in *. rewrite E5, E6, E7. exact B.
  - rewrite E3, E4. exact C.
Qed.

Lemma fm_primed x y p :
  d_ins_h y = d_ins_h x -> d_window y = d_window x -> d_hash_shift y = d_hash_shift x ->
  d_hash_mask y = d_hash_mask x -> primed x p -> primed y p.
Proof.
  intros E1 E2 E3 E4 (h0 & H). exists h0. unfold update_hash in *. rewrite E1, E2, E3, E4. exact H.
Qed.

(** ** Results *)
Lemma fm_FI_FQ dict D BS p s0 z0 s z bs :
  FI dict D BS p s0 z0 s z -> fin_bs bs = false -> FQ dict D BS p s0 z0 s z bs.
Proof.
  intros (k & x & BS' & syms & A & B & C) Hf. exists k, x, BS', syms.
  rewrite Hf. split; [exact A|]. split; [exact B|]. split; [exact C|]. intros E; discriminate E.
Qed.

(** ** The part *)
Theorem fmatch_ok : fmatch_part.
Proof.
  intros dict D BS p s0 z0 flush s z evs s1 r Hs HfS HSI Hrdy Hmid Hfm HG HFI HP3 HmlP E.
  pose proof Hs as (Hfill & Hins & Hlm & Htally & Hfbo & Hfp).
  pose proof HfS as (Ffill & Fins & Flm & Ffp & Ffbo).
  destruct Hfm as (Fch1 & Fpr1 & _).
  destruct HFI as (k & x & BS' & syms0 & Hzs & Hk3 & Hbits).
  unfold kcore3, kdata3 in Hk3. cbv zeta in Hk3.
  set (HH := dict ++ (D ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0))) in *.
  destruct Hk3 as ((K1 & K2 & K3 & K4 & K5 & K6 & K7) & (Kh1 & Kh2)).
  revert E.
  pose proof HSI as (HW2 & Hq & HL & HEI).
  pose proof HW2 as ((Hprm & Hwst & Hwpos & Hwwin & Hwh & Hwm & Hl0 & syms & Hwt) & Hse).
  destruct Hmid as (Hpk & Hwst1 & (G1 & Hch1) & Epl1 & Epm1 & Hml1 & Hml1').
  destruct Hwm as (M1 & M2 & M3 & M4 & M5).
  assert (Hav : d_match_available s = 1).
  { destruct M3 as [M3|M3]; [|exact M3]. destruct (M4 M3). lia. }
  destruct (M5 Hav) as (Hfn & HS1 & Hcand).
  destruct (Hcand ltac:(clear - HP3 Epl1; lia)) as (HPla & Hdist & Htoo).
  assert (Es1 : d_strstart s1 = d_strstart s) by exact (f_equal d_strstart Hpk).
  assert (Ela1 : d_lookahead s1 = d_lookahead s) by exact (f_equal d_lookahead Hpk).
  assert (Etr1 : d_tr s1 = d_tr s) by exact (f_equal d_tr Hpk).
  assert (Epbm1 : d_pbm s1 = d_pbm s) by exact (f_equal d_pbm Hpk).
  assert (Ews1 : d_w_size s1 = d_w_size s) by exact (f_equal d_w_size Hpk).
  assert (Hprm1 : prm (pre_keep s1)) by (rewrite Hpk; exact Hprm).
  change (prm s1) in Hprm1.
  pose proof Hprm as (Pwb & Pws & Pwm & Phb & Phs & Phm & Phsh & PL & Ppbs & Pob & Ppbm & Pse & Plv & Pst & Pme).
  assert (HLb : 128 <= d_L s <= 32768).
  { rewrite PL. split.
    - change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia.
    - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (HWb : 512 <= d_w_size s <= 32768).
  { rewrite Pws. split.
    - change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia.
    - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  destruct Hwt as (T1 & T2 & T3 & T4 & T5).
  assert (Esy : syms0 = syms) by exact (fm_tree_ok_uniq _ _ _ _ (proj1 K3) T1). subst syms0.
  assert (Hlv : d_level s <> 0).
  { intros E. unfold fn_of in Hfn. rewrite E in Hfn. cbn in Hfn. discriminate. }
  specialize (T5 Hlv). rewrite Hav in T5.
  set (P := d_prev_length s1) in *.
  assert (HPb : 3 <= P <= 258) by (clear - HP3 Epl1 M1; unfold MIN_MATCH, MAX_MATCH in *; lia).
  set (dist := u32 (d_strstart s1 - 1 - d_prev_match s1)).
  assert (Edist : dist = u32 (d_strstart s - 1 - d_match_start s)) by (unfold dist; rewrite Es1, Epm1; reflexivity).
  destruct (K2 Hav ltac:(rewrite <- Epl1; exact HP3)) as (Kd & Kq).
  rewrite <- Edist in Kd, Kq. rewrite <- Epl1 in Kq. fold P in Kq.
  assert (Hlen : u32 (P - MIN_MATCH) = P - 3) by (apply u32_small; clear - HPb; unfold MIN_MATCH; lia).
  destruct (proj2 Htally (d_tr s1) (d_pbm s1) syms dist (u32 (P - MIN_MATCH)))
    as (t' & m' & Et & Ht' & Hfr).
  { rewrite Etr1, Epbm1. exact T1. }
  { rewrite Etr1. exact T2. }
  { rewrite Etr1. clear - HLb. unfold d_L in HLb. lia. }
  { rewrite Edist. clear - Hdist HWb. unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hdist. lia. }
  { rewrite Hlen. clear - HPb. lia. }
  unfold dsl_match. change (d_prev_length s1) with P. change (u32 (d_strstart s1 - 1 - d_prev_match s1)) with dist.
  unfold c_dtally_dist at 1. unfold d_trm at 1. rewrite Et. cbn [bind].
  change (d_lookahead (set_d_trm s1 (t', m'))) with (d_lookahead s1).
  change (d_prev_length (set_d_trm s1 (t', m'))) with P.
  rewrite Ela1, (u32_small (P - 1)) by (clear - HPb; lia).
  assert (HSw : d_strstart s + 262 <= d_window_size s /\ d_window_size s = 2 * d_w_size s).
  { destruct Hrdy as (_ & R2 & _). destruct Hwst as (_ & _ & R3 & _). clear - R2 R3. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in R2. lia. }
  destruct Hwpos as (Wp1 & Wp2 & Wp3 & Wp4 & Wp5 & Wp6 & Wp7 & Wp8 & Wp9).
  rewrite (u32_small (d_lookahead s - (P - 1))) by (clear - HPb HPla Epl1 Wp1 Wp2 Wp3 HSw HWb; lia).
  change (d_prev_length (set_d_lookahead (set_d_trm s1 (t', m')) (d_lookahead s - (P - 1)))) with P.
  rewrite (u32_small (P - 2)) by (clear - HPb; lia).
  rewrite Es1, (u32_small (d_strstart s + d_lookahead s - MIN_MATCH))
    by (clear - HPb HPla Epl1 HS1 Wp1 Wp3 HSw HWb; unfold MIN_MATCH; lia).
  set (b := set_d_prev_length (set_d_lookahead (set_d_trm s1 (t', m')) (d_lookahead s - (P - 1))) (P - 2)).
  destruct Hfr as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (Hprmb : prm b).
  { pose proof F7 as (G1' & G2' & _). exact (prm_tally s1 t' m' Hprm1 F1 G1' G2'). }
  assert (Ewin1 : d_window s1 = d_window s) by exact (f_equal d_window Hpk).
  destruct (ins_loop_ok Hins b (d_strstart s + d_lookahead s - MIN_MATCH) (lim s) G1 Hprmb Hwst1)
    as (a & Eloop & Hka & Hsa & Hpla & Hwsa & Ga & Hcha).
  { change (chain_with s1 (d_strstart s1 + 1) (lim s) G1). rewrite Es1. exact Hch1. }
  { change (1 <= P - 2). clear - HPb. lia. }
  { change (0 <= d_strstart s1). clear - Es1 HS1. lia. }
  { change (d_strstart s1 + (P - 2) < 65536). clear - Es1 HPb HSw HWb. lia. }
  { change (forall p, d_strstart s1 < p <= d_strstart s + d_lookahead s - MIN_MATCH -> p <= d_strstart s1 + (P - 2) ->
      p + 2 < Zlength (mb_val (d_window s1)) /\ Znth (p + 2) (mb_def (d_window s1)) = true /\
      p - d_w_size s1 < lim s).
    rewrite Es1, Ewin1, Ews1. intros pp Hp1 Hp2.
    destruct Hwst as (Q1 & _). split; [|split].
    - clear - Hp1 Hp2 Q1 HSw Wp3. unfold MIN_MATCH in Hp1. lia.
    - apply Hwwin. clear - Hp1 Hp2 Wp2 Wp3. unfold MIN_MATCH in Hp1. lia.
    - unfold lim, MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH.
      destruct (Z.gtb_spec (d_strstart s) (d_w_size s - (258 + 3 + 1))); clear - Hp2 HPb H; lia. }
  assert (Hsb : d_strstart s - d_block_start s <= 8453629).
  { pose proof (blk_len_bound syms (proj1 (proj2 (proj2 (proj2 T1))))) as Hb.
    clear - Hb T5 T2 HLb. lia. }
  assert (E1bs : d_block_start s1 = d_block_start s) by exact (f_equal d_block_start Hpk).
  assert (E1ins : d_insert s1 = d_insert s) by exact (f_equal d_insert Hpk).
  assert (E1hw : d_high_water s1 = d_high_water s) by exact (f_equal d_high_water Hpk).
  assert (E1wsz : d_window_size s1 = d_window_size s) by exact (f_equal d_window_size Hpk).
  destruct (ins_loop_fok Hins Fins b (d_strstart s + d_lookahead s - MIN_MATCH) (lim s) G1
              (d_strstart s + d_lookahead s) a Hprmb Hwst1) as (Fcha & Fpra).
  { change (chain_with s1 (d_strstart s1 + 1) (lim s) G1). rewrite Es1. exact Hch1. }
  { change (1 <= P - 2). clear - HPb. lia. }
  { change (0 <= d_strstart s1). clear - Es1 HS1. lia. }
  { change (d_strstart s1 + (P - 2) < 65536). clear - Es1 HPb HSw HWb. lia. }
  { change (forall p, d_strstart s1 < p <= d_strstart s + d_lookahead s - MIN_MATCH -> p <= d_strstart s1 + (P - 2) ->
      p + 2 < Zlength (mb_val (d_window s1)) /\ Znth (p + 2) (mb_def (d_window s1)) = true /\
      p - d_w_size s1 < lim s).
    rewrite Es1, Ewin1, Ews1. intros pp Hp1 Hp2.
    destruct Hwst as (Q1 & _). split; [|split].
    - clear - Hp1 Hp2 Q1 HSw Wp3. unfold MIN_MATCH in Hp1. lia.
    - apply Hwwin. clear - Hp1 Hp2 Wp2 Wp3. unfold MIN_MATCH in Hp1. lia.
    - unfold lim, MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH.
      destruct (Z.gtb_spec (d_strstart s) (d_w_size s - (258 + 3 + 1))); clear - Hp2 HPb H; lia. }
  { change (lim s <= lim s1). unfold lim, MAX_DIST. rewrite Es1, Ews1. lia. }
  { unfold MIN_MATCH. lia. }
  { intros pp Hp1. change (d_strstart s1 <= pp <= d_strstart s1 + (P - 2)) in Hp1. rewrite Es1 in Hp1.
    unfold b, wpos, MAX_DIST. dsimp. rewrite E1bs, E1ins, E1hw, E1wsz, Ews1.
    clear - Hp1 HPb HPla Epl1 Wp1 Wp2 Wp3 Wp4 Wp6 Wp7 Wp8 Wp9 Hsb.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [intros Hn; specialize (Wp6 Hn); unfold MAX_DIST in Wp6; lia|]. lia. }
  { pose proof (proj1 (chain_hokS_iff s1) Fch1) as Fch1'. rewrite Es1, Ela1 in Fch1'.
    apply (fm_chain_hokS_mono s1 b _); try reflexivity; exact Fch1'. }
  { intros Hle. change (d_strstart s1 + 1 <= d_strstart s + d_lookahead s - MIN_MATCH) in Hle.
    change (primed b (d_strstart s1 + 1)). rewrite Es1 in Hle |- *.
    apply (fm_primed s1 b); try reflexivity. apply Fpr1. clear - Hle. unfold MIN_MATCH in *. lia. }
  { exact Eloop. }
  rewrite Eloop. cbn [bind].
  clear Hml1' M5 Hcand M4.
  change (d_strstart (set_d_match_length (set_d_match_available a 0) (MIN_MATCH - 1))) with (d_strstart a).
  assert (Hsa' : d_strstart a = d_strstart s + P - 2).
  { rewrite Hsa. change (d_strstart s1 + (P - 2) = d_strstart s + P - 2). rewrite Es1. lia. }
  rewrite Hsa', (u32_small (d_strstart s + P - 2 + 1)) by (clear - HPb HSw HWb Wp2; lia).
  remember (set_d_strstart (set_d_match_length (set_d_match_available a 0) (MIN_MATCH - 1))
               (d_strstart s + P - 2 + 1)) as s5 eqn:Hs5.
  unfold b in Hka.
  assert (E5win : d_window s5 = d_window s) by f5 d_window Hka Hpk Hs5.
  assert (E5wsz : d_window_size s5 = d_window_size s) by f5 d_window_size Hka Hpk Hs5.
  assert (E5w : d_w_size s5 = d_w_size s) by f5 d_w_size Hka Hpk Hs5.
  assert (E5wb : d_w_bits s5 = d_w_bits s) by f5 d_w_bits Hka Hpk Hs5.
  assert (E5hb : d_hash_bits s5 = d_hash_bits s) by f5 d_hash_bits Hka Hpk Hs5.
  assert (E5bs : d_block_start s5 = d_block_start s) by f5 d_block_start Hka Hpk Hs5.
  assert (E5ins : d_insert s5 = d_insert s) by f5 d_insert Hka Hpk Hs5.
  assert (E5hw : d_high_water s5 = d_high_water s) by f5 d_high_water Hka Hpk Hs5.
  assert (E5po : d_po s5 = d_po s) by f5 d_po Hka Hpk Hs5.
  assert (E5pbs : d_pending_buf_size s5 = d_pending_buf_size s) by f5 d_pending_buf_size Hka Hpk Hs5.
  assert (E5st : d_status s5 = d_status s) by f5 d_status Hka Hpk Hs5.
  assert (E5wr : d_wrap s5 = d_wrap s) by f5 d_wrap Hka Hpk Hs5.
  assert (E5gz : d_gzhead s5 = d_gzhead s) by f5 d_gzhead Hka Hpk Hs5.
  assert (E5gi : d_gzindex s5 = d_gzindex s) by f5 d_gzindex Hka Hpk Hs5.
  assert (E5lf : d_last_flush s5 = d_last_flush s) by f5 d_last_flush Hka Hpk Hs5.
  assert (E5me : d_method s5 = d_method s) by f5 d_method Hka Hpk Hs5.
  assert (E5tr : d_tr s5 = t').
  { pose proof (f_equal d_tr Hka) as Ha. dsimp_in Ha. rewrite Hs5. dsimp. exact Ha. }
  assert (E5pbm : d_pbm s5 = m').
  { pose proof (f_equal d_pbm Hka) as Ha. dsimp_in Ha. rewrite Hs5. dsimp. exact Ha. }
  assert (E5la : d_lookahead s5 = d_lookahead s - (P - 1)).
  { pose proof (f_equal d_lookahead Hka) as Ha. dsimp_in Ha. rewrite Hs5. dsimp. exact Ha. }
  assert (E5ss : d_strstart s5 = d_strstart s + P - 2 + 1) by (rewrite Hs5; dsimp; reflexivity).
  assert (E5av : d_match_available s5 = 0) by (rewrite Hs5; dsimp; reflexivity).
  assert (E5ml : d_match_length s5 = 2) by (rewrite Hs5; dsimp; reflexivity).
  assert (E5pl : d_prev_length s5 = 0) by (rewrite Hs5; dsimp; exact Hpla).
  rewrite Etr1 in F1, F2, F3, F4, F5, F6, F7. rewrite Epbm1 in F7. rewrite Etr1 in Et |- *. rewrite Hlen in Ht'.
  unfold tr_cfg in F1. injection F1 as C1 C2 C3 C4.
  assert (E5L : d_L s5 = d_L s) by (unfold d_L; rewrite E5tr; exact C1).
  assert (E5lv : d_level s5 = d_level s) by (unfold d_level; rewrite E5tr; exact C3).
  assert (E5sg : d_strategy s5 = d_strategy s) by (unfold d_strategy; rewrite E5tr; exact C4).
  assert (E5pd : d_pending s5 = d_pending s) by (unfold d_pending; rewrite E5tr; exact F3).
  assert (E5bv : d_bi_valid s5 = d_bi_valid s) by (unfold d_bi_valid; rewrite E5tr; exact F5).
  assert (E5mt : d_matches s5 = d_matches s) by (unfold d_matches; rewrite E5tr; exact F2).
  assert (H5prm : prm s5).
  { assert (E5wm : d_w_mask s5 = d_w_mask s) by f5 d_w_mask Hka Hpk Hs5.
    assert (E5hs : d_hash_size s5 = d_hash_size s) by f5 d_hash_size Hka Hpk Hs5.
    assert (E5hm : d_hash_mask s5 = d_hash_mask s) by f5 d_hash_mask Hka Hpk Hs5.
    assert (E5hsh : d_hash_shift s5 = d_hash_shift s) by f5 d_hash_shift Hka Hpk Hs5.
    pose proof F7 as (G1' & G2' & _).
    clear - Hprm E5wb E5w E5wm E5hb E5hs E5hm E5hsh E5pbs E5me E5tr E5pbm C1 C2 C3 C4 G1' G2'.
    unfold prm, d_L, d_level, d_strategy in *.
    rewrite E5wb, E5w, E5wm, E5hb, E5hs, E5hm, E5hsh, E5pbs, E5me, E5tr, E5pbm, C1, C2, C3, C4, G1', G2'.
    exact Hprm. }
  assert (H5ws : wstruct s5).
  { assert (E5pr : d_prev s5 = d_prev a) by (rewrite Hs5; dsimp; reflexivity).
    assert (E5hd : d_head s5 = d_head a) by (rewrite Hs5; dsimp; reflexivity).
    assert (Eaw : d_window a = d_window s5) by (rewrite Hs5; dsimp; reflexivity).
    assert (Eawz : d_w_size a = d_w_size s5) by (rewrite Hs5; dsimp; reflexivity).
    assert (Eawsz : d_window_size a = d_window_size s5) by (rewrite Hs5; dsimp; reflexivity).
    assert (Eahs : d_hash_size a = d_hash_size s5) by (rewrite Hs5; dsimp; reflexivity).
    unfold wstruct in *. rewrite E5pr, E5hd, <- Eaw, <- Eawz, <- Eawsz, <- Eahs. exact Hwsa. }
  assert (H5ch : chain_ok s5).
  { assert (E5pr : d_prev s5 = d_prev a) by (rewrite Hs5; dsimp; reflexivity).
    assert (E5hd : d_head s5 = d_head a) by (rewrite Hs5; dsimp; reflexivity).
    assert (Eawm : d_w_mask a = d_w_mask s5) by (rewrite Hs5; dsimp; reflexivity).
    assert (Eahs : d_hash_size a = d_hash_size s5) by (rewrite Hs5; dsimp; reflexivity).
    exists Ga. unfold chain_with in *. rewrite E5pr, E5hd, <- Eawm, <- Eahs.
    fold (chain_with a (d_strstart s5) (lim s5) Ga).
    apply (chain_with_mono _ _ _ _ _ _ Hcha).
    - rewrite Hsa', E5ss. lia.
    - apply lim_mono; [exact E5w|]. rewrite E5ss. clear - HPb. lia. }
  assert (Hvs : forall x, In x (syms ++ [(dist, P - 3)]) -> valid_sym (fst x) (snd x))
    by (destruct Ht' as (_ & _ & _ & Hv & _); exact Hv).
  assert (Hdist' : 1 <= dist <= MAX_DIST s) by (rewrite Edist; exact Hdist).
  assert (H5blk : blk_len (syms ++ [(dist, P - 3)]) = d_strstart s5 - d_block_start s5).
  { rewrite blk_len_app, blk_len_one, T5, E5ss, E5bs. unfold sym_len. cbn [fst snd].
    destruct (Z.eqb_spec dist 0); [clear - Hdist' e; lia|]. lia. }
  assert (H5bnd : blk_len (syms ++ [(dist, P - 3)]) <= 258 * (Zlength syms + 1)).
  { pose proof (blk_len_bound _ Hvs) as Hb. rewrite Zlength_app in Hb.
    change (Zlength [(dist, P - 3)]) with 1 in Hb. exact Hb. }
  assert (H5pos : wpos s5).
  { unfold wpos, MAX_DIST in *. rewrite E5la, E5ss, E5wsz, E5bs, E5ins, E5w, E5hw.
    clear - HPb HPla Epl1 Wp1 Wp2 Wp3 Wp4 Wp6 Wp7 Wp8 Wp9 H5blk H5bnd T2 HLb E5ss E5bs.
    rewrite E5ss, E5bs in H5blk.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [intros Hn; specialize (Wp6 Hn); lia|]. lia. }
  assert (H5win : wwin s5).
  { unfold wwin in *. rewrite E5win, E5ss, E5la, E5hw. intros i Hi. apply Hwwin.
    replace (d_strstart s + P - 2 + 1 + (d_lookahead s - (P - 1))) with (d_strstart s + d_lookahead s) in Hi
      by lia. exact Hi. }
  assert (H5m : wmatch s5).
  { unfold wmatch. rewrite E5ml, E5pl, E5av. unfold MAX_MATCH, MIN_MATCH.
    split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [intros _; lia|].
    intros E; discriminate E. }
  assert (H5sym : Forall (sym_ok s5) (syms ++ [(dist, P - 3)])).
  { rewrite (sym_ok_eq s5 s E5w E5lv E5sg). apply Forall_app. split; [exact T3|].
    constructor; [|constructor]. unfold sym_ok, valid_sym. cbn [fst snd].
    split; [unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hdist'; clear - Hdist' HPb HWb; lia|].
    split; [intros _; exact (proj2 Hdist')|].
    intros _ Hf _ H0. rewrite Edist. apply Htoo; [|exact Hf]. unfold MIN_MATCH. clear - H0 Epl1. lia. }
  assert (H5q : quiet s5).
  { unfold quiet in *. rewrite E5pd, E5po, E5bv. exact Hq. }
  assert (H5mt : d_matches s5 = 0).
  { rewrite E5mt. unfold whash in Hwh. destruct (Z.eqb_spec (d_level s) 0) as [E|_]; [contradiction|].
    exact (proj1 Hwh). }
  assert (H5EI : EI s0 z0 flush s5 z evs).
  { destruct HEI as (Ec & Efn & Eo & Esp & Eapi & Ez & Ead & Ezs & Ech & Eev).
    split; [exact Ec|]. split; [exact Efn|]. split.
    { apply (outok_grow s s5 Eo).
      - rewrite E5tr, E5pbm. exact F7.
      - exact E5po.
      - exact E5pd.
      - exact E5pbs.
      - rewrite E5tr. destruct Eo as (_ & Hb & _). unfold bits_ok in *. rewrite F3, F4, F5. exact Hb. }
    split; [unfold same_prm in *; rewrite E5wb, E5w, E5hb, E5L, E5pbs, E5lv, E5sg; exact Esp|].
    split; [unfold api_eq in *; rewrite E5st, E5wr, E5gz, E5gi, E5lf, E5me; exact Eapi|].
    split; [exact Ez|]. split; [exact Ead|].
    split.
    { destruct Ezs as (k1 & x1 & Hk1 & Hk2 & Hk3). exists k1, x1. split; [exact Hk1|]. split; [exact Hk2|].
      unfold ub in *. rewrite E5ss, E5bs, E5la. clear - Hk3. lia. }
    split; [|exact Eev].
    replace (Gb s5 (z_total_out z)) with (Gb s (z_total_out z)) by (unfold Gb; rewrite E5pd, E5bv; reflexivity).
    exact Ech. }
  assert (H5lv : d_level s5 <> 0) by (rewrite E5lv; exact Hlv).
  assert (H5tree : tree_ok (d_tr s5) (d_pbm s5) (syms ++ [(dist, P - 3)])) by (rewrite E5tr, E5pbm; exact Ht').
  assert (Hlen' : Zlength (syms ++ [(dist, P - 3)]) = Zlength syms + 1)
    by (rewrite Zlength_app; reflexivity).
  assert (Hmsr : d_lookahead s5 < d_lookahead s) by (rewrite E5la; clear - HPb; lia).
  (** the functional facts at s5 *)
  assert (HS5 : d_strstart s5 + d_lookahead s5 = d_strstart s + d_lookahead s)
    by (rewrite E5ss, E5la; clear; lia).
  rewrite (proj2 (Z.eqb_neq _ _) Hlv), Hav in K7.
  assert (Hkl : d_strstart s + d_lookahead s <= Zlength HH) by (destruct K1 as [Kl _]; exact Kl).
  assert (Hwb : dist <= 2 ^ d_w_bits s).
  { rewrite <- Pws. clear - Hdist' HWb. unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hdist'. lia. }
  assert (KP : kpre dict (D ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0)) (BS ++ BS')
                 (syms ++ [(dist, P - 3)]) s5).
  { unfold kpre. cbv zeta. fold HH. rewrite HS5, E5wb, E5bs, E5ss.
    split; [unfold kwin in *; rewrite HS5, E5win; exact K1|].
    split; [exact K4|]. split; [exact K5|].
    split.
    { apply fm_syms_rok_app. split; [exact K6|]. rewrite K7. cbn [syms_rok fst snd].
      replace (dist =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Kd; lia).
      rewrite Zlength_sublist by (clear - Kd Hkl Wp1; lia). split; [|exact I].
      split; [clear - HPb; lia|]. split; [clear - Kd; lia|]. exact Hwb. }
    split.
    { rewrite fm_syms_data_app, K7. unfold F.syms_data. cbn [map fold_left]. unfold fsym. cbn [fst snd].
      replace (dist =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Kd; lia).
      cbn [F.sym_data]. replace (P - 3 + 3) with P by lia.
      replace (Zlength HH - (d_strstart s + d_lookahead s) + (d_strstart s - 1))
        with (Zlength HH - d_lookahead s - 1) by lia.
      rewrite fm_lz_copy, Z2Nat.id.
      - f_equal. lia.
      - clear - HPb. lia.
      - clear - Kd. lia.
      - rewrite Z2Nat.id by (clear - HPb; lia). clear - HPb HPla Epl1 Hkl Wp2. lia.
      - rewrite Z2Nat.id by (clear - HPb; lia). exact Kq. }
    unfold khash. rewrite E5lv, (proj2 (Z.eqb_neq _ _) Hlv). split.
    - apply chain_hokS_iff. rewrite HS5.
      apply (fm_chain_hokS_mono a s5 _); try (rewrite Hs5; reflexivity); [|exact Fcha].
      apply lim_mono; [rewrite Hs5; reflexivity|]. rewrite E5ss, Hsa'. clear; lia.
    - intros _ H3. rewrite E5la in H3. split.
      + rewrite E5ins. refine (proj1 (Kh2 (or_intror Hfn) _)). clear - H3 HPb. unfold MIN_MATCH in *. lia.
      + rewrite E5ss. apply (fm_primed a s5); try (rewrite Hs5; reflexivity).
        replace (d_strstart s + P - 2 + 1) with (d_strstart a + 1) by (clear - Hsa'; lia).
        apply Fpra. rewrite Hsa'. clear - H3 HPb. unfold MIN_MATCH in *. lia. }
  assert (Hbits5 : F.bytes_bits (x ++ pend s5) ++ bibits s5 = bibits s0 ++ enc_out p BS' false).
  { rewrite (pend_quiet s5 H5q), <- (pend_quiet s Hq). replace (bibits s5) with (bibits s); [exact Hbits|].
    unfold bibits, d_bi_valid. rewrite E5tr, F4, F5. reflexivity. }
  unfold c_bflush.
  destruct (Z.eqb_spec (3 * Zlength syms + 3) (tr_sym_end (d_tr s))) as [Ebf|Ebf].
  - (* FLUSH_BLOCK(s, 0) *)
    assert (HlenL : Zlength (syms ++ [(dist, P - 3)]) = d_L s5 - 1).
    { rewrite Hlen', E5L. rewrite Pse in Ebf. clear - Ebf. lia. }
    assert (Hfpre : fbo_pre s5 z (syms ++ [(dist, P - 3)]) 0).
    { pose proof H5pos as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9).
      split; [exact H5prm|]. split; [exact H5ws|]. split; [clear - H5lv E5lv Plv; lia|].
      split; [exact H5tree|]. split; [clear - HlenL; lia|]. split; [exact H5blk|].
      split; [exact V4|]. split; [exact V5|].
      split.
      { intros Hb0. rewrite E5ss, E5bs. rewrite E5bs in Hb0. destruct H5ws as (Q1 & _).
        rewrite E5win. split; [clear - Hb0 HPb HSw HWb; lia|]. split.
        - destruct Hwst as (R1 & _). rewrite R1. clear - HPb HSw. lia.
        - intros i Hi. apply Hwwin. clear - Hi Hb0 HPb HPla Epl1. lia. }
      split; [exact (proj1 (proj2 (proj2 H5EI)))|]. split; [exact H5q|]. split; [lia|].
      destruct H5EI as (_ & _ & _ & _ & _ & (_ & Hzo) & _). exact Hzo. }
    unfold c_flush_block. destruct (c_flush_block_only s5 z 0) as [[s6 z6]|] eqn:Efb; cbn [bind];
      [|intros E; discriminate E].
    pose proof (fbo_FI Hfbo Ffbo dict D BS p s0 z0 flush s5 z evs _ k x BS' s6 z6 HG H5EI Hfpre E5av Hzs KP
                  Hbits5 Efb) as HF6.
    change (0 =? 1) with false. cbn [negb orb andb].
    destruct (z_avail_out z6 =? 0); intros E; injection E as <-; cbn [fstep_ok].
    + apply fm_FI_FQ; [exact HF6|reflexivity].
    + exact HF6.
  - (* no flush *)
    assert (H5wt : wtrees s5 (syms ++ [(dist, P - 3)])).
    { split; [exact H5tree|]. split; [rewrite Hlen', E5L; rewrite Pse in Ebf; clear - Ebf T2; lia|].
      split; [exact H5sym|]. split; [intros E; contradiction|].
      intros _. rewrite E5av, H5blk. lia. }
    intros E. injection E as <-. cbn [fstep_ok].
    exists k, x, BS', (syms ++ [(dist, P - 3)]). split; [exact Hzs|]. split; [|exact Hbits5].
    unfold kpre in KP. cbv zeta in KP. destruct KP as (P1 & P2 & P3 & P4 & P5 & P6).
    split; [|exact P6].
    unfold kdata3. cbv zeta.
    split; [exact P1|]. split; [intros E; rewrite E5av in E; discriminate E|]. split; [exact H5wt|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
    rewrite E5lv, (proj2 (Z.eqb_neq _ _) Hlv), E5av, Z.sub_0_r. exact P5.
Qed.
