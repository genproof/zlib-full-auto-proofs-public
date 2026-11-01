(** * deflate_slow for wide streams, part Match: the match branch

    Port of LTCSlowMatch.v to the invariant [SIw] / [EIw] of DetCoreSlowInv.v; the helpers that do not mention
    the invariant are LTCSlowMatch's. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetCoreSlowInv.
Require Import Zlib.proof.deflate.LTCSlowMatch.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem match_okw : ins_spec -> tally_spec2 -> fboev_partw -> match_partw.
Proof.
  intros Hins Htally Hev s0 z0 flush s z evs s1 HSI Hrdy Hmid HP3 HmlP.
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
  assert (Hlv : d_level s <> 0).
  { intros E. unfold fn_of in Hfn. rewrite E in Hfn. cbn in Hfn. discriminate. }
  specialize (T5 Hlv). rewrite Hav in T5.
  set (P := d_prev_length s1) in *.
  assert (HPb : 3 <= P <= 258) by (clear - HP3 Epl1 M1; unfold MIN_MATCH, MAX_MATCH in *; lia).
  set (dist := u32 (d_strstart s1 - 1 - d_prev_match s1)).
  assert (Edist : dist = u32 (d_strstart s - 1 - d_match_start s)) by (unfold dist; rewrite Es1, Epm1; reflexivity).
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
    rewrite Es1, Ewin1, Ews1. intros p Hp1 Hp2.
    destruct Hwst as (Q1 & _). split; [|split].
    - clear - Hp1 Hp2 Q1 HSw Wp3. unfold MIN_MATCH in Hp1. lia.
    - apply Hwwin. clear - Hp1 Hp2 Wp2 Wp3. unfold MIN_MATCH in Hp1. lia.
    - unfold lim, MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH.
      destruct (Z.gtb_spec (d_strstart s) (d_w_size s - (258 + 3 + 1))); clear - Hp2 HPb H; lia. }
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
  assert (H5EI : EIw s0 z0 flush s5 z evs).
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
    { destruct Ezs as (k & x & Hk1 & Hk2 & Hk3). exists k, x. split; [exact Hk1|]. split; [exact Hk2|].
      unfold ub in *. rewrite E5ss, E5bs, E5la. clear - Hk3. lia. }
    split; [|exact Eev].
    replace (Gb s5 (z_total_out z)) with (Gb s (z_total_out z)) by (unfold Gb; rewrite E5pd, E5bv; reflexivity).
    exact Ech. }
  assert (H5lv : d_level s5 <> 0) by (rewrite E5lv; exact Hlv).
  assert (H5tree : tree_ok (d_tr s5) (d_pbm s5) (syms ++ [(dist, P - 3)])) by (rewrite E5tr, E5pbm; exact Ht').
  assert (Hlen' : Zlength (syms ++ [(dist, P - 3)]) = Zlength syms + 1)
    by (rewrite Zlength_app; reflexivity).
  assert (Hmsr : d_lookahead s5 < d_lookahead s) by (rewrite E5la; clear - HPb; lia).
  unfold c_bflush.
  destruct (Z.eqb_spec (3 * Zlength syms + 3) (tr_sym_end (d_tr s))) as [Ebf|Ebf].
  - (* FLUSH_BLOCK(s, 0) *)
    assert (HlenL : Zlength (syms ++ [(dist, P - 3)]) = d_L s5 - 1).
    { rewrite Hlen', E5L. rewrite Pse in Ebf. clear - Ebf. lia. }
    assert (Hfbo : fbo_pre s5 z (syms ++ [(dist, P - 3)]) 0).
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
    destruct (Hev s0 z0 flush s5 z evs (syms ++ [(dist, P - 3)]) 0 H5EI Hfbo H5sym
                (fun H => ltac:(discriminate H)) (fun _ => or_introl HlenL))
      as (s6 & z6 & e & Efb & Hlast & HEI6 & Hfk & Ebs6 & Htr6 & Hcfg6 & Hmt6 & Hbv6 & _ & Hpe6 & Hai6).
    { intros Hn. destruct H5pos as (_ & _ & _ & _ & _ & V6 & _). exact (V6 Hn). }
    assert (HW6 : W2 s6).
    { apply (W2_after_flush s5 s6 H5prm H5ws H5pos H5win H5ch H5lv E5av E5ml E5pl Hfk Ebs6 Htr6 Hcfg6 Hmt6). }
    assert (HL6 : Forall (fun e => ev_last e = 0) (evs ++ [e])).
    { apply Forall_app. split; [exact HL|]. constructor; [exact Hlast|constructor]. }
    unfold c_flush_block. rewrite Efb. cbn [bind].
    change (0 =? 1) with false. cbn [negb orb andb].
    destruct (Z.eqb_spec (z_avail_out z6) 0) as [Ea|Ea]; cbn [andb].
    + eexists; split; [reflexivity|]. cbn [step_okw]. exists (evs ++ [e]).
      exact (EIw_need_more s0 z0 flush s6 z6 (evs ++ [e]) HW6 HL6 HEI6 Hbv6 (or_intror Ea)).
    + eexists; split; [reflexivity|]. cbn [step_okw]. exists (evs ++ [e]).
      assert (Ela6 : d_lookahead s6 = d_lookahead s5) by fk d_lookahead Hfk.
      split.
      * split; [exact HW6|]. split; [|split; [exact HL6|exact HEI6]].
        destruct Hpe6 as [Hpe6|Hpe6]; [|contradiction].
        destruct HEI6 as (_ & _ & Ho6 & _). destruct Ho6 as (_ & _ & _ & _ & _ & Hpo6).
        unfold quiet. split; [exact Hpe6|]. split; [exact (Hpo6 Hpe6)|]. exact Hbv6.
      * unfold msr. rewrite Hai6, Ela6. clear - Hmsr. lia.
  - (* no flush *)
    eexists; split; [reflexivity|]. cbn [step_okw]. exists evs.
    split; [|unfold msr; clear - Hmsr; lia].
    split; [|split; [exact H5q|split; [exact HL|exact H5EI]]].
    split; [|unfold slow_extra; rewrite E5av; intros E; discriminate E].
    split; [exact H5prm|]. split; [exact H5ws|]. split; [exact H5pos|]. split; [exact H5win|].
    split; [unfold whash; destruct (Z.eqb_spec (d_level s5) 0) as [E|_]; [contradiction|];
            split; [exact H5mt|exact H5ch]|].
    split; [exact H5m|]. split; [intros E; contradiction|].
    exists (syms ++ [(dist, P - 3)]).
    split; [exact H5tree|]. split; [rewrite Hlen', E5L; rewrite Pse in Ebf; clear - Ebf T2; lia|].
    split; [exact H5sym|]. split; [intros E; contradiction|].
    intros _. rewrite E5av, H5blk. lia.
Qed.
