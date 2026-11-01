(* RT-D part SLOW: the functional part frefill_part of deflate_slow (statement: RTDSlowKit.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSlowKit.
Require Import Zlib.proof.roundtrip.RTDLTCSlowRefill.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma frf_sublist_app (H X : list Z) n : n <= Zlength H -> sublist 0 n (H ++ X) = sublist 0 n H.
Proof.
  intros Hn. destruct (Z_lt_le_dec n 0) as [N|N].
  - rewrite !sublist_nil_gen by lia. reflexivity.
  - apply sublist_app1; lia.
Qed.

(** FI after fill_window (the safety facts of fill_spec, the functional ones of fill_fspec) *)
Lemma frf_fill dict D BS p s0 z0 flush s z evs s' z' :
  sspecs -> fspecs -> SI s0 z0 flush s z evs -> FI dict D BS p s0 z0 s z ->
  c_fill_window s z = Some (s', z') -> FI dict D BS p s0 z0 s' z'.
Proof.
  intros Hs Hf HSI HF Ec.
  destruct Hs as (Hfill & _). destruct Hf as (Hff & _).
  pose proof HSI as (HW2 & Hq & HL & HE).
  destruct HW2 as [HW Hx].
  destruct HW as (Hp & Hws & Hpos & Hwin & Hh & Hm & H0 & _).
  destruct HE as (Hc & Hfn & Ho & Hsp & Hapi & Hza & Had & _ & _ & _).
  assert (Hlv : d_level s <> 0) by (apply rf_fn_level; rewrite (rf_fn_same s0 s Hsp); exact Hfn).
  assert (Hfs : fn_of s = 2) by (rewrite (rf_fn_same s0 s Hsp); exact Hfn).
  assert (Hfp : fill_pre s).
  { split; [exact Hp|]. split; [exact Hws|]. split; [exact Hpos|]. split; [exact Hwin|].
    unfold whash in Hh. destruct (Z.eqb_spec (d_level s) 0) as [E|_]; [contradiction|]. apply Hh. }
  assert (Ewr0 : d_wrap s = d_wrap s0) by (destruct Hapi as (_ & B & _); exact B).
  assert (Had' : adler_ok (d_wrap s) (z_adler z)) by (rewrite Ewr0; exact Had).
  destruct (Hfill s z Hfp Hza Had') as (s1 & z1 & k & d & Ec1 & Hfp' & Hk & Hz & Hd & ES & EB & EM0 & EM1 & EL
    & _).
  rewrite Ec in Ec1. injection Ec1 as <- <-.
  destruct HF as (k0 & x0 & BS' & syms & Hz0 & Hk3 & Hbits).
  set (X0 := sublist (z_next_in z0) (z_next_in z0 + k0) (z_in z0)) in *.
  destruct Hk3 as ((K1 & K2 & K3 & K4 & K5 & K6 & K7) & Kh1 & Kh2).
  destruct (Hff s z s' z' (dict ++ D ++ X0) Hfp Hza Had' Ec K1) as (k' & Hz' & Kw & Hch & Hpr).
  assert (Ekk : k' = k).
  { destruct Hz as (_ & _ & N1 & _). destruct Hz' as (_ & _ & N2 & _). lia. }
  subst k'.
  pose proof (rf_fw_keep s s' Hk) as (Etr & Epbm & Epo & Est & Ewr & Egz & Egi & Elf & Eme & Ews & Ewb & Ewsz
    & Ehb & Eml & Ema & Epl & Epbs).
  assert (Elv : d_level s' = d_level s) by (unfold d_level; rewrite Etr; reflexivity).
  assert (Esg : d_strategy s' = d_strategy s) by (unfold d_strategy; rewrite Etr; reflexivity).
  assert (EMD : MAX_DIST s' = MAX_DIST s) by (unfold MAX_DIST; rewrite Ews; reflexivity).
  assert (Efn : fn_of s' = fn_of s) by (apply rf_fn_of; exact Etr).
  (* the input consumed *)
  destruct Hc as (_ & _ & _ & _ & Hzi & _ & Had0).
  pose proof Hzi as (Ib & In & Ia & Il & _).
  pose proof Hz0 as (A1 & A2 & A3 & A4 & _).
  pose proof Hz as (B1 & B2 & B3 & B4 & _).
  set (X := sublist (z_next_in z) (z_next_in z + k) (z_in z)) in *.
  assert (EX : X0 ++ X = sublist (z_next_in z0) (z_next_in z0 + (k0 + k)) (z_in z0)).
  { unfold X0, X. rewrite A1, A3. rewrite Z.add_assoc. apply sublist_rejoin; lia. }
  assert (LX : Zlength X = k) by (unfold X; rewrite A1, A3, Zlength_sublist by lia; lia).
  set (H := dict ++ D ++ X0) in *.
  assert (EH : dict ++ (D ++ sublist (z_next_in z0) (z_next_in z0 + (k0 + k)) (z_in z0)) = H ++ X).
  { unfold H. rewrite <- EX, !app_assoc. reflexivity. }
  assert (Hk0 : 0 <= k) by lia.
  destruct Hpos as (P1 & P2 & P3 & P4 & _).
  pose proof K1 as (Kl & _).
  exists (k0 + k), (x0 ++ []), BS', syms.
  split.
  { rewrite <- Ewr0 in Hz0, Had0 |- *.
    exact (zstep_trans _ _ _ _ _ _ _ _ (proj1 (zin_ok_zall _ Hzi)) Had0 Hz0 Hz). }
  split.
  - unfold kcore3, kdata3. cbv zeta. rewrite EH.
    assert (ELH : Zlength (H ++ X) = Zlength H + k) by (rewrite Zlength_app, LX; reflexivity).
    rewrite ELH, Ewb, Elv.
    assert (E1 : Zlength H + k - (d_strstart s' + d_lookahead s') + d_block_start s' =
                 Zlength H - (d_strstart s + d_lookahead s) + d_block_start s) by lia.
    assert (E2 : Zlength H + k - (d_strstart s' + d_lookahead s') + (d_strstart s' - d_match_available s') =
                 Zlength H - (d_strstart s + d_lookahead s) + (d_strstart s - d_match_available s))
      by (rewrite Ema; lia).
    assert (Hma : 0 <= d_match_available s) by (destruct Hm as (_ & _ & [M|M] & _); lia).
    split; [split; [exact Kw|]|].
    + split.
      { (* kmatch3 *)
        unfold kmatch3 in K2 |- *. cbv zeta in K2 |- *. rewrite Ema, Eml. intros Ha Hml.
        destruct (K2 Ha Hml) as (D1 & D2).
        destruct Hm as (_ & _ & _ & _ & M5). destruct (M5 Ha) as (_ & _ & N3). destruct (N3 Hml) as (N1 & _).
        assert (Eu : u32 (d_strstart s' - 1 - d_match_start s') = u32 (d_strstart s - 1 - d_match_start s)).
        { rewrite ES. destruct (Z.eq_dec d 0) as [Dz|Dz].
          - rewrite (EM0 Dz), Dz. f_equal. lia.
          - rewrite (EM1 Dz), rf_u32_sub_u32. f_equal. lia. }
        rewrite Eu, ELH.
        replace (Zlength H + k - d_lookahead s' - 1) with (Zlength H - d_lookahead s - 1) by lia.
        split; [exact D1|]. intros i Hi.
        rewrite !app_Znth1 by lia. apply D2. exact Hi. }
      split.
      { (* wtrees *)
        destruct K3 as (T1 & T2 & T3 & T4 & T5). unfold wtrees.
        split; [rewrite Etr, Epbm; exact T1|].
        split; [unfold d_L; rewrite Etr; exact T2|].
        split.
        { eapply Forall_impl; [|exact T3]. intros y (Y1 & Y2 & Y3). unfold sym_ok.
          rewrite EMD, Elv, Esg. split; [exact Y1|]. split; [exact Y2|exact Y3]. }
        split; [rewrite Elv; exact T4|].
        intros Hl. rewrite Elv in Hl. rewrite ES, EB, Ema, (T5 Hl). lia. }
      split; [exact K4|].
      split.
      { rewrite E1, frf_sublist_app by lia. exact K5. }
      split; [exact K6|].
      destruct (d_level s =? 0).
      * rewrite E1, frf_sublist_app by lia. exact K7.
      * rewrite E2, frf_sublist_app by lia. exact K7.
    + (* khash *)
      unfold khash in Kh1, Kh2 |- *. rewrite Elv in *.
      destruct (Z.eqb_spec (d_level s) 0) as [E|_]; [contradiction|].
      split; [exact (Hch Kh1)|].
      intros Hfn' Hla. rewrite Efn in Hfn'.
      apply Hpr; [exact Hla|].
      destruct (Z.eq_dec k 0) as [Kz|Kz]; [right|left; lia].
      apply Kh2; [exact Hfn'|]. lia.
  - rewrite app_nil_r.
    unfold pend, bibits, d_pending, d_bi_valid in *. rewrite Etr, Epo. exact Hbits.
Qed.

Theorem frefill_ok : frefill_part.
Proof.
  intros dict D BS p s0 z0 flush s z evs r Hs Hf HSI HG HF E.
  unfold c_refill, need_min_lookahead in E.
  destruct (Z.ltb_spec (d_lookahead s) MIN_LOOKAHEAD) as [Hlt|Hge].
  2: { injection E as <-. exact HF. }
  destruct (c_fill_window s z) as [[s' z']|] eqn:Ec; [|discriminate E].
  cbn [bind] in E.
  pose proof (frf_fill dict D BS p s0 z0 flush s z evs s' z' Hs Hf HSI HF Ec) as HF'.
  destruct ((d_lookahead s' <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH)).
  - injection E as <-. cbn [fstep_ok].
    destruct HF' as (k & x & BS' & syms & A & B & C).
    exists k, x, BS', syms. split; [exact A|]. split; [exact B|]. split; [exact C|].
    intros N. discriminate N.
  - destruct (d_lookahead s' =? 0); injection E as <-; exact HF'.
Qed.
