(* RT-D part SLOW: the functional part fcand_part of deflate_slow (statement: RTDSlowKit.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSlowKit.
Require Import Zlib.proof.roundtrip.RTDLTCSlowCand.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Frames of the functional predicates *)

Lemma kwin_frame H a b :
  d_window b = d_window a -> d_strstart b + d_lookahead b = d_strstart a + d_lookahead a -> kwin H a -> kwin H b.
Proof. intros Ew Es. unfold kwin. rewrite Ew, Es. tauto. Qed.

Lemma h3_frame a b q :
  d_window b = d_window a -> d_hash_shift b = d_hash_shift a -> d_hash_mask b = d_hash_mask a -> h3 b q = h3 a q.
Proof. intros Ew Es Em. unfold h3, update_hash. rewrite Ew, Es, Em. reflexivity. Qed.

Lemma chain_hok_frame a b :
  d_window b = d_window a -> d_hash_shift b = d_hash_shift a -> d_hash_mask b = d_hash_mask a ->
  d_hash_size b = d_hash_size a -> d_head b = d_head a -> d_prev b = d_prev a -> d_w_mask b = d_w_mask a ->
  d_strstart b + d_lookahead b = d_strstart a + d_lookahead a -> lim a <= lim b ->
  chain_hok a -> chain_hok b.
Proof.
  intros Ew Es Em Ehs Ehd Epv Ewm Esl Hl H bk Hb. rewrite Ehs in Hb.
  destruct (H bk Hb) as (Gb & G0 & G1). exists Gb. rewrite Ehd. split; [exact G0|].
  intros q Gq Hq Hlq. destruct (G1 q Gq Hq ltac:(lia)) as (A1 & A2 & A3).
  rewrite Esl, (h3_frame a b q Ew Es Em), Epv, Ewm. auto.
Qed.

Lemma primed_frame a b p :
  d_window b = d_window a -> d_hash_shift b = d_hash_shift a -> d_hash_mask b = d_hash_mask a ->
  d_ins_h b = d_ins_h a -> primed a p -> primed b p.
Proof.
  intros Ew Es Em Ei (h0 & H). exists h0. unfold update_hash in *. rewrite Ew, Es, Em, Ei. exact H.
Qed.

Theorem fcand_ok : fcand_part.
Proof.
  intros dict D BS p s0 z0 flush s z evs s1 r _ _ HSI Hrdy HMID HFM HG HFI Hnm Hma E.
  destruct HMID as (Hpk & Hws1 & _ & Hpl & Hpm & Hml & Hmid).
  destruct HFM as (Fch & Fpr & Fm).
  pose proof (cand_pre_keep_inv s s1 Hpk) as E1. clear Hpk.
  set (hd := d_head s1) in *. set (pv := d_prev s1) in *. set (ih := d_ins_h s1) in *.
  set (pl := d_prev_length s1) in *. set (pm := d_prev_match s1) in *.
  set (ml := d_match_length s1) in *. set (ms := d_match_start s1) in *.
  clearbody hd pv ih pl pm ml ms. subst s1.
  cbn [d_match_start d_match_length d_prev_match d_prev_length d_ins_h d_prev d_head d_match_available
       set_d_match_start set_d_match_length set_d_prev_match set_d_prev_length set_d_ins_h set_d_prev set_d_head]
    in Hpl, Hpm, Hmid, Hnm, Hma.
  set (X := set_d_match_start (set_d_match_length (set_d_prev_match (set_d_prev_length
                (set_d_ins_h (set_d_prev (set_d_head s hd) pv) ih) pl) pm) ml) ms) in *.
  unfold dsl_cand in E. injection E as <-. cbn [fstep_ok].
  set (s' := set_d_lookahead (set_d_strstart (set_d_match_available X 1) (u32 (d_strstart X + 1)))
               (u32 (d_lookahead X - 1))).
  change (FI dict D BS p s0 z0 s' z).
  destruct HSI as [[HW Hse] [Hq [HL HE]]].
  destruct HW as (Hprm & Hws & Hwp & Hww & Hwh & Hwm & Hl0 & _).
  destruct HE as (Hc0 & Hf0 & Ho & Hsp & Hapi & _).
  assert (Hfn : fn_of s = 2).
  { destruct Hsp as (_ & _ & _ & _ & _ & Hlv & Hst). unfold fn_of in *. rewrite Hlv, Hst. exact Hf0. }
  assert (Hlv0 : d_level s <> 0).
  { intros E0. unfold fn_of in Hfn. rewrite E0 in Hfn. cbn in Hfn. discriminate. }
  destruct Hwm as (Hm1 & Hm2 & _ & Hm4 & _).
  destruct (Hm4 Hma) as [Hmls Hpls].
  destruct Hwp as (Hp1 & Hp2 & Hp3 & Hp4 & Hp5 & Hp6 & Hp7 & Hp8 & Hp9).
  destruct Hrdy as (Hr1 & Hr2 & Hr3).
  assert (Hwsz : d_window_size s <= 65536).
  { destruct Hws as (_ & _ & Hws3 & _).
    destruct Hprm as (Hb1 & Hb2 & _). assert (d_w_size s <= 2 ^ 15) by (rewrite Hb2; apply Z.pow_le_mono_r; lia).
    change (2 ^ 15) with 32768 in *. lia. }
  assert (Hu1 : u32 (d_strstart s + 1) = d_strstart s + 1) by (unfold u32; apply Z.mod_small; lia).
  assert (Hu2 : u32 (d_lookahead s - 1) = d_lookahead s - 1) by (unfold u32; apply Z.mod_small; lia).
  assert (Ess : d_strstart s' = d_strstart s + 1) by exact Hu1.
  assert (Ela : d_lookahead s' = d_lookahead s - 1) by exact Hu2.
  assert (Ema : d_match_available s' = 1) by reflexivity.
  assert (Eml : d_match_length s' = ml) by reflexivity.
  assert (Ems : d_match_start s' = ms) by reflexivity.
  assert (Ebs : d_block_start s' = d_block_start s) by reflexivity.
  assert (Ein : d_insert s' = d_insert s) by reflexivity.
  assert (Ewin : d_window s' = d_window s) by reflexivity.
  assert (Elv : d_level s' = d_level s) by reflexivity.
  assert (Etr : d_tr s' = d_tr s) by reflexivity.
  assert (Epbm : d_pbm s' = d_pbm s) by reflexivity.
  assert (Epo : d_po s' = d_po s) by reflexivity.
  assert (EL : d_L s' = d_L s) by reflexivity.
  assert (Ewb : d_w_bits s' = d_w_bits s) by reflexivity.
  assert (EMD : MAX_DIST s' = MAX_DIST s) by reflexivity.
  assert (Efn : fn_of s' = fn_of s) by reflexivity.
  assert (Ehs : d_hash_shift s' = d_hash_shift X) by reflexivity.
  assert (Ehm : d_hash_mask s' = d_hash_mask X) by reflexivity.
  assert (Ehz : d_hash_size s' = d_hash_size X) by reflexivity.
  assert (Ehd : d_head s' = d_head X) by reflexivity.
  assert (Epv : d_prev s' = d_prev X) by reflexivity.
  assert (Ewm : d_w_mask s' = d_w_mask X) by reflexivity.
  assert (Eih : d_ins_h s' = d_ins_h X) by reflexivity.
  assert (EXw : d_window X = d_window s) by reflexivity.
  assert (EXss : d_strstart X = d_strstart s) by reflexivity.
  assert (EXla : d_lookahead X = d_lookahead s) by reflexivity.
  assert (EXws : d_w_size X = d_w_size s) by reflexivity.
  assert (Ewsz : d_w_size s' = d_w_size s) by reflexivity.
  destruct HFI as (k & x & BS' & syms & Hzs & Hk & Hbits).
  exists k, x, BS', syms. split; [exact Hzs|].
  split.
  2: { unfold pend, bibits, d_bi_valid in *. rewrite Etr, Epo. exact Hbits. }
  unfold kcore3, kdata3 in Hk. cbv zeta in Hk. unfold khash in Hk.
  destruct Hk as ((Kw & Km & Kt & Kb & Ke & Kr & Kd) & Kh1 & Kh2).
  set (H := dict ++ D ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0)) in *.
  assert (Hsl : d_strstart s' + d_lookahead s' = d_strstart s + d_lookahead s) by lia.
  unfold kcore3, kdata3. cbv zeta.
  split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
  - exact (kwin_frame H s s' Ewin Hsl Kw).
  - intros _ H3. rewrite Eml in H3 |- *. rewrite Ela, Ess, Ems.
    assert (Hplt : pl < ml) by (rewrite Hpl; lia).
    destruct (Fm H3 Hplt) as (Hlm & Hms & Heq). cbv zeta. fold H.
    cbn [d_match_start d_strstart] in Hms, Heq. fold X in Heq. rewrite EXw, EXss in Heq.
    destruct (Hmid H3) as [Hmll _].
    destruct Kw as [Kw1 Kw2].
    assert (Hd : u32 (d_strstart s + 1 - 1 - ms) = d_strstart s - ms).
    { rewrite EXss in Hms. replace (d_strstart s + 1 - 1 - ms) with (d_strstart s - ms) by lia.
      unfold u32. apply Z.mod_small. lia. }
    rewrite EXss in Hms. rewrite Hd. split; [lia|]. intros i Hi. specialize (Heq i Hi).
    rewrite (Kw2 (ms + i)) in Heq by lia. rewrite (Kw2 (d_strstart s + i)) in Heq by lia.
    replace (Zlength H - (d_lookahead s - 1) - 1 - (d_strstart s - ms) + i)
      with (Zlength H - (d_strstart s + d_lookahead s) + (ms + i)) by lia.
    replace (Zlength H - (d_lookahead s - 1) - 1 + i)
      with (Zlength H - (d_strstart s + d_lookahead s) + (d_strstart s + i)) by lia.
    exact Heq.
  - destruct Kt as (Kt1 & Kt2 & Kt3 & Kt4 & Kt5). unfold wtrees, sym_ok in *.
    rewrite Etr, Epbm, EL, Elv, EMD, Ess, Ebs, Ema.
    split; [exact Kt1|]. split; [exact Kt2|].
    split; [eapply Forall_impl; [|exact Kt3]; intros a Ha; rewrite <- Elv; exact Ha|].
    split; [exact Kt4|]. intros Hl. specialize (Kt5 Hl). rewrite Hma in Kt5. lia.
  - rewrite Ewb. exact Kb.
  - rewrite Ebs, Hsl. exact Ke.
  - rewrite Ewb. exact Kr.
  - fold H. rewrite Hsl, Elv, Ess, Ema. rewrite Hma, (proj2 (Z.eqb_neq _ _) Hlv0) in Kd.
    rewrite (proj2 (Z.eqb_neq _ _) Hlv0). rewrite Kd. f_equal. lia.
  - unfold khash. rewrite Elv, Efn. rewrite (proj2 (Z.eqb_neq _ _) Hlv0) in Kh1 |- *. split.
    + apply (chain_hok_frame X s'); auto.
      apply lim_mono; [reflexivity|rewrite Ess, EXss; lia].
    + intros _ H3. rewrite Ela in H3. rewrite Hfn in Kh2.
      destruct (Kh2 (or_intror eq_refl) ltac:(lia)) as [Hi0 _]. split; [rewrite Ein; exact Hi0|].
      rewrite Ess. apply (primed_frame X s'); auto. apply Fpr. lia.
Qed.
