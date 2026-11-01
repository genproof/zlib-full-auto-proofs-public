(** * RT-D part FAST, piece: frefill_stmt (statement and definitions: RTDFastKit.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFastKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma fr_sublist0_app n (H X : list Z) : n <= Zlength H -> sublist 0 n (H ++ X) = sublist 0 n H.
Proof.
  intros Hn. destruct (Z_lt_le_dec n 0) as [N|N].
  - rewrite !sublist_nil_gen' by lia. reflexivity.
  - apply sublist_app1; lia.
Qed.

Theorem frefill_ok : frefill_stmt.
Proof.
  intros s z flush r dict D BS syms Hff HW Ho Hq Hz Ha Hfn Hfl HK Hr.
  unfold c_refill in Hr.
  destruct (need_min_lookahead s) eqn:Hn.
  2:{ injection Hr as <-. cbn [rst fst snd]. exists 0.
      split; [apply zstep_refl; assumption|].
      rewrite Z.add_0_r, sublist_nil, app_nil_r.
      split; [exact HK|split; reflexivity]. }
  assert (Hfp : fill_pre s).
  { destruct HW as (Hp & Hs & Hpos & Hw & Hh & _).
    assert (Hlev := fn_of_fast s Hp Hfn).
    unfold whash in Hh. destruct (Z.eqb_spec (d_level s) 0) as [E|N]; [lia|].
    destruct Hh as (_ & Hc).
    split; [exact Hp|]. split; [exact Hs|]. split; [exact Hpos|]. split; [exact Hw|exact Hc]. }
  destruct (fill_ok s z Hfp Hz Ha) as (s1 & z1 & k & d & Hfw & Hfp' & Hk & Hst & Hd & Es & Eb & _ & _ &
    El & _).
  rewrite Hfw in Hr. cbn [bind] in Hr.
  assert (Hrs : rst r = (s1, z1)).
  { repeat match type of Hr with context [if ?b then _ else _] => destruct b end;
      injection Hr as <-; reflexivity. }
  rewrite Hrs. cbn [fst snd]. clear Hr Hrs.
  destruct (fwk_fields s s1 Hk) as (Etr & Epbm & Epo & Ews & Ewz & Eml & Ema & Epl & Epbs & Ewb &
    Est & Ewr & Egz & Egi & Elf & Eme).
  destruct HK as (Kd & Kh).
  destruct Kd as (Kw & Km & Kt & Kb & Ke & Kr & Ks).
  destruct (Hff s z s1 z1 (dict ++ D) Hfp Hz Ha Hfw Kw) as (k' & Hst' & Kw' & Hch & Hpr).
  assert (Ek : k' = k).
  { destruct Hst as (_ & _ & N1 & _). destruct Hst' as (_ & _ & N2 & _). lia. }
  subst k'.
  exists k. split; [exact Hst|].
  split; cycle 1.
  { unfold pend, bibits, d_pending, d_bi_valid. rewrite Etr, Epo. split; reflexivity. }
  assert (HW0 := HW).
  destruct HW0 as (Hp & _ & Hpos & _ & _ & Hm & _ & _).
  assert (Hlev := fn_of_fast s Hp Hfn).
  assert (Ma : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  assert (Elv : d_level s1 = d_level s) by (unfold d_level; rewrite Etr; reflexivity).
  assert (Esg : d_strategy s1 = d_strategy s) by (unfold d_strategy; rewrite Etr; reflexivity).
  assert (EMD : MAX_DIST s1 = MAX_DIST s) by (unfold MAX_DIST; rewrite Ews; reflexivity).
  assert (Hfn1 : fn_of s1 = fn_of s) by (unfold fn_of; rewrite Elv, Esg; reflexivity).
  destruct Hpos as (Pl & Ps & _ & Pbs & _).
  assert (Hzs := Hz). destruct Hzs as [(_ & Hn0 & _ & Hlz & _) _].
  assert (Hk0 : 0 <= k <= z_avail_in z) by (destruct Hst as (_ & K & _); exact K).
  assert (Lnew : Zlength (sublist (z_next_in z) (z_next_in z + k) (z_in z)) = k)
    by (rewrite Zlength_sublist by lia; lia).
  destruct Kw as (Kwl & _).
  split.
  - unfold kdata. cbv zeta. rewrite app_assoc.
    set (H := dict ++ D) in *. set (X := sublist (z_next_in z) (z_next_in z + k) (z_in z)) in *.
    split; [exact Kw'|].
    split; [unfold kmatch; rewrite Ema, Ma; intros; lia|].
    split.
    { destruct Kt as (T1 & T2 & T3 & T4 & T5). unfold wtrees.
      split; [rewrite Etr, Epbm; exact T1|].
      split; [unfold d_L; rewrite Etr; exact T2|].
      split.
      { eapply Forall_impl; [|exact T3]. intros x (X1 & X2 & X3). unfold sym_ok.
        rewrite EMD, Elv, Esg. split; [exact X1|]. split; [exact X2|exact X3]. }
      split; [intros; lia|].
      intros _. rewrite Es, Eb, Ema. rewrite T5 by lia. lia. }
    split; [rewrite Ewb; exact Kb|].
    split.
    { rewrite Ke, fr_sublist0_app by (rewrite Zlength_app, Es, Eb, El; lia).
      f_equal. rewrite Zlength_app, Es, Eb, El. lia. }
    split; [rewrite Ewb; exact Kr|].
    rewrite Ks, fr_sublist0_app by (rewrite Zlength_app, Es, Ema, El; lia).
    f_equal. rewrite Zlength_app, Es, Ema, El. lia.
  - destruct Kh as (Kh1 & Kh2). split.
    + rewrite Elv. destruct (Z.eqb_spec (d_level s) 0) as [E|N]; [lia|]. apply Hch.
      unfold khash in Kh1. destruct (Z.eqb_spec (d_level s) 0) as [E|_]; [lia|]. exact Kh1.
    + intros Hf Hml. apply Hpr; [exact Hml|].
      destruct (Z.eq_dec k 0) as [K0|K0]; [|left; lia].
      right. apply Kh2; [left; exact Hfn|]. rewrite El, K0 in Hml. lia.
Qed.
