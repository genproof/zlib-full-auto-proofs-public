(** * deflate_huff part: see RTDLTCHuffKit.v for the statement and the design. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCHuffKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The fields fill_window keeps. *)
Lemma hfwk_fields s s' : fw_keep s' = fw_keep s ->
  d_tr s' = d_tr s /\ d_pbm s' = d_pbm s /\ d_po s' = d_po s /\ d_w_size s' = d_w_size s /\
  d_window_size s' = d_window_size s /\ d_match_length s' = d_match_length s /\
  d_match_available s' = d_match_available s /\ d_prev_length s' = d_prev_length s /\
  d_pending_buf_size s' = d_pending_buf_size s /\ d_w_bits s' = d_w_bits s /\
  d_status s' = d_status s /\ d_wrap s' = d_wrap s /\ d_gzhead s' = d_gzhead s /\
  d_gzindex s' = d_gzindex s /\ d_last_flush s' = d_last_flush s /\ d_method s' = d_method s.
Proof.
  intros E.
  pose proof (f_equal d_tr E) as E1. pose proof (f_equal d_pbm E) as E2. pose proof (f_equal d_po E) as E3.
  pose proof (f_equal d_w_size E) as E4. pose proof (f_equal d_window_size E) as E5.
  pose proof (f_equal d_match_length E) as E6. pose proof (f_equal d_match_available E) as E7.
  pose proof (f_equal d_prev_length E) as E8. pose proof (f_equal d_pending_buf_size E) as E9.
  pose proof (f_equal d_w_bits E) as E10. pose proof (f_equal d_status E) as E11.
  pose proof (f_equal d_wrap E) as E12. pose proof (f_equal d_gzhead E) as E13.
  pose proof (f_equal d_gzindex E) as E14. pose proof (f_equal d_last_flush E) as E15.
  pose proof (f_equal d_method E) as E16.
  unfold fw_keep in *. cbn [d_tr d_pbm d_po d_w_size d_window_size d_match_length d_match_available
    d_prev_length d_pending_buf_size d_w_bits d_status d_wrap d_gzhead d_gzindex d_last_flush d_method] in *.
  repeat (split; [assumption|]). assumption.
Qed.

(** The state after a fill, composed with the loop invariant. *)
Theorem hrefill_ok : fill_spec -> hrefill_stmt.
Proof.
  intros Hfill s0 z0 flush s z evs HI Hfn0 Hla.
  destruct HI as (Hz0 & Ha0 & Hc & Hq & Hz & Ha & Hlast).
  destruct Hc as (HW & He & Ho & Hsp & Hae & (k1 & x1 & Hzs1 & Hb1 & Hub1) & Hch & Hev).
  assert (Hfn : fn_of s = 3) by (rewrite (fn_of_same_prm' s0 s Hsp); exact Hfn0).
  assert (HW0 := HW).
  destruct HW0 as (Hp & Hs & Hpos & Hw & Hh & Hm & H0 & syms & Ht).
  assert (Hlev := fn_of_huff s Hp Hfn).
  assert (Hfp : fill_pre s).
  { unfold whash in Hh. destruct (Z.eqb_spec (d_level s) 0) as [E|N]; [lia|].
    destruct Hh as (_ & Hc).
    split; [exact Hp|]. split; [exact Hs|]. split; [exact Hpos|]. split; [exact Hw|exact Hc]. }
  destruct (Hfill s z Hfp Hz Ha) as (s' & z' & k & d & Hfw & Hfp' & Hk & Hst & Hd & Es & Eb & _ & _ &
    El & Hss & Hor & Hhw).
  destruct (hfwk_fields s s' Hk) as (Etr & Epbm & Epo & Ews & Ewz & Eml & Ema & Epl & Epbs & Ewb &
    Est & Ewr & Egz & Egi & Elf & Eme).
  destruct Hfp' as (Hp' & Hs' & Hpos' & Hw' & Hc').
  assert (Elv : d_level s' = d_level s) by (unfold d_level; rewrite Etr; reflexivity).
  assert (Esg : d_strategy s' = d_strategy s) by (unfold d_strategy; rewrite Etr; reflexivity).
  assert (EMD : MAX_DIST s' = MAX_DIST s) by (unfold MAX_DIST; rewrite Ews; reflexivity).
  assert (Ma : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  assert (Hfn' : fn_of s' = fn_of s) by (unfold fn_of; rewrite Elv, Esg; reflexivity).
  assert (Esn : d_sym_next s' = d_sym_next s) by (unfold d_sym_next; rewrite Etr; reflexivity).
  assert (HW' : W s').
  { unfold W. split; [exact Hp'|]. split; [exact Hs'|]. split; [exact Hpos'|]. split; [exact Hw'|].
    split.
    { unfold whash in *. rewrite Elv. destruct (Z.eqb_spec (d_level s) 0) as [E|N]; [lia|].
      destruct Hh as (Hm0 & _). split; [|exact Hc']. unfold d_matches in *. rewrite Etr. exact Hm0. }
    split.
    { destruct Hm as (M1 & M2 & M3 & M4 & M5). unfold wmatch. rewrite Eml, Ema, Epl.
      split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
      intros A. lia. }
    split; [intros; lia|].
    exists syms. destruct Ht as (T1 & T2 & T3 & T4 & T5). unfold wtrees.
    split; [rewrite Etr, Epbm; exact T1|].
    split; [unfold d_L; rewrite Etr; exact T2|].
    split.
    { eapply Forall_impl; [|exact T3]. intros x (X1 & X2 & X3). unfold sym_ok.
      rewrite EMD, Elv, Esg. split; [exact X1|]. split; [exact X2|exact X3]. }
    split; [intros; lia|].
    intros _. rewrite Es, Eb, Ema. rewrite T5 by lia. lia. }
  assert (He' : huff_extra s').
  { intros _. rewrite Es, Eb, Esn. specialize (He Hfn). lia. }
  assert (Ho' : outok s').
  { destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6). unfold outok, d_pb, d_pending in *.
    rewrite Etr, Epbm, Epo, Epbs. repeat (split; [assumption|]). assumption. }
  assert (Hq' : quiet s').
  { unfold quiet, d_pending, d_bi_valid in *. rewrite Etr, Epo. exact Hq. }
  assert (Hzs := Hz). destruct Hzs as [(Hb & Hn & Hai & Hl & Hti) (Hao & Hto & Hs0)].
  assert (Hst0 := Hst).
  destruct Hst0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A7x & A8 & A9 & A10).
  rewrite Zlength_nil, Z.add_0_r in A9. rewrite Zlength_nil, Z.sub_0_r in A8.
  rewrite u64_id in A9 by lia.
  assert (Hz' : zall z').
  { eapply zall_zstep; [exact Hz|exact Hst|]. lia. }
  assert (Ha' : adler_ok (d_wrap s') (z_adler z')).
  { rewrite Ewr, A6. apply adler_ok_upd; [apply bytes_sublist; exact Hb|exact Ha]. }
  assert (Hwr0 : d_wrap s = d_wrap s0) by (destruct Hae as (_ & X & _); exact X).
  assert (Hzs : zstep (d_wrap s0) z0 z' (k1 + k) (x1 ++ [])).
  { apply zstep_trans with z; [destruct Hz0 as (X & _); exact X|exact Ha0|exact Hzs1|].
    rewrite <- Hwr0. exact Hst. }
  exists s', z'. split; [exact Hfw|].
  split.
  { unfold HFI, hcrel.
    split; [exact Hz0|]. split; [exact Ha0|].
    split.
    { split; [exact HW'|]. split; [exact He'|]. split; [exact Ho'|].
      split.
      { destruct Hsp as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
        pose proof (f_equal d_hash_bits Hk) as Eh. unfold fw_keep in Eh. cbn [d_hash_bits] in Eh.
        unfold same_prm. rewrite Ewb, Ews, Eh, Epbs, Elv, Esg.
        assert (EL : d_L s' = d_L s) by (unfold d_L; rewrite Etr; reflexivity). rewrite EL.
        split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
        split; [exact P5|]. split; [exact P6|exact P7]. }
      split.
      { destruct Hae as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
        unfold api_eq. rewrite Est, Ewr, Egz, Egi, Elf, Eme.
        split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
        split; [exact Q5|exact Q6]. }
      split.
      { exists (k1 + k), (x1 ++ []). split; [exact Hzs|].
        split; [rewrite app_nil_r; exact Hb1|]. unfold ub in *. lia. }
      split; [|exact Hev].
      assert (EG : Gb s' (z_total_out z') = Gb s (z_total_out z)).
      { unfold Gb, d_pending, d_bi_valid. rewrite A9, Etr. reflexivity. }
      rewrite EG. exact Hch. }
    split; [exact Hq'|]. split; [exact Hz'|]. split; [exact Ha'|exact Hlast]. }
  split; [lia|].
  intros L0. destruct Hor as [Hor|Hor]; [|exact Hor].
  replace MIN_LOOKAHEAD with 262 in Hor by reflexivity. lia.
Qed.
