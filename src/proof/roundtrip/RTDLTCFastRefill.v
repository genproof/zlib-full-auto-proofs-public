(** * deflate_fast, part: the refill at the top of the loop (c_refill).  Statement and definitions: RTDLTCFastKit.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCFastKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The fields fill_window keeps. *)
Lemma fwk_fields s s' : fw_keep s' = fw_keep s ->
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

(** The state after a fill: the invariant and the stream facts. *)
Lemma refill_fill_FI s z flush s' z' k d :
  W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 1 ->
  fill_pre s' -> fw_keep s' = fw_keep s -> zstep (d_wrap s) z z' k [] ->
  d_strstart s' = d_strstart s - d -> d_block_start s' = d_block_start s - d ->
  d_lookahead s' = d_lookahead s + k ->
  FI s z flush s' z' [] /\ d_w_size s' = d_w_size s /\ d_window_size s' = d_window_size s /\
  z_avail_in z' = z_avail_in z - k.
Proof.
  intros HW Ho Hq Hz Ha Hfn Hfp Hk Hst Es Eb El.
  destruct (fwk_fields s s' Hk) as (Etr & Epbm & Epo & Ews & Ewz & Eml & Ema & Epl & Epbs & Ewb &
    Est & Ewr & Egz & Egi & Elf & Eme).
  destruct HW as (Hp & Hs & Hpos & Hw & Hh & Hm & H0 & syms & Ht).
  destruct Hfp as (Hp' & Hs' & Hpos' & Hw' & Hc').
  assert (Hlev := fn_of_fast s Hp Hfn).
  assert (Elv : d_level s' = d_level s) by (unfold d_level; rewrite Etr; reflexivity).
  assert (Esg : d_strategy s' = d_strategy s) by (unfold d_strategy; rewrite Etr; reflexivity).
  assert (EMD : MAX_DIST s' = MAX_DIST s) by (unfold MAX_DIST; rewrite Ews; reflexivity).
  assert (Ma : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  assert (Hfn' : fn_of s' = fn_of s) by (unfold fn_of; rewrite Elv, Esg; reflexivity).
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
  assert (Ho' : outok s').
  { destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6). unfold outok, d_pb, d_pending in *.
    rewrite Etr, Epbm, Epo, Epbs. repeat (split; [assumption|]). assumption. }
  assert (Hq' : quiet s').
  { unfold quiet, d_pending, d_bi_valid in *. rewrite Etr, Epo. exact Hq. }
  assert (Hzs := Hz). destruct Hzs as [(Hb & Hn & Hai & Hl & Hti) (Hao & Hto & Hs0)].
  destruct Hst as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A7x & A8 & A9 & A10).
  rewrite Zlength_nil, Z.sub_0_r, Z.add_0_r in *.
  rewrite u64_id in A9 by lia.
  assert (Hz' : zall z').
  { eapply zall_zstep; [exact Hz| |].
    - unfold zstep. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
      split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [exact A7x|].
      split; [rewrite Zlength_nil; lia|]. split; [rewrite Zlength_nil, Z.add_0_r, u64_id; lia|exact A10].
    - lia. }
  assert (Ha' : adler_ok (d_wrap s') (z_adler z')).
  { rewrite Ewr, A6. apply adler_ok_upd; [apply bytes_sublist; exact Hb|exact Ha]. }
  split; [|split; [exact Ews|split; [exact Ewz|exact A4]]].
  unfold FI, crel.
  split; [|split; [exact Hq'|split; [exact Hz'|split; [exact Ha'|constructor]]]].
  split; [exact HW'|]. split; [exact Ho'|].
  split.
  { unfold same_prm, d_L. rewrite Ewb, Ews, Epbs, Elv, Esg, Etr.
    split; [reflexivity|]. split; [reflexivity|]. split; [|split; [reflexivity|split; [reflexivity|split; reflexivity]]].
    pose proof (f_equal d_hash_bits Hk) as Eh. unfold fw_keep in Eh. cbn [d_hash_bits] in Eh. exact Eh. }
  split.
  { unfold api_eq. rewrite Est, Ewr, Egz, Egi, Elf, Eme.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; reflexivity. }
  split.
  { exists k, []. split.
    - unfold zstep. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
      split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [exact A7x|].
      split; [rewrite Zlength_nil; lia|]. split; [rewrite Zlength_nil, Z.add_0_r, u64_id; lia|exact A10].
    - split; [constructor|]. unfold ub. cbn [sum_len fold_right]. lia. }
  split; [|constructor].
  cbn [ev_chain]. unfold Gb, d_pending, d_bi_valid. rewrite A9, Etr. reflexivity.
Qed.

Theorem refill_ok : fill_spec -> refill_stmt.
Proof.
  intros Hfill s z flush HW Ho Hq Hz Ha Hfn Hfl.
  unfold c_refill.
  destruct (need_min_lookahead s) eqn:Hn.
  - assert (Hfp : fill_pre s).
    { destruct HW as (Hp & Hs & Hpos & Hw & Hh & _).
      assert (Hlev := fn_of_fast s Hp Hfn).
      unfold whash in Hh. destruct (Z.eqb_spec (d_level s) 0) as [E|N]; [lia|].
      destruct Hh as (_ & Hc).
      split; [exact Hp|]. split; [exact Hs|]. split; [exact Hpos|]. split; [exact Hw|exact Hc]. }
    destruct (Hfill s z Hfp Hz Ha) as (s' & z' & k & d & Hfw & Hfp' & Hk & Hst & Hd & Es & Eb & _ & _ &
      El & Hss & Hor & Hhw).
    destruct (refill_fill_FI s z flush s' z' k d HW Ho Hq Hz Ha Hfn Hfp' Hk Hst Es Eb El)
      as (HFI & Ews & Ewz & Eai).
    assert (EMD : MAX_DIST s' = MAX_DIST s) by (unfold MAX_DIST; rewrite Ews; reflexivity).
    assert (Hl0 : 0 <= d_lookahead s').
    { destruct Hfp' as (_ & _ & (P & _) & _). exact P. }
    rewrite Hfw. cbn [bind].
    destruct (need_min_lookahead s' && (flush =? Z_NO_FLUSH)) eqn:Hnf.
    + apply andb_true_iff in Hnf. destruct Hnf as (_ & Hf0). apply Z.eqb_eq in Hf0.
      eexists. split; [reflexivity|].
      split; [reflexivity|]. destruct HFI as (Hc & Hq' & _). split; [exact Hc|].
      unfold bpost. split; [constructor|split; [exact (proj2 (proj2 Hq'))|left; exact Hf0]].
    + destruct (Z.eqb_spec (d_lookahead s') 0) as [E0|N0].
      * eexists. split; [reflexivity|].
        split; [exact HFI|]. split; [exact E0|].
        split.
        { destruct Hor as [Hor|Hor]; [replace MIN_LOOKAHEAD with 262 in Hor by reflexivity; lia|exact Hor]. }
        split.
        { intros Hf0. unfold need_min_lookahead in Hnf. rewrite E0, Hf0 in Hnf. discriminate Hnf. }
        rewrite Ews, EMD. exact Hss.
      * eexists. split; [reflexivity|].
        split; [exact HFI|]. split.
        { right. rewrite Ews, Ewz, EMD. split; [exact Hss|exact Hhw]. }
        split; [lia|]. lia.
  - eexists. split; [reflexivity|].
    unfold need_min_lookahead in Hn. apply Z.ltb_ge in Hn.
    split; [apply FI_refl; assumption|]. split; [left; exact Hn|].
    split; [replace MIN_LOOKAHEAD with 262 in Hn by reflexivity; lia|reflexivity].
Qed.
