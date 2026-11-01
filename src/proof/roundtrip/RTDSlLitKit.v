(* RT-D part SLOW, part LIT: helpers of RTDSlowFLit.v.  The step after the tally (and the
   flush): strstart++, lookahead--, then need_more or go on, functionally (the analogue of
   RTDLTCSlowLit.lit_post). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSlowKit.
Require Export Zlib.proof.roundtrip.RTDLTCSlowLit Zlib.proof.roundtrip.RTDLTCSlowFbo.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma sll_syms_rok_snoc w out syms c :
  syms_rok w out syms -> 0 <= c < 256 -> syms_rok w out (syms ++ [(0, c)]).
Proof.
  revert out. induction syms as [|a r IH]; intros out H Hc.
  - cbn. split; [exact Hc|exact I].
  - cbn [app syms_rok] in *. destruct H as [H1 H2]. split; [exact H1|]. apply IH; assumption.
Qed.

Lemma sll_syms_data_snoc out syms c :
  F.syms_data out (map fsym (syms ++ [(0, c)])) = F.syms_data out (map fsym syms) ++ [c].
Proof. unfold F.syms_data. rewrite map_app, fold_left_app. reflexivity. Qed.

Lemma sll_chain_hok_frame s s' :
  d_hash_size s' = d_hash_size s -> d_head s' = d_head s -> d_prev s' = d_prev s -> d_w_mask s' = d_w_mask s ->
  d_strstart s' + d_lookahead s' = d_strstart s + d_lookahead s -> lim s <= lim s' ->
  d_window s' = d_window s -> d_hash_shift s' = d_hash_shift s -> d_hash_mask s' = d_hash_mask s ->
  chain_hok s -> chain_hok s'.
Proof.
  intros E1 E2 E3 E4 E5 E6 E7 E8 E9 H b Hb. rewrite E1 in Hb. destruct (H b Hb) as (Gb & G0 & G1).
  exists Gb. rewrite E2. split; [exact G0|]. intros q Hq Hq0 Hl.
  destruct (G1 q Hq Hq0 ltac:(lia)) as (A & B & C).
  split; [lia|]. split.
  - unfold h3, update_hash in *. rewrite E7, E8, E9. exact B.
  - rewrite E3, E4. exact C.
Qed.

Lemma sll_primed_frame s s' n :
  d_ins_h s' = d_ins_h s -> d_window s' = d_window s -> d_hash_shift s' = d_hash_shift s ->
  d_hash_mask s' = d_hash_mask s -> primed s n -> primed s' n.
Proof.
  intros E1 E2 E3 E4 (h0 & H). exists h0. unfold update_hash in *. rewrite E1, E2, E3, E4. exact H.
Qed.

(** After the tally (and the flush), functionally. *)
Lemma flit_fin dict D BS p s0 z0 flush s z evs s1 s3 z3 k x3 BS3 syms3 :
  let D' := D ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0) in
  let H := dict ++ D' in
  let off := Zlength H - (d_strstart s + d_lookahead s) in
  SI s0 z0 flush s z evs -> rdy s -> MID s s1 -> FMID s s1 ->
  ~ (MIN_MATCH <= d_prev_length s1 /\ d_match_length s1 <= d_prev_length s1) -> d_match_available s1 <> 0 ->
  kwin H s -> khash s ->
  lk s3 = lk s ->
  d_prev s3 = d_prev s1 -> d_head s3 = d_head s1 -> d_ins_h s3 = d_ins_h s1 ->
  d_match_length s3 = d_match_length s1 -> d_match_start s3 = d_match_start s1 ->
  d_strstart s3 = d_strstart s -> d_lookahead s3 = d_lookahead s ->
  tree_ok (d_tr s3) (d_pbm s3) syms3 -> Zlength syms3 <= d_L s - 2 -> Forall (sym_ok s) syms3 ->
  blk_len syms3 = d_strstart s - d_block_start s3 ->
  tr_cfg (d_tr s3) = tr_cfg (d_tr s) ->
  zstep (d_wrap s0) z0 z3 k x3 ->
  F.blocks_ok (2 ^ d_w_bits s) dict (BS ++ BS3) ->
  F.expand dict (BS ++ BS3) = sublist 0 (off + d_block_start s3) H ->
  syms_rok (2 ^ d_w_bits s) (F.expand dict (BS ++ BS3)) syms3 ->
  F.syms_data (F.expand dict (BS ++ BS3)) (map fsym syms3) = sublist 0 (off + d_strstart s) H ->
  F.bytes_bits (x3 ++ pend s3) ++ bibits s3 = bibits s0 ++ enc_out p BS3 false ->
  fstep_ok dict D BS p s0 z0
    (let s' := set_d_strstart s3 (u32 (d_strstart s3 + 1)) in
     let s' := set_d_lookahead s' (u32 (d_lookahead s' - 1)) in
     if z_avail_out z3 =? 0 then inr (s', z3, Some need_more) else inl (s', z3)).
Proof.
  intros D' H off HSI Hrdy HMID HFM Hnot Hav Hkw Hkh Hlk Ep Eh Ei Eml Ems Ess Ela HT HLen HFs Hblk Hcfg
    Hz Hb He Hr Hd Hbits.
  destruct HSI as (HW2 & Hq & HLs & HEI). destruct HW2 as [HW Hse].
  destruct HW as (Hp & Hws & Hwp & Hww & Hwh & Hwm & Hl0 & _).
  destruct HMID as (Hpk & Hws1 & _ & Hpl1 & Hpm1 & Hml1 & Hmid).
  destruct HFM as (Hch1 & Hpr1 & Hfm).
  pose proof (lk_pre s s1 Hpk) as H1.
  lkf H1 d_match_available. rename E into Eav1.
  destruct Hwm as (Wm1 & Wm2 & Wm3 & Wm4 & Wm5).
  assert (Hav0 : d_match_available s = 1) by (clear - Eav1 Wm3 Hav; lia).
  destruct (Wm5 Hav0) as (Hfn & HS1 & _).
  assert (Hlev : d_level s <> 0).
  { intros E. unfold fn_of in Hfn. rewrite E in Hfn. discriminate. }
  pose proof (wsize_range s Hp) as Hwsz.
  destruct Hrdy as (Hla & Hroom & Hdef).
  destruct Hwp as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  destruct Hws as (S1 & S2 & S3 & S4 & S5).
  assert (HPm : MIN_MATCH <= d_match_length s1 -> d_prev_length s1 < d_match_length s1)
    by (clear - Hnot; lia).
  cbv zeta.
  set (s4 := set_d_lookahead (set_d_strstart s3 (u32 (d_strstart s3 + 1)))
               (u32 (d_lookahead (set_d_strstart s3 (u32 (d_strstart s3 + 1))) - 1))).
  assert (Gss : d_strstart s4 = d_strstart s + 1).
  { change (u32 (d_strstart s3 + 1) = d_strstart s + 1). rewrite Ess. apply u32_small. clear - P1 P2 P3 S3 Hwsz; lia. }
  assert (Gla : d_lookahead s4 = d_lookahead s - 1).
  { change (u32 (d_lookahead s3 - 1) = d_lookahead s - 1). rewrite Ela. apply u32_small. clear - P1 P2 P3 S3 Hwsz Hla; lia. }
  assert (H4 : lk s4 = lk s) by (unfold s4; rewrite lk_pos; exact Hlk).
  assert (H41 : lk s4 = lk s1) by congruence.
  lkf H4 d_w_size. rename E into Gws.
  lkf H4 d_w_bits. rename E into Gwb.
  lkf H4 d_window. rename E into Gwin.
  lkf H4 d_insert. rename E into Gins.
  lkf H4 d_match_available. rename E into Gav.
  lkf H41 d_hash_size. rename E into Ghs1.
  lkf H41 d_w_mask. rename E into Gwm1.
  lkf H41 d_window. rename E into Gwin1.
  lkf H41 d_hash_shift. rename E into Gsh1.
  lkf H41 d_hash_mask. rename E into Ghm1.
  lkf Hpk d_strstart. rename E into Fss.
  lkf Hpk d_lookahead. rename E into Fla.
  lkf Hpk d_window. rename E into Fwin.
  assert (Gcfg : tr_cfg (d_tr s4) = tr_cfg (d_tr s)) by exact Hcfg.
  pose proof Gcfg as Gc. unfold tr_cfg in Gc. injection Gc as C1 C2 C3 C4.
  assert (GL : d_L s4 = d_L s) by exact C1.
  assert (Glev : d_level s4 = d_level s) by exact C3.
  assert (Gstr : d_strategy s4 = d_strategy s) by exact C4.
  assert (Gfn : fn_of s4 = fn_of s) by (unfold fn_of; rewrite Glev, Gstr; reflexivity).
  assert (Gbs : d_block_start s4 = d_block_start s3) by reflexivity.
  assert (Gml : d_match_length s4 = d_match_length s1) by exact Eml.
  assert (Gms : d_match_start s4 = d_match_start s1) by exact Ems.
  assert (Gp : d_prev s4 = d_prev s1) by exact Ep.
  assert (Gh : d_head s4 = d_head s1) by exact Eh.
  assert (Gi : d_ins_h s4 = d_ins_h s1) by exact Ei.
  assert (Gwl : d_strstart s4 + d_lookahead s4 = d_strstart s + d_lookahead s) by (rewrite Gss, Gla; lia).
  assert (Hoff : Zlength H - (d_strstart s4 + d_lookahead s4) = off) by (rewrite Gwl; reflexivity).
  assert (Hpend : pend s4 = pend s3) by reflexivity.
  assert (Hbib : bibits s4 = bibits s3) by reflexivity.
  destruct Hkw as [Hkw1 Hkw2].
  assert (Hoff0 : 0 <= off) by (unfold off; lia).
  (* kcore3 *)
  assert (Hk : kcore3 dict D' (BS ++ BS3) syms3 s4).
  { split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
    - (* kwin *)
      split; [rewrite Gwl; exact Hkw1|]. intros i Hi. rewrite Gwin, Gwl. apply Hkw2. rewrite <- Gwl. exact Hi.
    - (* kmatch3 *)
      intros _ Hm3. cbv zeta. rewrite Gml in Hm3.
      destruct (Hmid Hm3) as (Hm4 & _).
      destruct (Hfm Hm3 (HPm Hm3)) as (_ & (Hms0 & Hms1) & Hbyt).
      rewrite Fss in Hms1.
      rewrite Gss, Gms, Gla, Gml. fold H.
      replace (d_strstart s + 1 - 1 - d_match_start s1) with (d_strstart s - d_match_start s1) by lia.
      rewrite u32_small by (clear - Hms0 Hms1 P1 P2 P3 S3 Hwsz; lia).
      split; [clear - Hms0 Hms1 Hkw1 Hla; lia|]. intros i Hi.
      replace (Zlength H - (d_lookahead s - 1) - 1 - (d_strstart s - d_match_start s1) + i)
        with (Zlength H - (d_strstart s + d_lookahead s) + (d_match_start s1 + i)) by lia.
      replace (Zlength H - (d_lookahead s - 1) - 1 + i)
        with (Zlength H - (d_strstart s + d_lookahead s) + (d_strstart s + i)) by lia.
      pose proof (Hm4) as Hm4'. 
      rewrite <- (Hkw2 (d_match_start s1 + i)) by (clear - Hms0 Hms1 Hi Hm4; lia).
      rewrite <- (Hkw2 (d_strstart s + i)) by (clear - Hms0 Hms1 Hi Hm4 P2; lia).
      rewrite <- Fwin, <- Fss. apply Hbyt. exact Hi.
    - (* wtrees *)
      unfold wtrees. split; [exact HT|]. split; [rewrite GL; exact HLen|]. split.
      + eapply Forall_impl; [|exact HFs]. intros y. apply sym_ok_frame; assumption.
      + rewrite Glev. split; [intros E; contradiction|]. intros _.
        rewrite Gav, Gss, Gbs. clear - Hblk Hav0; lia.
    - rewrite Gwb. exact Hb.
    - fold H. rewrite Hoff, Gbs. exact He.
    - rewrite Gwb. exact Hr.
    - fold H. rewrite Hoff, Glev, (proj2 (Z.eqb_neq _ _) Hlev), Gav, Gss, Hav0.
      replace (off + (d_strstart s + 1 - 1)) with (off + d_strstart s) by lia. exact Hd.
    - (* khash *)
      destruct Hkh as [_ Hkh2]. split.
      + rewrite Glev, (proj2 (Z.eqb_neq _ _) Hlev).
        apply (sll_chain_hok_frame s1 s4 Ghs1 Gh Gp Gwm1); [| |exact Gwin1|exact Gsh1|exact Ghm1|exact Hch1].
        * rewrite Gwl, Fss, Fla. reflexivity.
        * apply lim_mono; [rewrite Gws; lkf H1 d_w_size; congruence|rewrite Gss, Fss; lia].
      + intros Hf Hl3. rewrite Gfn in Hf. rewrite Gla in Hl3.
        destruct (Hkh2 Hf ltac:(clear - Hl3; lia)) as [Hi0 _]. split; [rewrite Gins; exact Hi0|].
        rewrite Gss. apply (sll_primed_frame s1 s4 _ Gi Gwin1 Gsh1 Ghm1).
        apply Hpr1. clear - Hl3; lia. }
  destruct (Z.eqb_spec (z_avail_out z3) 0) as [A0|A0]; cbn [fstep_ok FI FQ].
  - exists k, x3, BS3, syms3. split; [exact Hz|]. split; [exact Hk|]. split.
    + rewrite Hpend, Hbib. exact Hbits.
    + intros E. discriminate E.
  - exists k, x3, BS3, syms3. split; [exact Hz|]. split; [exact Hk|].
    rewrite Hpend, Hbib. exact Hbits.
Qed.
