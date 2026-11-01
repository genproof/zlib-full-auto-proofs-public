(** * deflate_slow for wide streams, part End: after the loop's break

    Port of LTCSlowEnd.v to the invariant [SIw] / [EIw] of DetCoreSlowInv.v; the helpers that do not mention
    the invariant are LTCSlowEnd's. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetCoreSlowInv.
Require Import Zlib.proof.deflate.LTCSlowEnd.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** EIw, quiet and prm carry over to the state after the literal. *)
Lemma se_EIw s0 z0 flush s z evs t m :
  EIw s0 z0 flush s z evs -> tally_frame (d_tr s) (d_pbm s) t m -> EIw s0 z0 flush (se_s2 s t m) z evs.
Proof.
  intros (Hc & Hf & Ho & Hsp & Hapi & Hz & Ha & Hk & Hch & Hev) Hfr.
  pose proof Hfr as (Hcfg & Hmt & Hpd & Hbb & Hbv & Hbu & Hg).
  assert (E_L : tr_lit_bufsize t = d_L s) by exact (f_equal (fun c => fst (fst (fst c))) Hcfg).
  assert (E_lev : tr_level t = d_level s) by exact (f_equal (fun c => snd (fst c)) Hcfg).
  assert (E_str : tr_strategy t = d_strategy s) by exact (f_equal (fun c => snd c) Hcfg).
  split; [exact Hc|]. split; [exact Hf|].
  split.
  { apply (outok_grow s); [exact Ho|exact Hg|reflexivity|exact Hpd|reflexivity|].
    destruct Ho as (_ & Hbo & _). change (bits_ok (tr_out t)). unfold bits_ok in *.
    rewrite Hbv, Hbb, Hpd. exact Hbo. }
  split.
  { destruct Hsp as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
    split; [change (tr_lit_bufsize t = d_L s0); rewrite E_L; exact A4|].
    split; [exact A5|]. split; [change (tr_level t = d_level s0); rewrite E_lev; exact A6|].
    change (tr_strategy t = d_strategy s0); rewrite E_str; exact A7. }
  split; [exact Hapi|]. split; [exact Hz|]. split; [exact Ha|]. split; [exact Hk|].
  split; [|exact Hev].
  replace (Gb (se_s2 s t m) (z_total_out z)) with (Gb s (z_total_out z)); [exact Hch|].
  change (8 * (z_total_out z + o_pending (tr_out (d_tr s))) + o_bi_valid (tr_out (d_tr s)) =
          8 * (z_total_out z + o_pending (tr_out t)) + o_bi_valid (tr_out t)).
  rewrite Hpd, Hbv. reflexivity.
Qed.

(** cpost from EIw. *)
Lemma se_cpostw s0 z0 flush s z bs evs :
  W2 s -> EIw s0 z0 flush s z evs ->
  match bs with
  | need_more =>
      Forall (fun e => ev_last e = 0) evs /\ d_bi_valid s <= 7 /\
      (flush = Z_NO_FLUSH \/ z_avail_out z = 0 \/ d_level s0 = 0)
  | block_done =>
      Forall (fun e => ev_last e = 0) evs /\ flush <> Z_NO_FLUSH /\ flush <> Z_FINISH /\
      z_avail_in z = 0 /\ ub s = 0 /\ quiet s /\ d_sym_next s = 0
  | finish_started =>
      last_ev evs /\ flush = Z_FINISH /\ z_avail_in z = 0 /\ ub s = 0 /\ d_sym_next s = 0 /\
      d_bi_valid s = 0 /\ z_avail_out z = 0 /\ (d_level s0 <> 0 -> d_pending s <> 0 \/ d_wrap s0 <> 0)
  | finish_done =>
      last_ev evs /\ flush = Z_FINISH /\ z_avail_in z = 0 /\ ub s = 0 /\ d_sym_next s = 0 /\
      quiet s /\ d_bi_valid s = 0
  end ->
  cpost W2 s0 z0 flush s z bs evs.
Proof.
  intros HW (_ & _ & Ho & Hsp & Hapi & _ & _ & Hz & Hc & He) Hb.
  unfold cpost. split; [exact HW|]. split; [exact Ho|]. split; [exact Hsp|]. split; [exact Hapi|].
  split; [exact Hz|]. split; [exact Hc|]. split; [exact He|]. exact Hb.
Qed.

Theorem end_okw : tally_spec2 -> fboev_partw -> end_partw.
Proof.
  intros Htal Hfbo s0 z0 flush s z evs HSI Hla Hai Hnf Hss.
  pose proof HSI as (HW2 & Hq & HL & HE).
  pose proof HE as (Hc0 & Hfn0 & Ho & Hsp & Hapi & Hz & Had & _ & _ & _).
  assert (Hlev : d_level s <> 0).
  { destruct Hsp as (_ & _ & _ & _ & _ & E & _). rewrite E. intro E0.
    unfold fn_of in Hfn0. rewrite E0 in Hfn0. cbn [Z.eqb] in Hfn0. discriminate. }
  destruct (se_lit s Htal HW2 Hla Hlev) as (t & m & syms1 & Hdsl & Ht1 & Hlen1 & Hsy1 & Hblk1 & Hfr).
  rewrite Hdsl.
  pose proof HW2 as [HW _]. pose proof HW as (Hp & Hs & Hpos & Hw & Hh & Hm & _ & _).
  destruct (se_prm_bounds s Hp) as [Hws HLb].
  pose proof Hpos as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _).
  pose proof Hs as (S1 & S2 & S3 & S4 & S5).
  pose proof Hfr as (Hcfg & Hmt & Hpd & Hbb & Hbv & Hbu & Hg).
  assert (E_L : tr_lit_bufsize t = d_L s) by exact (f_equal (fun c => fst (fst (fst c))) Hcfg).
  assert (E_lev : tr_level t = d_level s) by exact (f_equal (fun c => snd (fst c)) Hcfg).
  assert (E_str : tr_strategy t = d_strategy s) by exact (f_equal (fun c => snd c) Hcfg).
  assert (HE2 := se_EIw s0 z0 flush s z evs t m HE Hfr).
  assert (Hq2 := se_quiet s t m Hq Hfr).
  assert (Hp2 := se_prm s t m Hp Hfr).
  assert (Hmat : d_matches s = 0).
  { unfold whash in Hh. rewrite (proj2 (Z.eqb_neq _ _) Hlev) in Hh. exact (proj1 Hh). }
  assert (Hsy2 : Forall (sym_ok (se_s2 s t m)) syms1).
  { eapply Forall_impl; [|exact Hsy1]. intros x Hx. unfold sym_ok in *.
    change (d_level (se_s2 s t m)) with (tr_level t). change (d_strategy (se_s2 s t m)) with (tr_strategy t).
    rewrite E_lev, E_str. exact Hx. }
  assert (Hpre : forall last, 0 <= last <= 1 -> fbo_pre (se_s2 s t m) z syms1 last).
  { intros last Hl. unfold fbo_pre.
    split; [exact Hp2|]. split; [exact Hs|].
    split; [change (0 < tr_level t); rewrite E_lev;
            destruct Hp as (_&_&_&_&_&_&_&_&_&_&_&_&P13&_); lia|].
    split; [exact Ht1|]. split; [change (Zlength syms1 <= tr_lit_bufsize t - 1); rewrite E_L; exact Hlen1|].
    split; [exact Hblk1|]. split; [exact Q4|]. split; [exact Q5|].
    split.
    { intros Hb0. change (0 <= d_block_start s) in Hb0. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hss.
      split; [change (d_strstart s - d_block_start s <= 65535); lia|].
      split; [change (d_strstart s <= Zlength (mb_val (d_window s))); lia|].
      intros i Hi. apply Hw. rewrite Hla. change (d_block_start s <= i < d_strstart s) in Hi. lia. }
    split; [exact (proj1 (proj2 (proj2 HE2)))|]. split; [exact Hq2|]. split; [exact Hl|].
    destruct Hz as [_ Hzo]. exact Hzo. }
  unfold c_deflate_tail.
  destruct (Z.eqb_spec flush Z_FINISH) as [EF|EF].
  - destruct (Hfbo s0 z0 flush (se_s2 s t m) z evs syms1 1 HE2 (Hpre 1 ltac:(lia)) Hsy2
                (fun _ => EF) ltac:(intros H; discriminate H) Q6)
      as (s3 & z3 & e & Hc & Hlast & HE3 & Hk & Hbs3 & Ht3 & Hcfg3 & Hm3 & Hbv3 & Hbv31 & Hpz & Hai3).
    specialize (Hbv31 eq_refl).
    destruct (se_after s t m s3 HW2 Hla Hlev Hfr Hk Hbs3 Ht3 Hcfg3 Hm3) as (HW3 & Hub3 & Hsn3).
    pose proof HE3 as (_ & _ & Ho3 & Hsp3 & Hapi3 & _).
    assert (Hlev_ := se_last_ev evs e HL Hlast).
    assert (Hstarted : z_avail_out z3 = 0 -> d_pending s3 <> 0 \/ d_wrap s3 <> 0 ->
              cpost W2 s0 z0 flush s3 z3 finish_started (evs ++ [e])).
    { intros E PW. apply se_cpostw; [exact HW3|exact HE3|]. hnf.
      split; [exact Hlev_|]. split; [exact EF|]. split; [rewrite Hai3; exact Hai|]. split; [exact Hub3|].
      split; [exact Hsn3|]. split; [exact Hbv31|]. split; [exact E|].
      intros _. destruct Hapi3 as (_ & Hwr & _). rewrite <- Hwr. exact PW. }
    assert (Hdone : d_pending s3 = 0 -> cpost W2 s0 z0 flush s3 z3 finish_done (evs ++ [e])).
    { intros P0. apply se_cpostw; [exact HW3|exact HE3|]. hnf.
      split; [exact Hlev_|]. split; [exact EF|]. split; [rewrite Hai3; exact Hai|]. split; [exact Hub3|].
      split; [exact Hsn3|]. split; [|exact Hbv31].
      split; [exact P0|]. split; [|lia]. destruct Ho3 as (_ & _ & _ & _ & _ & Ho3'). exact (Ho3' P0). }
    unfold c_flush_block. rewrite Hc. cbn [bind].
    destruct (Z.eqb_spec (z_avail_out z3) 0) as [E|E];
      destruct (Z.eqb_spec (d_pending s3) 0) as [P|P];
      destruct (Z.eqb_spec (d_wrap s3) 0) as [Wr|Wr]; cbn [andb orb negb Z.eqb Pos.eqb bind].
    + exists s3, z3, finish_done, (evs ++ [e]). split; [reflexivity|]. exact (Hdone P).
    + exists s3, z3, finish_started, (evs ++ [e]). split; [reflexivity|]. exact (Hstarted E (or_intror Wr)).
    + exists s3, z3, finish_started, (evs ++ [e]). split; [reflexivity|]. exact (Hstarted E (or_introl P)).
    + exists s3, z3, finish_started, (evs ++ [e]). split; [reflexivity|]. exact (Hstarted E (or_introl P)).
    + exists s3, z3, finish_done, (evs ++ [e]). split; [reflexivity|]. exact (Hdone P).
    + exists s3, z3, finish_done, (evs ++ [e]). split; [reflexivity|]. exact (Hdone P).
    + destruct Hpz; contradiction.
    + destruct Hpz; contradiction.
  - destruct (Z.eqb_spec (d_sym_next (se_s2 s t m)) 0) as [S0|S0]; cbn [negb].
    + assert (Hsy : syms1 = []).
      { destruct Ht1 as (_ & _ & T3 & _). change (tr_sym_next t = 0) in S0. rewrite S0 in T3.
        destruct syms1 as [|y syms1]; [reflexivity|]. rewrite Zlength_cons in T3.
        pose proof (Zlength_nonneg syms1). lia. }
      subst syms1. rewrite se_blk_len_nil in Hblk1.
      exists (se_s2 s t m), z, block_done, evs. split; [reflexivity|].
      apply se_cpostw; [|exact HE2|].
      { apply (se_W2_fin s _ HW2 Hla Hlev).
        - exact (se_kp_s2 s t m).
        - reflexivity.
        - reflexivity.
        - change (d_block_start s = d_strstart s). lia.
        - exact Ht1.
        - exact Hcfg.
        - change (tr_matches t = 0). rewrite Hmt. exact Hmat. }
      hnf. split; [exact HL|]. split; [exact Hnf|]. split; [exact EF|]. split; [exact Hai|].
      split; [change (d_strstart s - d_block_start s + d_lookahead s = 0); lia|].
      split; [exact Hq2|]. exact S0.
    + destruct (Hfbo s0 z0 flush (se_s2 s t m) z evs syms1 0 HE2 (Hpre 0 ltac:(lia)) Hsy2
                  ltac:(intros H; discriminate H) ltac:(intros _; right; split; assumption) Q6)
        as (s3 & z3 & e & Hc & Hlast & HE3 & Hk & Hbs3 & Ht3 & Hcfg3 & Hm3 & Hbv3 & _ & Hpz & Hai3).
      destruct (se_after s t m s3 HW2 Hla Hlev Hfr Hk Hbs3 Ht3 Hcfg3 Hm3) as (HW3 & Hub3 & Hsn3).
      pose proof HE3 as (_ & _ & Ho3 & _).
      assert (HL3 := se_last0 evs e HL Hlast).
      unfold c_flush_block. rewrite Hc. cbn [bind].
      destruct (Z.eqb_spec (z_avail_out z3) 0) as [E|E]; cbn [andb orb negb Z.eqb Pos.eqb bind].
      * exists s3, z3, need_more, (evs ++ [e]). split; [reflexivity|].
        apply se_cpostw; [exact HW3|exact HE3|]. hnf. split; [exact HL3|]. split; [exact Hbv3|]. right; left; exact E.
      * exists s3, z3, block_done, (evs ++ [e]). split; [reflexivity|].
        assert (P0 : d_pending s3 = 0) by (destruct Hpz; [assumption|contradiction]).
        apply se_cpostw; [exact HW3|exact HE3|]. hnf.
        split; [exact HL3|]. split; [exact Hnf|]. split; [exact EF|]. split; [rewrite Hai3; exact Hai|].
        split; [exact Hub3|]. split; [|exact Hsn3].
        split; [exact P0|]. split; [|exact Hbv3].
        destruct Ho3 as (_ & _ & _ & _ & _ & Ho3'). exact (Ho3' P0).
Qed.
