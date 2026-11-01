(** * deflate_slow for wide streams: cf_still (next_in never goes back during deflate_slow)

    Port of LTCStillSlowKit.v (the facts that mention the invariant) and LTCStillSlow.v ([still_slow_ok]) to
    [compress_pre2w] and the invariant of DetCoreSlowInv.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetCoreSlowInv.
Require Import Zlib.proof.deflate.LTCSlowRefill Zlib.proof.deflate.LTCSlow2 Zlib.proof.deflate.LTCStillSlowKit
  Zlib.proof.deflate.DetCoreSlowRefill Zlib.proof.deflate.DetCoreSlowLoop.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma ss_fill_prew s0 z0 flush s z evs : SIw s0 z0 flush s z evs ->
  fill_pre s /\ zall z /\ adler_ok (d_wrap s) (z_adler z).
Proof.
  intros HSI. pose proof HSI as (HW2 & Hq & HL & HE).
  destruct HW2 as [HW Hx].
  destruct HW as (Hp & Hws & Hpos & Hwin & Hh & Hm & H0 & syms & Ht).
  destruct HE as (Hc & Hf & Ho & Hsp & Hapi & Hza & Had & _ & _ & _).
  assert (Hlv : d_level s <> 0) by (apply rf_fn_level; rewrite (rf_fn_same s0 s Hsp); exact Hf).
  split; [|split; [exact Hza|]].
  - split; [exact Hp|]. split; [exact Hws|]. split; [exact Hpos|]. split; [exact Hwin|].
    unfold whash in Hh. destruct (Z.eqb_spec (d_level s) 0) as [E|_]; [contradiction|]. apply Hh.
  - destruct Hapi as (_ & B & _); rewrite B; exact Had.
Qed.

Lemma ss_bodyw s0 z0 flush s z r : fill_spec -> slow_Pw s0 z0 flush (s, z) -> dsl_body flush (s, z) = Some r ->
  z_next_in z <= z_next_in (ss_z r).
Proof.
  intros Hfill [evs HSI]. cbn [fst snd] in HSI.
  destruct (ss_fill_prew s0 z0 flush s z evs HSI) as (Hfp & Hza & Had).
  unfold dsl_body, c_refill, need_min_lookahead.
  destruct (d_lookahead s <? MIN_LOOKAHEAD).
  - destruct (Hfill s z Hfp Hza Had) as (s' & z' & k & d & Ec & _ & _ & Hz & _).
    pose proof Hz as (_ & Hk & Hn & _).
    rewrite Ec. unfold bind.
    destruct (_ && _); [intros H; inversion H; subst; cbn; lia|].
    destruct (_ =? 0); [intros H; inversion H; subst; cbn; lia|].
    intros H. apply ss_step in H. lia.
  - unfold bind. intros H. apply ss_step in H. lia.
Qed.

Lemma ss_runsw s0 z0 flush : fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec ->
  forall a b, runs (dsl_body flush) a b -> slow_Pw s0 z0 flush a -> z_next_in (snd a) <= z_next_in (ss_z (inr b)).
Proof.
  intros Hfill Hins Hlm Htally Hfbo a b Hr. induction Hr as [a b E|a a' b E Hr IH]; intros HP.
  - destruct a as [s z]. exact (ss_bodyw s0 z0 flush s z (inr b) Hfill HP E).
  - destruct a as [s z]. pose proof (ss_bodyw s0 z0 flush s z (inl a') Hfill HP E) as H1.
    destruct (slow_body_okw Hfill Hins Hlm Htally Hfbo s0 z0 flush (s, z) HP) as (_ & r & E' & Hr').
    rewrite E in E'. inversion E'; subst r. destruct Hr' as [HP' _].
    specialize (IH HP'). destruct a' as [s' z']. cbn in *. lia.
Qed.

Lemma ss_fill0w s z flush : fill_spec -> SIw s z flush s z [] -> still_at s ->
  exists s1 z1 k, c_fill_window s z = Some (s1, z1) /\ d_strstart s1 = 0 /\ d_match_available s1 = 0 /\
    d_lookahead s1 = k /\ z_next_in z1 = z_next_in z + k /\ 0 <= k.
Proof.
  intros Hfill HI (ES0 & EB0 & EL0).
  destruct (ss_fill_prew s z flush s z [] HI) as (Hfp & Hza & Had).
  pose proof HI as ((HW & _) & _).
  destruct HW as (Hp & _ & _ & _ & _ & Hm & _).
  pose proof (rf_w512 s Hp) as Hw.
  destruct (Hfill s z Hfp Hza Had) as (s1 & z1 & k & d & Ec & _ & Hk & Hz & Hd & ES & _ & _ & _ & EL1 & _).
  pose proof (rf_fw_keep s s1 Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ema & _).
  pose proof Hz as (_ & Hk0 & Hn & _).
  exists s1, z1, k. split; [exact Ec|]. split.
  { rewrite ES, ES0. destruct Hd as [Hd|[Hd Hd2]]; [lia|].
    unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. lia. }
  split.
  { rewrite Ema. destruct Hm as (_ & _ & [M|M] & _ & M5); [exact M|].
    destruct (M5 M) as (_ & M6 & _). lia. }
  split; [lia|]. split; [exact Hn|]. lia.
Qed.

Theorem still_slow_okw : fill_idem_spec -> fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec ->
  fpend_spec2 -> slow_spec2w ->
  forall s z flush, compress_pre2w s z flush -> still_at s -> fn_of s = 2 -> still_concl c_deflate_slow s z flush.
Proof.
  intros _ Hfill Hins Hlm Htally Hfbo _ _ s z flush Hpre Hst Hfn s' z' bs E Enx.
  pose proof (SIw_init s z flush Hpre Hfn) as HI.
  apply ss_slow_inv in E. destruct E as (s2 & z2 & o & EL & E).
  apply loop_runs in EL.
  apply ss_loop_end in E. destruct E as (Fn & Fs & Fo).
  destruct (ss_fill0w s z flush Hfill HI Hst) as (s1 & z1 & k & Ec & ES1 & Hma & EL1 & Hn & Hk0).
  pose proof (ss_first s z s1 z1 flush (proj2 (proj2 Hst)) Ec) as Eb.
  apply runs_inv in EL. destruct EL as [EL|(a' & EL & Hr)].
  - rewrite Eb in EL.
    destruct ((d_lookahead s1 <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH)).
    + injection EL as <- <- <-. rewrite (Fo ltac:(discriminate)). exact ES1.
    + destruct (Z.eqb_spec (d_lookahead s1) 0) as [E0|E0].
      * injection EL as <- <- <-. rewrite (Fs eq_refl Hma). exact ES1.
      * apply ss_step in EL. simpl ss_z in EL. lia.
  - pose proof (ss_runsw s z flush Hfill Hins Hlm Htally Hfbo a' _ Hr) as Hmono.
    destruct (slow_body_okw Hfill Hins Hlm Htally Hfbo s z flush (s, z) (ex_intro _ [] HI)) as (_ & r & E' & Hr').
    rewrite EL in E'. injection E' as <-. destruct Hr' as [HP' _]. specialize (Hmono HP').
    rewrite Eb in EL. simpl ss_z in Hmono.
    destruct ((d_lookahead s1 <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH)); [discriminate|].
    destruct (Z.eqb_spec (d_lookahead s1) 0) as [E0|E0]; [discriminate|].
    apply ss_step in EL. destruct a' as [sa za]. simpl ss_z in EL. simpl snd in Hmono. lia.
Qed.
