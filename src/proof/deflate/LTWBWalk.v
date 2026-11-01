(** * The deflateBound accounting for the short laws: one deflate() call

    The assembly of the stages (LTDefs.c_deflate_stages): entry (LTWBEntry), headers (LTWBHdr), compression
    (LTWBComp), trailer (LTWBTrail); [BrunW] gives [MidW] at the call and back at its end.  Port of
    LTBWalk.deflate_walk. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWBKit.
Require Import Zlib.proof.deflate.LTWBEntry Zlib.proof.deflate.LTWBHdr Zlib.proof.deflate.LTWBComp
  Zlib.proof.deflate.LTWBTrail.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma deflate_walk_w : forall W HI, core_facts_w W -> hdr_facts_w HI -> block_bound_statement ->
  forall n b pos fin s tin tout adler inb aout flush msg,
  BrunW W HI n b pos fin s tin tout adler ->
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH) -> (fin = true -> flush = Z_FINISH) ->
  bytes inb -> pos + Zlength inb <= n -> (flush = Z_FINISH -> pos + Zlength inb = n) ->
  0 <= aout <= 4294967295 -> Zlength inb <= 4294967295 ->
  (d_level s = 0 -> flush <> Z_NO_FLUSH -> ub s + Zlength inb <= 4294967295) ->
  exists s' z' code,
    c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) /\
    d_gzhead s' = d_gzhead s /\ (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_END) /\
    0 <= z_avail_in z' <= Zlength inb /\ z_total_out z' <= b /\
    (code <> Z_STREAM_END ->
     BrunW W HI n b (pos + Zlength inb - z_avail_in z') (flush =? Z_FINISH) s'
          (z_total_in z') (z_total_out z') (z_adler z')) /\
    (flush = Z_FINISH -> fin = false -> pos = 0 -> b <= tout + aout ->
     code = Z_STREAM_END /\ z_avail_in z' = 0).
Proof.
  intros W HI CF HF BB n b pos fin s tin tout adler inb aout flush msg HB Hfl Hfin Hinb Hpn HpF Ha Hib Hl0.
  destruct (brunw_status _ _ _ _ _ _ _ _ _ _ HF HB) as (Hbad & Hnf).
  pose proof (midw_start _ _ _ _ _ _ _ _ _ _ _ _ _ msg HB Hfl Hfin Hinb Hpn HpF Ha) as HM0.
  rewrite c_deflate_stages, Hbad.
  assert (Hfr : false || (flush >? Z_BLOCK) || (flush <? 0) = false)
    by (destruct Hfl as [E|E]; rewrite E; reflexivity).
  rewrite Hfr. cbn iota beta.
  destruct (entry_stage_w W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM0 eq_refl eq_refl)
    as (s1 & z1 & o1 & He & HM1 & Hn1 & Hst1 & Hw1 & Hce1 & _ & Ho1 & Hr1).
  rewrite He. destruct o1 as [c1|].
  { (* the entry stage returns *)
    cbn [then_stage bind]. exists s1, z1, c1. destruct Ho1 as (Hc1 & _).
    destruct (midw_out W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM1 (or_intror (or_intror Hn1)))
      as (Hgz & Hav & Hto & HB1).
    split; [reflexivity|]. split; [exact Hgz|]. split; [tauto|]. split; [exact Hav|].
    split; [exact Hto|]. split; [intros _; exact HB1|].
    intros HF' Hfin' Hp0 Hroom. specialize (Hr1 HF' Hp0 Hroom (Hnf Hfin')). discriminate. }
  destruct Ho1 as (Hp1 & Hpo1 & Hbv1 & Hfz1).
  cbn [then_stage bind].
  destruct (hdr_stage_w W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM1 Hn1 Hp1 Hpo1 Hbv1 Hfz1)
    as (s2 & z2 & o2 & Hh & HM2 & Hn2 & Hce2 & Ho2N & Ho2S & Hr2).
  rewrite Hh. destruct o2 as [c2|].
  { (* a header stage returns *)
    cbn [then_stage bind]. exists s2, z2, c2.
    destruct (midw_out W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM2 (or_intror (or_intror Hn2)))
      as (Hgz & Hav & Hto & HB2).
    split; [reflexivity|]. split; [exact Hgz|]. split; [left; exact (Ho2S c2 eq_refl)|].
    split; [exact Hav|]. split; [exact Hto|]. split; [intros _; exact HB2|].
    intros HF' Hfin' Hp0 Hroom. specialize (Hr2 HF' Hp0 Hroom). discriminate. }
  destruct (Ho2N eq_refl) as (Hst2 & Hp2 & Hpo2 & Hbv2 & Hfz2').
  assert (Hfz2 : d_status s2 = FINISH_STATE -> z_avail_in z2 = 0) by (intros E; exact (proj2 (Hfz2' E))).
  assert (Hbusy : fin = false -> d_status s2 = BUSY_STATE).
  { intros Hf. destruct Hst2 as [E|E]; [exact E|]. exfalso.
    apply (Hnf Hf). rewrite <- Hst1. exact (proj1 (Hfz2' E)). }
  cbn [then_stage bind].
  assert (Hl2 : d_level s2 = 0 -> flush <> Z_NO_FLUSH -> ub s2 + z_avail_in z2 <= 4294967295).
  { pose proof (core_eq_fields s s1 Hce1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & El1 & _).
    pose proof (core_eq_fields s1 s2 Hce2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & El2 & _).
    rewrite (ub_core_eq s1 s2 Hce2), (ub_core_eq s s1 Hce1), El2, El1.
    destruct HM2 as ((_ & _ & Hsum & _) & _). rewrite Hn2 in Hsum. rewrite Z.add_0_l in Hsum.
    rewrite Hsum. exact Hl0. }
  destruct (comp_stage_w BB W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM2 Hn2 Hib Hst2 Hp2 Hpo2 Hbv2 Hfz2 (or_introl Hl2))
    as (s3 & z3 & o3 & Hcm & HM3 & Hav3 & _ & Ho3N & Ho3S & Hr3).
  rewrite Hcm. destruct o3 as [c3|].
  { (* the compression stage returns *)
    cbn [bind]. exists s3, z3, c3.
    destruct (midw_out W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM3 (or_intror (or_introl Hav3)))
      as (Hgz & Hav & Hto & HB3).
    split; [reflexivity|]. split; [exact Hgz|]. split; [left; exact (Ho3S c3 eq_refl)|].
    split; [exact Hav|]. split; [exact Hto|]. split; [intros _; exact HB3|].
    intros HF' Hfin' Hp0 Hroom. specialize (Hr3 HF' Hp0 Hroom (Hbusy Hfin')). discriminate. }
  cbn [bind].
  destruct (trailer_stage_w W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM3 (Ho3N eq_refl))
    as (s4 & z4 & code & Ht & Hgz4 & _ & Hcf4 & Hcode & Hto4 & HSE & HM4 & Hr4).
  rewrite Ht. exists s4, z4, code.
  assert (Hav4 : flush = Z_FINISH \/ 0 <= z_avail_in z4 \/ z_next_in z4 = 0).
  { destruct Hfl as [E|E]; [right; left|left; exact E].
    unfold c_deflate_trailer in Ht. rewrite E in Ht. cbn [negb Z.eqb Z_NO_FLUSH Z_FINISH] in Ht.
    inversion Ht; subst; exact Hav3. }
  assert (Hav4' : 0 <= z_avail_in z4 <= Zlength inb).
  { destruct (Z.eq_dec code Z_STREAM_END) as [E|E].
    - rewrite (HSE E). pose proof (Zlength_nonneg inb). lia.
    - exact (proj1 (proj2 (midw_out W HI CF HF _ _ _ _ _ _ _ _ _ _ _ (HM4 E) Hav4))). }
  split; [reflexivity|]. split; [exact Hgz4|]. split; [tauto|]. split; [exact Hav4'|].
  split; [exact Hto4|]. split.
  - intros E. exact (proj2 (proj2 (proj2 (midw_out W HI CF HF _ _ _ _ _ _ _ _ _ _ _ (HM4 E) Hav4)))).
  - intros HF' Hfin' Hp0 Hroom. assert (Hc : code = Z_STREAM_END) by exact (Hr4 HF' Hroom).
    split; [exact Hc|exact (HSE Hc)].
Qed.
