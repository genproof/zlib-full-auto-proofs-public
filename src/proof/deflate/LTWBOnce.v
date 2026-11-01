(** * res_bound's one deflate(Z_FINISH): what the stream's fields say after it

    harness/res_bound.c checks, after the one deflate(Z_FINISH) call offered all [n] bytes of data and exactly
    deflateBound bytes of output space, that it read all of the data (avail_in 0, next_in at the data's end,
    total_in up by [n]) and that total_out counts the bytes it wrote (total_out was 0 before the call).
    LawFactsW.bw_once only says that the call returns Z_STREAM_END; [once_acct_w] adds the call frame of the stages
    (LTBDefs.cframe: next_in + avail_in = n, total_in = tin + next_in, |out| + avail_out = the output space,
    total_out = tout + |out|), and that deflateInit2 (with deflateSetDictionary / deflateSetHeader after it)
    leaves total_out at 0.  [bound_theory_acct] gives both from the same invariants as LTWBound.bound_theory_w. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWBKit.
Require Import Zlib.proof.deflate.LTWBEntry Zlib.proof.deflate.LTWBHdr Zlib.proof.deflate.LTWBComp
  Zlib.proof.deflate.LTWBTrail.
Require Import Zlib.proof.deflate.LTWBInit Zlib.proof.deflate.LTWBound.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The facts res_bound's main needs beyond [bound_facts_w]. *)
Definition once_acct_w (Bpre : bpre_inv) (Brun : brun_inv) : Prop :=
  (forall level wbits mem strategy ds s tin tout adler,
     Bpre level wbits mem strategy ds s tin tout adler -> tout = 0) /\
  (forall n b s tin tout adler data msg,
     Brun n b 0 false s tin tout adler -> b <= 4294967295 -> bytes data -> Zlength data = n ->
     exists s' z',
       c_deflate s (zcall data 0 n tin b tout adler msg) Z_FINISH = Some (s', z', Z_STREAM_END) /\
       d_gzhead s' = d_gzhead s /\
       z_avail_in z' = 0 /\ z_next_in z' = n /\ z_total_in z' = tin + n /\
       0 <= z_avail_out z' /\ Zlength (z_out z') + z_avail_out z' = b /\
       z_total_out z' = tout + Zlength (z_out z')).

(** The walk of LTWBWalk.deflate_walk_w for the first call, Z_FINISH with all the data and at least the bound's
    room: no stage returns before the trailer, which returns Z_STREAM_END with the call frame. *)
Lemma once_walk_cf : forall W HI, core_facts_w W -> hdr_facts_w HI -> block_bound_statement ->
  forall n b s tin tout adler inb aout msg,
  BrunW W HI n b 0 false s tin tout adler ->
  bytes inb -> Zlength inb = n -> 0 <= aout <= 4294967295 -> Zlength inb <= 4294967295 ->
  (d_level s = 0 -> ub s + Zlength inb <= 4294967295) -> b <= tout + aout ->
  exists s' z',
    c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) Z_FINISH = Some (s', z', Z_STREAM_END) /\
    d_gzhead s' = d_gzhead s /\ cframe inb aout tin tout z' /\ z_avail_in z' = 0.
Proof.
  intros W HI CF HF BB n b s tin tout adler inb aout msg HB Hinb Hn Ha Hib Hl0 Hroom.
  destruct (brunw_status _ _ _ _ _ _ _ _ _ _ HF HB) as (Hbad & Hnf).
  pose proof (midw_start _ _ _ _ _ _ _ _ _ _ inb aout Z_FINISH msg HB ltac:(right; reflexivity)
                ltac:(intros E; discriminate E) Hinb ltac:(lia) ltac:(intros _; lia) Ha) as HM0.
  rewrite c_deflate_stages, Hbad.
  change (false || (Z_FINISH >? Z_BLOCK) || (Z_FINISH <? 0)) with false.
  cbn iota beta.
  destruct (entry_stage_w W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM0 eq_refl eq_refl)
    as (s1 & z1 & o1 & He & HM1 & Hn1 & Hst1 & Hw1 & Hce1 & _ & Ho1 & Hr1).
  rewrite He.
  specialize (Hr1 eq_refl eq_refl Hroom (Hnf eq_refl)). subst o1.
  destruct Ho1 as (Hp1 & Hpo1 & Hbv1 & Hfz1).
  cbn [then_stage bind].
  destruct (hdr_stage_w W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM1 Hn1 Hp1 Hpo1 Hbv1 Hfz1)
    as (s2 & z2 & o2 & Hh & HM2 & Hn2 & Hce2 & Ho2N & _ & Hr2).
  rewrite Hh.
  specialize (Hr2 eq_refl eq_refl Hroom). subst o2.
  destruct (Ho2N eq_refl) as (Hst2 & Hp2 & Hpo2 & Hbv2 & Hfz2').
  assert (Hfz2 : d_status s2 = FINISH_STATE -> z_avail_in z2 = 0) by (intros E; exact (proj2 (Hfz2' E))).
  assert (Hbusy : d_status s2 = BUSY_STATE).
  { destruct Hst2 as [E|E]; [exact E|]. exfalso.
    apply (Hnf eq_refl). rewrite <- Hst1. exact (proj1 (Hfz2' E)). }
  cbn [then_stage bind].
  assert (Hl2 : d_level s2 = 0 -> Z_FINISH <> Z_NO_FLUSH -> ub s2 + z_avail_in z2 <= 4294967295).
  { pose proof (core_eq_fields s s1 Hce1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & El1 & _).
    pose proof (core_eq_fields s1 s2 Hce2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & El2 & _).
    rewrite (ub_core_eq s1 s2 Hce2), (ub_core_eq s s1 Hce1), El2, El1.
    destruct HM2 as ((_ & _ & Hsum & _) & _). rewrite Hn2 in Hsum. rewrite Z.add_0_l in Hsum.
    rewrite Hsum. intros L _. exact (Hl0 L). }
  destruct (comp_stage_w BB W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM2 Hn2 Hib Hst2 Hp2 Hpo2 Hbv2 Hfz2 (or_introl Hl2))
    as (s3 & z3 & o3 & Hcm & HM3 & Hav3 & _ & Ho3N & _ & Hr3).
  rewrite Hcm.
  specialize (Hr3 eq_refl eq_refl Hroom Hbusy). subst o3.
  cbn [bind].
  destruct (trailer_stage_w W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM3 (Ho3N eq_refl))
    as (s4 & z4 & code & Ht & Hgz4 & _ & Hcf4 & _ & _ & HSE & _ & Hr4).
  rewrite Ht.
  assert (Hc : code = Z_STREAM_END) by exact (Hr4 eq_refl Hroom). subst code.
  exists s4, z4.
  destruct HM0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hgz0 & _).
  split; [reflexivity|]. split; [rewrite Hgz4; exact Hgz0|]. split; [exact Hcf4|]. exact (HSE eq_refl).
Qed.

(** One deflate(Z_FINISH) offered all the data and b < 2^32 bytes of output space, from [BrunW] at the start. *)
Lemma once_acct_run_w : forall W HI, core_facts_w W -> hdr_facts_w HI -> block_bound_statement ->
  forall n b s tin tout adler data msg,
  BrunW W HI n b 0 false s tin tout adler -> b <= 4294967295 -> bytes data -> Zlength data = n ->
  exists s' z',
    c_deflate s (zcall data 0 n tin b tout adler msg) Z_FINISH = Some (s', z', Z_STREAM_END) /\
    d_gzhead s' = d_gzhead s /\
    z_avail_in z' = 0 /\ z_next_in z' = n /\ z_total_in z' = tin + n /\
    0 <= z_avail_out z' /\ Zlength (z_out z') + z_avail_out z' = b /\
    z_total_out z' = tout + Zlength (z_out z').
Proof.
  intros W HI CF HF BB n b s tin tout adler data msg HB Hb Hd Hn.
  destruct (brunw_facts W HI CF HF _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & Hpos & _).
  assert (Hnb : n <= b).
  { destruct HB as (H & w0 & _ & _ & _ & Hbe & _ & Hn' & _).
    pose proof (body_range_w (bcls_of s) n (proj1 Hn')). pose proof (Zlength_nonneg H).
    pose proof (tlen_range w0). lia. }
  assert (Hto : 0 <= tout) by (destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  subst n.
  destruct (once_walk_cf W HI CF HF BB (Zlength data) b s tin tout adler data b msg HB Hd eq_refl
              ltac:(pose proof (Zlength_nonneg data); lia) ltac:(lia)
              ltac:(rewrite (brunw_ub0 W HI CF _ _ _ _ _ _ _ HB); lia) ltac:(lia))
    as (s' & z' & E & G & Hcf & Hav).
  destruct Hcf as (_ & Hni & Hsum & Hti & Hao & Hout & Htout & _).
  exists s', z'. split; [exact E|]. split; [exact G|]. split; [exact Hav|].
  split; [lia|]. split; [lia|]. split; [exact Hao|]. split; [lia|]. exact Htout.
Qed.

(** [bound_facts_w] and [once_acct_w] on the invariants of LTWBound.bound_theory_w. *)
Theorem bound_theory_acct : block_bound_statement -> core_w_stmt -> hdr_w_stmt ->
  exists Bpre Brun, bound_facts_w Bpre Brun /\ once_acct_w Bpre Brun.
Proof.
  intros BB [W CF] [HI HF]. exists (BpreW W), (BrunW W HI). split.
  - constructor.
    + intros. apply bpre_init_w; auto.
    + intros. eapply bpre_dict_w; eauto.
    + intros. apply bpre_head_w; auto.
    + intros. eapply bound_of_bpre_w; eauto; lia.
    + intros. eapply once_w; eauto.
  - split.
    + intros level wbits mem strategy ds s tin tout adler HB.
      destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht & _). exact Ht.
    + intros. eapply once_acct_run_w; eauto.
Qed.
