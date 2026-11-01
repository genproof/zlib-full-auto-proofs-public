(** * deflate_bound theory: one deflate() call of deflate_bound(_split)

    The assembly of the stages (LTDefs.c_deflate_stages): entry (LTBStages), headers (LTBHdrSt), compression
    (LTBComp), trailer (LTBStages); [Brun] gives [Mid] at the call and back at its end. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTBEntry Zlib.proof.deflate.LTBTrail Zlib.proof.deflate.LTBHdrSt Zlib.proof.deflate.LTBComp.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Helpers *)

(** [fin] matters only in the phase P3. *)
Lemma brun_fin : forall W HI n b pos fin fin' s tin tout adler,
  Brun W HI n b pos fin s tin tout adler -> (fin = true -> fin' = true) ->
  Brun W HI n b pos fin' s tin tout adler.
Proof.
  intros W HI n b pos fin fin' s tin tout adler (H & w0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & Hph) Hf.
  exists H, w0. do 11 (split; [assumption|]).
  unfold bphase in *. destruct Hph as [P|[P|[P|P]]];
    [left; exact P|right; left; exact P|right; right; left; exact P|right; right; right].
  destruct P as (P1 & P2 & P3). split; [exact P1|split; [auto|exact P3]].
Qed.

(** The status of a stream in [Brun] passes deflateStateCheck; it is FINISH_STATE only in P3 ([fin = true]). *)
Lemma brun_status : forall W HI n b pos fin s tin tout adler, hdr_facts HI ->
  Brun W HI n b pos fin s tin tout adler ->
  bad_state s = false /\ (fin = false -> d_status s <> FINISH_STATE).
Proof.
  intros W HI n b pos fin s tin tout adler HF (H & w0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph).
  unfold bad_state, c_deflateStateCheck, status_ok.
  destruct Hph as [(Hs & _)|[(_ & _ & (k & Hk & _) & _)|[(Hs & _)|(Hs & Hf & _)]]].
  - rewrite Hs. destruct (w0 =? 2); split; try reflexivity; unfold INIT_STATE, GZIP_STATE, FINISH_STATE; lia.
  - destruct (hf_status _ HF _ _ _ _ Hk) as (_ & _ & Hs & _).
    destruct Hs as [Hs|[Hs|[Hs|Hs]]]; rewrite Hs; split; try reflexivity;
      unfold EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE, FINISH_STATE; lia.
  - rewrite Hs. split; [reflexivity|]. unfold BUSY_STATE, FINISH_STATE; lia.
  - rewrite Hs. split; [reflexivity|]. intros Hf'. congruence.
Qed.

(** total_out is within the bound: [8 tout <= Gb <= 8 b] in every phase. *)
Lemma brun_tout : forall W HI n b pos fin s tin tout adler, core_facts W -> hdr_facts HI ->
  Brun W HI n b pos fin s tin tout adler -> tout <= b.
Proof.
  intros W HI n b pos fin s tin tout adler CF HF
    (H & w0 & HW & Ho & Hw & Hb & HH & Hn & Hp & Hti & Hto & Hg & Hl & Hph).
  pose proof (body_range (bcls_of s) n Hn) as Hbody.
  assert (Htl : 0 <= tlen w0) by (unfold tlen; destruct (w0 =? 1); [lia|destruct (w0 =? 2); lia]).
  pose proof (Zlength_nonneg H) as HL.
  assert (Hpe : 0 <= d_pending s) by (destruct Ho as (_ & HB & _); exact (proj2 (proj2 HB))).
  assert (Hbv : 0 <= d_bi_valid s) by (destruct Ho as (_ & HB & _); exact (proj1 (proj1 HB))).
  destruct Hph as [P|[P|[P|P]]].
  - destruct P as (_ & _ & _ & _ & Ht & _). lia.
  - destruct P as (_ & _ & (k & Hk & Htk) & _).
    destruct (hf_status _ HF _ _ _ _ Hk) as (_ & _ & _ & _ & Hk2). lia.
  - destruct P as (_ & _ & _ & _ & E & k & HE & Hk0 & Hmk & HG).
    destruct (cf_pos _ CF s HW) as (Hla & Hss & Hbs & _).
    assert (Hub : 0 <= ub s) by (unfold ub; lia).
    pose proof (acc_mid (bcls_of s) (Zlength H) E k n HL Hk0 Hmk ltac:(lia)) as HA.
    unfold Gb in HG. lia.
  - destruct P as (_ & _ & _ & _ & _ & _ & _ & [(_ & HG)|(_ & _ & HG)]); unfold Gb in HG; lia.
Qed.

(** [Mid] at the start of the call. *)
Lemma mid_start : forall W HI n b pos fin s tin tout adler inb aout flush msg,
  Brun W HI n b pos fin s tin tout adler ->
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH) -> (fin = true -> flush = Z_FINISH) ->
  bytes inb -> pos + Zlength inb <= n -> (flush = Z_FINISH -> pos + Zlength inb = n) ->
  0 <= aout <= 1073741824 ->
  Mid W HI n b pos inb aout tin tout flush (d_gzhead s) s (zcall inb 0 (Zlength inb) tin aout tout adler msg).
Proof.
  intros W HI n b pos fin s tin tout adler inb aout flush msg HB Hfl Hfin Hinb Hpn HpF Ha.
  pose proof HB as (H & w0 & _ & _ & _ & _ & _ & _ & Hp & Hti & Hto & _).
  unfold Mid, cframe, zcall; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler].
  rewrite Zlength_nil.
  repeat split; try lia; auto.
  - constructor.
  - rewrite !Z.add_0_r. apply (brun_fin _ _ _ _ _ fin); [exact HB|].
    intros Hf. rewrite (Hfin Hf). reflexivity.
Qed.

(** What the end of the call needs from [Mid]. *)
Lemma mid_out : forall W HI n b pos inb aout tin tout flush gz0 s z, core_facts W -> hdr_facts HI ->
  Mid W HI n b pos inb aout tin tout flush gz0 s z ->
  (flush = Z_FINISH \/ 0 <= z_avail_in z \/ z_next_in z = 0) ->
  d_gzhead s = gz0 /\ 0 <= z_avail_in z <= Zlength inb /\ z_total_out z <= b /\
  Brun W HI n b (pos + Zlength inb - z_avail_in z) (flush =? Z_FINISH) s (z_total_in z) (z_total_out z)
       (z_adler z).
Proof.
  intros W HI n b pos inb aout tin tout flush gz0 s z CF HF
    (Hc & Hinb & Hp0 & Hpn & Hfl & HfF & Ha & Ht0 & Hto & Hgz & HB) Hav.
  destruct Hc as (Hzi & Hni & Hsum & _).
  pose proof (brun_tout _ _ _ _ _ _ _ _ _ _ CF HF HB) as Ht.
  replace (pos + Zlength inb - z_avail_in z) with (pos + z_next_in z) by lia.
  assert (0 <= z_avail_in z).
  { destruct Hav as [Hf|[Hav|Hav]]; [|exact Hav|pose proof (Zlength_nonneg inb); lia].
    destruct HB as (H & w0 & _ & _ & _ & _ & _ & _ & Hpp & _). specialize (HfF Hf). lia. }
  repeat split; auto; lia.
Qed.

(** flush_pending does not touch the input. *)
Lemma flush_pending_avail_in : forall s z s' z', c_flush_pending s z = Some (s', z') ->
  z_avail_in z' = z_avail_in z.
Proof.
  intros s z s' z' H. unfold c_flush_pending, out_put, bind in H.
  destruct (c_tr_flush_bits (d_out s)) as [o|]; [|discriminate].
  match type of H with context [if ?c then _ else _] => destruct c end.
  - inversion H; reflexivity.
  - match type of H with context [mb_read ?a ?b ?c] => destruct (mb_read a b c) end; [|discriminate].
    match type of H with context [if ?c then _ else _] => destruct c end; [|discriminate].
    inversion H; subst; reflexivity.
Qed.

(** The compression stage leaves [0 <= avail_in] (by [cf_compress]'s [zstep]; [comp_stage] does not say it). *)
Lemma comp_avail : forall W HI n b pos0 inb aout tin0 tout0 flush gz0 s z s3 z3 o,
  core_facts W -> hdr_facts HI ->
  Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s z -> z_next_in z = 0 ->
  (d_status s = BUSY_STATE \/ d_status s = FINISH_STATE) -> d_pending s = 0 -> d_po s = 0 ->
  d_bi_valid s <= 7 -> (d_status s = FINISH_STATE -> z_avail_in z = 0) ->
  c_deflate_compress s z flush = Some (s3, z3, o) -> 0 <= z_avail_in z3.
Proof.
  intros W HI n b pos0 inb aout tin0 tout0 flush gz0 s z s3 z3 o CF HF HM Hn0 Hst Hp Hpo Hbv HfZ Hc.
  pose proof HM as (Hcf & Hinb & Hp0 & Hpn & Hfl & HfF & Ha & Ht0 & Hto & Hgz & HB).
  pose proof Hcf as (Hzi & Hni & Hsum & Hti & Hao & Hol & Hto' & Hob).
  pose proof (Zlength_nonneg inb) as Hinb0.
  assert (Hav : z_avail_in z = Zlength inb) by lia.
  pose proof (brun_tout _ _ _ _ _ _ _ _ _ _ CF HF HB) as Htb.
  destruct HB as (H & w0 & HW & Ho & Hw & Hb & HH & Hn & Hp' & Hti' & Hto2 & Hg & Hl & Hph).
  destruct (cf_pos _ CF s HW) as (Hla & Hss & Hbs & _).
  unfold c_deflate_compress in Hc.
  destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
            (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:G.
  2: { inversion Hc; subst; lia. }
  assert (HP2 : d_wrap s = w0 /\ adler_ok w0 (z_adler z)).
  { destruct Hph as [(Hs' & _)|[(_ & _ & (k & Hk & _) & _)|[(Hs' & Hw' & _ & Had & _)|(Hs' & _ & _ & Hu & _)]]].
    - exfalso. destruct Hst as [Hs|Hs]; rewrite Hs in Hs'; destruct (w0 =? 2);
        unfold BUSY_STATE, FINISH_STATE, INIT_STATE, GZIP_STATE in Hs'; lia.
    - exfalso. destruct (hf_status _ HF _ _ _ _ Hk) as (_ & _ & Hs' & _).
      destruct Hst as [Hs|Hs]; rewrite Hs in Hs';
        unfold BUSY_STATE, FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in Hs'; lia.
    - split; assumption.
    - exfalso. specialize (HfZ Hs'). assert (Hl0 : d_lookahead s = 0) by (unfold ub in Hu; lia).
      rewrite HfZ, Hl0, Hs' in G. rewrite !Z.eqb_refl in G.
      destruct (flush =? Z_NO_FLUSH); discriminate. }
  destruct HP2 as (Hwr & Had).
  pose proof (body_range (bcls_of s) n Hn) as Hbody.
  assert (Htl : tlen w0 <= 8) by (unfold tlen; destruct (w0 =? 1); [lia|destruct (w0 =? 2); lia]).
  assert (Hzin : zin_ok z).
  { unfold zin_ok. rewrite Hzi. pose proof (Zlength_nonneg (z_out z)). repeat split; try lia; auto. }
  destruct (cf_compress _ CF s z flush HW Ho (conj Hp (conj Hpo Hbv))
              ltac:(destruct Hfl as [E|E]; rewrite E; unfold Z_NO_FLUSH, Z_FINISH; lia) Hzin ltac:(lia)
              ltac:(rewrite Hwr; exact Had)) as (s' & z' & bs & evs & Hcc & Hpost).
  destruct Hpost as (_ & _ & _ & _ & (k & x & Hzs & _) & _).
  destruct Hzs as (_ & Hk & _ & Hav' & _).
  assert (Hz' : 0 <= z_avail_in z') by lia.
  rewrite Hcc in Hc. cbn [bind] in Hc.
  destruct bs.
  - inversion Hc; subst; assumption.
  - match type of Hc with bind ?a _ = _ => destruct a as [s5|]; [|discriminate] end.
    cbn [bind] in Hc.
    destruct (c_flush_pending s5 z') as [[s6 z6]|] eqn:Hfp; [|discriminate].
    cbn [bind] in Hc. rewrite <- (flush_pending_avail_in _ _ _ _ Hfp) in Hz'.
    destruct (z_avail_out z6 =? 0); inversion Hc; subst; assumption.
  - inversion Hc; subst; assumption.
  - inversion Hc; subst; assumption.
Qed.

Lemma deflate_walk : forall W HI, core_facts W -> hdr_facts HI -> block_bound_statement -> cpost_extra W ->
  forall n b pos fin s tin tout adler inb aout flush msg,
  Brun W HI n b pos fin s tin tout adler ->
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH) -> (fin = true -> flush = Z_FINISH) ->
  bytes inb -> pos + Zlength inb <= n -> (flush = Z_FINISH -> pos + Zlength inb = n) ->
  0 <= aout <= 1073741824 ->
  exists s' z' code,
    c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) /\
    d_gzhead s' = d_gzhead s /\ (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_END) /\
    0 <= z_avail_in z' <= Zlength inb /\ z_total_out z' <= b /\
    (code <> Z_STREAM_END ->
     Brun W HI n b (pos + Zlength inb - z_avail_in z') (flush =? Z_FINISH) s'
          (z_total_in z') (z_total_out z') (z_adler z')) /\
    (flush = Z_FINISH -> fin = false -> pos = 0 -> b <= tout + aout ->
     code = Z_STREAM_END /\ z_avail_in z' = 0).
Proof.
  intros W HI CF HF BB CX n b pos fin s tin tout adler inb aout flush msg HB Hfl Hfin Hinb Hpn HpF Ha.
  destruct (brun_status _ _ _ _ _ _ _ _ _ _ HF HB) as (Hbad & Hnf).
  pose proof (mid_start _ _ _ _ _ _ _ _ _ _ _ _ _ msg HB Hfl Hfin Hinb Hpn HpF Ha) as HM0.
  rewrite c_deflate_stages, Hbad.
  assert (Hfr : false || (flush >? Z_BLOCK) || (flush <? 0) = false)
    by (destruct Hfl as [E|E]; rewrite E; reflexivity).
  rewrite Hfr. cbn iota beta.
  destruct (entry_stage W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM0 eq_refl eq_refl)
    as (s1 & z1 & o1 & He & HM1 & Hn1 & Hst1 & Hw1 & Ho1 & Hr1).
  rewrite He. destruct o1 as [c1|].
  { (* the entry stage returns *)
    cbn [then_stage bind]. exists s1, z1, c1. destruct Ho1 as (Hc1 & _).
    destruct (mid_out _ _ _ _ _ _ _ _ _ _ _ _ _ CF HF HM1 (or_intror (or_intror Hn1)))
      as (Hgz & Hav & Hto & HB1).
    split; [reflexivity|]. split; [exact Hgz|]. split; [tauto|]. split; [exact Hav|].
    split; [exact Hto|]. split; [intros _; exact HB1|].
    intros HF' Hfin' Hp0 Hroom. specialize (Hr1 HF' Hp0 Hroom (Hnf Hfin')). discriminate. }
  destruct Ho1 as (Hp1 & Hpo1 & Hbv1 & Hfz1).
  cbn [then_stage bind].
  destruct (hdr_stage W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM1 Hn1 Hp1 Hpo1 Hbv1 Hfz1)
    as (s2 & z2 & o2 & Hh & HM2 & Hn2 & Ho2N & Ho2S & Hr2).
  rewrite Hh. destruct o2 as [c2|].
  { (* a header stage returns *)
    cbn [then_stage bind]. exists s2, z2, c2.
    destruct (mid_out _ _ _ _ _ _ _ _ _ _ _ _ _ CF HF HM2 (or_intror (or_intror Hn2)))
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
  destruct (comp_stage W HI CF HF BB CX _ _ _ _ _ _ _ _ _ _ _ HM2 Hn2 Hst2 Hp2 Hpo2 Hbv2 Hfz2)
    as (s3 & z3 & o3 & Hcm & HM3 & Ho3N & Ho3S & Hr3).
  pose proof (comp_avail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CF HF HM2 Hn2 Hst2 Hp2 Hpo2 Hbv2 Hfz2 Hcm) as Hav3.
  rewrite Hcm. destruct o3 as [c3|].
  { (* the compression stage returns *)
    cbn [bind]. exists s3, z3, c3.
    destruct (mid_out _ _ _ _ _ _ _ _ _ _ _ _ _ CF HF HM3 (or_intror (or_introl Hav3)))
      as (Hgz & Hav & Hto & HB3).
    split; [reflexivity|]. split; [exact Hgz|]. split; [left; exact (Ho3S c3 eq_refl)|].
    split; [exact Hav|]. split; [exact Hto|]. split; [intros _; exact HB3|].
    intros HF' Hfin' Hp0 Hroom. specialize (Hr3 HF' Hp0 Hroom (Hbusy Hfin')). discriminate. }
  cbn [bind].
  destruct (trailer_stage W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM3 (Ho3N eq_refl))
    as (s4 & z4 & code & Ht & Hgz4 & Hcf4 & Hcode & Hto4 & HSE & HM4 & Hr4).
  rewrite Ht. exists s4, z4, code.
  assert (Hav4 : flush = Z_FINISH \/ 0 <= z_avail_in z4 \/ z_next_in z4 = 0).
  { destruct Hfl as [E|E]; [right; left|left; exact E].
    unfold c_deflate_trailer in Ht. rewrite E in Ht. cbn [negb Z.eqb Z_NO_FLUSH Z_FINISH] in Ht.
    inversion Ht; subst; exact Hav3. }
  assert (Hav4' : 0 <= z_avail_in z4 <= Zlength inb).
  { destruct (Z.eq_dec code Z_STREAM_END) as [E|E].
    - rewrite (HSE E). pose proof (Zlength_nonneg inb). lia.
    - exact (proj1 (proj2 (mid_out _ _ _ _ _ _ _ _ _ _ _ _ _ CF HF (HM4 E) Hav4))). }
  split; [reflexivity|]. split; [exact Hgz4|]. split; [tauto|]. split; [exact Hav4'|].
  split; [exact Hto4|]. split.
  - intros E. exact (proj2 (proj2 (proj2 (mid_out _ _ _ _ _ _ _ _ _ _ _ _ _ CF HF (HM4 E) Hav4)))).
  - intros HF' Hfin' Hp0 Hroom. assert (Hc : code = Z_STREAM_END) by exact (Hr4 HF' Hroom).
    split; [exact Hc|exact (HSE Hc)].
Qed.
