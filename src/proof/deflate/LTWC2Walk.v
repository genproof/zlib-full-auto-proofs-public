(** * The deflateBound accounting for compress2_z's loop: one deflate() call

    The walk of the stages (entry, headers, compression, trailer) of LTWBWalk.deflate_walk_w, for a call from
    [BrunC2] offered all of an object [inb] from offset 0 (Z_NO_FLUSH or Z_FINISH, up to 2^32-1 bytes of input
    and of output space), with what compress2_z's loop needs besides the accounting ([c2post]):

    - Z_BUF_ERROR only without output space, or without input at Z_NO_FLUSH;
    - a Z_OK with output space, and with input or Z_FINISH, consumed input or wrote output (each stage returns
      Z_OK after filling the output space, except the compression stage after need_more:
      LTWC2Prog.compress_progress);
    - for n >= 2^25, total_out stays below deflateBound until the end of the stream ([mg]: LTWC2Margin);
    - with all the data, a fresh stream and deflateBound bytes of output space, Z_STREAM_END.

    The compression facts are taken as section hypotheses: [CC] is the compression call of the wide core theory
    (LTWIface.cw_compress for any level and flush), [PROG] the progress of LTWC2Prog. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWBKit.
Require Import Zlib.proof.deflate.LTWBEntry Zlib.proof.deflate.LTWBHdr Zlib.proof.deflate.LTWBComp
  Zlib.proof.deflate.LTWBTrail Zlib.proof.deflate.LTWCWalk.
Require Export Zlib.proof.deflate.LTWC2Stages Zlib.proof.deflate.LTWC2Margin.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** What a call of compress2_z's loop gives (LawFactsC2W.c2f_split's conclusion after the model run, for the
    call on the object [inb] from offset 0). *)
Definition c2post (W : dstate -> Prop) (HI : hdr_inv) (n b pos tin tout aout flush : Z) (inb : list Z)
    (fin : bool) (s s' : dstate) (z' : strm) (code : Z) : Prop :=
  d_gzhead s' = d_gzhead s /\ cframe inb aout tin tout z' /\ 0 <= z_avail_in z' /\ z_total_out z' <= b /\
  (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_END) /\
  (code = Z_BUF_ERROR -> aout = 0 \/ (Zlength inb = 0 /\ flush = Z_NO_FLUSH)) /\
  (code = Z_OK -> 0 < aout -> (0 < Zlength inb \/ flush = Z_FINISH) ->
   0 < z_next_in z' + (aout - z_avail_out z')) /\
  (33554432 <= n -> code = Z_OK -> z_avail_out z' = 0 -> z_total_out z' < b) /\
  (flush = Z_FINISH -> fin = false -> pos = 0 -> b <= tout + aout -> code = Z_STREAM_END) /\
  (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) /\
  (code <> Z_STREAM_END ->
   BrunC2 W HI n b (pos + Zlength inb - z_avail_in z') (flush =? Z_FINISH) s' (z_total_in z') (z_total_out z')
     (z_adler z')).

Section C2Walk.
Context (W : dstate -> Prop) (HI : hdr_inv) (CF : core_facts_w W) (HF : hdr_facts_w HI)
  (BB : block_bound_statement).

Hypothesis CC : forall s z flush,
  W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_okw z ->
  0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
  exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W s z flush s' z' bs evs.

Hypothesis PROG : forall s z flush s' z' bs,
  W s -> outok s -> quiet s -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH) -> zin_okw z ->
  0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
  c_compress_func s z flush = Some (s', z', bs) -> bs = need_more ->
  0 < z_avail_out z -> (0 < z_avail_in z \/ flush = Z_FINISH) ->
  z_avail_in z' < z_avail_in z \/ z_avail_out z' < z_avail_out z.

(** After the last block: no window, no symbols, an empty bit buffer, a wrap of at most 2 either way. *)
Lemma brunw_fin_facts : forall n b pos fin s tin tout adler,
  BrunW W HI n b pos fin s tin tout adler -> d_status s = FINISH_STATE ->
  ub s = 0 /\ d_sym_next s = 0 /\ d_bi_valid s = 0 /\ -2 <= d_wrap s <= 2 /\ d_lookahead s = 0.
Proof.
  intros n b pos fin s tin tout adler (H & w0 & HW & Ho & Hw0 & _ & _ & _ & _ & _ & _ & _ & _ & Hph) Hst.
  destruct (cw_pos W CF s HW) as (L1 & L2 & L3 & L4).
  destruct Hph as [P|[P|[P|P]]].
  - exfalso. destruct P as (Hs & _). rewrite Hst in Hs.
    destruct (w0 =? 2); unfold FINISH_STATE, INIT_STATE, GZIP_STATE in Hs; lia.
  - exfalso. destruct P as (_ & _ & (k & Hk & _) & _). destruct (hw_status HI HF _ _ _ _ Hk) as (_ & _ & Hs & _).
    rewrite Hst in Hs. unfold FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in Hs; lia.
  - exfalso. destruct P as (Hs & _). rewrite Hst in Hs. unfold FINISH_STATE, BUSY_STATE in Hs. lia.
  - destruct P as (_ & _ & _ & Hu & Hsy & Hbv & _ & Hw).
    unfold ub in Hu. split; [unfold ub; lia|]. split; [exact Hsy|]. split; [exact Hbv|].
    split; [destruct Hw as [(Hw & _)|(_ & Hw & _)]; lia|]. lia.
Qed.

Lemma tleft_range : forall s, 0 <= tleft s <= 8.
Proof.
  intros s. unfold tleft, tlen.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

(** For n >= 2^25, total_out stays below deflateBound between the calls. *)
Lemma c2_strict : forall n b pos fin s tin tout adler,
  BrunC2 W HI n b pos fin s tin tout adler -> 33554432 <= n -> tout < b.
Proof.
  intros n b pos fin s tin tout adler [HB [Hmg _]] Hn.
  destruct (brunw_facts W HI CF HF _ _ _ _ _ _ _ _ HB) as (Hpd & _ & _ & _ & _ & _ & _ & _ & _ & Hnf).
  pose proof (tleft_range s).
  destruct (Z.eq_dec (d_status s) FINISH_STATE) as [E|E].
  - specialize (Hmg Hn E). lia.
  - specialize (Hnf E). lia.
Qed.

(** The end of a call in [MidW] that returns Z_OK or Z_BUF_ERROR. *)
Lemma c2_mid_end : forall n b pos inb aout tin tout flush fin s s' z' code,
  MidW W HI n b pos inb aout tin tout flush (d_gzhead s) s' z' ->
  (flush = Z_FINISH \/ 0 <= z_avail_in z' \/ z_next_in z' = 0) ->
  d_gzhead s = None -> (4294967295 < b -> 33554432 <= n) -> mg n b s' (z_total_out z') ->
  (code = Z_OK \/ code = Z_BUF_ERROR) ->
  (code = Z_BUF_ERROR -> aout = 0 \/ (Zlength inb = 0 /\ flush = Z_NO_FLUSH)) ->
  (code = Z_OK -> 0 < aout -> (0 < Zlength inb \/ flush = Z_FINISH) ->
   0 < z_next_in z' + (aout - z_avail_out z')) ->
  (flush = Z_FINISH -> fin = false -> pos = 0 -> b <= tout + aout -> code = Z_STREAM_END) ->
  c2post W HI n b pos tin tout aout flush inb fin s s' z' code.
Proof.
  intros n b pos inb aout tin tout flush fin s s' z' code HM Hav Hg0 Hbn Hmg Hc Hbuf Hprog Honce.
  destruct (midw_out W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM Hav) as (Hgz & Hai & Hto & HB).
  assert (HB2 : BrunC2 W HI n b (pos + Zlength inb - z_avail_in z') (flush =? Z_FINISH) s' (z_total_in z')
                  (z_total_out z') (z_adler z')) by (split; [exact HB|split; [exact Hmg|split; [congruence|exact Hbn]]]).
  split; [exact Hgz|]. split; [exact (proj1 HM)|]. split; [lia|]. split; [exact Hto|].
  split; [tauto|]. split; [exact Hbuf|]. split; [exact Hprog|].
  split; [intros Hn _ _; exact (c2_strict _ _ _ _ _ _ _ _ HB2 Hn)|].
  split; [exact Honce|].
  split; [intros E; destruct Hc as [Hc|Hc]; rewrite Hc in E; discriminate E|].
  intros _. exact HB2.
Qed.

Lemma walk_c2 : forall n b pos fin s tin tout adler inb aout flush msg,
  BrunC2 W HI n b pos fin s tin tout adler ->
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH) -> (fin = true -> flush = Z_FINISH) ->
  bytes inb -> pos + Zlength inb <= n -> (flush = Z_FINISH -> pos + Zlength inb = n) ->
  0 <= aout <= 4294967295 -> Zlength inb <= 4294967295 ->
  exists s' z' code,
    c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) /\
    c2post W HI n b pos tin tout aout flush inb fin s s' z' code.
Proof.
  intros n b pos fin s tin tout adler inb aout flush msg [HB [Hmg [Hg0 Hbn]]] Hfl Hfin Hinb Hpn HpF Ha Hib.
  pose proof (brunw_facts W HI CF HF _ _ _ _ _ _ _ _ HB) as (Hpd & Hbv & Ht & Htb & Hb & Hpos & Hn & Htin & HFs & _).
  destruct (brunw_status _ _ _ _ _ _ _ _ _ _ HF HB) as (Hbad & Hnf).
  pose proof HB as (H0 & w0 & HW & Ho & _).
  pose proof (Zlength_nonneg inb) as Hib0.
  set (z0 := zcall inb 0 (Zlength inb) tin aout tout adler msg).
  pose proof (midw_start _ _ _ _ _ _ _ _ _ _ _ _ _ msg HB Hfl Hfin Hinb Hpn HpF Ha) as HM0.
  fold z0 in HM0.
  rewrite c_deflate_stages, Hbad.
  assert (Hfr : false || (flush >? Z_BLOCK) || (flush <? 0) = false)
    by (destruct Hfl as [E|E]; rewrite E; reflexivity).
  rewrite Hfr. cbn iota beta.
  (* the entry stage *)
  destruct (entry_stage_w W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM0 eq_refl eq_refl)
    as (s1 & z1 & o1 & He & HM1 & Hn1 & Hst1 & Hw1 & Hce1 & Hout1 & Ho1 & Hr1).
  assert (Hcons1 : z_total_out z1 + d_pending s1 = tout + d_pending s).
  { exact (entry_cons s z0 flush s1 z1 o1 He Ho ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)). }
  assert (Hmg1 : mg n b s1 (z_total_out z1)).
  { intros Hn25 Hs1. rewrite Hst1 in Hs1. specialize (Hmg Hn25 Hs1).
    unfold tleft in *. rewrite Hw1. lia. }
  rewrite He. destruct o1 as [c1|].
  { (* the entry stage returns *)
    cbn [then_stage bind]. exists s1, z1, c1. destruct Ho1 as (Hc1 & Hb1).
    split; [reflexivity|].
    apply (c2_mid_end _ _ _ _ _ _ _ _ _ _ _ _ _ HM1 (or_intror (or_intror Hn1)) Hg0 Hbn Hmg1 Hc1).
    - intros E. subst c1. destruct (entry_buf s z0 flush s1 z1 He) as [E0|[(E0 & Ef)|(Ef & E0)]].
      + left. exact E0.
      + right. split; [exact E0|]. destruct Hfl; [assumption|contradiction].
      + exfalso. destruct (HFs Ef) as [Hpn' _]. cbn in E0. lia.
    - intros E Hao _. subst c1.
      assert (Hp1 : 0 <= d_pending s1).
      { destruct (midw_out W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM1 (or_intror (or_intror Hn1))) as (_ & _ & _ & HB1).
        exact (proj1 (brunw_facts W HI CF HF _ _ _ _ _ _ _ _ HB1)). }
      rewrite (entry_ok s z0 flush s1 z1 He ltac:(cbn; lia) Hp1). lia.
    - intros HF' Hfin' Hp0 Hroom. specialize (Hr1 HF' Hp0 Hroom (Hnf Hfin')). discriminate. }
  destruct Ho1 as (Hp1 & Hpo1 & Hbv1 & Hfz1).
  cbn [then_stage bind].
  (* the header stages *)
  destruct (hdr_stage_w W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM1 Hn1 Hp1 Hpo1 Hbv1 Hfz1)
    as (s2 & z2 & o2 & Hh & HM2 & Hn2 & Hce2 & Ho2N & Ho2S & Hr2).
  assert (Hgz1 : d_gzhead s1 = None) by (destruct HM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G & _); congruence).
  rewrite Hh. destruct o2 as [c2|].
  { (* a header stage returns *)
    cbn [then_stage bind]. exists s2, z2, c2.
    split; [reflexivity|].
    pose proof (Ho2S c2 eq_refl) as Hc2. subst c2.
    destruct (midw_out W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM2 (or_intror (or_intror Hn2))) as (_ & _ & _ & HB2).
    pose proof (brunw_facts W HI CF HF _ _ _ _ _ _ _ _ HB2) as (Hp2 & _).
    assert (Hz1 : 0 <= z_avail_out z1 <= 4294967295).
    { destruct HM1 as ((_ & _ & _ & _ & Hao & Hol & _) & _). pose proof (Zlength_nonneg (z_out z1)). lia. }
    destruct (hdr_stages_ok s1 z1 s2 z2 Z_OK Hh Hgz1 Hz1 Hp2) as [Ha2 Hs2].
    apply (c2_mid_end _ _ _ _ _ _ _ _ _ _ _ _ _ HM2 (or_intror (or_intror Hn2)) Hg0 Hbn).
    - intros _ E. rewrite Hs2 in E. discriminate E.
    - left; reflexivity.
    - intros E. discriminate E.
    - intros _ Hao _. rewrite Ha2. lia.
    - intros HF' Hfin' Hp0 Hroom. specialize (Hr2 HF' Hp0 Hroom). discriminate. }
  destruct (Ho2N eq_refl) as (Hst2 & Hp2 & Hpo2 & Hbv2 & Hfz2').
  assert (Hfz2 : d_status s2 = FINISH_STATE -> z_avail_in z2 = 0) by (intros E; exact (proj2 (Hfz2' E))).
  assert (Hbusy : fin = false -> d_status s2 = BUSY_STATE).
  { intros Hf. destruct Hst2 as [E|E]; [exact E|]. exfalso.
    apply (Hnf Hf). rewrite <- Hst1. exact (proj1 (Hfz2' E)). }
  assert (Hmg2 : mg n b s2 (z_total_out z2)).
  { intros Hn25 Hs2. destruct (Hfz2' Hs2) as [Hs1 _].
    rewrite (hdr_stages_busy s1 z1 (or_intror Hs1)) in Hh. injection Hh as <- <-. exact (Hmg1 Hn25 Hs1). }
  assert (Hgz2 : d_gzhead s2 = None) by (destruct HM2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G & _); congruence).
  assert (Eai2 : z_avail_in z2 = Zlength inb).
  { destruct HM2 as ((_ & _ & Hsum & _) & _). lia. }
  cbn [then_stage bind].
  (* the compression stage *)
  destruct (midw_out W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM2 (or_intror (or_intror Hn2))) as (_ & _ & _ & HB2).
  assert (Hcomp : (d_level s2 = 0 -> flush <> Z_NO_FLUSH -> ub s2 + z_avail_in z2 <= 4294967295) \/
     (exists s' z' bs evs, c_compress_func s2 z2 flush = Some (s', z', bs) /\ cpost W s2 z2 flush s' z' bs evs)).
  { destruct Hst2 as [Hs2|Hs2].
    - right. destruct (comp_pre W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM2 Hn2 Hib Hs2 Hp2 Hpo2 Hbv2)
        as (HW2 & Ho2 & Hq2 & Hfr2 & Hz2 & Hw2 & Ha2).
      exact (CC s2 z2 flush HW2 Ho2 Hq2 Hfr2 Hz2 Hw2 Ha2).
    - left. intros _ _. destruct (brunw_fin_facts _ _ _ _ _ _ _ _ HB2 Hs2) as (Hu & _).
      rewrite Hu, (Hfz2 Hs2). lia. }
  destruct (comp_stage_w BB W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM2 Hn2 Hib Hst2 Hp2 Hpo2 Hbv2 Hfz2 Hcomp)
    as (s3 & z3 & o3 & Hcm & HM3 & Hav3 & _ & Ho3N & Ho3S & Hr3).
  (* the compression call, when deflate() makes it *)
  assert (Hcall : d_status s2 = BUSY_STATE ->
    exists s' z' bs evs, c_compress_func s2 z2 flush = Some (s', z', bs) /\ cpost W s2 z2 flush s' z' bs evs /\
      W s2 /\ outok s2 /\ quiet s2 /\ zin_okw z2 /\ 0 <= d_wrap s2 <= 2 /\ adler_pre (d_wrap s2) (z_adler z2)).
  { intros Hs2. destruct (comp_pre W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM2 Hn2 Hib Hs2 Hp2 Hpo2 Hbv2)
      as (HW2 & Ho2 & Hq2 & Hfr2 & Hz2 & Hw2 & Ha2).
    destruct (CC s2 z2 flush HW2 Ho2 Hq2 Hfr2 Hz2 Hw2 Ha2) as (s' & z' & bs & evs & Ec & Hcp).
    exists s', z', bs, evs. auto 10. }
  assert (Hmg3 : mg n b s3 (z_total_out z3)).
  { intros Hn25 Hs3.
    destruct Hst2 as [Hs2|Hs2].
    - destruct (Hcall Hs2) as (s' & z' & bs & evs & Ec & Hcp & _).
      destruct o3 as [c3|].
      + destruct (comp_some s2 z2 flush s3 z3 c3 Hcm) as (s'' & z'' & bs' & Ec' & Hbs & Hx).
        rewrite Ec in Ec'. injection Ec' as <- <- <-.
        destruct Hbs as [ ->|[ ->| ->]].
        * exfalso. destruct (Hx (or_introl eq_refl)) as (_ & _ & _ & Es). rewrite Hs3 in Es.
          destruct Hcp as (_ & _ & _ & (Ea & _) & _). rewrite Ea, Hs2 in Es. discriminate Es.
        * destruct (Hx (or_intror eq_refl)) as (-> & Ep & Ew & _).
          pose proof (comp_margin BB W HI CF HF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM2 Hn2 Hs2 Hp2 Hpo2
                        ltac:(lia) Ec Hcp (or_introl eq_refl) Hn25) as Hm.
          unfold tleft in *. rewrite Ep, Ew. exact Hm.
        * exfalso. destruct Hcp as (_ & _ & _ & _ & _ & _ & _ & Hb').
          destruct Hb' as (_ & Hn1' & Hn2' & _). destruct Hfl; contradiction.
      + destruct (comp_none s2 z2 flush s3 z3 Hcm) as [(_ & _ & _ & -> & ->)|(s'' & z'' & bs' & Ec' & Hbs & Hx)].
        * rewrite Hs2 in Hs3. discriminate Hs3.
        * rewrite Ec in Ec'. injection Ec' as <- <- <-.
          destruct Hbs as [ ->| ->].
          -- exfalso. destruct Hcp as (_ & _ & _ & _ & _ & _ & _ & Hb').
             destruct Hb' as (_ & Hn1' & Hn2' & _). destruct Hfl; contradiction.
          -- destruct (Hx eq_refl) as [ -> ->].
             pose proof (comp_margin BB W HI CF HF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM2 Hn2 Hs2 Hp2 Hpo2
                           ltac:(lia) Ec Hcp (or_intror eq_refl) Hn25) as Hm.
             unfold tleft in *. destruct s'; exact Hm.
    - (* the stream had finished: the compression function is not called *)
      destruct (brunw_fin_facts _ _ _ _ _ _ _ _ HB2 Hs2) as (_ & _ & _ & _ & Hla).
      unfold c_deflate_compress in Hcm. rewrite (Hfz2 Hs2), Hla, Hs2 in Hcm. cbn in Hcm.
      rewrite andb_false_r in Hcm. cbn in Hcm. injection Hcm as <- <- _. exact (Hmg2 Hn25 Hs2). }
  assert (Hgz3 : d_gzhead s3 = None) by (destruct HM3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G & _); congruence).
  rewrite Hcm. destruct o3 as [c3|].
  { (* the compression stage returns *)
    cbn [bind]. exists s3, z3, c3.
    split; [reflexivity|].
    pose proof (Ho3S c3 eq_refl) as Hc3. subst c3.
    apply (c2_mid_end _ _ _ _ _ _ _ _ _ _ _ _ _ HM3 (or_intror (or_introl Hav3)) Hg0 Hbn Hmg3).
    - left; reflexivity.
    - intros E. discriminate E.
    - intros _ Hao Hin.
      assert (Hs2 : d_status s2 = BUSY_STATE).
      { destruct Hst2 as [E|E]; [exact E|]. exfalso.
        destruct (brunw_fin_facts _ _ _ _ _ _ _ _ HB2 E) as (_ & _ & _ & _ & Hla).
        unfold c_deflate_compress in Hcm. rewrite (Hfz2 E), Hla, E in Hcm. cbn in Hcm.
        rewrite andb_false_r in Hcm. cbn in Hcm. discriminate Hcm. }
      destruct (Hcall Hs2) as (s' & z' & bs & evs & Ec & Hcp & HW2 & Ho2 & Hq2 & Hz2 & Hw2 & Ha2).
      destruct (comp_some s2 z2 flush s3 z3 Z_OK Hcm) as (s'' & z'' & bs' & Ec' & Hbs & Hx).
      rewrite Ec in Ec'. injection Ec' as <- <- <-.
      pose proof Hcp as (_ & _ & _ & _ & (kk & x & Hzs & _) & _ & _ & Hb').
      destruct Hzs as (_ & _ & _ & _ & _ & _ & _ & _ & Zao & _).
      pose proof (Zlength_nonneg x).
      assert (Hao2 : z_avail_out z2 <= aout)
        by (destruct HM2 as ((_ & _ & _ & _ & _ & Hol2 & _) & _); pose proof (Zlength_nonneg (z_out z2)); lia).
      destruct HM3 as ((_ & Hni3 & Hsum3 & _ & Hao3 & _) & _).
      destruct Hbs as [ ->|[ ->| ->]].
      + destruct (Hx (or_introl eq_refl)) as (-> & _).
        destruct (Z.eq_dec (z_avail_out z2) 0) as [E0|E0]; [lia|].
        assert (Hz2o : 0 < z_avail_out z2) by (destruct Hz2 as (_ & _ & _ & _ & ? & _); lia).
        destruct (PROG s2 z2 flush s' z' need_more HW2 Ho2 Hq2 Hfl Hz2 Hw2 Ha2 Ec eq_refl Hz2o
                    ltac:(rewrite Eai2; exact Hin)) as [P|P]; lia.
      + destruct (Hx (or_intror eq_refl)) as (-> & _).
        destruct Hb' as (_ & _ & _ & _ & _ & _ & Ha0 & _). lia.
      + exfalso. destruct Hb' as (_ & Hn1' & Hn2' & _). destruct Hfl; contradiction.
    - intros HF' Hfin' Hp0 Hroom. specialize (Hr3 HF' Hp0 Hroom (Hbusy Hfin')). discriminate. }
  cbn [bind].
  (* the trailer *)
  destruct (trailer_stage_w W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM3 (Ho3N eq_refl))
    as (s4 & z4 & code & Ht4 & Hgz4 & _ & Hcf4 & Hcode & Hto4 & HSE & HM4 & Hr4).
  rewrite Ht4. exists s4, z4, code.
  split; [reflexivity|].
  assert (Hav4 : flush = Z_FINISH \/ 0 <= z_avail_in z4 \/ z_next_in z4 = 0).
  { destruct Hfl as [E|E]; [right; left|left; exact E].
    unfold c_deflate_trailer in Ht4. rewrite E in Ht4. cbn [negb Z.eqb Z_NO_FLUSH Z_FINISH] in Ht4.
    inversion Ht4; subst; exact Hav3. }
  destruct (Z.eq_dec code Z_STREAM_END) as [Ec|Ec].
  - (* Z_STREAM_END: only with Z_FINISH, all the input consumed *)
    assert (HfE : flush = Z_FINISH).
    { destruct Hfl as [E|E]; [|exact E]. exfalso. unfold c_deflate_trailer in Ht4. rewrite E in Ht4.
      cbn [negb Z.eqb Z_NO_FLUSH Z_FINISH] in Ht4. injection Ht4 as _ _ Hc.
      rewrite <- Hc in Ec. unfold Z_OK, Z_STREAM_END in Ec. lia. }
    subst code.
    split; [congruence|]. split; [exact Hcf4|]. split; [rewrite (HSE eq_refl); lia|]. split; [exact Hto4|].
    split; [right; right; reflexivity|]. split; [intros E; discriminate E|].
    split; [intros E; discriminate E|]. split; [intros _ E; discriminate E|].
    split; [intros; reflexivity|]. split; [intros _; split; [exact HfE|exact (HSE eq_refl)]|].
    intros E; contradiction.
  - destruct Hcode as [Hc|Hc]; [|contradiction]. subst code.
    assert (Hmg4 : mg n b s4 (z_total_out z4)).
    { destruct Hfl as [E|E].
      - unfold c_deflate_trailer in Ht4. rewrite E in Ht4. cbn [negb Z.eqb Z_NO_FLUSH Z_FINISH] in Ht4.
        injection Ht4 as <- <-. exact Hmg3.
      - intros Hn25 Hs4.
        destruct (Ho3N eq_refl) as [E'|(Hs3 & Hp3 & Hpo3 & _)]; [rewrite E in E'; discriminate E'|].
        destruct (midw_out W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM3 (or_introl E)) as (_ & _ & Hto3 & HB3).
        destruct (brunw_fin_facts _ _ _ _ _ _ _ _ HB3 Hs3) as (_ & Hsy3 & Hbv3 & Hw3 & _).
        pose proof HB3 as (_ & _ & HW3 & Ho3 & _).
        pose proof (brunw_facts W HI CF HF _ _ _ _ _ _ _ _ HB3) as (_ & _ & Ht3 & Htb3 & Hb3 & _).
        assert (Hz3 : 0 <= z_avail_out z3 <= 4294967295).
        { destruct HM3 as ((_ & _ & _ & _ & Hao & Hol & _) & _). pose proof (Zlength_nonneg (z_out z3)). lia. }
        rewrite E in Ht4.
        destruct (trailer_cons s3 z3 Z_FINISH s4 z4 Z_OK Ht4 (cw_prm W CF s3 HW3) Ho3 Hp3 Hpo3 Hsy3
                    ltac:(lia) ltac:(lia) Hz3 ltac:(lia)) as [Es4 Ec4].
        rewrite Es4 in Hs4. specialize (Hmg3 Hn25 Hs4). lia. }
    apply (c2_mid_end _ _ _ _ _ _ _ _ _ _ _ _ _ (HM4 Ec) Hav4 Hg0 Hbn Hmg4).
    + left; reflexivity.
    + intros E; discriminate E.
    + intros _ Hao Hin. destruct Hfl as [E|E].
      * (* Z_NO_FLUSH: the compression function was called, and returned need_more: not here *)
        exfalso. destruct Hin as [Hin|Hin]; [|rewrite E in Hin; discriminate Hin].
        assert (Hs2 : d_status s2 = BUSY_STATE).
        { destruct Hst2 as [S|S]; [exact S|]. exfalso. destruct (Hfz2' S) as [S1 _].
          rewrite Hst1 in S1. destruct (HFs S1) as [_ Hf1]. specialize (Hfin Hf1). rewrite E in Hfin. discriminate Hfin. }
        destruct (comp_none s2 z2 flush s3 z3 Hcm) as [(Hi0 & _)|(s'' & z'' & bs' & Ec' & Hbs & _)]; [lia|].
        destruct (Hcall Hs2) as (s' & z' & bs & evs & Ec2 & Hcp & _).
        rewrite Ec2 in Ec'. injection Ec' as <- <- <-.
        destruct Hcp as (_ & _ & _ & _ & _ & _ & _ & Hb').
        destruct Hbs as [ ->| ->]; destruct Hb' as (_ & Hn1' & _); [contradiction|].
        rewrite E in Hn1'. discriminate Hn1'.
      * rewrite E in Ht4.
        assert (Hz3 : 0 <= z_avail_out z3 <= 4294967295).
        { destruct HM3 as ((_ & _ & _ & _ & Hao3 & Hol & _) & _). pose proof (Zlength_nonneg (z_out z3)). lia. }
        destruct (midw_out W HI CF HF _ _ _ _ _ _ _ _ _ _ _ (HM4 Ec) Hav4) as (_ & _ & _ & HB4).
        pose proof (brunw_facts W HI CF HF _ _ _ _ _ _ _ _ HB4) as (Hp4 & _).
        rewrite (trailer_ok s3 z3 s4 z4 Ht4 Hz3 Hp4).
        destruct (HM4 Ec) as ((_ & Hni4 & _) & _). lia.
    + intros HF' Hfin' Hp0 Hroom. exact (Hr4 HF' Hroom).
Qed.

End C2Walk.
