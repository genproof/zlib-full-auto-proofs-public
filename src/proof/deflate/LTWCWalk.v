(** * The deflateBound accounting of the clip() loops: one call

    harness/rt_partial.c, rj_truncated.c, rj_bad_checksum.c and rfc_trailing_bytes.c call deflate() on the next
    min(n - pos, 2^32 - 1) bytes of the data with min(b - total_out, 2^32 - 1) bytes of output space, Z_FINISH
    exactly when the rest of the data fits in one call (LawFactsW2.bw_clip).  [BrunC] is LTWBDefs.BrunW with, at
    level 0, at most 65535 bytes in the window ([ub]) between the calls ([clip_ub], from LTWIfaceClip.cw_stored_ub).

    The walk of the stages is LTWBWalk.deflate_walk_w's.  What is new is the compression stage of a level-0
    Z_FINISH call with [ub s + avail_in >= 2^32], where LTWIface.cw_compress does not apply: then the window is
    not empty, so the stream is compressing (phase P2), its header is out and the header stages do nothing; the
    accounting leaves at least [ub s + avail_in >= 2^32] bytes of deflateBound (LTWCArith.clip_left), so the call
    has all 2^32 - 1 bytes of output space, and after the entry stage handed out at most pending_buf_size bytes
    the compressor still has at least 131072 ([clip_comp], from LTWIfaceClip.cw_compress_clip).

    The two level-0 facts are stated here as they are used ([clip_comp], [clip_ub]): LTWIfaceClip's
    [cw_compress_clip] / [cw_stored_ub] imply them (with 65540 or 131072 bytes of output space). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWBKit.
Require Import Zlib.proof.deflate.LTWBEntry Zlib.proof.deflate.LTWBHdr Zlib.proof.deflate.LTWBComp
  Zlib.proof.deflate.LTWBTrail Zlib.proof.deflate.LTWCArith.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** At level 0 at most 65535 bytes in the window. *)
Definition uok (s : dstate) : Prop := d_level s = 0 -> ub s <= 65535.

Definition BrunC (W : dstate -> Prop) (HI : hdr_inv) (n b pos : Z) (fin : bool) (s : dstate) (tin tout adler : Z)
    : Prop :=
  BrunW W HI n b pos fin s tin tout adler /\ uok s.

(** What a call of the clip() loop gives (LawFactsW2.bw_clip's conclusion after the model run). *)
Definition clip_post (W : dstate -> Prop) (HI : hdr_inv) (n b pos tin tout aout flush : Z) (inb : list Z)
    (s s' : dstate) (z' : strm) (code : Z) : Prop :=
  d_gzhead s' = d_gzhead s /\
  z_in z' = inb /\ 0 <= z_avail_in z' <= Zlength inb /\ z_next_in z' = Zlength inb - z_avail_in z' /\
  0 <= z_avail_out z' <= aout /\ Zlength (z_out z') = aout - z_avail_out z' /\ bytes (z_out z') /\
  z_total_in z' = tin + (Zlength inb - z_avail_in z') /\ z_total_out z' = tout + (aout - z_avail_out z') /\
  z_total_out z' <= b /\
  (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_END) /\
  (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) /\
  (code <> Z_STREAM_END ->
   BrunC W HI n b (pos + (Zlength inb - z_avail_in z')) (flush =? Z_FINISH) s' (z_total_in z') (z_total_out z')
     (z_adler z')).

(** The compressor at level 0 with at most 65535 bytes in the window and at least 131072 bytes of output space,
    whatever the input (LTWIfaceClip.cw_compress_clip). *)
Definition clip_comp (W : dstate -> Prop) : Prop :=
  forall s z flush,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_okw z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    d_level s = 0 -> ub s <= 65535 -> 131072 <= z_avail_out z ->
    exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W s z flush s' z' bs evs.

(** After a level-0 compression call at most 65535 bytes are in the window (LTWIfaceClip.cw_stored_ub). *)
Definition clip_ub (W : dstate -> Prop) : Prop :=
  forall s z flush s' z' bs,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_okw z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    d_level s = 0 -> ub s <= 65535 ->
    c_compress_func s z flush = Some (s', z', bs) -> ub s' <= 65535.

Lemma uok_core_eq : forall s s', core_eq s s' -> uok s -> uok s'.
Proof.
  intros s s' H U. unfold uok in *.
  pose proof (core_eq_fields s s' H) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & El & _).
  rewrite (ub_core_eq s s' H), El. exact U.
Qed.

(** The pending bytes fit in pending_buf (at most 4 * 2^15 bytes). *)
Lemma pend_small : forall s, prm s -> outok s -> d_pending s <= 131072.
Proof.
  intros s (_ & _ & _ & (Hh1 & Hh2) & _ & _ & _ & HL & Hpb & _) (_ & _ & Hpo & Hpp & _).
  assert (2 ^ (d_hash_bits s - 1) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Section Clip.
Context (W : dstate -> Prop) (HI : hdr_inv) (CF : core_facts_w W) (HF : hdr_facts_w HI).

(** A call that starts with bytes in the window at level 0: the stream is compressing, and deflateBound leaves
    room for the window and the rest of the data. *)
Lemma clip_start : forall n b pos fin s tin tout adler,
  BrunW W HI n b pos fin s tin tout adler -> d_level s = 0 -> 0 < ub s ->
  d_status s = BUSY_STATE /\ ub s + (n - pos) <= b - tout - d_pending s.
Proof.
  intros n b pos fin s tin tout adler (H & w0 & HW & Ho & Hw0 & Hb & HH & Hn & Hpos & Htin & Htout & Hgz & Hlf & Hph)
    Hl0 Hu.
  destruct Hph as [P|[P|[P|P]]].
  - destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & Hu0 & _). lia.
  - destruct P as (_ & _ & _ & _ & _ & _ & Hu0). lia.
  - destruct P as (Hst & _ & _ & _ & E & k & HE & Hk0 & Hmk & Hg).
    split; [exact Hst|].
    destruct (cw_pos W CF s HW) as (L1 & L2 & L3 & L4).
    destruct (outok_ranges s Ho) as [Hp Hbi].
    assert (Hcl : bcls_of s <> BFixed).
    { unfold bcls_of. destruct (tight_b s); [discriminate|]. rewrite Hl0. cbn.
      rewrite andb_false_r. discriminate. }
    assert (Hub0 : 0 <= ub s) by (unfold ub; lia).
    pose proof (clip_left (bcls_of s) (Zlength H) n E k tout (d_pending s) (d_bi_valid s) w0 Hcl Hk0 Hmk
                  ltac:(lia) Hbi Hw0 Hg) as HL.
    lia.
  - destruct P as (_ & _ & _ & Hu0 & _). lia.
Qed.

(** At the compression stage, in BUSY_STATE with nothing pending: the hypotheses of the compression facts. *)
Lemma comp_pre : forall n b pos0 inb aout tin0 tout0 flush gz0 s z,
  MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s z -> z_next_in z = 0 -> Zlength inb <= 4294967295 ->
  d_status s = BUSY_STATE -> d_pending s = 0 -> d_po s = 0 -> d_bi_valid s <= 7 ->
  W s /\ outok s /\ quiet s /\ 0 <= flush <= 5 /\ zin_okw z /\ 0 <= d_wrap s <= 2 /\
  adler_pre (d_wrap s) (z_adler z).
Proof.
  intros n b pos0 inb aout tin0 tout0 flush gz0 s z HM Hni Hib Hst Hpd Hpo Hbv.
  pose proof HM as ((Hin & _ & Hav & Htin & Hao & Hol & Hto & Hby) & Hbytes & Hpos0 & Hle & Hfl & Hfin & Haout &
                    Htin0 & Htout0 & Hgz & Hbr).
  pose proof (brunw_facts W HI CF HF _ _ _ _ _ _ _ _ Hbr) as (_ & _ & Ht & Htb & Hb & Hpos & Hn & Htinr & _).
  destruct Hbr as (H & w0 & HW & Ho & Hw0 & _ & _ & _ & _ & _ & _ & _ & _ & Hph).
  assert (HP2 : d_wrap s = w0 /\ adler_ok w0 (z_adler z)).
  { destruct Hph as [(Hs' & _)|[(_ & _ & (k & Hk & _) & _)|[(_ & Hw' & _ & Had & _)|(Hs' & _)]]].
    - exfalso. rewrite Hst in Hs'. destruct (w0 =? 2); unfold BUSY_STATE, INIT_STATE, GZIP_STATE in Hs'; lia.
    - exfalso. destruct (hw_status HI HF _ _ _ _ Hk) as (_ & _ & Hs' & _). rewrite Hst in Hs'.
      unfold BUSY_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in Hs'; lia.
    - split; assumption.
    - exfalso. rewrite Hst in Hs'. unfold BUSY_STATE, FINISH_STATE in Hs'. lia. }
  destruct HP2 as [Hwr Had].
  pose proof (Zlength_nonneg (z_out z)). pose proof (Zlength_nonneg inb).
  split; [exact HW|]. split; [exact Ho|]. split; [unfold quiet; auto|].
  split; [destruct Hfl as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia|].
  split.
  { unfold zin_okw. rewrite Hin, Hni. repeat split; try lia; exact Hbytes. }
  split; [lia|].
  unfold adler_pre. destruct Had as [A1 A2]. split; intros Hw1; [apply A1|apply A2]; congruence.
Qed.

(** The end of the call in [MidW] (any stage that returns, or the trailer without Z_STREAM_END). *)
Lemma clip_mid_end : forall n b pos inb aout tin tout flush s s' z' code,
  MidW W HI n b pos inb aout tin tout flush (d_gzhead s) s' z' ->
  (flush = Z_FINISH \/ 0 <= z_avail_in z' \/ z_next_in z' = 0) -> uok s' ->
  (code = Z_OK \/ code = Z_BUF_ERROR) ->
  clip_post W HI n b pos tin tout aout flush inb s s' z' code.
Proof.
  intros n b pos inb aout tin tout flush s s' z' code HM Hav U Hc.
  destruct (midw_out W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM Hav) as (Hgz & Hai & Hto & HB).
  destruct HM as ((Hin & Hni & Hsum & Htin & Hao & Hol & Hto' & Hby) & _).
  pose proof (Zlength_nonneg (z_out z')).
  unfold clip_post. split; [exact Hgz|]. split; [exact Hin|]. split; [exact Hai|]. split; [lia|].
  split; [lia|]. split; [lia|]. split; [exact Hby|]. split; [lia|]. split; [lia|]. split; [exact Hto|].
  split; [tauto|].
  split; [intros E; destruct Hc as [Hc|Hc]; rewrite Hc in E; discriminate E|].
  intros _. replace (pos + (Zlength inb - z_avail_in z')) with (pos + Zlength inb - z_avail_in z') by lia.
  split; [exact HB|exact U].
Qed.

(** The end of the call with Z_STREAM_END (the trailer). *)
Lemma clip_se_post : forall n b pos inb aout tin tout flush s s' z',
  cframe inb aout tin tout z' -> d_gzhead s' = d_gzhead s -> z_total_out z' <= b -> flush = Z_FINISH ->
  z_avail_in z' = 0 -> clip_post W HI n b pos tin tout aout flush inb s s' z' Z_STREAM_END.
Proof.
  intros n b pos inb aout tin tout flush s s' z' (Hin & Hni & Hsum & Htin & Hao & Hol & Hto & Hby) Hgz Htb Hf Hai.
  pose proof (Zlength_nonneg (z_out z')). pose proof (Zlength_nonneg inb).
  unfold clip_post. split; [exact Hgz|]. split; [exact Hin|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. split; [exact Hby|]. split; [lia|]. split; [lia|]. split; [exact Htb|].
  split; [right; right; reflexivity|]. split; [intros _; split; assumption|]. intros E; contradiction.
Qed.

Context (CC : clip_comp W) (CU : clip_ub W) (BB : block_bound_statement).

Lemma deflate_walk_c : forall n b pos fin s tin tout adler inb msg flush aout,
  BrunC W HI n b pos fin s tin tout adler -> bytes inb ->
  Zlength inb = Z.min (n - pos) 4294967295 -> (fin = true -> n - pos <= 4294967295) ->
  flush = (if n - pos <=? 4294967295 then Z_FINISH else Z_NO_FLUSH) ->
  aout = Z.min (b - tout) 4294967295 ->
  exists s' z' code,
    c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) /\
    clip_post W HI n b pos tin tout aout flush inb s s' z' code.
Proof.
  intros n b pos fin s tin tout adler inb msg flush aout [HB U] Hinb Hlen Hfin0 Ef Ea.
  pose proof (brunw_facts W HI CF HF _ _ _ _ _ _ _ _ HB) as (Hpd & Hbv & Ht & Htb & Hb & Hpos & Hn & Htin & _).
  assert (Hfl : flush = Z_NO_FLUSH \/ flush = Z_FINISH) by (rewrite Ef; destruct (_ <=? _); [right|left]; reflexivity).
  assert (HfF : flush = Z_FINISH <-> n - pos <= 4294967295).
  { rewrite Ef. destruct (Z.leb_spec (n - pos) 4294967295) as [L|L]; unfold Z_FINISH, Z_NO_FLUSH; split; intros; lia. }
  assert (Hfin : fin = true -> flush = Z_FINISH) by (intros Hf; apply HfF; auto).
  assert (Hpn : pos + Zlength inb <= n) by lia.
  assert (HpF : flush = Z_FINISH -> pos + Zlength inb = n) by (intros Hf; apply HfF in Hf; lia).
  assert (Ha : 0 <= aout <= 4294967295) by lia.
  assert (Hib : Zlength inb <= 4294967295) by lia.
  destruct (brunw_status _ _ _ _ _ _ _ _ _ _ HF HB) as (Hbad & Hnf).
  pose proof (midw_start _ _ _ _ _ _ _ _ _ _ _ _ _ msg HB Hfl Hfin Hinb Hpn HpF Ha) as HM0.
  rewrite c_deflate_stages, Hbad.
  assert (Hfr : false || (flush >? Z_BLOCK) || (flush <? 0) = false)
    by (destruct Hfl as [E|E]; rewrite E; reflexivity).
  rewrite Hfr. cbn iota beta.
  destruct (entry_stage_w W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM0 eq_refl eq_refl)
    as (s1 & z1 & o1 & He & HM1 & Hn1 & Hst1 & Hw1 & Hce1 & Hout1 & Ho1 & _).
  pose proof (uok_core_eq _ _ Hce1 U) as U1.
  rewrite He. destruct o1 as [c1|].
  { (* the entry stage returns *)
    cbn [then_stage bind]. exists s1, z1, c1. destruct Ho1 as (Hc1 & _).
    split; [reflexivity|].
    exact (clip_mid_end _ _ _ _ _ _ _ _ _ _ _ _ HM1 (or_intror (or_intror Hn1)) U1 Hc1). }
  destruct Ho1 as (Hp1 & Hpo1 & Hbv1 & Hfz1).
  cbn [then_stage bind].
  destruct (hdr_stage_w W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM1 Hn1 Hp1 Hpo1 Hbv1 Hfz1)
    as (s2 & z2 & o2 & Hh & HM2 & Hn2 & Hce2 & Ho2N & Ho2S & _).
  pose proof (uok_core_eq _ _ Hce2 U1) as U2.
  rewrite Hh. destruct o2 as [c2|].
  { (* a header stage returns *)
    cbn [then_stage bind]. exists s2, z2, c2.
    split; [reflexivity|].
    exact (clip_mid_end _ _ _ _ _ _ _ _ _ _ _ _ HM2 (or_intror (or_intror Hn2)) U2 (or_introl (Ho2S c2 eq_refl))). }
  destruct (Ho2N eq_refl) as (Hst2 & Hp2 & Hpo2 & Hbv2 & Hfz2').
  assert (Hfz2 : d_status s2 = FINISH_STATE -> z_avail_in z2 = 0) by (intros E; exact (proj2 (Hfz2' E))).
  cbn [then_stage bind].
  (* the window and the level are those at the call *)
  pose proof (core_eq_fields s s1 Hce1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & El1 & _).
  pose proof (core_eq_fields s1 s2 Hce2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & El2 & _).
  assert (Eub2 : ub s2 = ub s) by (rewrite (ub_core_eq s1 s2 Hce2), (ub_core_eq s s1 Hce1); reflexivity).
  assert (El : d_level s2 = d_level s) by congruence.
  assert (Eai2 : z_avail_in z2 = Zlength inb).
  { destruct HM2 as ((_ & _ & Hsum & _) & _). lia. }
  (* the compression call: cw_compress, or at level 0 with too much for 32 bits cw_compress_clip *)
  assert (Hcomp : (d_level s2 = 0 -> flush <> Z_NO_FLUSH -> ub s2 + z_avail_in z2 <= 4294967295) \/
     (exists s' z' bs evs, c_compress_func s2 z2 flush = Some (s', z', bs) /\ cpost W s2 z2 flush s' z' bs evs)).
  { destruct (Z.eq_dec (d_level s) 0) as [Hl0|Hl0]; [|left; intros; congruence].
    destruct (Z.eq_dec flush Z_NO_FLUSH) as [Hf0|Hf0]; [left; intros; contradiction|].
    destruct (Z_le_gt_dec (ub s + Zlength inb) 4294967295) as [Hsm|Hbig]; [left; intros; lia|].
    right.
    assert (Hu : 0 < ub s) by lia.
    destruct (clip_start _ _ _ _ _ _ _ _ HB Hl0 Hu) as [Hbusy Hroom].
    assert (HfE : flush = Z_FINISH) by (destruct Hfl; [contradiction|assumption]).
    assert (Hrest : Zlength inb = n - pos) by (apply HfF in HfE; lia).
    assert (Ea' : aout = 4294967295) by lia.
    pose proof HB as (H0 & w0 & HW & Ho & _).
    pose proof (pend_small s (cw_prm W CF s HW) Ho) as Hps.
    assert (E2 : s2 = s1 /\ z2 = z1).
    { rewrite (hdr_stages_busy s1 z1 (or_introl (eq_trans Hst1 Hbusy))) in Hh. injection Hh as <- <-. auto. }
    destruct E2 as [-> ->].
    assert (Hao1 : 131072 <= z_avail_out z1).
    { destruct HM1 as ((_ & _ & _ & _ & _ & Hol & _) & _). specialize (Hout1 eq_refl). lia. }
    destruct (comp_pre _ _ _ _ _ _ _ _ _ _ _ HM2 Hn2 Hib (eq_trans Hst1 Hbusy) Hp2 Hpo2 Hbv2)
      as (HW2 & Ho2 & Hq2 & Hfr2 & Hz2 & Hw2 & Ha2).
    assert (Hu1 : ub s1 <= 65535) by (rewrite Eub2; exact (U Hl0)).
    exact (CC s1 z1 flush HW2 Ho2 Hq2 Hfr2 Hz2 Hw2 Ha2 (eq_trans El Hl0) Hu1 Hao1). }
  destruct (comp_stage_w BB W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM2 Hn2 Hib Hst2 Hp2 Hpo2 Hbv2 Hfz2 Hcomp)
    as (s3 & z3 & o3 & Hcm & HM3 & Hav3 & Hub3 & Ho3N & Ho3S & _).
  (* at most 65535 bytes in the window after the compression stage *)
  assert (U3 : uok s3).
  { destruct Hub3 as [(E1 & E2)|(Hb2 & s' & z' & bs & Ec & E1 & E2)].
    - unfold uok. rewrite E1, E2. exact U2.
    - unfold uok. rewrite E1, E2. intros Hl0.
      destruct (comp_pre _ _ _ _ _ _ _ _ _ _ _ HM2 Hn2 Hib Hb2 Hp2 Hpo2 Hbv2)
        as (HW2 & Ho2 & Hq2 & Hfr2 & Hz2 & Hw2 & Ha2).
      exact (CU s2 z2 flush s' z' bs HW2 Ho2 Hq2 Hfr2 Hz2 Hw2 Ha2 Hl0 (U2 Hl0) Ec). }
  rewrite Hcm. destruct o3 as [c3|].
  { (* the compression stage returns *)
    cbn [bind]. exists s3, z3, c3.
    split; [reflexivity|].
    exact (clip_mid_end _ _ _ _ _ _ _ _ _ _ _ _ HM3 (or_intror (or_introl Hav3)) U3 (or_introl (Ho3S c3 eq_refl))). }
  cbn [bind].
  destruct (trailer_stage_w W HI CF HF _ _ _ _ _ _ _ _ _ _ _ HM3 (Ho3N eq_refl))
    as (s4 & z4 & code & Ht4 & Hgz4 & Hce4 & Hcf4 & Hcode & Hto4 & HSE & HM4 & _).
  pose proof (uok_core_eq _ _ Hce4 U3) as U4.
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
    rewrite Ec. exact (clip_se_post _ _ _ _ _ _ _ _ _ _ _ Hcf4 Hgz4 Hto4 HfE (HSE Ec)).
  - destruct Hcode as [Hc|Hc]; [|contradiction].
    exact (clip_mid_end _ _ _ _ _ _ _ _ _ _ _ _ (HM4 Ec) Hav4 U4 (or_introl Hc)).
Qed.

End Clip.
