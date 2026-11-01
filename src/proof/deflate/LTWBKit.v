(** * The deflateBound accounting for the short laws: facts of [BrunW] and [MidW] shared by the stages

    Ports of LTBWalk.brun_fin / brun_status / brun_tout / mid_start / mid_out and LTBEntry.brun_facts /
    brun_frame / mid_msg / mid_step to the invariants of LTWBDefs.v, with LTWIface's [core_facts_w] /
    [hdr_facts_w] and LTWBArith's limit-free arithmetic. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWBArith.
Require Export Zlib.proof.deflate.LTBEntry.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** [fin] matters only in the phase P3. *)
Lemma brunw_fin : forall W HI n b pos fin fin' s tin tout adler,
  BrunW W HI n b pos fin s tin tout adler -> (fin = true -> fin' = true) ->
  BrunW W HI n b pos fin' s tin tout adler.
Proof.
  intros W HI n b pos fin fin' s tin tout adler (H & w0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & Hph) Hf.
  exists H, w0. do 11 (split; [assumption|]).
  unfold bphase in *. destruct Hph as [P|[P|[P|P]]];
    [left; exact P|right; left; exact P|right; right; left; exact P|right; right; right].
  destruct P as (P1 & P2 & P3). split; [exact P1|split; [auto|exact P3]].
Qed.

(** The status passes deflateStateCheck; it is FINISH_STATE only in P3 ([fin = true]). *)
Lemma brunw_status : forall W HI n b pos fin s tin tout adler, hdr_facts_w HI ->
  BrunW W HI n b pos fin s tin tout adler ->
  bad_state s = false /\ (fin = false -> d_status s <> FINISH_STATE).
Proof.
  intros W HI n b pos fin s tin tout adler HF (H & w0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph).
  unfold bad_state, c_deflateStateCheck, status_ok.
  destruct Hph as [(Hs & _)|[(_ & _ & (k & Hk & _) & _)|[(Hs & _)|(Hs & Hf & _)]]].
  - rewrite Hs. destruct (w0 =? 2); split; try reflexivity; unfold INIT_STATE, GZIP_STATE, FINISH_STATE; lia.
  - destruct (hw_status _ HF _ _ _ _ Hk) as (_ & _ & Hs & _).
    destruct Hs as [Hs|[Hs|[Hs|Hs]]]; rewrite Hs; split; try reflexivity;
      unfold EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE, FINISH_STATE; lia.
  - rewrite Hs. split; [reflexivity|]. unfold BUSY_STATE, FINISH_STATE; lia.
  - rewrite Hs. split; [reflexivity|]. intros Hf'. congruence.
Qed.

Section Kit.
Variable W : dstate -> Prop.
Variable HI : hdr_inv.
Hypothesis CF : core_facts_w W.
Hypothesis HF : hdr_facts_w HI.

(** The ranges: what is handed out or pending is within the bound, strictly before the end of the stream. *)
Lemma brunw_facts : forall n b pos fin s tin tout adler,
  BrunW W HI n b pos fin s tin tout adler ->
  0 <= d_pending s /\ 0 <= d_bi_valid s <= 7 /\ 0 <= tout /\ tout + d_pending s <= b /\ b <= 13835058055282163712 /\
  0 <= pos <= n /\ n <= 9223372036854775807 /\ 0 <= tin <= 4294967295 + pos /\
  (d_status s = FINISH_STATE -> pos = n /\ fin = true) /\
  (d_status s <> FINISH_STATE -> tout + d_pending s < b).
Proof.
  intros n b pos fin s tin tout adler
    (H & w0 & HW & Ho & Hw0 & Hb & HH & Hn & Hpos & Htin & Htout & Hgz & Hlf & Hph).
  destruct (outok_ranges s Ho) as [Hp Hbi].
  pose proof (Zlength_nonneg H) as HH0. pose proof (tlen_range w0) as Ht.
  pose proof (body_range_w (bcls_of s) n (proj1 Hn)) as Hbr.
  assert (Hn4 : n / 4 <= 2305843009213693952) by (apply Z.div_le_upper_bound; lia).
  unfold Gb in Hph.
  destruct Hph as [P0|[P1|[P2|P3]]].
  - destruct P0 as (Hst & _ & _ & _ & Ht0 & Hp0 & Hbi0 & _).
    rewrite Hst. unfold FINISH_STATE, INIT_STATE, GZIP_STATE.
    do 8 (split; [lia|]).
    split; [destruct (w0 =? 2); intros; lia|]. intros; lia.
  - destruct P1 as (_ & _ & (k & HI1 & Hk) & _ & Hbi0 & _).
    destruct (hw_status HI HF _ _ _ _ HI1) as (_ & _ & Hst & _ & Hk2).
    do 8 (split; [lia|]).
    split; [|intros; lia].
    unfold FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in *. lia.
  - destruct P2 as (Hst & _ & Hbi7 & _ & E & k & HE & Hk0 & Hmk & Hg).
    destruct (cw_pos W CF s HW) as (L1 & L2 & L3 & L4).
    unfold ub in HE. unfold Gb in Hg. pose proof (minblk_pos (bcls_of s)).
    assert (0 <= E) by nia.
    pose proof (acc_mid_w (bcls_of s) (Zlength H) E k n HH0 Hk0 Hmk ltac:(lia)).
    rewrite Hst. unfold FINISH_STATE, BUSY_STATE.
    do 8 (split; [lia|]).
    split; intros; lia.
  - destruct P3 as (Hst & Hfin & Hpn & _ & _ & Hbi0 & _ & Hg). unfold Gb in Hg.
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [destruct Hg as [(_ & Hg)|(_ & _ & Hg)]; lia|].
    do 4 (split; [lia|]).
    split; [auto|]. intros; contradiction.
Qed.

(** A step of deflate()'s own stages (not the compressor): [BrunW] is kept when the core part is unchanged and the
    output part only moves bytes from pending to next_out. *)
Lemma brunw_frame : forall n b pos fin s s' tin tout tout' adler,
  BrunW W HI n b pos fin s tin tout adler ->
  core_eq s s' -> d_status s' = d_status s -> d_wrap s' = d_wrap s -> d_gzhead s' = d_gzhead s ->
  d_gzindex s' = d_gzindex s -> -2 <= d_last_flush s' <= 5 -> outok s' -> d_bi_valid s' = d_bi_valid s ->
  tout' + d_pending s' = tout + d_pending s -> 0 <= tout' ->
  (d_pending s = 0 -> hdr_bytes s' adler = hdr_bytes s adler) ->
  BrunW W HI n b pos fin s' tin tout' adler.
Proof.
  intros n b pos fin s s' tin tout tout' adler
    (H & w0 & HW & Ho & Hw0 & Hb & HH & Hn & Hpos & Htin & Htout & Hgz & Hlf & Hph)
    Hce Est Ewr Egz Egi Hlf' Ho' Ebi Etp Ht' Ehd.
  destruct (outok_ranges s Ho) as [Hp Hbi]. destruct (outok_ranges s' Ho') as [Hp' Hbi'].
  pose proof (core_eq_fields s s' Hce) as (_ & _ & _ & _ & _ & _ & _ & Epbs & Esym & _).
  pose proof (bcls_core_eq s s' Hce) as Ecl. pose proof (ub_core_eq s s' Hce) as Eub.
  exists H, w0. rewrite Ecl.
  split; [exact (cw_frame W CF s s' HW Hce)|]. split; [exact Ho'|]. split; [exact Hw0|].
  split; [exact Hb|]. split; [exact HH|]. split; [exact Hn|]. split; [exact Hpos|].
  split; [exact Htin|]. split; [exact Ht'|].
  split; [unfold gzh_ok_w in *; rewrite Egz; exact Hgz|]. split; [exact Hlf'|].
  assert (EG : Gb s' tout' = Gb s tout) by (unfold Gb; lia).
  unfold bphase in *. rewrite EG, Est, Ewr, Esym, Eub, Ebi, Ecl.
  destruct Hph as [P0|[P1|[P2|P3]]].
  - left. destruct P0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    rewrite Ehd by exact A6. repeat (split; [assumption|]). split; [lia|]. split; [lia|]. tauto.
  - right; left. destruct P1 as (A1 & A2 & (k & HI1 & Hk) & A4 & A5 & A6 & A7).
    split; [exact A1|]. split; [exact A2|]. split.
    + exists k. split; [|lia]. apply (hw_frame HI HF s s' adler H k HI1); auto.
    + auto.
  - right; right; left. exact P2.
  - right; right; right. exact P3.
Qed.

Lemma midw_msg : forall n b pos0 inb aout tin0 tout0 flush gz0 s z m,
  MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s z ->
  MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s (set_z_msg z m).
Proof. intros. destruct z; exact H. Qed.

(** An output step inside the call: [x] goes from pending to next_out. *)
Lemma midw_step : forall n b pos0 inb aout tin0 tout0 flush gz0 s z s' z' x,
  MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s z ->
  z_in z' = z_in z -> z_next_in z' = z_next_in z -> z_avail_in z' = z_avail_in z ->
  z_total_in z' = z_total_in z -> z_out z' = z_out z ++ x -> z_avail_out z' = z_avail_out z - Zlength x ->
  z_total_out z' = z_total_out z + Zlength x -> z_adler z' = z_adler z ->
  Zlength x <= z_avail_out z -> bytes x ->
  core_eq s s' -> d_status s' = d_status s -> d_wrap s' = d_wrap s -> d_gzhead s' = d_gzhead s ->
  d_gzindex s' = d_gzindex s -> -2 <= d_last_flush s' <= 5 -> outok s' -> d_bi_valid s' = d_bi_valid s ->
  d_pending s' = d_pending s - Zlength x ->
  (d_pending s = 0 -> hdr_bytes s' (z_adler z) = hdr_bytes s (z_adler z)) ->
  MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s' z'.
Proof.
  intros n b pos0 inb aout tin0 tout0 flush gz0 s z s' z' x
    ((Hin & Hni & Hav & Htin & Hao & Hol & Hto & Hby) & Hbytes & Hpos0 & Hle & Hfl & Hfin & Haout &
     Htin0 & Htout0 & Hgz & Hbr)
    E1 E2 E3 E4 E5 E6 E7 E8 Hx Hbx Hce Est Ewr Egz Egi Hlf Ho Ebi Ep Ehd.
  pose proof (Zlength_nonneg x). pose proof (Zlength_nonneg (z_out z)).
  split; [|split; [exact Hbytes|]].
  { unfold cframe. rewrite E1, E2, E3, E4, E5, E6, E7, Zlength_app.
    repeat split; try lia; try assumption. unfold bytes in *. apply Forall_app. split; assumption. }
  repeat (split; [assumption|]). split; [rewrite Egz; exact Hgz|].
  rewrite E2, E4, E7, E8.
  apply (brunw_frame _ _ _ _ s s' _ _ _ _ Hbr Hce Est Ewr Egz Egi Hlf Ho Ebi); [lia|lia|exact Ehd].
Qed.

(** What the end of the call needs from [MidW]. *)
Lemma midw_out : forall n b pos inb aout tin tout flush gz0 s z,
  MidW W HI n b pos inb aout tin tout flush gz0 s z ->
  (flush = Z_FINISH \/ 0 <= z_avail_in z \/ z_next_in z = 0) ->
  d_gzhead s = gz0 /\ 0 <= z_avail_in z <= Zlength inb /\ z_total_out z <= b /\
  BrunW W HI n b (pos + Zlength inb - z_avail_in z) (flush =? Z_FINISH) s (z_total_in z) (z_total_out z)
       (z_adler z).
Proof.
  intros n b pos inb aout tin tout flush gz0 s z
    (Hc & Hinb & Hp0 & Hpn & Hfl & HfF & Ha & Ht0 & Hto & Hgz & HB) Hav.
  destruct Hc as (Hzi & Hni & Hsum & _).
  pose proof (brunw_facts _ _ _ _ _ _ _ _ HB) as (Hp & _ & _ & Ht & _).
  replace (pos + Zlength inb - z_avail_in z) with (pos + z_next_in z) by lia.
  assert (0 <= z_avail_in z).
  { destruct Hav as [Hf|[Hav|Hav]]; [|exact Hav|pose proof (Zlength_nonneg inb); lia].
    destruct HB as (H & w0 & _ & _ & _ & _ & _ & _ & Hpp & _). specialize (HfF Hf). lia. }
  repeat split; auto; lia.
Qed.

End Kit.

(** [MidW] at the start of the call. *)
Lemma midw_start : forall W HI n b pos fin s tin tout adler inb aout flush msg,
  BrunW W HI n b pos fin s tin tout adler ->
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH) -> (fin = true -> flush = Z_FINISH) ->
  bytes inb -> pos + Zlength inb <= n -> (flush = Z_FINISH -> pos + Zlength inb = n) ->
  0 <= aout <= 4294967295 ->
  MidW W HI n b pos inb aout tin tout flush (d_gzhead s) s (zcall inb 0 (Zlength inb) tin aout tout adler msg).
Proof.
  intros W HI n b pos fin s tin tout adler inb aout flush msg HB Hfl Hfin Hinb Hpn HpF Ha.
  pose proof HB as (H & w0 & _ & _ & _ & _ & _ & _ & Hp & Hti & Hto & _).
  unfold MidW, cframe, zcall; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler].
  rewrite Zlength_nil.
  repeat split; try lia; auto.
  - constructor.
  - rewrite !Z.add_0_r. apply (brunw_fin _ _ _ _ _ fin); [exact HB|].
    intros Hf. rewrite (Hfin Hf). reflexivity.
Qed.
