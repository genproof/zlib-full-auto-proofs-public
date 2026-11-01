(** * deflate_slow for wide streams: the loop and the assembly

    Port of LTCSlow2.v (the loop by its measure, [slow_ok2]) to the invariant of DetCoreSlowInv.v and the
    parts DetCoreSlow<Part>.v; [loop_measure] is LTCSlow2's. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetCoreSlowInv.
Require Import Zlib.proof.deflate.LTCSlow2 Zlib.proof.deflate.DetCoreSlowRefill Zlib.proof.deflate.DetCoreSlowPre
  Zlib.proof.deflate.DetCoreSlowMatch Zlib.proof.deflate.DetCoreSlowLit Zlib.proof.deflate.DetCoreSlowCand
  Zlib.proof.deflate.DetCoreSlowEnd Zlib.proof.deflate.DetCoreSlowFbo.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The loop of deflate_slow *)

Definition slow_Pw (s0 : dstate) (z0 : strm) (flush : Z) (a : dstate * strm) : Prop :=
  exists evs, SIw s0 z0 flush (fst a) (snd a) evs.

Definition slow_Qw (s0 : dstate) (z0 : strm) (flush : Z) (b : dexit) : Prop :=
  let '(s, z, o) := b in
  match o with
  | Some bs => exists evs, cpost W2 s0 z0 flush s z bs evs
  | None => exists evs, SIw s0 z0 flush s z evs /\ d_lookahead s = 0 /\ z_avail_in z = 0 /\
              flush <> Z_NO_FLUSH /\ d_strstart s + MIN_LOOKAHEAD <= d_window_size s
  end.

Lemma SIw_msr s0 z0 flush s z evs : SIw s0 z0 flush s z evs -> 0 <= msr s z < 2 ^ 40.
Proof.
  intros ((HW & _) & _ & _ & HE).
  destruct HW as (Hp & (_ & _ & Hws & _) & (P1 & P2 & P3 & _) & _).
  destruct HE as (_ & _ & _ & _ & _ & ((_ & _ & Ha & _) & _) & _).
  destruct Hp as (Hwb & Hws2 & _).
  assert (d_w_size s <= 2 ^ 15).
  { rewrite Hws2. apply Z.pow_le_mono_r; lia. }
  change (2 ^ 15) with 32768 in *. change (2 ^ 40) with 1099511627776. unfold msr. lia.
Qed.

Lemma slow_body_okw : fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec ->
  forall s0 z0 flush a, slow_Pw s0 z0 flush a ->
  0 <= msr (fst a) (snd a) /\ exists r, dsl_body flush a = Some r /\
    match r with
    | inl a' => slow_Pw s0 z0 flush a' /\ msr (fst a') (snd a') < msr (fst a) (snd a)
    | inr b => slow_Qw s0 z0 flush b
    end.
Proof.
  intros Hfill Hins Hlm Htally Hfbo s0 z0 flush [s z] [evs HI]. cbn [fst snd] in *.
  pose proof (fboev_okw Hfbo) as Hev.
  split; [apply (SIw_msr _ _ _ _ _ _ HI)|].
  unfold dsl_body.
  destruct (refill_okw Hfill s0 z0 flush s z evs HI) as (r & Er & Hr). rewrite Er. cbn [bind].
  destruct r as [[s' z']|[[s' z'] [bs|]]].
  - destruct Hr as (HI' & Hrdy & Hm).
    rewrite dsl_step_eq.
    destruct (pre_okw Hins Hlm s0 z0 flush s' z' evs HI' Hrdy) as (s1 & E1 & Hmid). rewrite E1. cbn [bind].
    assert (Hst : exists r, (if (d_prev_length s1 >=? MIN_MATCH) && (d_match_length s1 <=? d_prev_length s1)
                             then dsl_match s1 z'
                             else if negb (d_match_available s1 =? 0) then dsl_lit s1 z' else dsl_cand s1 z')
                            = Some r /\ step_okw s0 z0 flush s' z' r).
    { destruct ((d_prev_length s1 >=? MIN_MATCH) && (d_match_length s1 <=? d_prev_length s1)) eqn:Eb.
      - apply andb_true_iff in Eb as [Eb1 Eb2]. apply Z.geb_le in Eb1. apply Z.leb_le in Eb2.
        exact (match_okw Hins Htally Hev s0 z0 flush s' z' evs s1 HI' Hrdy Hmid Eb1 Eb2).
      - assert (Hn : ~ (MIN_MATCH <= d_prev_length s1 /\ d_match_length s1 <= d_prev_length s1)).
        { intros [N1 N2]. apply Z.geb_le in N1. apply Z.leb_le in N2. rewrite N1, N2 in Eb. discriminate. }
        destruct (Z.eqb_spec (d_match_available s1) 0) as [Ea|Ea]; cbn [negb].
        + exact (cand_okw s0 z0 flush s' z' evs s1 HI' Hrdy Hmid Hn Ea).
        + exact (lit_okw Htally Hev s0 z0 flush s' z' evs s1 HI' Hrdy Hmid Hn Ea). }
    destruct Hst as (r & Es & Hs). rewrite Es. exists r. split; [reflexivity|].
    destruct r as [[s2 z2]|[[s2 z2] [bs|]]]; cbn [step_okw] in Hs.
    + destruct Hs as (evs' & HI2 & Hm2). split; [exists evs'; exact HI2|]. cbn [fst snd]. lia.
    + exact Hs.
    + destruct Hs.
  - exists (inr (s', z', Some bs)). split; [reflexivity|]. exact Hr.
  - exists (inr (s', z', None)). split; [reflexivity|].
    destruct Hr as (HI' & H1 & H2 & H3 & H4). exists evs. auto.
Qed.

Theorem slow_ok2w : fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec -> fpend_spec2 -> slow_spec2w.
Proof.
  intros Hfill Hins Hlm Htally Hfbo _ s z flush Hpre Hfn.
  pose proof (SIw_init s z flush Hpre Hfn) as HI.
  destruct (loop_measure (dsl_body flush) (slow_Pw s z flush) (slow_Qw s z flush) (fun a => msr (fst a) (snd a))
              (slow_body_okw Hfill Hins Hlm Htally Hfbo s z flush) (s, z) (ex_intro _ [] HI)
              (proj2 (SIw_msr _ _ _ _ _ _ HI))) as ([[s1 z1] o] & E & HQ).
  rewrite c_deflate_slow_eq, E. cbn [bind].
  destruct o as [bs|]; cbn [slow_Qw] in HQ.
  - destruct HQ as (evs & Hc). exists s1, z1, bs, evs. split; [reflexivity|exact Hc].
  - destruct HQ as (evs & HI1 & H1 & H2 & H3 & H4).
    destruct (end_okw Htally (fboev_okw Hfbo) s z flush s1 z1 evs HI1 H1 H2 H3 H4) as (s' & z' & bs & evs' & E' & Hc).
    exists s', z', bs, evs'. split; [exact E'|exact Hc].
Qed.
