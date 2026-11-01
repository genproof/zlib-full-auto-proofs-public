(* RT-D part SLOW: deflate_slow against interface v3 (RTDV3.v: kmatch3 on the history;
   RTDDefs' kmatch is false).  The loop by the safety measure (RTDLTCSlow2.loop_measure) with the
   safety invariant and the functional one (RTDSlowKit.FI); the parts in RTDSlowF<Part>.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSlowKit.
Require Import Zlib.proof.roundtrip.RTDLTCSlow2 Zlib.proof.roundtrip.RTDLTCSlowRefill Zlib.proof.roundtrip.RTDLTCSlowPre Zlib.proof.roundtrip.RTDLTCSlowMatch Zlib.proof.roundtrip.RTDLTCSlowLit Zlib.proof.roundtrip.RTDLTCSlowCand Zlib.proof.roundtrip.RTDLTCSlowEnd Zlib.proof.roundtrip.RTDLTCSlowFbo.
Require Import Zlib.proof.roundtrip.RTDSlowFRefill Zlib.proof.roundtrip.RTDSlowFPre Zlib.proof.roundtrip.RTDSlowFMatch Zlib.proof.roundtrip.RTDSlowFLit Zlib.proof.roundtrip.RTDSlowFCand Zlib.proof.roundtrip.RTDSlowFEnd.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Definition fparts : Prop :=
  frefill_part /\ fpre_part /\ fmatch_part /\ flit_part /\ fcand_part /\ fend_part.

(** One iteration, functionally *)
Lemma fbody_ok dict D BS p s0 z0 flush s z evs r :
  fparts -> sspecs -> fspecs -> FG dict D p s0 ->
  SI s0 z0 flush s z evs -> FI dict D BS p s0 z0 s z ->
  dsl_body flush (s, z) = Some r -> fstep_ok dict D BS p s0 z0 r.
Proof.
  intros (Pr & Pp & Pm & Pl & Pc & Pe) Hs Hf HG HI HF E.
  pose proof Hs as (Hfill & Hins & Hlm & Htally & Hfbo & Hfp).
  unfold dsl_body in E.
  destruct (refill_ok Hfill s0 z0 flush s z evs HI) as (r1 & Er & Hr). rewrite Er in E.
  pose proof (Pr dict D BS p s0 z0 flush s z evs r1 Hs Hf HI HG HF Er) as Hfr.
  destruct r1 as [[s' z']|e]; cbn [bind] in E.
  2: { injection E as <-. exact Hfr. }
  destruct Hr as (HI' & Hrdy & _). cbn [fstep_ok] in Hfr.
  rewrite dsl_step_eq in E.
  destruct (pre_ok Hins Hlm s0 z0 flush s' z' evs HI' Hrdy) as (s1 & E1 & Hmid). rewrite E1 in E. cbn [bind] in E.
  assert (Hfm : FMID s' s1).
  { destruct Hfr as (k & x & BS' & syms & _ & Hk & _).
    exact (Pp s0 z0 flush s' z' evs s1 dict _ _ _ Hs Hf HI' Hrdy Hk E1). }
  destruct ((d_prev_length s1 >=? MIN_MATCH) && (d_match_length s1 <=? d_prev_length s1)) eqn:Eb.
  - apply andb_true_iff in Eb as [Eb1 Eb2]. apply Z.geb_le in Eb1. apply Z.leb_le in Eb2.
    exact (Pm dict D BS p s0 z0 flush s' z' evs s1 r Hs Hf HI' Hrdy Hmid Hfm HG Hfr Eb1 Eb2 E).
  - assert (Hn : ~ (MIN_MATCH <= d_prev_length s1 /\ d_match_length s1 <= d_prev_length s1)).
    { intros [N1 N2]. apply Z.geb_le in N1. apply Z.leb_le in N2. rewrite N1, N2 in Eb. discriminate. }
    destruct (Z.eqb_spec (d_match_available s1) 0) as [Ea|Ea]; cbn [negb] in E.
    + exact (Pc dict D BS p s0 z0 flush s' z' evs s1 r Hs Hf HI' Hrdy Hmid Hfm HG Hfr Hn Ea E).
    + exact (Pl dict D BS p s0 z0 flush s' z' evs s1 r Hs Hf HI' Hrdy Hmid Hfm HG Hfr Hn Ea E).
Qed.

Definition fslow_P dict D BS p s0 z0 flush (a : dstate * strm) : Prop :=
  slow_P s0 z0 flush a /\ FI dict D BS p s0 z0 (fst a) (snd a).

Definition fslow_Q dict D BS p s0 z0 flush (b : dexit) : Prop :=
  slow_Q s0 z0 flush b /\
  (let '(s, z, o) := b in
   match o with Some bs => FQ dict D BS p s0 z0 s z bs | None => FI dict D BS p s0 z0 s z end).

Lemma fslow_body_ok dict D BS p s0 z0 flush :
  fparts -> sspecs -> fspecs -> FG dict D p s0 ->
  forall a, fslow_P dict D BS p s0 z0 flush a ->
  0 <= msr (fst a) (snd a) /\ exists r, dsl_body flush a = Some r /\
    match r with
    | inl a' => fslow_P dict D BS p s0 z0 flush a' /\ msr (fst a') (snd a') < msr (fst a) (snd a)
    | inr b => fslow_Q dict D BS p s0 z0 flush b
    end.
Proof.
  intros Hp Hs Hf HG [s z] [HP HF].
  pose proof Hs as (Hfill & Hins & Hlm & Htally & Hfbo & Hfp).
  destruct (slow_body_ok Hfill Hins Hlm Htally Hfbo s0 z0 flush (s, z) HP) as (Hm & r & E & Hr).
  split; [exact Hm|]. exists r. split; [exact E|].
  destruct HP as [evs HI]. cbn [fst snd] in *.
  pose proof (fbody_ok dict D BS p s0 z0 flush s z evs r Hp Hs Hf HG HI HF E) as Hfr.
  destruct r as [[s' z']|[[s' z'] [bs|]]]; cbn [fstep_ok] in Hfr.
  - destruct Hr as [Hr1 Hr2]. split; [split; [exact Hr1|exact Hfr]|exact Hr2].
  - split; [exact Hr|exact Hfr].
  - split; [exact Hr|exact Hfr].
Qed.

Theorem slow3_assembly : fparts -> sspecs -> fspecs -> comp_fspec3 2 c_deflate_slow.
Proof.
  intros Hp Hs Hf s z flush s' z' bs dict D BS syms p HW3 Ho Hq Hfl Hz Hw Ha Hfn Hd HD Hk Hp0 Hal E.
  pose proof Hs as (Hfill & Hins & Hlm & Htally & Hfbo & Hfp).
  assert (Hpre : compress_pre2 s z flush).
  { destruct HW3 as [HW2 _]. split; [exact HW2|]. split; [exact Ho|]. split; [exact Hq|].
    split; [exact Hfl|]. split; [exact Hz|]. split; [exact Hw|]. apply adler_pre_ok. exact Ha. }
  assert (HG : FG dict D p s) by (split; [exact Hd|split; [exact HD|split; [exact Hp0|exact Hal]]]).
  pose proof (SI_init s z flush Hpre Hfn) as HI.
  pose proof (FI_init dict D BS p s z flush syms Hpre Hk) as HF.
  destruct (loop_measure (dsl_body flush) (fslow_P dict D BS p s z flush) (fslow_Q dict D BS p s z flush)
              (fun a => msr (fst a) (snd a))
              (fslow_body_ok dict D BS p s z flush Hp Hs Hf HG) (s, z)
              (conj (ex_intro _ [] HI) HF)
              (proj2 (SI_msr _ _ _ _ _ _ HI))) as ([[s1 z1] o] & El & HQ & HQf).
  rewrite c_deflate_slow_eq, El in E. cbn [bind] in E.
  assert (HFQ : FQ dict D BS p s z s' z' bs).
  { destruct o as [bs1|].
    - injection E as <- <- <-. exact HQf.
    - cbn [slow_Q] in HQ. destruct HQ as (evs & HI1 & H1 & H2 & H3 & H4).
      destruct Hp as (_ & _ & _ & _ & _ & Pe).
      exact (Pe dict D BS p s z flush s1 z1 evs s' z' bs Hs Hf HI1 H1 H2 H3 H4 HG HQf E). }
  exact HFQ.
Qed.

Theorem fparts_ok : fparts.
Proof.
  exact (conj frefill_ok (conj fpre_ok (conj fmatch_ok (conj flit_ok (conj fcand_ok fend_ok))))).
Qed.

Theorem rtd_slow_ok3 : Zlib.proof.huffman.Overlay.overlay_statement -> fill_fspec -> ins_fspec2 -> lm_fspec ->
  fpend_fspec2 -> fbo_fspec -> comp_fspec3 2 c_deflate_slow.
Proof.
  intros Hov H1 H2 H3 H4 H5.
  exact (slow3_assembly fparts_ok (sspecs_ok Hov) (conj H1 (conj H2 (conj H3 (conj H4 H5))))).
Qed.
