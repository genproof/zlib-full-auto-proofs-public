(** * deflate_api theory: deflate()

    [api_deflate] (the field af_deflate of [api_facts (Iapi W HI) Iend]) from the four stages ([c_deflate_stages]:
    LTApiEntry, LTApiHdrSt, LTApiComp, LTApiTrail), and the facts after Z_STREAM_END ([Iend]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTApiEntry Zlib.proof.roundtrip.RTDLTApiHdrSt Zlib.proof.roundtrip.RTDLTApiComp Zlib.proof.roundtrip.RTDLTApiTrail.
Require Import Zlib.proof.roundtrip.RTDLTApiInit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** What af_deflate says of the result of a call. *)
Definition dfin (W : dstate -> Prop) (HI : hdr_inv) (dict : list Z) (wrap : Z) (D O inb : list Z)
    (aout tin tout flush : Z) (s' : dstate) (z' : strm) (code : Z) : Prop :=
      call_ok inb aout tin tout z' /\
      (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) /\
      (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) /\
      (code = Z_BUF_ERROR -> z_avail_in z' = Zlength inb /\ z_avail_out z' = aout) /\
      (let used := Zlength inb - z_avail_in z' in
       let D' := D ++ sublist 0 used inb in
       let O' := O ++ z_out z' in
       if code =? Z_STREAM_END then Iend s' /\ final_ok dict wrap D' O' (z_adler z')
       else Iapi W HI dict wrap D' O'
              (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
              s' (z_total_in z') (z_total_out z') (z_adler z')).

Lemma mid_start : forall W HI dict wrap D O fin s tin tout adler inb aout flush msg,
  Iapi W HI dict wrap D O fin s tin tout adler -> bytes inb -> Zlength D + Zlength inb <= 1048576 ->
  0 <= aout <= 1048576 -> Zlength O + aout <= 4194304 ->
  (forall R, fin = Some R -> flush = Z_FINISH /\ inb = R) ->
  Mid W HI dict wrap D O inb aout tin tout flush s (zcall inb 0 (Zlength inb) tin aout tout adler msg).
Proof.
  intros W HI dict wrap D O fin s tin tout adler inb aout flush msg HI' Hb Hd Ha Ho Hfin.
  unfold Mid, zrun, zcall; cbn [z_in z_next_in z_avail_in z_total_in z_avail_out z_out z_total_out z_adler].
  split.
  { split; [reflexivity|]. split; [pose proof (Zlength_nonneg inb); lia|]. split; [lia|].
    split; [lia|]. split; [lia|]. split; [rewrite Zlength_nil; lia|]. split; [rewrite Zlength_nil; lia|].
    constructor. }
  split; [lia|]. split; [lia|].
  replace (sublist 0 0 inb) with (@nil Z) by (unfold sublist; reflexivity).
  rewrite !app_nil_r. replace (tin + 0) with tin by lia.
  destruct HI' as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  unfold Iapi. do 12 (split; [assumption|]). split; [|exact A14].
  intros Hst. destruct (Hfin _ (A13 Hst)) as [-> ->]. reflexivity.
Qed.

Lemma mid_post : forall W HI dict wrap D O inb aout tin tout flush s' z' code,
  Mid W HI dict wrap D O inb aout tin tout flush s' z' ->
  (code = Z_OK \/ (code = Z_BUF_ERROR /\ z_next_in z' = 0 /\ z_out z' = [])) ->
  dfin W HI dict wrap D O inb aout tin tout flush s' z' code.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s' z' code (Hz & _ & _ & HI') Hc.
  destruct Hz as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8).
  pose proof (Zlength_nonneg (z_out z')) as Hnn.
  assert (Hu : Zlength inb - z_avail_in z' = z_next_in z') by lia.
  unfold dfin. split.
  { unfold call_ok. split; [exact Z1|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [lia|]. split; [lia|]. exact Z8. }
  split; [destruct Hc as [->|(->&_)]; auto|].
  split; [intros E; destruct Hc as [->|(->&_)]; discriminate|].
  split.
  { intros E. destruct Hc as [->|(_ & H1 & H2)]; [discriminate|].
    rewrite H2, Zlength_nil in Z6. lia. }
  cbv zeta. rewrite Hu. destruct Hc as [->|(->&_)]; exact HI'.
Qed.

Lemma end_post : forall W HI dict wrap D O inb aout tin tout flush s' z',
  zrun inb aout tin tout z' -> Iend s' ->
  final_ok dict wrap (D ++ sublist 0 (z_next_in z') inb) (O ++ z_out z') (z_adler z') ->
  flush = Z_FINISH -> z_avail_in z' = 0 ->
  dfin W HI dict wrap D O inb aout tin tout flush s' z' Z_STREAM_END.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s' z' Hz Hend Hfo Hf Ha.
  destruct Hz as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8).
  pose proof (Zlength_nonneg (z_out z')) as Hnn.
  unfold dfin. split.
  { unfold call_ok. split; [exact Z1|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [lia|]. split; [lia|]. exact Z8. }
  split; [auto|]. split; [auto|]. split; [intros E; discriminate|].
  cbv zeta. replace (Zlength inb - z_avail_in z') with (z_next_in z') by lia. split; assumption.
Qed.

Lemma api_deflate : forall W HI dict wrap D O fin s tin tout adler inb aout flush msg,
    core_facts W -> hdr_facts HI ->
    Iapi W HI dict wrap D O fin s tin tout adler ->
    0 <= flush <= 5 -> bytes inb -> Zlength D + Zlength inb <= 1048576 ->
    0 <= aout <= 1048576 -> Zlength O + aout <= 4194304 ->
    (forall R, fin = Some R -> flush = Z_FINISH /\ inb = R) ->
    exists s' z' code,
      c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\ call_ok inb aout tin tout z' /\
      (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) /\
      (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) /\
      (code = Z_BUF_ERROR -> z_avail_in z' = Zlength inb /\ z_avail_out z' = aout) /\
      (let used := Zlength inb - z_avail_in z' in
       let D' := D ++ sublist 0 used inb in
       let O' := O ++ z_out z' in
       if code =? Z_STREAM_END then Iend s' /\ final_ok dict wrap D' O' (z_adler z')
       else Iapi W HI dict wrap D' O'
              (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
              s' (z_total_in z') (z_total_out z') (z_adler z')).
Proof.
  intros W HI dict wrap D O fin s tin tout adler inb aout flush msg CF HF HI' Hfl Hb Hd Ha Ho Hfin.
  pose proof (mid_start W HI dict wrap D O fin s tin tout adler inb aout flush msg HI' Hb Hd Ha Ho Hfin) as M0.
  set (z0 := zcall inb 0 (Zlength inb) tin aout tout adler msg) in *.
  enough (exists s' z' code, c_deflate s z0 flush = Some (s', z', code) /\ d_gzhead s' = d_gzhead s /\
            dfin W HI dict wrap D O inb aout tin tout flush s' z' code) as (s' & z' & code & E & G & F)
    by (exists s', z', code; split; [exact E|]; split; [exact G|]; exact F).
  rewrite c_deflate_stages.
  rewrite (Iapi_bad_state W HI dict wrap D O fin s tin tout adler HF HI').
  replace (flush >? Z_BLOCK) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; unfold Z_BLOCK; lia).
  replace (flush <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  destruct (entry_ok W HI dict wrap D O inb aout tin tout flush s z0 CF HF M0 eq_refl eq_refl eq_refl
              (proj2 Ha) Hfl) as (s1 & z1 & o1 & E1 & G1 & M1 & P1).
  rewrite E1. destruct o1 as [c|].
  { cbn [then_stage bind]. exists s1, z1, c. split; [reflexivity|]. split; [exact G1|].
    apply mid_post; [exact M1|]. destruct P1 as [->|(->&H1&H2)]; [left; reflexivity|right; auto]. }
  cbn [then_stage bind]. destruct P1 as (Q1 & Q2 & Q3 & Q4 & Q5).
  destruct (hdr_stage_ok W HI dict wrap D O inb aout tin tout flush s1 z1 CF HF M1 Q1 Q2 Hfl Q3 (proj2 Ha) Q5)
    as (s2 & z2 & r2 & E2 & G2 & M2 & N2 & P2).
  rewrite E2. destruct r2 as [c|].
  { cbn [then_stage bind]. exists s2, z2, c. split; [reflexivity|]. split; [congruence|].
    apply mid_post; [exact M2|]. left; exact P2. }
  cbn [then_stage bind]. destruct P2 as (R1 & R2).
  destruct (comp_stage_ok W HI dict wrap D O inb aout tin tout flush s2 z2 CF HF Hb M2 R1 Hfl (proj2 Ha) R2)
    as (s3 & z3 & o3 & E3 & G3 & M3 & P3).
  rewrite E3. destruct o3 as [c|].
  { cbn [bind]. exists s3, z3, c. split; [reflexivity|]. split; [congruence|].
    apply mid_post; [exact M3|]. left; exact P3. }
  cbn [bind]. destruct P3 as (T1 & T2 & T3).
  destruct (trailer_ok W HI dict wrap D O inb aout tin tout flush s3 z3 CF HF M3 T1 Hfl (proj2 Ha) T2 T3)
    as (s4 & z4 & c & E4 & G4 & P4).
  exists s4, z4, c. split; [exact E4|]. split; [congruence|].
  destruct P4 as [(-> & M4) | (-> & Hf & Hz & Zr & Ie & Fo)].
  - apply mid_post; [exact M4|]. left; reflexivity.
  - apply end_post; auto.
Qed.
