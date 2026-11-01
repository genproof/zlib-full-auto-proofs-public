(* The round trips without the limits of deflate_roundtrip: each call of deflate keeps K7 (RTK7Defs.v) or ends
   in dfinal, for calls of up to 2^32 - 1 bytes of input and of output space, from the wide core and header facts
   and the wide functional specifications of the compression functions.

   As RTDDeflate3.rtd_deflate_okg, stage by stage (c_deflate_stages): the safety half with Mid7 (RTK7DEntry,
   RTK7DHdrSt, RTK7DComp, RTK7DTrail), the functional half with KMid (RTK7DgEntry, RTK7DgHdr, RTK7DgComp,
   RTK7DgTrail).  Two ways lead to Stuck7: a call that starts in Stuck7 returns from its entry stage
   (RTK7DStuck.stuck_entry), and a compression stage that meets the defect of deflate_stored (stuck7) goes through
   the trailer stage without leaving FINISH_STATE (RTK7DStuck.stuck_trailer); in both the input is not all
   consumed, so the call does not return Z_STREAM_END. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTK7Defs.
Require Import Zlib.proof.roundtrip.RTK7DMid.
Require Import Zlib.proof.roundtrip.RTK7DEntry Zlib.proof.roundtrip.RTK7DHdrSt Zlib.proof.roundtrip.RTK7DComp
  Zlib.proof.roundtrip.RTK7DTrail.
Require Import Zlib.proof.roundtrip.RTK7DgEntry Zlib.proof.roundtrip.RTK7DgHdr Zlib.proof.roundtrip.RTK7DgComp
  Zlib.proof.roundtrip.RTK7DgTrail.
Require Import Zlib.proof.roundtrip.RTK7DStoredW Zlib.proof.roundtrip.RTK7DStuck.
Require Import Zlib.proof.roundtrip.RTDWriter.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem rtk7_deflate_ok : Zlib.proof.huffman.Overlay.overlay_statement -> core_facts7 W3 -> hdr_facts7 hinv7 -> fpend_fspec7 -> comp_fspec7 0 c_deflate_stored -> comp_fspec7 1 c_deflate_fast -> comp_fspec7 2 c_deflate_slow -> comp_fspec7 3 c_deflate_huff -> comp_fspec7 4 c_deflate_rle -> kf7_deflate_stmt K7.
Proof.
  intros Hov CF HF Hfp H0 H1 H2 H3 H4.
  pose proof (compf7_of H0 H1 H2 H3 H4) as Hcf.
  destruct rtd_writer_ok as (Hwr & Hsb & Hal).
  intros dict wrap D O fin s tin tout adler inb aout flush msg s' z' code HK Hfl Hb Hl Hd Ha Ho Hfin Hrun
    _ Hcall Hcode Hend _.
  change (rzcall inb 0 (Zlength inb) tin aout tout adler msg) with (zcall inb 0 (Zlength inb) tin aout tout adler msg)
    in Hrun.
  change (rbytes inb) with (bytes inb) in Hb.
  set (z0 := zcall inb 0 (Zlength inb) tin aout tout adler msg) in *.
  destruct Hcall as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  (* the end of a call left in FINISH_STATE with input *)
  assert (Send : d_w_bits s' = d_w_bits s -> d_status s' = FINISH_STATE -> flush = Z_FINISH ->
                 0 < z_avail_in z' ->
    d_w_bits s' = d_w_bits s /\
    (let used := Zlength inb - z_avail_in z' in
     let D' := D ++ sublist 0 used inb in
     let O' := O ++ z_out z' in
     if code =? Z_STREAM_END then dfinal dict wrap (d_w_bits s) (d_gzhead s) D' O'
     else K7 dict wrap D' O' (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
            s' (z_total_in z') (z_total_out z') (z_adler z'))).
  { intros Hw Hs Hf Hai. split; [exact Hw|]. cbv zeta.
    destruct (Z.eqb_spec code Z_STREAM_END) as [Ee|_]; [specialize (Hend Ee); lia|].
    right. split; [exact Hs|]. rewrite Hf. cbn [Z.eqb Pos.eqb Z_FINISH].
    eexists. split; [reflexivity|]. intros E.
    assert (Hz : Zlength (sublist (Zlength inb - z_avail_in z') (Zlength inb) inb) = 0) by (rewrite E; reflexivity).
    rewrite Zlength_sublist in Hz by lia. lia. }
  rewrite c_deflate_stages in Hrun.
  replace (flush >? Z_BLOCK) with false in Hrun by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; unfold Z_BLOCK; lia).
  replace (flush <? 0) with false in Hrun by (symmetry; apply Z.ltb_ge; lia).
  rewrite !orb_false_r in Hrun.
  destruct HK as [[HIa HKF] | (Hst & R & HR & Hne)].
  2:{ (* a call from Stuck7 returns from its entry stage *)
    destruct (Hfin R HR) as [Hf ->].
    destruct (bad_state s).
    { injection Hrun as _ _ <-. exfalso. unfold Z_OK, Z_STREAM_END, Z_BUF_ERROR, Z_STREAM_ERROR in Hcode. lia. }
    assert (Hai0 : 0 < z_avail_in z0).
    { subst z0. cbn. destruct R; [congruence|]. rewrite Zlength_cons. pose proof (Zlength_nonneg R). lia. }
    destruct (c_deflate_entry s z0 flush) as [[[s1 z1] o1]|] eqn:E1; [|discriminate].
    rewrite Hf in E1.
    destruct (stuck_entry s z0 s1 z1 o1 Hst Hai0 E1) as (Ho1 & Hw1 & Hs1 & Ha1).
    destruct o1 as [c|]; [|congruence].
    cbn [then_stage bind] in Hrun. injection Hrun as <- <- <-.
    apply Send; auto. lia. }
  (* the end of a call in Mid7 that does not return Z_STREAM_END *)
  assert (Mend : forall s4 z4,
    d_w_bits s4 = d_w_bits s -> Mid7 W3 hinv7 dict wrap D O inb aout tin tout flush s4 z4 ->
    KMid dict wrap D O inb s4 z4 -> s4 = s' -> z4 = z' -> code <> Z_STREAM_END ->
    d_w_bits s' = d_w_bits s /\
    (let used := Zlength inb - z_avail_in z' in
     let D' := D ++ sublist 0 used inb in
     let O' := O ++ z_out z' in
     if code =? Z_STREAM_END then dfinal dict wrap (d_w_bits s) (d_gzhead s) D' O'
     else K7 dict wrap D' O' (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
            s' (z_total_in z') (z_total_out z') (z_adler z'))).
  { intros s4 z4 Hw M4 K4 -> -> Hne. split; [exact Hw|]. cbv zeta.
    destruct (Z.eqb_spec code Z_STREAM_END) as [Ee|_]; [contradiction|].
    replace (Zlength inb - z_avail_in z') with (z_next_in z') by lia.
    left. split.
    - destruct M4 as (_ & _ & _ & _ & _ & I4). exact I4.
    - apply KFd_KF3. unfold KMid in K4. eapply KFd_args. exact K4. }
  pose proof (mid7_start W3 hinv7 dict wrap D O fin s tin tout adler inb aout flush msg HIa Hb Hl Hd Ha Ho Hfin)
    as M0.
  fold z0 in M0.
  assert (K0 : KMid dict wrap D O inb s z0).
  { unfold KMid. subst z0. cbn [z_next_in z_out]. rewrite sublist_nil, !app_nil_r.
    apply KFd_KF3 in HKF. eapply KFd_args. exact HKF. }
  rewrite (Iapi7_bad_state W3 hinv7 dict wrap D O fin s tin tout adler HF HIa) in Hrun.
  (* entry *)
  destruct (c_deflate_entry s z0 flush) as [[[s1 z1] o1]|] eqn:E1; [|discriminate].
  destruct (entry_ok7 W3 hinv7 dict wrap D O inb aout tin tout flush s z0 s1 z1 o1 CF HF M0 eq_refl eq_refl
              eq_refl Hfl E1) as (G1 & M1 & P1).
  destruct (kf_entry_ok7 CF HF Hfp dict wrap D O inb aout tin tout flush s z0 s1 z1 o1 M0 K0 E1) as [W1 K1].
  destruct o1 as [c|].
  { cbn [then_stage bind] in Hrun. injection Hrun as <- <- <-.
    apply (Mend s1 z1 W1 M1 K1 eq_refl eq_refl).
    destruct P1 as [->|(->&_)]; discriminate. }
  cbn [then_stage bind] in Hrun. destruct P1 as (Q1 & Q2 & Q3 & Q4 & Q5).
  (* the header *)
  destruct (hdr_stages s1 z1) as [[[s2 z2] r2]|] eqn:E2; [|discriminate].
  destruct (hdr_stage_ok7 W3 hinv7 dict wrap D O inb aout tin tout flush s1 z1 s2 z2 r2 CF HF M1 Q1 Q2 Hfl Q3 Q5
              E2) as (G2 & M2 & N2 & P2).
  destruct (kf_hdr_ok7 CF HF dict wrap D O inb aout tin tout flush s1 z1 s2 z2 r2 M1 K1 Q1 Q2 Hfl Q3 Q5 E2) as [W2 K2].
  destruct r2 as [c|].
  { cbn [then_stage bind] in Hrun. injection Hrun as <- <- <-.
    apply (Mend s2 z2 ltac:(congruence) M2 K2 eq_refl eq_refl). rewrite P2. discriminate. }
  cbn [then_stage bind] in Hrun. destruct P2 as (R1 & R2).
  (* the compression *)
  destruct (c_deflate_compress s2 z2 flush) as [[[s3 z3] o3]|] eqn:E3; [|discriminate].
  cbn [bind] in Hrun.
  destruct (comp_stage_ok7 W3 hinv7 dict wrap D O inb aout tin tout flush s2 z2 s3 z3 o3 CF HF stored_wbits Hb M2
              R1 Hfl R2 E3) as [(G3 & M3 & P3) | (Eo3 & W3s & St3)].
  2:{ (* deflate_stored met its defect: the trailer stage keeps FINISH_STATE *)
    subst o3. destruct St3 as (Hf3 & Hs3 & Ha3).
    destruct (stuck_trailer s3 z3 flush s' z' code Hs3 Hrun) as (Wt & St & At).
    apply Send; auto; [congruence|lia]. }
  destruct (kf_comp_ok7 Hov CF HF Hwr Hsb Hal Hfp Hcf dict wrap D O inb aout tin tout flush s2 z2 s3 z3 o3 Hb M2 K2 R1 Hfl
              R2 E3) as [[W3' K3] | St3].
  2:{ exfalso. exact (mid7_not_stuck _ _ _ _ _ _ _ _ _ _ _ _ _ M3 St3). }
  destruct o3 as [c|].
  { injection Hrun as <- <- <-.
    apply (Mend s3 z3 ltac:(congruence) M3 K3 eq_refl eq_refl). rewrite P3. discriminate. }
  destruct P3 as (T1 & T2 & T3).
  (* the trailer *)
  destruct (kf_trailer_ok7 CF HF Hwr Hfp dict wrap D O inb aout tin tout flush s3 z3 s' z' code M3 K3 T1 Hfl T2 T3 Hrun)
    as (W4 & K4 & F4).
  destruct (trailer_ok7 W3 hinv7 dict wrap D O inb aout tin tout flush s3 z3 s' z' code CF HF M3 T1 Hfl T2 T3 Hrun)
    as (G4 & P4).
  destruct (Z.eqb_spec code Z_STREAM_END) as [Ee|Ne].
  - split; [congruence|]. cbv zeta.
    replace (Zlength inb - z_avail_in z') with (z_next_in z') by lia.
    replace (d_w_bits s) with (d_w_bits s3) by congruence.
    replace (d_gzhead s) with (d_gzhead s3) by congruence.
    exact (F4 Ee).
  - destruct P4 as [(_ & M4) | E4]; [|contradiction].
    apply (Mend s' z' ltac:(congruence) M4 (K4 Ne) eq_refl eq_refl Ne).
Qed.
