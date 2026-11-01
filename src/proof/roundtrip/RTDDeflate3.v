(* RT-D part DEFLATE over interface v3 (RTDV3.v): deflate() keeps the round-trip invariant Krt3 and
   ends in dfinal.  [rtd_deflate_okg] for [Krtd] (RTDDgDefs.v: KF2 with kcore3, and while the header is not complete
   the bytes produced are a prefix of a header of khdr), equivalent to Krt3 by [KFd_KF3].  The Iapi half by the
   deflate laws' api_deflate (RTDDfXDeflate: aout <= 2097152), the KF half stage by stage (RTDDgEntry, RTDDgHdr,
   RTDDgComp, RTDDgTrail), along the same stage decomposition as api_deflate. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDDgDefs.
Require Import Zlib.proof.roundtrip.RTDDgEntry Zlib.proof.roundtrip.RTDDgHdr Zlib.proof.roundtrip.RTDDgComp Zlib.proof.roundtrip.RTDDgTrail.
Require Import Zlib.proof.roundtrip.RTDLTApiInit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(* the end of a call that does not return Z_STREAM_END: Iapi by api_deflate, KFd from KMid *)
Lemma df_fin : forall dict wrap D O inb aout tin tout flush s' z' code,
  call_ok inb aout tin tout z' -> code <> Z_STREAM_END ->
  (let used := Zlength inb - z_avail_in z' in
   Iapi W3 hinv dict wrap (D ++ sublist 0 used inb) (O ++ z_out z')
     (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
     s' (z_total_in z') (z_total_out z') (z_adler z')) ->
  KMid dict wrap D O inb s' z' ->
  let used := Zlength inb - z_avail_in z' in
  Krtd dict wrap (D ++ sublist 0 used inb) (O ++ z_out z')
    (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
    s' (z_total_in z') (z_total_out z') (z_adler z').
Proof.
  intros dict wrap D O inb aout tin tout flush s' z' code Hc _ HI HK. cbv zeta in *.
  split; [exact HI|].
  destruct Hc as (_ & _ & Hn & _). unfold KMid in HK. rewrite <- Hn.
  eapply KFd_args. exact HK.
Qed.

Theorem rtd_deflate_okg : Zlib.proof.huffman.Overlay.overlay_statement -> writer_fspec -> stored_block_fspec ->
  align_fspec -> fpend_fspec2 ->
  comp_fspec3 0 c_deflate_stored -> comp_fspec3 1 c_deflate_fast -> comp_fspec3 2 c_deflate_slow ->
  comp_fspec3 3 c_deflate_huff -> comp_fspec3 4 c_deflate_rle -> kf_deflate_stmt Krtd.
Proof.
  intros Hov Hwr Hsb Hal Hfp H0 H1 H2 H3 H4.
  pose proof (compf_of H0 H1 H2 H3 H4) as Hcf.
  pose proof (W3_facts Hov) as CF. pose proof hinv_facts as HF.
  intros dict wrap D O fin s tin tout adler inb aout flush msg s' z' code [HIa HKF] Hfl Hb Hd Ha Ho Hfin Hrun
    _ _ _ _ _.
  change (rzcall inb 0 (Zlength inb) tin aout tout adler msg) with (zcall inb 0 (Zlength inb) tin aout tout adler msg)
    in Hrun.
  change (rbytes inb) with (bytes inb) in Hb.
  (* the Iapi half *)
  destruct (RTDDfXDeflate.api_deflate W3 hinv dict wrap D O fin s tin tout adler inb aout flush msg CF HF HIa Hfl Hb
              Hd Ha Ho Hfin) as (s'' & z'' & code'' & E & _ & Hcall & Hcode & _ & _ & Post).
  rewrite Hrun in E. injection E as <- <- <-.
  (* the KF half, stage by stage *)
  pose proof (RTDDfXDeflate.mid_start W3 hinv dict wrap D O fin s tin tout adler inb aout flush msg HIa Hb Hd Ha Ho Hfin)
    as M0.
  set (z0 := zcall inb 0 (Zlength inb) tin aout tout adler msg) in *.
  assert (K0 : KMid dict wrap D O inb s z0).
  { unfold KMid. subst z0. cbn [z_next_in z_out]. rewrite sublist_nil, !app_nil_r. eapply KFd_args. exact HKF. }
  assert (Hend : forall s4 z4,
    d_w_bits s4 = d_w_bits s -> KMid dict wrap D O inb s4 z4 -> s4 = s' -> z4 = z' -> code <> Z_STREAM_END ->
    d_w_bits s' = d_w_bits s /\
    (let used := Zlength inb - z_avail_in z' in
     let D' := D ++ sublist 0 used inb in
     let O' := O ++ z_out z' in
     if code =? Z_STREAM_END then dfinal dict wrap (d_w_bits s) (d_gzhead s) D' O'
     else Krtd dict wrap D' O' (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
            s' (z_total_in z') (z_total_out z') (z_adler z'))).
  { intros s4 z4 Hw K4 -> -> Hne. split; [exact Hw|]. cbv zeta.
    destruct (Z.eqb_spec code Z_STREAM_END) as [Ee|_]; [contradiction|].
    exact (df_fin dict wrap D O inb aout tin tout flush s' z' code Hcall Hne Post K4). }
  clear Post.
  rewrite c_deflate_stages in Hrun.
  rewrite (Iapi_bad_state W3 hinv dict wrap D O fin s tin tout adler HF HIa) in Hrun.
  replace (flush >? Z_BLOCK) with false in Hrun by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; unfold Z_BLOCK; lia).
  replace (flush <? 0) with false in Hrun by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in Hrun.
  destruct (RTDDfXEntry.entry_ok W3 hinv dict wrap D O inb aout tin tout flush s z0 CF HF M0 eq_refl eq_refl eq_refl
              (proj2 Ha) Hfl) as (s1 & z1 & o1 & E1 & G1 & M1 & P1).
  destruct (kf_entry_ok Hfp dict wrap D O inb aout tin tout flush s z0 s1 z1 o1 M0 K0 E1) as [W1 K1].
  rewrite E1 in Hrun. destruct o1 as [c|].
  { cbn [then_stage bind] in Hrun. injection Hrun as <- <- <-.
    apply (Hend s1 z1 W1 K1 eq_refl eq_refl).
    destruct P1 as [->|(->&_)]; discriminate. }
  cbn [then_stage bind] in Hrun. destruct P1 as (Q1 & Q2 & Q3 & Q4 & Q5).
  destruct (RTDDfXHdrSt.hdr_stage_ok W3 hinv dict wrap D O inb aout tin tout flush s1 z1 CF HF M1 Q1 Q2 Hfl Q3
              (proj2 Ha) Q5) as (s2 & z2 & r2 & E2 & G2 & M2 & N2 & P2).
  destruct (kf_hdr_ok dict wrap D O inb aout tin tout flush s1 z1 s2 z2 r2 M1 K1 Q1 Q2 Hfl Q3 (proj2 Ha) Q5 E2)
    as [W2 K2].
  rewrite E2 in Hrun. destruct r2 as [c|].
  { cbn [then_stage bind] in Hrun. injection Hrun as <- <- <-.
    apply (Hend s2 z2 ltac:(congruence) K2 eq_refl eq_refl). rewrite P2. discriminate. }
  cbn [then_stage bind] in Hrun. destruct P2 as (R1 & R2).
  destruct (RTDDfXComp.comp_stage_ok W3 hinv dict wrap D O inb aout tin tout flush s2 z2 CF HF Hb M2 R1 Hfl
              (proj2 Ha) R2) as (s3 & z3 & o3 & E3 & G3 & M3 & P3).
  destruct (kf_comp_ok Hov Hwr Hsb Hal Hfp Hcf dict wrap D O inb aout tin tout flush s2 z2 s3 z3 o3 Hb M2 K2 R1 Hfl
              (proj2 Ha) R2 E3) as [W3' K3].
  rewrite E3 in Hrun. destruct o3 as [c|].
  { cbn [bind] in Hrun. injection Hrun as <- <- <-.
    apply (Hend s3 z3 ltac:(congruence) K3 eq_refl eq_refl). rewrite P3. discriminate. }
  cbn [bind] in Hrun. destruct P3 as (T1 & T2 & T3).
  destruct (kf_trailer_ok Hwr Hfp dict wrap D O inb aout tin tout flush s3 z3 s' z' code M3 K3 T1 Hfl (proj2 Ha)
              T2 T3 Hrun) as (W4 & K4 & F4).
  destruct (RTDDfXTrail.trailer_ok W3 hinv dict wrap D O inb aout tin tout flush s3 z3 CF HF M3 T1 Hfl (proj2 Ha)
              T2 T3) as (s4 & z4 & c4 & E4 & G4 & P4).
  rewrite Hrun in E4. injection E4 as <- <- <-.
  destruct (Z.eqb_spec code Z_STREAM_END) as [Ee|Ne].
  - split; [congruence|]. cbv zeta.
    destruct Hcall as (_ & _ & Hn & _). rewrite <- Hn.
    replace (d_w_bits s) with (d_w_bits s3) by congruence.
    replace (d_gzhead s) with (d_gzhead s3) by congruence.
    exact (F4 Ee).
  - apply (Hend s' z' ltac:(congruence) (K4 Ne) eq_refl eq_refl Ne).
Qed.

Lemma Krtd_Krt3 : forall dict wrap D O fin s tin tout adler,
  Krtd dict wrap D O fin s tin tout adler <-> Krt3 dict wrap D O fin s tin tout adler.
Proof.
  intros. unfold Krtd, Krt3. rewrite KFd_KF3. tauto.
Qed.

Theorem rtd_deflate_ok3 : Zlib.proof.huffman.Overlay.overlay_statement -> writer_fspec -> stored_block_fspec ->
  align_fspec -> fpend_fspec2 ->
  comp_fspec3 0 c_deflate_stored -> comp_fspec3 1 c_deflate_fast -> comp_fspec3 2 c_deflate_slow ->
  comp_fspec3 3 c_deflate_huff -> comp_fspec3 4 c_deflate_rle -> kf_deflate_stmt Krt3.
Proof.
  intros Hov Hwr Hsb Hal Hfp H0 H1 H2 H3 H4.
  pose proof (rtd_deflate_okg Hov Hwr Hsb Hal Hfp H0 H1 H2 H3 H4) as K.
  intros dict wrap D O fin s tin tout adler inb aout flush msg s' z' code HK Hfl Hb Hd Ha Ho Hfin Hrun
    Hgz Hcall Hcode Hend Hbuf.
  apply Krtd_Krt3 in HK.
  destruct (K dict wrap D O fin s tin tout adler inb aout flush msg s' z' code HK Hfl Hb Hd Ha Ho Hfin Hrun
    Hgz Hcall Hcode Hend Hbuf) as [Hw P].
  split; [exact Hw|]. cbv zeta in *. destruct (code =? Z_STREAM_END); [exact P|].
  apply Krtd_Krt3. exact P.
Qed.
