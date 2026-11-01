(* Law deflate_roundtrip, gzip header: the pure facts of the inflate() call with the gzip header
   (RTRSKit.gz_first_ok) from RTHIfDefs.ifacts6: if6_gzpass (the call passes the header: hd6_ok), if_gzhead (the
   data and the header's fields), if6_gzend (h_xp/h_np/h_cp and the mode past the header), at the run's
   dfinal (wrap 2, so no dictionary) with deflateSetHeader's header hdr_of (rhdr_ok from rs_ok). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec Zlib.proof.roundtrip.RTRRunKit Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRMainSpec.
Require Import Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.proof.roundtrip.RTHSpec Zlib.proof.roundtrip.RTHIfDefs.
Require Import Zlib.harness.x_deflate_roundtrip.code.
Require Import Zlib.proof.roundtrip.RTRMKit Zlib.proof.roundtrip.RTRSKit.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma rmh_land1 x : Z.land x 1 = 0 \/ Z.land x 1 = 1.
Proof.
  assert (E : Z.land x 1 = x mod 2) by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
  rewrite E. pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
Qed.

Lemma rmh_rhdr rs : rs_ok rs -> RF.rhdr_ok (hdr_of rs).
Proof.
  intros RS.
  destruct RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hmt & _ & _ & _ & Htx & Hos & Hhc & _ & _ & Hxl & Hnl & Hcl &
                  _ & _ & Hbx & Hbn & Hbc & _).
  unfold RF.rhdr_ok, hdr_of; cbn.
  split; [apply rmh_land1 | ]. split; [apply rmh_land1 | ].
  unfold u32r in Hmt.
  split; [lia | ]. split; [lia | ]. split; [pose proof (Zlength_nonneg (rs_xf rs)); lia | ].
  split; [intros x E; injection E as <-; split; [reflexivity | exact Hbx] | ].
  split; intros l E; injection E as <-; eexists; (split; [reflexivity | split; assumption]).
Qed.

Lemma rmh_first_facts Iend vR rf : ifacts6 -> rf_ok Iend vR rf -> rf_hset rf = 1 ->
  forall sp vih xb nb cb, gz_first_ok rf (rm_hL rf sp vih xb nb cb).
Proof.
  intros IF OK H1 sp vih xb nb cb.
  destruct OK as (RS & _ & _ & _ & NF & OL & DS & HS & DF & WB & HW).
  assert (W2 : rf_wrap rf = 2) by auto.
  assert (HG : d_gzhead (rf_s rf) = Some (hdr_of (rf_rs rf))).
  { destruct HS as [(_ & _ & G) | (E & _)]; [exact G | lia]. }
  rewrite HG, W2 in DF.
  assert (Hd : rf_dict rf = []) by (destruct DF as (_ & _ & _ & _ & ? & _); assumption).
  rewrite Hd in DF. fold (rm_D rf) in DF.
  assert (HD : Zlength (rm_D rf) <= 1048576).
  { unfold rm_D. rewrite Zlength_sublist by lia. unfold rs_ok in RS. lia. }
  unfold COMP_MAX in OL.
  pose proof (rmh_rhdr _ RS) as RH.
  assert (Lx : Zlength (Zrepeat 0 (Zlength (rm_x rf))) = Zlength (rm_x rf))
    by (rewrite Zlength_Zrepeat by (apply Zlength_nonneg); reflexivity).
  assert (Ln : Zlength (Zrepeat 0 (Zlength (rm_nm rf))) = Zlength (rm_nm rf))
    by (rewrite Zlength_Zrepeat by (apply Zlength_nonneg); reflexivity).
  assert (Lc : Zlength (Zrepeat 0 (Zlength (rm_cm rf))) = Zlength (rm_cm rf))
    by (rewrite Zlength_Zrepeat by (apply Zlength_nonneg); reflexivity).
  intros z Hl Hz. unfold rm_hL in *. split.
  - exact (if6_gzpass IF _ (hdr_of (rf_rs rf)) (rm_x rf) (rm_nm rf) (rm_cm rf) (rm_D rf) (rf_O rf) sp z
             (rm_h0 rf) vih Tsh xb nb cb DF RH eq_refl eq_refl eq_refl HD OL
             eq_refl eq_refl Lx eq_refl eq_refl Ln eq_refl eq_refl Lc Hl Hz).
  - intros res Hr.
    destruct (if_gzhead (if6_base IF) _ (hdr_of (rf_rs rf)) (rm_x rf) (rm_nm rf) (rm_cm rf) (rm_D rf) (rf_O rf) sp z
                res (rm_h0 rf) vih Tsh xb nb cb DF RH eq_refl eq_refl eq_refl HD OL
                eq_refl eq_refl Lx eq_refl eq_refl Ln eq_refl eq_refl Lc Hl Hz Hr) as [RD HE].
    split; [exact RD | ]. intros Hend.
    destruct (if6_gzend IF _ (hdr_of (rf_rs rf)) (rm_x rf) (rm_nm rf) (rm_cm rf) (rm_D rf) (rf_O rf) sp z
                res (rm_h0 rf) vih Tsh xb nb cb DF RH eq_refl eq_refl eq_refl HD OL
                eq_refl eq_refl Lx eq_refl eq_refl Ln eq_refl eq_refl Lc Hl Hz Hr Hend) as (X & N & C & M).
    destruct (HE Hend) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
    split; [ | exact M].
    unfold gz_end. repeat split; assumption.
Qed.
