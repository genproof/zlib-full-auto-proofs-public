(* Law api_short_output (data of any length): the entries of WAsmKit.G_top, from main's body
   (WMainDefs.body_main_w_stmt with the model facts it takes), the helpers of laws_common.h (laws_common_ok;
   bytes_eq against BytesEqNull.bytes_eq_spec_n: BytesEqNullBody.bytes_eq_n_body), compress.c's compressBound(_z)
   (Obligations9.deflate_bodies_ok9) and compress2(_z) for any sizes (RTCBodiesW.rtc_w_bodies), deflate.c's
   deflateInit_ (RTCBWrap.rtcb_deflateInit_) and uncompr.c's uncompress2(_z) for any sizes
   (USpecW.uncompr_bodies_w_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.deflate.Obligations Zlib.proof.deflate.Obligations9.
Require Zlib.proof.roundtrip.RTCSpec Zlib.proof.roundtrip.RTCSpecW.
Require Zlib.proof.roundtrip.RTCBodiesW Zlib.proof.roundtrip.RTCBWrap.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_common.BytesEqNullBody.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.roundtrip.RTC2W Zlib.proof.roundtrip.RTC2WFinal Zlib.proof.uncompr.UTheoryW.
Require Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.harness.api_short_output.WLawCS.
Require Import Zlib.proof.harness.api_short_output.WMainDefs.
Require Import Zlib.proof.harness.api_short_output.WAsmKit.
#[local] Existing Instance Zlib.proof.harness.api_short_output.WLawCS.CS.

Lemma w_entries_top :
  laws_common_ok -> Zlib.proof.inflate_api.SpecWLib.specw_bridge_stmt -> deflate_bodies_ok9 ->
  body_main_w_stmt -> uncompr_bodies_w_stmt -> c2w_bound_stmt -> c2w_final_stmt -> uw_theory_stmt ->
  w_entries G_top.
Proof.
  intros LC BR DB BM HU CB CF UT.
  pose proof (main_entry BM CB CF UT) as M.
  pose proof (Zlib.proof.harness.laws_common.BytesEqNullBody.bytes_eq_n_body LC) as B_eq.
  destruct LC as (B_upto & _ & B_any & B_copy & _).
  destruct Zlib.proof.roundtrip.RTCBodiesW.rtc_w_bodies as (C_c2z & C_c2).
  pose proof Zlib.proof.roundtrip.RTCBWrap.rtcb_deflateInit_ as D_init.
  destruct (HU NullExtension.Espec) as (U_u2z & U_u2).
  destruct DB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  _ & _ & D_cbz & D_cb & _).
  unfold ob_compressBound_z, ob_compressBound, Zlib.proof.roundtrip.RTCSpec.ob_deflateInit_,
    Zlib.proof.roundtrip.RTCSpecW.ob_compress2_z_w, Zlib.proof.roundtrip.RTCSpecW.ob_compress2_w in *.
  unfold w_entries, G_top.
  w_entry M BR.
  w_entry B_upto BR. w_entry B_any BR. w_entry B_copy BR. w_entry B_eq BR.
  w_entry D_cbz BR. w_entry D_cb BR. w_entry C_c2z BR. w_entry C_c2 BR. w_entry D_init BR.
  w_entry U_u2z BR. w_entry U_u2 BR.
  apply Forall_nil.
Qed.
