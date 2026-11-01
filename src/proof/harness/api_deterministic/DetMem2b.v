(* Law api_deterministic (data of any length): offer's postcondition as the pieces of a stream (DetKit2.v).
   (In a file of its own: unfolding the z_stream at DCS.CS is slow.) *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.ApiKit.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.
Module DC := Zlib.deflate.code.
Require Import Zlib.proof.harness.api_deterministic.DetMem2.

(* offer's postcondition as deflate_spec's api_fields, the six fields and the padding *)
Lemma det_offer_post (p inp : val) (ai : Z) (outp : val) (ao tin tout adler : Z) (msgv sp za zf op dt : val) :
  u32_ok ai -> u64_ok tin -> u32_ok ao -> u64_ok tout -> u64_ok adler ->
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val inp (vi ai) (vl tin) outp (vi ao) (vl tout) msgv sp za zf op dt (vl adler) Vundef) p
  |-- api_fields p inp ai tin outp ao tout msgv adler * strm_own p sp za zf op dt * BoundKit.strm_pad p.
Proof.
  intros. rewrite det_strm_cs. unfold api_fields, strm_own, BoundKit.strm_pad. unfold_data_at (data_at _ _ _ p).
  unfold field_at_; simpl. entailer!.
Qed.
