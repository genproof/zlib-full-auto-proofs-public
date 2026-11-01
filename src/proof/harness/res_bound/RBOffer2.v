(* Law res_bound, main: offer's postcondition back to deflate_spec's api_fields (used by RBRun.part_run). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LawFactsW Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.harness.bound_common.BoundKit Zlib.proof.harness.deflate_bound.MainKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.res_bound.RBCS Zlib.proof.harness.res_bound.RBString Zlib.proof.harness.res_bound.RBKit.
Require Import Zlib.proof.harness.res_bound.RBOffer1.
Require Import Zlib.harness.res_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.


(* offer's postcondition as deflate_spec's api_fields, the six fields and the padding *)
Lemma rr_offer_post (p inp : val) (ai : Z) (outp : val) (ao tin tout adler : Z) (msgv sp : val) (gv : globals)
    (s : dstate) (za zf : val) :
  za = gv deflate.code._zcalloc -> zf = gv deflate.code._zcfree -> u32_ok ai -> u64_ok tin -> u32_ok ao -> u64_ok tout -> u64_ok adler ->
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val inp (vi ai) (vl tin) outp (vi ao) (vl tout) msgv sp za zf nullval
       (vi (tr_data_type (fst (d_trm s)))) (vl adler) Vundef) p
  |-- api_fields p inp ai tin outp ao tout msgv adler * rr_own p sp gv s * BoundKit.strm_pad p.
Proof.
  intros -> -> **. rewrite rr_strm_cs. unfold api_fields, rr_own, BoundKit.strm_pad. unfold_data_at (data_at _ _ _ p).
  unfold field_at_; simpl. entailer!.
Qed.
