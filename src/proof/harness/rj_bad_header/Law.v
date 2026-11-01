(* The law rj_bad_header (harness/rj_bad_header.c): a zlib header that breaks RFC 1950 2.2 is refused with
   Z_DATA_ERROR before any output. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.rj_bad_header.
(* inflate.c's bodies: the allocator-generic port of inflate's proofs at zlib's default allocator (src/proof/za/:
   the switch cases, inflate_fast, inflate()'s body, the API functions, their one-specification-per-function form,
   the wide machine invariant) and the bridge to the wide specifications of SpecW.v *)
Require Import Zlib.proof.inflate_api.SpecWLib.
Require Zlib.proof.inflate_api.SpecWBridge.
Require Import Zlib.proof.za.inflate_api.ULib.
Require Import Zlib.proof.za.inflate.CasesAllZ.
Require Import Zlib.proof.za.inffast.FastZ.
Require Import Zlib.proof.za.inflate_api.BodyZ.
Require Import Zlib.proof.za.inflate_api.ApiZ.
Require Import Zlib.proof.za.inflate.StepZ.
Require Import Zlib.proof.inflate.StepW.
(* the law's theory, main and assembly *)
Require Zlib.proof.harness.rj_bad_header.RBHLawAsm Zlib.proof.harness.rj_bad_header.RBHMain.

Lemma rj_bad_header_ok : laws_common_ok ->
  harness_safe Zlib.contracts.rj_bad_header.whole_prog.
Proof.
  intros H. apply Zlib.proof.harness.rj_bad_header.RBHLawAsm.rbh_core.
  - split.
    + destruct (za_ulib _ zc_alloc) as [_ Hlib]. apply Hlib.
      * exact za_cases_proof.
      * exact za_body_inflate_proof.
      * exact (za_step_proof stepf2_mwf3W).
      * exact za_fast_proof.
      * exact za_api_proof.
    + exact Zlib.proof.inflate_api.SpecWBridge.specw_bridge.
  - exact H.
  - exact Zlib.proof.harness.rj_bad_header.RBHMain.body_main.
Qed.
