(* The laws res_free_inflate and res_memory_inflate (harness/res_free_inflate.c, harness/res_memory_inflate.c,
   their first comments): inflate.c with the harness's counting allocator (src/proof/harness/counted/). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Zlib.contracts.res_free_inflate Zlib.contracts.res_memory_inflate.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Zlib.proof.harness.laws_session.Bodies.
(* the parts: the laws from inflate.c's bodies (LawsFrom), the bodies of laws_session.h's helpers
   (laws_session/Bodies.v), the bodies of the allocator-generic port of inflate's proofs (src/proof/za/: the
   switch cases, inflate_fast, inflate()'s body, the API functions, their one-specification-per-function form),
   the wide machine invariant (StepW, StepZ) and the model fact of res_memory_inflate (Model) *)
Require Import Zlib.proof.harness.res_inflate.LawsFrom.
Require Import Zlib.proof.harness.res_inflate.Model.
Require Import Zlib.proof.za.inflate_api.ULib.
Require Import Zlib.proof.za.inflate.CasesAllZ.
Require Import Zlib.proof.za.inffast.FastZ.
Require Import Zlib.proof.za.inflate_api.BodyZ.
Require Import Zlib.proof.za.inflate_api.ApiZ.
Require Import Zlib.proof.za.inflate.StepZ.
Require Import Zlib.proof.inflate.StepW.

Lemma res_inflate_ok :
  laws_common_ok -> counted_ok ->
  harness_safe Zlib.contracts.res_free_inflate.whole_prog /\ harness_safe Zlib.contracts.res_memory_inflate.whole_prog.
Proof.
  intros LC CO.
  destruct (za_ulib _ Acount) as [Hsub Hlib].
  apply res_inflate_from; auto.
  - exact Zlib.proof.harness.laws_session.Bodies.laws_session_bodies.
  - apply Hlib.
    + exact za_cases_proof.
    + exact za_body_inflate_proof.
    + exact (za_step_proof stepf2_mwf3W).
    + exact za_fast_proof.
    + exact za_api_proof.
  - exact res_model.
Qed.
