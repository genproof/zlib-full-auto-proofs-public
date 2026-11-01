(* The law res_memory_deflate (harness/res_memory_deflate.c, its first comment): main's proof and the assembly of the
   law from the shared specifications: laws_common.h's and laws_session.h's helpers, the counting allocator
   (src/proof/harness/counted/), and deflate.c with a caller-supplied allocator (src/proof/za/deflate/). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Zlib.contracts.res_memory_deflate.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.deflate.AnyCalls.
Require Import Zlib.proof.harness.res_memory_deflate.MainStmt Zlib.proof.harness.res_memory_deflate.Main
               Zlib.proof.harness.res_memory_deflate.LawAsm.

Lemma res_memory_deflate_ok :
  laws_common_ok -> Zlib.proof.harness.laws_session.Spec.laws_session_ok -> counted_ok -> za_deflate_bodies_stmt ->
  za_deflate_api_stmt -> za_dstream_end_stmt -> any_calls_stmt -> harness_safe Zlib.contracts.res_memory_deflate.whole_prog.
Proof.
  intros HL HS HC HB HA _ HM.
  apply law_asm; auto.
  apply body_main; [exact HM | ].
  intros ZA. destruct (HB ZA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TE). exact TE.
Qed.
