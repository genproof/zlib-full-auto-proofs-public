(* The law res_free_deflate (harness/res_free_deflate.c, its first comment): main's proof and the assembly of the law from the
   shared specifications: laws_common.h's helpers, the counting allocator (src/proof/harness/counted/), and
   deflate.c with a caller-supplied allocator (src/proof/za/deflate/). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Zlib.contracts.res_free_deflate.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.za.deflate.Stmt.
Require Zlib.proof.harness.res_free_deflate.LawAsm Zlib.proof.harness.res_free_deflate.Main.

Lemma res_free_deflate_ok :
  laws_common_ok -> counted_ok -> za_deflate_bodies_stmt -> za_deflate_api_stmt -> za_dstream_end_stmt ->
  za_deflate_model_stmt -> harness_safe Zlib.contracts.res_free_deflate.whole_prog.
Proof.
  intros L C B A E M.
  exact (Zlib.proof.harness.res_free_deflate.LawAsm.law_asm
           (Zlib.proof.harness.res_free_deflate.Main.body_main M E B) L C B A).
Qed.
