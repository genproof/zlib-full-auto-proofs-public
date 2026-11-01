(* Law res_memory_deflate: the statement of main's body proof (Main.v), in the context of its callees
   (res_alloc_deflate/Gmain.v) at the law's compspecs. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.res_alloc_deflate.ACS Zlib.proof.harness.res_alloc_deflate.Gmain.
Require Zlib.contracts.res_memory_deflate.
Require Import Zlib.harness.res_memory_deflate.code.

Definition main_memory_stmt : Prop :=
  @semax_body (QPvarspecs Zlib.contracts.res_memory_deflate.whole_prog) Gmain_mem CSa f_main
    (_main, main_core_spec (Ra ___stringlit_res_memory_deflate_1)).
