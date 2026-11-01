(* Law res_free_deflate: harness_safe of its program from main's body (MainStmt.v) and the shared bodies
   (res_alloc_deflate/AsmLib.v), with the program's globals (Globals.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.deflate.MainCoreCfg Zlib.proof.deflate.GlobalsFixed.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.res_alloc_deflate.ACS Zlib.proof.harness.res_alloc_deflate.Gmain
               Zlib.proof.harness.res_alloc_deflate.AsmLib.
Require Import Zlib.proof.harness.res_free_deflate.MainStmt Zlib.proof.harness.res_free_deflate.Globals.
Require Zlib.contracts.res_free_deflate.
Require Import Zlib.harness.res_free_deflate.code.

Definition p := Zlib.contracts.res_free_deflate.whole_prog.

Definition G : funspecs := (_main, QPmain_spec_ext' p tt main_post_TT) :: G_lib_free.

Theorem law_asm :
  main_free_stmt -> laws_common_ok -> counted_ok -> za_deflate_bodies_stmt -> za_deflate_api_stmt ->
  harness_safe p.
Proof.
  intros HM HL HC HB HA.
  pose proof (semax_body_main_core_cfg _ _ p cfg_funs _main f_main (Ra ___stringlit_res_free_deflate_1)
    globals_free_fixed HM eq_refl) as M.
  harness_safe_by_specs CSa G main_post_TT.
  - reflexivity.
  - asm_entries_free M HL HC HB HA.
Qed.
