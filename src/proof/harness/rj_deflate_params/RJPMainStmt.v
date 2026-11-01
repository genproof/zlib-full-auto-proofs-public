(* Law rj_deflate_params: the statement of main's proof (RJPMain.v): main of harness/rj_deflate_params.c
   against MainLib.main_core_spec R, at the compspecs of deflate.c + trees.c (DCS.CS; the body moves to the
   law's compspecs by entry_shared), calling deflateInit2_ through its shared specification
   (DSpec9.deflateInit2__spec_v9) and laws_common.h's new_stream through its own (laws_common/Spec.v, at the
   compress unit's compspecs).  The model facts main needs about deflateInit2_ (the return code is
   Z_STREAM_ERROR exactly when params_ok fails, else Z_OK or Z_MEM_ERROR) are LawFacts.af_init of api_facts;
   ob_dstream_to_end gives the stream's memory back at the returns. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.rj_deflate_params.
Require Import Zlib.harness.rj_deflate_params.code.
Local Open Scope logic.

(* main's callees *)
Definition Gmain : funspecs :=
  [deflateInit2__spec_v9; new_stream_spec; nondet_u32_spec; gp_assert_spec].

Definition vlit : ident := ___stringlit_rj_deflate_params_1.

(* the globals main gets (RJPGlobals.globals_rjp) *)
Definition R (gv : globals) : mpred := deflate_globals gv * version_at gv vlit.

Definition rjp_main_stmt : Prop :=
  (exists I Iend, api_facts I Iend) -> ob_dstream_to_end ->
  @semax_body (QPvarspecs Zlib.contracts.rj_deflate_params.whole_prog) Gmain DCS.CS f_main
    (_main, main_core_spec R).
