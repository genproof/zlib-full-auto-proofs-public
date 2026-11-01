(* Law api_deterministic (data of any length): the statement of main's proof (DetMain2.v): main of
   harness/api_deterministic.c against MainLib.main_core_spec R, at the compspecs of deflate.c + trees.c (DCS.CS;
   the body moves to the law's compspecs by entry_shared), calling deflateInit2_, deflateParams and deflate
   through their shared specifications (DSpec9.deflateInit2__spec_v9, DSpec.deflateParams_spec,
   DSpec.deflate_spec; for deflate and deflateParams the compressor choice [ef] is the identity, DSpec.ef_ok_id,
   so the model runs are DModel4's c_deflate / c_deflateParams: DModel5.c_deflate_g_id, c_deflateParams_g_id) and
   laws_common.h's helpers through theirs (laws_common/Spec.v, clip() included), laws_session.h's
   deflate_params_ok through laws_session/Spec.v.  The model facts main needs are
   [det_facts2 J] (DetFacts2.v) for any [J]: the two streams have the same state and the same fields after every
   pair of calls, every call is defined. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.DetFacts2.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Zlib.contracts.api_deterministic.
Require Import Zlib.harness.api_deterministic.code.
Local Open Scope logic.

(* main's callees: laws_session.h's deflate_params_ok and gp_assume (the parameters in zlib.h's ranges), then
   the library and laws_common.h's helpers *)
Definition Gmain : funspecs :=
  [Zlib.proof.harness.laws_session.Spec.deflate_params_ok_spec; gp_assume_spec; deflateInit2__spec_v9; deflateParams_spec; deflate_spec;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec;
   (_quickproof_malloc, @malloc_spec' DCS.CS); (_quickproof_free, @free_spec' DCS.CS);
   nondet_u32_spec; nondet_u8_spec; gp_assert_spec].

Definition vlit : ident := ___stringlit_api_deterministic_1.

(* the globals main gets (DetGlobals2.globals_det) *)
Definition R (gv : globals) : mpred := deflate_globals gv * version_at gv vlit.

Definition det_main2_stmt : Prop :=
  det_theory2_stmt ->
  @semax_body (QPvarspecs Zlib.contracts.api_deterministic.whole_prog) Gmain DCS.CS f_main
    (_main, main_core_spec R).
