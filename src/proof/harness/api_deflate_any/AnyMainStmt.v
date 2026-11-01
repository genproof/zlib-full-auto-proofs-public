(* Law api_deflate_any: the statement of main's proof (AnyMain.v): main of harness/api_deflate_any.c against
   MainLib.main_core_spec R, at the law's compspecs (AnyCS.CS: main's local struct position is not a composite
   of deflate.c; the body's statements are proved at DCS.CS and lifted by VST's semax_cssub), calling deflateInit2_, deflateParams and deflate through their shared
   specifications (DSpec9.deflateInit2__spec_v9, DSpec.deflateParams_spec, DSpec.deflate_spec, with the identity
   as the compressor choice [ef], DSpec.ef_ok_id), laws_common.h's helpers through theirs (laws_common/Spec.v) and
   laws_session.h's deflate_params_ok, position_of and unmoved through theirs (laws_session/Spec.v).
   The model facts main needs are [any_facts J] (AnyFacts.v) for some [J]. *)
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
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.api_deflate_any.AnyFacts.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Zlib.contracts.api_deflate_any.
Require Import Zlib.harness.api_deflate_any.code.
Local Open Scope logic.

(* main's callees: laws_session.h's helpers and gp_assume first, then the library and laws_common.h's helpers *)
Definition Gmain : funspecs :=
  [Zlib.proof.harness.laws_session.Spec.deflate_params_ok_spec; gp_assume_spec;
   Zlib.proof.harness.laws_session.Spec.position_of_spec; Zlib.proof.harness.laws_session.Spec.unmoved_spec;
   deflateInit2__spec_v9; deflateParams_spec; deflate_spec;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec;
   (_quickproof_malloc, @malloc_spec' DCS.CS); (_quickproof_free, @free_spec' DCS.CS);
   nondet_u32_spec; nondet_u8_spec; gp_assert_spec].

Definition vlit : ident := ___stringlit_api_deflate_any_1.

(* the globals main gets (AnyGlobals.globals_any) *)
Definition R (gv : globals) : mpred := deflate_globals gv * version_at gv vlit.

Definition any_main_stmt : Prop :=
  any_theory_stmt ->
  @semax_body (QPvarspecs Zlib.contracts.api_deflate_any.whole_prog) Gmain AnyCS.CS f_main
    (_main, main_core_spec R).
