(* Law api_reset: the statements of its main and of its globals.  The main (ARMain*.v) is proved against
   MainLib.main_core_spec R_ar for ANY invariants J0, J1 with ar_facts J0 J1 (ARFacts.v), calling inflate.c's
   API through its shared specifications (inflateInit2_: Spec5.v; inflate: the wide SpecW.v; inflateReset: the
   view ARSpec.inflateReset_specA; at the inflate unit's compspecs, moved to the law's with ARLawCS's
   instances) and the helpers of harness/laws_common.h through theirs (laws_common/Spec.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Export Zlib.proof.harness.api_reset.ARSpec.
Require Export Zlib.proof.harness.api_reset.ARFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Export Zlib.proof.harness.api_reset.ARLawCS.
Require Export Zlib.proof.harness.inflate_pieces.Globals.
Require Export Zlib.proof.harness.inflate_reset.IRGlobals.
Require Zlib.harness.api_reset.code.

(* the specifications main calls *)
Definition Gmain : funspecs :=
  [inflateInit2__spec; inflate_specW; inflateReset_specA; zcalloc_i; zcfree_i;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec;
   (_quickproof_malloc, @malloc_spec' CS); (_quickproof_free, @free_spec' CS);
   nondet_u32_spec; nondet_u8_spec; gp_assert_spec].

(* the resources of the program's globals that main needs: inflate's and crc32's tables, inflate.c's version
   literal, the harness's "1.3.2" (inflate_pieces/Globals.v's R_of), and the first byte of each of inflate's
   and inffast's message literals (main compares used.msg with fresh.msg, which needs valid pointers:
   inflate_reset/IRGlobals.v's ir_msg_lits) *)
Definition R_ar (gv: globals) : mpred :=
  (@R_of CS Zlib.harness.api_reset.code.___stringlit_api_reset_1 gv * ir_msg_lits gv)%logic.

Definition ar_main_stmt : Prop :=
  forall J0 J1, ar_facts J0 J1 ->
  @semax_body (QPvarspecs p) Gmain CS Zlib.harness.api_reset.code.f_main
    (Zlib.harness.api_reset.code._main, main_core_spec R_ar).

Definition ar_globals_stmt : Prop :=
  forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
    globvars2pred gv (QPprog_vars p) |-- R_ar gv * TT.
