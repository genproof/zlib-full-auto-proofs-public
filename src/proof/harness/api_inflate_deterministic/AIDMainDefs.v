(* Law api_inflate_deterministic: the statements of its main and of its globals.  The main (AIDMain*.v) is
   proved against MainLib.main_core_spec R_aid for ANY invariant J with aid_facts J (AIDFacts.v), calling
   inflate.c's API through its shared specifications (inflateInit2_: Spec5.v; inflate: the wide SpecW.v; at the
   inflate unit's compspecs, moved to the law's with AIDLawCS's instances), the helpers of harness/laws_common.h
   through theirs (laws_common/Spec.v) and laws_session.h's inflate_window_ok through laws_session/Spec.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Export Zlib.proof.inflate_api.SpecW.
Require Export Zlib.proof.harness.api_inflate_deterministic.AIDFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Export Zlib.proof.harness.api_inflate_deterministic.AIDLawCS.
Require Export Zlib.proof.harness.inflate_pieces.Globals.
Require Export Zlib.proof.harness.inflate_reset.IRGlobals.
Require Zlib.harness.api_inflate_deterministic.code.

(* the specifications main calls: laws_session.h's inflate_window_ok and gp_assume (windowBits in zlib.h's
   ranges), then the library and laws_common.h's helpers *)
Definition Gmain : funspecs :=
  [Zlib.proof.harness.laws_session.Spec.inflate_window_ok_spec; gp_assume_spec;
   inflateInit2__spec; inflate_specW; zcalloc_i; zcfree_i;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec;
   (_quickproof_malloc, @malloc_spec' CS); (_quickproof_free, @free_spec' CS);
   nondet_u32_spec; nondet_u8_spec; gp_assert_spec].

(* the resources of the program's globals that main needs: inflate's and crc32's tables, inflate.c's version
   literal, the harness's "1.3.2" (inflate_pieces/Globals.v's R_of), and the first byte of each of inflate's
   and inffast's message literals (main compares first.msg with second.msg, which needs valid pointers:
   inflate_reset/IRGlobals.v's ir_msg_lits) *)
Definition R_aid (gv: globals) : mpred :=
  (@R_of CS Zlib.harness.api_inflate_deterministic.code.___stringlit_api_inflate_deterministic_1 gv *
   ir_msg_lits gv)%logic.

Definition aid_main_stmt : Prop :=
  forall J, aid_facts J ->
  @semax_body (QPvarspecs p) Gmain CS Zlib.harness.api_inflate_deterministic.code.f_main
    (Zlib.harness.api_inflate_deterministic.code._main, main_core_spec R_aid).

Definition aid_globals_stmt : Prop :=
  forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
    globvars2pred gv (QPprog_vars p) |-- R_aid gv * TT.
