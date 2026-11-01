(* Law rt_stream (harness/rt_stream.c, data of any length): the interface between main's body proof and the
   assembly (UAsm.v).

   - [Rm gv] (MainStmt.v): main's resources out of the program's global variables, unchanged.
   - [Gmain_u]: the functions main calls, with THE specifications the law's G has for them (one per function):
     MainStmt.Gmain, laws_common.h's clip(), which the harness calls to cut its pieces, and copy_of(), which makes
     the copy of the data that the output is compared with, and the helpers of laws_session.h main calls:
     deflate_params_ok() (with gp_assume, the parameters in zlib.h's ranges), position_of() and unmoved() (a
     call offered no output space, or no input and no output space, moves nothing).
   - [urts_main_stmt]: main's body against main_core_spec Rm, for ANY invariants with the facts of UDFacts.v
     and UIFacts.v.
   The globals are MainStmt.rts_globals_stmt (proved by Globals.rts_globals). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.deflate.DSpecV.
Require Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.inflate_api.Bodies5.
Require Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Export Zlib.proof.harness.rt_stream.MainStmt.
Require Zlib.proof.harness.rt_stream.UDFacts.
Require Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.harness.rt_stream.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* the functions main calls *)
Definition Gmain_u : funspecs :=
  [deflateInit2__spec_v9; Zlib.proof.deflate.DSpecV.deflate_specV;
   Zlib.proof.inflate_api.Spec5.inflateInit2__spec; Zlib.proof.inflate_api.SpecW.inflate_specW;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; new_stream_spec;
   (_quickproof_malloc, malloc_spec'); nondet_u32_spec; gp_assert_spec;
   gp_assume_spec; Zlib.proof.harness.laws_session.Spec.deflate_params_ok_spec;
   Zlib.proof.harness.laws_session.Spec.position_of_spec; Zlib.proof.harness.laws_session.Spec.unmoved_spec].

(* main's body *)
Definition urts_main_stmt : Prop :=
  forall J P, UDFacts.urts_dfacts J -> UIFacts.urts_ifacts P ->
    semax_body (QPvarspecs p) Gmain_u f_main (_main, main_core_spec Rm).
