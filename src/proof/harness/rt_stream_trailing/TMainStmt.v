(* Law rt_stream_trailing (harness/rt_stream_trailing.c): the interface between main's body proof and the assembly
   (TAsm.v).

   The program's composites are rt_stream's (the same z_stream_s, position and library structs), so the law is
   proved at rt_stream's compspecs LawCS.CS (TAsm checks that they are the program's).
   - [Rm_t gv]: main's resources out of the program's global variables: rt_stream's (MainStmt.Rm) with this
     harness's ZLIB_VERSION literal.
   - [Gmain_t]: the functions main calls, with THE specifications the law's G has for them (one per function):
     rt_stream's UMainStmt.Gmain_u and laws_session.h's accounted() (each call moves next_in and next_out exactly
     as far as it lowers avail_in and avail_out).
   - [trl_main_stmt]: main's body against main_core_spec Rm_t, for ANY invariants with the facts of rt_stream's
     UDFacts.v (the deflate loop is rt_stream's) and TIFacts.v (inflate fed the stream followed by any bytes).
   - [trl_globals_stmt]: Rm_t out of globvars2pred. *)
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
Require Zlib.proof.deflate.GlobalsFixed.
Require Zlib.proof.inflate.Rep.
Require Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.inflate_api.Bodies5.
Require Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Zlib.proof.harness.rt_stream.UDFacts.
Require Zlib.proof.harness.rt_stream_trailing.TIFacts.
Require Zlib.contracts.rt_stream_trailing.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

Definition p_t := Zlib.contracts.rt_stream_trailing.whole_prog.

(* the harness's ZLIB_VERSION literal *)
Definition hversion_at_t (gv : globals) : mpred :=
  data_at Ers (tarray tschar 6) (map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0])
    (gv ___stringlit_rt_stream_trailing_1).

(* main's resources *)
Definition Rm_t (gv : globals) : mpred :=
  deflate_globals gv * Zlib.proof.inflate.Rep.tables_rep Ers gv * Zlib.proof.inflate_api.Spec5.version_lit gv *
  hversion_at_t gv.

(* the functions main calls *)
Definition Gmain_t : funspecs :=
  [deflateInit2__spec_v9; Zlib.proof.deflate.DSpecV.deflate_specV;
   Zlib.proof.inflate_api.Spec5.inflateInit2__spec; Zlib.proof.inflate_api.SpecW.inflate_specW;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; new_stream_spec;
   (_quickproof_malloc, malloc_spec'); nondet_u32_spec; gp_assert_spec;
   gp_assume_spec; Zlib.proof.harness.laws_session.Spec.deflate_params_ok_spec;
   Zlib.proof.harness.laws_session.Spec.position_of_spec; Zlib.proof.harness.laws_session.Spec.unmoved_spec;
   Zlib.proof.harness.laws_session.Spec.accounted_spec].

(* main's body *)
Definition trl_main_stmt : Prop :=
  forall J P, Zlib.proof.harness.rt_stream.UDFacts.urts_dfacts J ->
    Zlib.proof.harness.rt_stream_trailing.TIFacts.trl_ifacts P ->
    semax_body (QPvarspecs p_t) Gmain_t f_main (_main, main_core_spec Rm_t).

(* the globals *)
Definition trl_globals_stmt : Prop :=
  forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  (forall f, In f Zlib.proof.deflate.GlobalsFixed.cfg_funs -> gv f = Vundef \/ isptr (gv f)) ->
  globvars2pred gv (QPprog_vars p_t) |-- Rm_t gv * TT.
