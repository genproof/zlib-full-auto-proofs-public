(* Law rt_stream (harness/rt_stream.c), round 1's bounded harness (UMainStmt.v builds on this file
   for the harness of any length): the interface between main's body proof, the globals of the program and the
   assembly (round 1's Law.v).

   - [Rm gv]: main's resources out of the program's global variables (what main_core_spec gives besides
     mem_mgr): the deflate side's (DSpec.deflate_globals: trees.c's tables, z_errmsg, configuration_table,
     my_version and crc32.c's crc_table at Ers), the inflate side's (inflate's fixed tables and inftrees'
     tables, Rep.tables_rep; inflate.c's own ZLIB_VERSION literal, Spec5.version_lit) and the harness's
     ZLIB_VERSION literal "1.3.2", the version argument of both deflateInit2_ and inflateInit2_.  crc_table_at
     Ers is inside deflate_globals: main hands it to inflate() (crc_table_at tsh with tsh := Ers) and takes it
     back.
   - [Gmain]: the functions main calls, with THE specifications the law's G has for them (one per function):
     deflateInit2_ (DSpec9, v9: it reads none of new_stream's undefined fields), deflate (DSpecV: DSpec's
     deflate_spec with one more witness of next_out's weak validity, a byte at next_out; main's first call may
     offer 0 bytes at the start of the compressed buffer), inflateInit2_
     (Spec5: on the raw fields of new_stream), inflate (SpecW: strm->adler is left undefined by new_stream and
     inflateInit2_ on a raw stream), zcalloc / zcfree at Inflate.CS (make_func_ptr gives the zfuncs of both
     units; the law's G has them at its own compspecs, a subspecification), the laws_common.h helpers
     (laws_common/Spec.v), malloc, nondet_u32, gp_assert.
   - [rts_main_stmt]: main's body against main_core_spec Rm, for ANY invariants with the facts of DFacts.v and
     IFacts.v.
   - [rts_globals_stmt]: Rm out of globvars2pred (as RTRMainSpec.rt_globals_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Zlib.proof.deflate.DSpecV.
Require Zlib.proof.deflate.GlobalsFixed.
Require Zlib.proof.inflate.Rep Zlib.proof.inflate_api.Spec5 Zlib.proof.inflate_api.Bodies5.
Require Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Zlib.proof.harness.rt_stream.DFacts Zlib.proof.harness.rt_stream.IFacts.
Require Import Zlib.harness.rt_stream.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* the harness's ZLIB_VERSION literal *)
Definition hversion_at (gv : globals) : mpred :=
  data_at Ers (tarray tschar 6) (map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0])
    (gv ___stringlit_rt_stream_1).

(* main's resources *)
Definition Rm (gv : globals) : mpred :=
  deflate_globals gv * Zlib.proof.inflate.Rep.tables_rep Ers gv * Zlib.proof.inflate_api.Spec5.version_lit gv *
  hversion_at gv.

(* the functions main calls *)
Definition Gmain : funspecs :=
  [deflateInit2__spec_v9; Zlib.proof.deflate.DSpecV.deflate_specV;
   Zlib.proof.inflate_api.Spec5.inflateInit2__spec; Zlib.proof.inflate_api.SpecW.inflate_specW;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   upto_spec; any_bytes_spec; bytes_eq_spec; new_stream_spec;
   (_quickproof_malloc, malloc_spec'); nondet_u32_spec; gp_assert_spec].

(* main's body *)
Definition rts_main_stmt : Prop :=
  forall J P, DFacts.rts_dfacts J -> IFacts.rts_ifacts P ->
    semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec Rm).

(* the globals *)
Definition rts_globals_stmt : Prop :=
  forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  (forall f, In f Zlib.proof.deflate.GlobalsFixed.cfg_funs -> gv f = Vundef \/ isptr (gv f)) ->
  globvars2pred gv (QPprog_vars p) |-- Rm gv * TT.
