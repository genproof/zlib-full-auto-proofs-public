(* Law deflate_roundtrip: the interface between main's body proof, the globals of the program
   and the assembly (RTRSLaw.v).

   - [Rm gv]: main's resources out of the program's global variables (what main_core_spec gives besides mem_mgr):
     the deflate side's (DSpec.deflate_globals: trees.c's tables, z_errmsg, configuration_table, my_version and
     crc32.c's crc_table at Ers; the harness's ZLIB_VERSION literal, the version argument of both deflateInit2 and
     inflateInit2) and the inflate side's (inflate's fixed tables and inftrees' tables (Rep.tables_rep), inflate.c's
     own ZLIB_VERSION literal (Spec5.version_lit)).  crc_table_at Ers is inside deflate_globals: main hands it to
     inflate() (crc_table_at tsh with tsh := Ers) and takes it back.
   - [Gmain I Iend]: the functions main calls, with THE specifications the law's G has for them (one per
     function): deflate_run (RTRRunSpec), deflateEnd (DSpec), stream_defaults / exact_copy (the deflate
     harness helpers, deflate/HarnessLib.v: main converts the z_stream t to the inflate specs' fields at
     Inflate.CS), inflateInit2_ / inflateGetHeader / inflateSetDictionary / inflate / inflateEnd (Spec5),
     ref_adler32, bytes_same, malloc, gp_assert, and zcalloc / zcfree at Inflate.CS (make_func_ptr gives
     Callees.zfuncs for inflateInit2_; the law's G has them at its own compspecs, a subspecification).
   - [rt_main_stmt]: main's body against main_core_spec Rm.
   - [rt_globals_stmt]: Rm out of globvars2pred (as GlobalsInit.globals_of, with GlobalsFixed.cfg_funs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations Zlib.proof.deflate.GlobalsFixed.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.inflate.Rep Zlib.proof.inflate_api.Spec5 Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.roundtrip.RTXFacts Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec.
Require Import Zlib.harness.x_deflate_roundtrip.code.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

(* main's resources *)
Definition Rm (gv : globals) : mpred :=
  deflate_globals gv * version_at gv vlit * Zlib.proof.inflate.Rep.tables_rep Ers gv *
  Zlib.proof.inflate_api.Spec5.version_lit gv.

(* the functions main calls *)
Definition Gmain (I : api_inv) (Iend : dstate -> Prop) : funspecs :=
  [deflate_run_spec I Iend; deflateEnd_spec; stream_defaults_spec; exact_copy_spec;
   Zlib.proof.inflate_api.Spec5.inflateInit2__spec; Zlib.proof.inflate_api.Spec5.inflateGetHeader_spec;
   Zlib.proof.inflate_api.Spec5.inflateSetDictionary_spec; Zlib.proof.inflate_api.Spec5.inflate_spec;
   Zlib.proof.inflate_api.Spec5.inflateEnd_spec;
   ref_adler32_spec; bytes_same_spec;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   (_quickproof_malloc, malloc_spec'); gp_assert_spec].

(* main's body, for ANY invariants with the facts of the deflate laws and of the round trip *)
Definition rt_main_stmt : Prop :=
  forall (I : api_inv) (Iend : dstate -> Prop),
    api_facts I Iend -> rt_extra I -> ifacts -> Zlib.proof.deflate.Obligations.ob_dstream_to_end ->
    semax_body (QPvarspecs p) (Gmain I Iend) f_main (_main, main_core_spec Rm).

(* the globals *)
Definition rt_globals_stmt : Prop :=
  forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  (forall f, In f Zlib.proof.deflate.GlobalsFixed.cfg_funs -> gv f = Vundef \/ isptr (gv f)) ->
  globvars2pred gv (QPprog_vars p) |-- Rm gv * TT.
