(* The laws rt_partial, rj_truncated, rj_bad_checksum and rfc_trailing_bytes: the resources of each program's
   global variables that its main needs, [R_of lit gv]: deflate's (DSpec.deflate_globals: trees.c's tables,
   z_errmsg, configuration_table, my_version, crc32.c's crc_table at Ers), the harness's ZLIB_VERSION literal
   "1.3.2" at the global [lit] (the version argument of deflateInit2 and of inflateInit2), inflate's read-only
   tables (Rep.tables_rep) and inflate.c's own ZLIB_VERSION literal (Spec5.version_lit).  As for
   deflate_roundtrip (roundtrip/RTRMainSpec.Rm, RTRGlobals.v), whose program links the same units.
   crc_table_at Ers is inside deflate_globals: main lends it to inflate() and takes it back.
   [clip_globals_stmt]: R out of globvars2pred for the four programs (proved in GlobalsOk.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.GlobalsFixed Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.inflate.Rep Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Zlib.harness.rt_partial.code Zlib.harness.rj_truncated.code Zlib.harness.rj_bad_checksum.code.
Require Zlib.harness.rfc_trailing_bytes.code.
Local Open Scope logic.

Definition R_of (lit : ident) (gv : globals) : mpred :=
  deflate_globals gv * Zlib.proof.deflate.GlobalsInit.version_at gv lit *
  Zlib.proof.inflate.Rep.tables_rep Ers gv * Zlib.proof.inflate_api.Spec5.version_lit gv.

Definition lit_rp : ident := Zlib.harness.rt_partial.code.___stringlit_rt_partial_1.
Definition lit_rt : ident := Zlib.harness.rj_truncated.code.___stringlit_rj_truncated_1.
Definition lit_bc : ident := Zlib.harness.rj_bad_checksum.code.___stringlit_rj_bad_checksum_1.
Definition lit_tb : ident := Zlib.harness.rfc_trailing_bytes.code.___stringlit_rfc_trailing_bytes_1.

Definition R_rp := R_of lit_rp.
Definition R_rt := R_of lit_rt.
Definition R_bc := R_of lit_bc.
Definition R_tb := R_of lit_tb.

(* [gv] as main gets it (offset 0 at every global; configuration_table's functions at a pointer or undefined,
   as GlobalsInit.globals_of) *)
Definition globals_of (p : QP.program Clight.function) (lit : ident) : Prop :=
  forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  (forall f, In f Zlib.proof.deflate.GlobalsFixed.cfg_funs -> gv f = Vundef \/ isptr (gv f)) ->
  globvars2pred gv (QPprog_vars p) |-- R_of lit gv * TT.

Definition clip_globals_stmt : Prop :=
  globals_of p_rp lit_rp /\ globals_of p_rt lit_rt /\ globals_of p_bc lit_bc /\ globals_of p_tb lit_tb.
