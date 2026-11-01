(* Law rt_session (harness/rt_session.c): the interface between main's body proof and the assembly (SAsm.v).

   - [Rm gv]: main's resources out of the program's global variables: deflate's globals (crc32.c's table at Ers
     among them, handed to inflate() as crc_table_at Ers), the harness's ZLIB_VERSION literal (the version
     argument of deflateInit2_ and inflateInit2_), inflate's tables and inflate.c's own ZLIB_VERSION literal.
   - [inflate_spec_ses]: inflate()'s specification in this law: the intersection of the two shared ones,
     SpecW.inflate_specW (no gz_header attached: the sessions without a header) and RTH9Spec.inflate_spec9
     (a gz_header attached, its fields written over several calls: the sessions with a header).  A caller uses
     one of them ([Gmain_W] and [Gmain_9] have it in place of the intersection; SMain.delta_ses_sub moves a
     proof in their context to main's).  The body is the two shared bodies (SAsmI.v,
     semax_body_binaryintersection).
   - [Gmain]: the functions main calls, with THE specifications the law's G has for them (one per function):
     deflateInit2_ (DSpec9 v9), deflateSetDictionary and deflateSetHeader (DSpec), deflate (DSpecV: a byte at
     next_out witnesses its validity when no output space is offered at the start of the output object),
     inflateInit2_ (Spec5), inflate (above), inflateGetHeader (RTH8Spec v8: any field values and buffer bytes),
     inflateSetDictionary (SpecW: a raw stream's strm->adler may be undefined), zcalloc / zcfree at Inflate.CS,
     the laws_common.h helpers (laws_common/Spec.v), the harness's any_string and same_field (as in
     rt_gzip_header: G2MainDefs), laws_session.h's deflate_params_ok, position_of, unmoved and accounted
     (laws_session/Spec.v) and the environment.
   - [ses_main_stmt]: main's body against main_core_spec Rm, for ANY invariants with the facts of SDFacts.v and
     SIFacts.v.
   - [ses_globals_stmt]: Rm out of globvars2pred. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9 Zlib.proof.deflate.DSpecV.
Require Zlib.proof.deflate.GlobalsInit Zlib.proof.deflate.GlobalsFixed.
Require Zlib.proof.inflate.Rep Zlib.proof.inflate_api.Spec5 Zlib.proof.inflate_api.Bodies5.
Require Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.roundtrip.RTH8Spec Zlib.proof.roundtrip.RTH9Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Zlib.proof.harness.rt_session.SDFacts.
Require Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* main's resources *)
Definition Rm (gv : globals) : mpred :=
  Zlib.proof.deflate.DSpec.deflate_globals gv *
  Zlib.proof.deflate.GlobalsInit.version_at gv ___stringlit_rt_session_1 *
  Zlib.proof.inflate.Rep.tables_rep Ers gv * Zlib.proof.inflate_api.Spec5.version_lit gv.

(* inflate(): both shared specifications *)
Definition inflate_fs_ses : funspec :=
  ltac:(let x := eval hnf in (snd Zlib.proof.inflate_api.SpecW.inflate_specW) in
        let y := eval hnf in (snd Zlib.proof.roundtrip.RTH9Spec.inflate_spec9) in
        exact (binary_intersection' x y eq_refl eq_refl)).
Definition inflate_spec_ses : ident * funspec := (_inflate, inflate_fs_ses).

Lemma inflate_ses_sub :
  funspec_sub inflate_fs_ses (snd Zlib.proof.inflate_api.SpecW.inflate_specW) /\
  funspec_sub inflate_fs_ses (snd Zlib.proof.roundtrip.RTH9Spec.inflate_spec9).
Proof. apply binary_intersection'_sub. Qed.

(* the functions main calls; [inf] is inflate()'s *)
Definition Gmain_of (inf : ident * funspec) : funspecs :=
  [Zlib.proof.deflate.DSpec9.deflateInit2__spec_v9; Zlib.proof.deflate.DSpecV.deflate_specV;
   Zlib.proof.deflate.DSpec.deflateSetDictionary_spec; Zlib.proof.deflate.DSpec.deflateSetHeader_spec;
   Zlib.proof.inflate_api.Spec5.inflateInit2__spec; inf;
   Zlib.proof.roundtrip.RTH8Spec.inflateGetHeader_spec8; Zlib.proof.inflate_api.SpecW.inflateSetDictionary_specW;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; new_stream_spec;
   Zlib.proof.harness.rt_gzip_header.G2MainDefs.any_string_spec;
   Zlib.proof.harness.rt_gzip_header.G2MainDefs.same_field_spec;
   (_quickproof_malloc, malloc_spec'); nondet_u8_spec; nondet_u32_spec; gp_assert_spec; gp_assume_spec;
   Zlib.proof.harness.laws_session.Spec.deflate_params_ok_spec;
   Zlib.proof.harness.laws_session.Spec.position_of_spec; Zlib.proof.harness.laws_session.Spec.unmoved_spec;
   Zlib.proof.harness.laws_session.Spec.accounted_spec].

Definition Gmain : funspecs := Gmain_of inflate_spec_ses.
Definition Gmain_W : funspecs := Gmain_of Zlib.proof.inflate_api.SpecW.inflate_specW.
Definition Gmain_9 : funspecs := Gmain_of Zlib.proof.roundtrip.RTH9Spec.inflate_spec9.

(* main's body *)
Definition ses_main_stmt : Prop :=
  forall J P PN, SDFacts.ses_dfacts J -> SIFacts.ses_ifacts (fun _ => True) P PN ->
    semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec Rm).

(* the globals *)
Definition ses_globals_stmt : Prop :=
  forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  (forall f, In f Zlib.proof.deflate.GlobalsFixed.cfg_funs -> gv f = Vundef \/ isptr (gv f)) ->
  globvars2pred gv (QPprog_vars p) |-- Rm gv * TT.
