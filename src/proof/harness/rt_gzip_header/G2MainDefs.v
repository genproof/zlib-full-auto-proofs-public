(* Law rt_gzip_header on the round-2 harness: the specifications of the harness's own functions, main's context
   and the statements of their bodies (round 1's MainDefs.v for the bounded harness is superseded by this file).

   - [any_string_spec]: any_string(len) gives NULL or a new object of len nonzero bytes and a zero byte;
     [same_field_spec]: same_field(present, got, given, len) is 1 exactly when got is Z_NULL for an absent field,
     and got is not Z_NULL and holds the len bytes at given for a present one.  Both at the compspecs of the
     adler32 unit, as the laws_common.h helpers (laws_common/Spec.v); [rtg2_helpers_stmt]: their bodies (the two
     functions are the same as in round 1's harness).
   - [R gv]: main's resources out of the program's global variables, as deflate_roundtrip's (RTRMainSpec.Rm):
     deflate's globals (crc32.c's table at Ers among them, handed to inflate() as crc_table_at Ers), the harness's
     ZLIB_VERSION literal (the version argument of deflateInit2 and inflateInit2), inflate's tables and inflate.c's
     own ZLIB_VERSION literal.  [rtg2_globals_stmt]: R out of globvars2pred.
   - [Gmain]: the functions main calls with THE specifications the law's G has for them (one per function):
     laws_common.h's upto / clip / any_bytes / copy_of / offer / new_stream, any_string, same_field, deflate.c's
     deflateInit2_ (DSpec9 v9), deflateSetHeader, deflateBound_z (DSpec), deflate (DSpecN: new_stream leaves
     next_in = Z_NULL), inflate.c's inflateInit2_ (Spec5), inflateGetHeader (RTH8Spec v8: any field values and
     buffer bytes, buffers of any uInt size) and inflate (RTH9Spec v9: v8's header, pieces of any uInt size, the
     header over several calls), zcalloc / zcfree at Inflate.CS (Spec5's zfuncs) and the environment.
   - [body_main2_stmt]: main's body for ANY invariants of the deflate loop (G2DFacts) and of the inflate loop
     (G2IFacts). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Zlib.proof.deflate.DSpec9 Zlib.proof.deflate.GlobalsInit Zlib.proof.deflate.GlobalsFixed.
Require Zlib.proof.deflate.DSpecN.
Require Zlib.proof.inflate.Rep Zlib.proof.inflate_api.Spec5 Zlib.proof.inflate_api.Bodies5.
Require Zlib.proof.roundtrip.RTH8Spec Zlib.proof.roundtrip.RTH9Spec.
Require Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.rt_gzip_header.G2DFacts.
Require Zlib.proof.harness.rt_gzip_header.G2IFacts.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.harness.rt_gzip_header.code.
Local Open Scope logic.

Section Helpers.
#[local] Existing Instance Zlib.units.Adler32.CS.

(* any_string(len): a new object of len nonzero bytes followed by a zero byte, or NULL when malloc fails *)
Definition any_string_spec :=
  DECLARE _any_string
  WITH len : Z, gv : globals
  PRE [ tulong ]
    PROP (0 <= len < Ptrofs.max_unsigned)
    PARAMS (Vlong (Int64.repr len)) GLOBALS (gv)
    SEP (mem_mgr gv)
  POST [ tptr tuchar ]
    EX q : val, EX bs : list Z,
    PROP (Zlength bs = len; Forall (fun b => 0 < b <= Byte.max_unsigned) bs)
    RETURN (q)
    SEP (mem_mgr gv;
         if eq_dec q nullval then emp
         else (malloc_token Ews (tarray tuchar (len + 1)) q *
               data_at Ews (tarray tuchar (len + 1)) (bytes_rep (bs ++ [0])) q)).

(* same_field(present, got, given, len): for an absent field (present = 0) got is Z_NULL and the result is 1;
   for a present one the result is 1 exactly when got is not Z_NULL and got[0..len) = given[0..len) *)
Definition same_field_spec :=
  DECLARE _same_field
  WITH present : Z, got : val, given : val, len : Z, shg : share, shv : share, dg : list Z, dv : list Z
  PRE [ tint, tptr tuchar, tptr tuchar, tulong ]
    PROP (Int.min_signed <= present <= Int.max_signed; 0 <= len <= Ptrofs.max_unsigned;
          present = 0 -> got = nullval;
          readable_share shg; readable_share shv; Zlength dg = len; Zlength dv = len; is_bytes dg; is_bytes dv)
    PARAMS (Vint (Int.repr present); got; given; Vlong (Int64.repr len))
    SEP (if present =? 0 then emp
         else (if eq_dec got nullval then emp
               else data_at shg (tarray tuchar len) (bytes_rep dg) got * malloc_token Ews (tarray tuchar len) got) *
              data_at shv (tarray tuchar len) (bytes_rep dv) given)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if present =? 0 then 1
                            else if eq_dec got nullval then 0
                            else if list_eq_dec Z.eq_dec dg dv then 1 else 0)))
    SEP (if present =? 0 then emp
         else (if eq_dec got nullval then emp
               else data_at shg (tarray tuchar len) (bytes_rep dg) got * malloc_token Ews (tarray tuchar len) got) *
              data_at shv (tarray tuchar len) (bytes_rep dv) given).

Definition Gprog_any_string : funspecs :=
  [Zlib.proof.harness.laws_common.Spec.any_bytes_spec; gp_assume_spec].
Definition Gprog_same_field : funspecs := [Zlib.proof.harness.laws_common.Spec.bytes_eq_spec].

End Helpers.

(* the bodies of the harness's own helpers *)
Definition rtg2_helpers_stmt : Prop :=
  @semax_body [] Gprog_any_string Zlib.units.Adler32.CS f_any_string any_string_spec /\
  @semax_body [] Gprog_same_field Zlib.units.Adler32.CS f_same_field same_field_spec.

(* main's resources *)
Definition R (gv : globals) : mpred :=
  Zlib.proof.deflate.DSpec.deflate_globals gv *
  Zlib.proof.deflate.GlobalsInit.version_at gv ___stringlit_rt_gzip_header_1 *
  Zlib.proof.inflate.Rep.tables_rep Ers gv * Zlib.proof.inflate_api.Spec5.version_lit gv.

Definition rtg2_globals_stmt : Prop :=
  forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  (forall f, In f Zlib.proof.deflate.GlobalsFixed.cfg_funs -> gv f = Vundef \/ isptr (gv f)) ->
  globvars2pred gv (QPprog_vars p) |-- R gv * TT.

(* the functions main calls *)
Definition Gmain : funspecs :=
  [Zlib.proof.harness.laws_common.Spec.upto_spec; Zlib.proof.harness.laws_common.Spec.clip_spec;
   Zlib.proof.harness.laws_common.Spec.any_bytes_spec; Zlib.proof.harness.laws_common.Spec.copy_of_spec;
   any_string_spec; same_field_spec;
   Zlib.proof.harness.laws_common.Spec.offer_spec; Zlib.proof.harness.laws_common.Spec.new_stream_spec;
   Zlib.proof.deflate.DSpec9.deflateInit2__spec_v9; Zlib.proof.deflate.DSpec.deflateSetHeader_spec;
   Zlib.proof.deflate.DSpec.deflateBound_z_spec; Zlib.proof.deflate.DSpecN.deflate_specN;
   Zlib.proof.inflate_api.Spec5.inflateInit2__spec; Zlib.proof.roundtrip.RTH8Spec.inflateGetHeader_spec8;
   Zlib.proof.roundtrip.RTH9Spec.inflate_spec9;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   (_quickproof_malloc, malloc_spec'); nondet_u8_spec; nondet_u32_spec; gp_assert_spec].

(* main's body *)
Definition body_main2_stmt : Prop :=
  forall J0 J P, Zlib.proof.harness.rt_gzip_header.G2DFacts.g2_dfacts J0 J ->
  Zlib.proof.harness.rt_gzip_header.G2IFacts.g2_ifacts P ->
  semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
