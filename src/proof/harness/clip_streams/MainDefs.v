(* The laws rt_partial, rj_truncated, rj_bad_checksum and rfc_trailing_bytes: main's context and the statements
   of the four bodies.

   [Gmain_rp / Gmain_rt / Gmain_bc / Gmain_tb]: the functions each main calls, with THE specifications the
   laws' G have for them (one per function; a program defines only the laws_common.h helpers its harness
   uses): deflate.c's deflateInit2_ (DSpec9, on a stream whose total_in / total_out / msg / adler are
   undefined, as new_stream leaves them), deflateBound_z and deflate (DSpec), inflate.c's inflateInit2_
   (Spec5) and inflate (SpecW.inflate_specW: avail_in / avail_out up to UINT_MAX, and strm->adler any value on a
   raw stream: new_stream does not set it and inflateInit2_ sets it only for zlib / gzip), zcalloc / zcfree
   at the inflate unit's compspecs (for inflateInit2_'s zfuncs), the helpers of harness/laws_common.h
   (laws_common/Spec.v) and the environment.

   Each main is proved against MainLib.main_core_spec (Globals.R_of the harness's literal) for ANY invariants
   with the facts of DFacts.v (the deflate loop) and IFacts.v (the inflate loop of the law). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Zlib.proof.deflate.DSpec9.
Require Zlib.proof.inflate_api.Spec5 Zlib.proof.inflate_api.SpecW Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts Zlib.proof.harness.clip_streams.IFacts.
Require Zlib.harness.rt_partial.code Zlib.harness.rj_truncated.code Zlib.harness.rj_bad_checksum.code.
Require Zlib.harness.rfc_trailing_bytes.code.

(* each program defines only the laws_common.h helpers and environment functions its harness uses: bytes_eq
   only in rt_partial, gp_assume only in rj_bad_checksum *)
Definition Gmain_rp : funspecs :=
  [Zlib.proof.deflate.DSpec9.deflateInit2__spec_v9; Zlib.proof.deflate.DSpec.deflateBound_z_spec;
   Zlib.proof.deflate.DSpec.deflate_spec;
   Zlib.proof.inflate_api.Spec5.inflateInit2__spec; Zlib.proof.inflate_api.SpecW.inflate_specW;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   upto_spec; clip_spec; any_bytes_spec; bytes_eq_spec;
   offer_spec; new_stream_spec; (_quickproof_malloc, malloc_spec'); nondet_u32_spec; gp_assert_spec].
Definition Gmain_rt : funspecs :=
  [Zlib.proof.deflate.DSpec9.deflateInit2__spec_v9; Zlib.proof.deflate.DSpec.deflateBound_z_spec;
   Zlib.proof.deflate.DSpec.deflate_spec;
   Zlib.proof.inflate_api.Spec5.inflateInit2__spec; Zlib.proof.inflate_api.SpecW.inflate_specW;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   upto_spec; clip_spec; any_bytes_spec;
   offer_spec; new_stream_spec; (_quickproof_malloc, malloc_spec'); nondet_u32_spec; gp_assert_spec].
Definition Gmain_bc : funspecs :=
  [Zlib.proof.deflate.DSpec9.deflateInit2__spec_v9; Zlib.proof.deflate.DSpec.deflateBound_z_spec;
   Zlib.proof.deflate.DSpec.deflate_spec;
   Zlib.proof.inflate_api.Spec5.inflateInit2__spec; Zlib.proof.inflate_api.SpecW.inflate_specW;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   upto_spec; clip_spec; any_bytes_spec; gp_assume_spec;
   offer_spec; new_stream_spec; (_quickproof_malloc, malloc_spec'); nondet_u32_spec; gp_assert_spec].
Definition Gmain_tb : funspecs := Gmain_rt.

Definition main_rp_stmt : Prop :=
  forall J0 J P, clip_dfacts J0 J -> pfx_facts P ->
  semax_body (QPvarspecs p_rp) Gmain_rp Zlib.harness.rt_partial.code.f_main
    (Zlib.harness.rt_partial.code._main, main_core_spec R_rp).

Definition main_rt_stmt : Prop :=
  forall J0 J P, clip_dfacts J0 J -> pfx_facts P ->
  semax_body (QPvarspecs p_rt) Gmain_rt Zlib.harness.rj_truncated.code.f_main
    (Zlib.harness.rj_truncated.code._main, main_core_spec R_rt).

Definition main_bc_stmt : Prop :=
  forall J0 J P, clip_dfacts J0 J -> bad_facts P ->
  semax_body (QPvarspecs p_bc) Gmain_bc Zlib.harness.rj_bad_checksum.code.f_main
    (Zlib.harness.rj_bad_checksum.code._main, main_core_spec R_bc).

Definition main_tb_stmt : Prop :=
  forall J0 J P, clip_dfacts J0 J -> trl_facts P ->
  semax_body (QPvarspecs p_tb) Gmain_tb Zlib.harness.rfc_trailing_bytes.code.f_main
    (Zlib.harness.rfc_trailing_bytes.code._main, main_core_spec R_tb).
