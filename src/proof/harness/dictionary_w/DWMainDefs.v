(* The laws rt_dictionary and api_dict_id: main's context and the statements of the two bodies.

   [Gmain_drt / Gmain_dai]: the functions each main calls, with THE specifications the laws' G have for them (one
   per function, as clip_streams/MainDefs.v): deflate.c's deflateInit2_ (DSpec9), deflateSetDictionary,
   deflateBound_z and deflate (DSpec), inflate.c's inflateInit2_ (Spec5), inflate (SpecW.inflate_specW:
   avail_in / avail_out up to UINT_MAX) and, for rt_dictionary, inflateSetDictionary
   (SpecW.inflateSetDictionary_specW), zcalloc / zcfree at the inflate unit's compspecs (for inflateInit2_'s
   zfuncs), adler32_z for api_dict_id's check, the helpers of harness/laws_common.h (laws_common/Spec.v; copy_of
   for the copies of round 3) and the environment.

   Each main is proved against MainLib.main_core_spec (Globals.R_of the harness's literal: DWCS.R_drt / R_dai)
   for ANY invariants with the facts of DWFacts.v (deflate) and DWIFacts.v (inflate). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DSpec9.
Require Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.inflate_api.Bodies5.
Require Zlib.proof.adler32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWIFacts.
Require Zlib.harness.rt_dictionary.code.
Require Zlib.harness.api_dict_id.code.

Definition Gmain_drt : funspecs :=
  [Zlib.proof.deflate.DSpec9.deflateInit2__spec_v9; Zlib.proof.deflate.DSpec.deflateSetDictionary_spec;
   Zlib.proof.deflate.DSpec.deflateBound_z_spec; Zlib.proof.deflate.DSpec.deflate_spec;
   Zlib.proof.inflate_api.Spec5.inflateInit2__spec; Zlib.proof.inflate_api.SpecW.inflate_specW;
   Zlib.proof.inflate_api.SpecW.inflateSetDictionary_specW;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec;
   offer_spec; new_stream_spec; (_quickproof_malloc, malloc_spec'); nondet_u32_spec; gp_assert_spec].

Definition Gmain_dai : funspecs :=
  [Zlib.proof.deflate.DSpec9.deflateInit2__spec_v9; Zlib.proof.deflate.DSpec.deflateSetDictionary_spec;
   Zlib.proof.deflate.DSpec.deflateBound_z_spec; Zlib.proof.deflate.DSpec.deflate_spec;
   Zlib.proof.inflate_api.Spec5.inflateInit2__spec; Zlib.proof.inflate_api.SpecW.inflate_specW;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   Zlib.proof.adler32.Spec.adler32_z_spec;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec;
   offer_spec; new_stream_spec; (_quickproof_malloc, malloc_spec'); nondet_u32_spec; gp_assert_spec].

Definition main_drt_stmt : Prop :=
  forall J0 J1 J Q P, dict_dfacts J0 J1 J -> dict_ifacts Q P ->
  semax_body (QPvarspecs p_drt) Gmain_drt Zlib.harness.rt_dictionary.code.f_main
    (Zlib.harness.rt_dictionary.code._main, main_core_spec R_drt).

Definition main_dai_stmt : Prop :=
  forall J0 J1 J Q P, dict_dfacts J0 J1 J -> dict_ifacts Q P ->
  semax_body (QPvarspecs p_dai) Gmain_dai Zlib.harness.api_dict_id.code.f_main
    (Zlib.harness.api_dict_id.code._main, main_core_spec R_dai).
