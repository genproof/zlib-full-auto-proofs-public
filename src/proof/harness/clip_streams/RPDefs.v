(* Law rt_partial: main's context and the statement of its body.  Since round 3 the harness keeps a copy of the
   data made with copy_of before compression and compares the output with it, so its main calls copy_of:
   Gmain_rpc is MainDefs.Gmain_rp (the same specifications of deflate.c, inflate.c, the laws_common.h helpers and
   the environment) with laws_common/Spec.v's copy_of_spec.  The other three mains of MainDefs.v do not call
   copy_of and keep their contexts. *)
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
Require Zlib.harness.rt_partial.code.

Definition Gmain_rpc : funspecs :=
  [Zlib.proof.deflate.DSpec9.deflateInit2__spec_v9; Zlib.proof.deflate.DSpec.deflateBound_z_spec;
   Zlib.proof.deflate.DSpec.deflate_spec;
   Zlib.proof.inflate_api.Spec5.inflateInit2__spec; Zlib.proof.inflate_api.SpecW.inflate_specW;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec;
   offer_spec; new_stream_spec; (_quickproof_malloc, malloc_spec'); nondet_u32_spec; gp_assert_spec].

Definition main_rpc_stmt : Prop :=
  forall J0 J P, clip_dfacts J0 J -> pfx_facts P ->
  semax_body (QPvarspecs p_rp) Gmain_rpc Zlib.harness.rt_partial.code.f_main
    (Zlib.harness.rt_partial.code._main, main_core_spec R_rp).
