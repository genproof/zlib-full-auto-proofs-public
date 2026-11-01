(* Law rj_bad_header: the statement of main's proof (RBHMain.v): main of harness/rj_bad_header.c against
   MainLib.main_core_spec R (RBHGlobals.v), calling inflate.c's API through its shared specifications
   (inflateInit2_: inflate_api/Spec5.v; inflate(): the wide inflate_specW of inflate_api/SpecW.v, since a call
   is offered up to UINT_MAX bytes of input and of output space) and laws_common.h's helpers through theirs
   (laws_common/Spec.v).  The pure fact main needs about the call is RBHTheory.rbh_theory. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rj_bad_header.RBHLawCS Zlib.proof.harness.rj_bad_header.RBHGlobals.
Require Import Zlib.harness.rj_bad_header.code.

Definition Gmain : funspecs :=
  [inflateInit2__spec; inflate_specW; zcalloc_i; zcfree_i;
   upto_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec;
   nondet_u32_spec; gp_assert_spec; gp_assume_spec].

Definition rbh_main_stmt : Prop :=
  semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
