(* Law inflate_header: the statement of main's proof (IHMain.v): main of harness/inflate_header.c against
   MainLib.main_core_spec R (IHGlobals.v), for ANY invariant I with the facts of IHFacts.v, calling inflate.c's
   API through its shared specifications (inflate_api/Spec5.v, at the inflate unit's compspecs), the
   zlib_common.h helpers through theirs (crc32/HarnessRef.v, adler32/HarnessBytes.v,
   inflate_common/HarnessLib.v) and the harness's own functions through IHHelpers.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_header.IHLawCS Zlib.proof.harness.inflate_header.IHGlobals
               Zlib.proof.harness.inflate_header.IHHelpers Zlib.proof.harness.inflate_header.IHFacts.
Require Import Zlib.harness.x_inflate_header.code.

Definition Gmain : funspecs :=
  [inflateInit2__spec; inflate_spec; inflateGetHeader_spec; inflateEnd_spec; zcalloc_i; zcfree_i;
   ref_crc32_spec; bytes_copy_spec; exact_copy_spec; exact_space_spec; stream_defaults_spec;
   draw_nonzero_spec; head_buf_spec; field_ok_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Definition ih_main_stmt : Prop :=
  forall I, ih_facts I -> semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
