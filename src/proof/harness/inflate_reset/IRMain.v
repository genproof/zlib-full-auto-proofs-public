(* Law inflate_reset: the main of harness/inflate_reset.c, proved against MainLib.main_core_spec R (IRGlobals.v)
   for ANY invariants I1, I2 with the facts of IRFacts.v (reset_facts I1 I2), calling inflate.c's API through
   its shared specifications (inflate_api/Spec5.v, at the inflate unit's compspecs: moved to the law's with
   IRLawCS's instances) and the harness helpers through theirs (inflate_common/HarnessLib.v,
   adler32/HarnessBytes.v bytes_same), as inflate_codes' Main*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_reset.IRLawCS Zlib.proof.harness.inflate_reset.IRGlobals
               Zlib.proof.harness.inflate_reset.IRFacts.
Require Import Zlib.harness.x_inflate_reset.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_reset.IRMainKit Zlib.proof.harness.inflate_reset.IRMainPh2
               Zlib.proof.harness.inflate_reset.IRMainRst Zlib.proof.harness.inflate_reset.IRMainLoop
               Zlib.proof.harness.inflate_reset.IRMainTop.

Definition Gmain : funspecs :=
  [inflateInit2__spec; inflate_spec; inflateEnd_spec; inflateReset_spec; inflateReset2_spec; zcalloc_i; zcfree_i;
   bytes_same_spec; exact_copy_spec; exact_space_spec; inflate_wbits_ok_spec; stream_defaults_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Lemma body_main I1 I2 : reset_facts I1 I2 -> semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  intros RF. change Gmain with Gmain_k. exact (main_of (loop_of ph2_proof rst_proof) I1 I2 RF).
Qed.
