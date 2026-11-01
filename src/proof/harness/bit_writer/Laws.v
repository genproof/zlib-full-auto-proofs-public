(* The two laws over raw deflate streams built bit by bit with the harnesses' put_bits/put_literal
   (harness/rj_bad_block.c, rj_far_back.c): an invalid first block, and a distance past the output, are refused
   with Z_DATA_ERROR. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.rj_bad_block.
Require Zlib.contracts.rj_far_back.
Require Zlib.proof.harness.bit_writer.BWLawAsm.
Require Zlib.proof.inflate_api.SpecWLib.
Require Zlib.proof.inflate_api.SpecWBridge.
Require Zlib.proof.za.inflate_api.ULib.
Require Zlib.proof.za.inflate.CasesAllZ.
Require Zlib.proof.za.inffast.FastZ.
Require Zlib.proof.za.inflate_api.BodyZ.
Require Zlib.proof.za.inflate_api.ApiZ.
Require Zlib.proof.za.inflate.StepZ.
Require Zlib.proof.inflate.StepW.

(* inflate.c's bodies for the wide specification of inflate() at zlib's default allocator: the bodies of the
   allocator-generic port at zc_alloc (ULib.za_ulib from its parts) and the bridge to SpecW's specifications *)
Lemma bw_specw_lib : Zlib.proof.inflate_api.SpecWLib.specw_lib_stmt.
Proof.
  split.
  - destruct (Zlib.proof.za.inflate_api.ULib.za_ulib _ Zlib.proof.inflate_api.SpecWLib.zc_alloc) as [_ Hlib].
    apply Hlib.
    + exact Zlib.proof.za.inflate.CasesAllZ.za_cases_proof.
    + exact Zlib.proof.za.inflate_api.BodyZ.za_body_inflate_proof.
    + exact (Zlib.proof.za.inflate.StepZ.za_step_proof Zlib.proof.inflate.StepW.stepf2_mwf3W).
    + exact Zlib.proof.za.inffast.FastZ.za_fast_proof.
    + exact Zlib.proof.za.inflate_api.ApiZ.za_api_proof.
  - exact Zlib.proof.inflate_api.SpecWBridge.specw_bridge.
Qed.

Lemma bit_writer_laws_ok : laws_common_ok ->
  harness_safe Zlib.contracts.rj_bad_block.whole_prog /\
  harness_safe Zlib.contracts.rj_far_back.whole_prog.
Proof.
  exact (Zlib.proof.harness.bit_writer.BWLawAsm.bw_core bw_specw_lib).
Qed.
