(* Law api_inflate_any (harness/api_inflate_any.c): any windowBits zlib.h allows, any input in any pieces, any
   flush, any output space, inflateSetDictionary between calls or not: inflateInit2 returns Z_OK, every inflate()
   returns a documented code, leaves its input and the unwritten output as they were, accounts next_in/next_out
   and total_in/total_out exactly, and does not return Z_OK without input and output space. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.api_inflate_any.
Require Zlib.proof.inflate_api.SpecWLibProof.
Require Zlib.proof.harness.laws_session.Bodies.
Require Zlib.proof.harness.api_inflate_any.LawAsm.

Lemma api_inflate_any_ok : laws_common_ok -> harness_safe Zlib.contracts.api_inflate_any.whole_prog.
Proof.
  intro LC.
  exact (Zlib.proof.harness.api_inflate_any.LawAsm.aia_core
           Zlib.proof.inflate_api.SpecWLibProof.specw_lib LC Zlib.proof.harness.laws_session.Bodies.laws_session_bodies).
Qed.
