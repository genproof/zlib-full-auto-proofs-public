(* Law api_inflate_deterministic (harness/api_inflate_deterministic.c): two streams made by inflateInit2 with
   the same windowBits (in zlib.h's ranges, both inits Z_OK) and given the same calls behave the same, call by
   call.  laws_session.h's inflate_window_ok is proved by laws_session/Bodies.v. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.api_inflate_deterministic.
Require Zlib.proof.inflate_api.SpecWLibProof.
Require Zlib.proof.harness.api_inflate_deterministic.AIDMain.
Require Zlib.proof.harness.api_inflate_deterministic.AIDLawAsm.
Require Zlib.proof.harness.laws_session.Bodies.

Lemma api_inflate_deterministic_ok : laws_common_ok ->
  harness_safe Zlib.contracts.api_inflate_deterministic.whole_prog.
Proof.
  intros L.
  exact (Zlib.proof.harness.api_inflate_deterministic.AIDLawAsm.aid_core
           Zlib.proof.harness.api_inflate_deterministic.AIDMain.aid_main
           Zlib.proof.inflate_api.SpecWLibProof.specw_lib L
           Zlib.proof.harness.laws_session.Bodies.laws_session_bodies).
Qed.
