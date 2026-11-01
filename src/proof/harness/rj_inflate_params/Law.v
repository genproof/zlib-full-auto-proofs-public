(* The law rj_inflate_params (harness/rj_inflate_params.c): inflateInit2 accepts exactly zlib.h's windowBits. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.rj_inflate_params.
Require Zlib.proof.harness.rj_inflate_params.RIPLawAsm.

Lemma rj_inflate_params_ok : laws_common_ok ->
  harness_safe Zlib.contracts.rj_inflate_params.whole_prog.
Proof.
  exact Zlib.proof.harness.rj_inflate_params.RIPLawAsm.rip_law.
Qed.
