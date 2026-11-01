(* The law rfc_stored (harness/rfc_stored.c): a raw, zlib or gzip stream of stored blocks of any sizes is inflated
   to exactly its data.

   From the assembly RSLawAsm.rs_core and its three premises: inflate.c's bodies for SpecW's clients
   (SpecWLibProof.specw_lib), the decode theory (Decode7a.decode7a) and laws_common.h's helpers. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.rfc_stored.
Require Zlib.proof.harness.rfc_stored.RSLawAsm.
Require Zlib.proof.wide.Decode7a.
Require Zlib.proof.inflate_api.SpecWLibProof.

Lemma rfc_stored_ok : laws_common_ok ->
  harness_safe Zlib.contracts.rfc_stored.whole_prog.
Proof.
  intros H. apply Zlib.proof.harness.rfc_stored.RSLawAsm.rs_core.
  - exact Zlib.proof.inflate_api.SpecWLibProof.specw_lib.
  - exact Zlib.proof.wide.Decode7a.decode7a.
  - exact H.
Qed.
