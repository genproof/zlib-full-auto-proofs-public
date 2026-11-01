(* The law api_split_invariant (harness/api_split_invariant.c): with the 32 KiB window, one inflate() call over all
   of the input gives the same bytes and final code as any split of it. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.api_split_invariant.
(* the assembly over inflate.c's wide bodies (SILawAsm.si_law), and those bodies (SpecWLibProof.specw_lib) *)
Require Zlib.proof.harness.api_split_invariant.SILawAsm.
Require Zlib.proof.inflate_api.SpecWLibProof.

Lemma api_split_invariant_ok : laws_common_ok ->
  harness_safe Zlib.contracts.api_split_invariant.whole_prog.
Proof.
  exact (Zlib.proof.harness.api_split_invariant.SILawAsm.si_law Zlib.proof.inflate_api.SpecWLibProof.specw_lib).
Qed.
