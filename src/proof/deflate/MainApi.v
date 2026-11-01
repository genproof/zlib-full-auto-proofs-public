(** * Law deflate_api: harness_safe of its program, from the model facts (LawFacts.v), the body obligations of
    trees.c / deflate.c / compress.c (Obligations.v), the harness helpers (HarnessLib.v) and the globals
    (GlobalsInit.v).

    The specifications and bodies of the harness functions, the body of main (against MainLib.main_core_spec with
    the resources of GlobalsInit) and the assembly (QuickProof.Assembly.harness_safe_by_specs) are in
    src/proof/harness/deflate_api9/ (Law.deflate_api_core). *)
Require Import QuickProof.Contract.
Require Zlib.contracts.x_deflate_api.
Require Import Zlib.proof.deflate.Obligations9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.harness.deflate_api9.Law.

Theorem deflate_api_law :
  (exists I Iend, api_facts I Iend) -> trees_bodies_ok -> deflate_bodies_ok9 -> harness_lib_ok -> globals_ok ->
  harness_safe Zlib.contracts.x_deflate_api.whole_prog.
Proof.
  exact Zlib.proof.harness.deflate_api9.Law.deflate_api_core.
Qed.
