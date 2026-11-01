(** * Law deflate_bound: harness_safe of its program, from the model facts (LawFacts.v), the body obligations of
    trees.c / deflate.c / compress.c (Obligations.v), the harness helpers (HarnessLib.v) and the globals
    (GlobalsInit.v).

    The specifications and bodies of the harness functions, the body of main (against MainLib.main_core_spec with
    the resources of GlobalsInit) and the assembly (QuickProof.Assembly.harness_safe_by_specs) are in
    src/proof/harness/deflate_bound/ (Law.law_of_main, Main.body_main). *)
Require Import QuickProof.Contract.
Require Zlib.contracts.x_deflate_bound.
Require Import Zlib.proof.deflate.Obligations9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.harness.deflate_bound.Law Zlib.proof.harness.deflate_bound.Main.

Theorem deflate_bound_law :
  (exists Bpre Brun, bound_facts Bpre Brun) -> trees_bodies_ok -> deflate_bodies_ok9 -> harness_lib_ok ->
  globals_ok -> harness_safe Zlib.contracts.x_deflate_bound.whole_prog.
Proof.
  apply Zlib.proof.harness.deflate_bound.Law.law_of_main.
  intros Bpre Brun BF TO. exact (Zlib.proof.harness.deflate_bound.Main.body_main Bpre Brun BF TO).
Qed.
