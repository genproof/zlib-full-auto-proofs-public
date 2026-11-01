(* The theory of the law api_split_invariant: the facts main() needs (SIFacts.v), from the parts. *)
Require Import Zlib.proof.harness.api_split_invariant.SIFacts.
Require Import Zlib.proof.harness.api_split_invariant.SITabRep.
Require Import Zlib.proof.harness.api_split_invariant.SIAwf.
Require Import Zlib.proof.harness.api_split_invariant.SIKit.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdr.
Require Import Zlib.proof.harness.api_split_invariant.SISimBlock.
Require Import Zlib.proof.harness.api_split_invariant.SISimDec.
Require Import Zlib.proof.harness.api_split_invariant.SISimTab.
Require Import Zlib.proof.harness.api_split_invariant.SISimFast.
Require Import Zlib.proof.harness.api_split_invariant.SICall.
Require Import Zlib.proof.harness.api_split_invariant.SIFactsProof.

Lemma si_theory : si_theory_stmt.
Proof.
  pose proof si_kit as K. pose proof (si_awf si_tabrep) as A.
  pose proof (si_fast K A) as F. pose proof (si_dec K A F) as D. pose proof (si_block K A) as B.
  pose proof (si_hdr K A B) as H. pose proof (si_tab K A D) as T.
  exact (si_facts_proof A (si_call K A H B T D)).
Qed.
