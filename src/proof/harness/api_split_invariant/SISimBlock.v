(* The simulation of the block modes (TYPE, TYPEDO, STORED, COPY_, COPY, CHECK, LENGTH, DONE, BAD). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimBlockKit.
Require Import Zlib.proof.harness.api_split_invariant.SISimBlockType.
Require Import Zlib.proof.harness.api_split_invariant.SISimBlockStored.
Require Import Zlib.proof.harness.api_split_invariant.SISimBlockCheck.
Require Import Zlib.proof.harness.api_split_invariant.SISimBlockEnd.
Import ListNotations.
Local Open Scope Z_scope.

Lemma si_block : block_sim_stmt.
Proof.
  intros K _. apply sib_sim_ok. intros md H.
  destruct H as [E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]; subst md.
  - apply sib_TYPE, K.
  - apply sib_TYPEDO, K.
  - apply sib_STORED, K.
  - apply sib_COPY_, K.
  - apply sib_COPY, K.
  - apply sib_CHECK, K.
  - apply sib_LENGTH, K.
  - apply sib_DONE.
  - apply sib_BAD.
Qed.
