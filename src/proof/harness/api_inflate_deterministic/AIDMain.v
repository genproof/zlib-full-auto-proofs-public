(* Law api_inflate_deterministic, main: harness/api_inflate_deterministic.c proved against
   MainLib.main_core_spec R_aid for ANY invariant J with the facts of AIDFacts.v, assembled from the parts of
   AIDMainKit.v. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainDefs.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainKit.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainTop.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainBody.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainTail.

Lemma aid_main : aid_main_stmt.
Proof. exact (main_of (body_of tail_proof)). Qed.
