(* Law api_reset, main: harness/api_reset.c proved against MainLib.main_core_spec R_ar for ANY invariants J0, J1
   with the facts of ARFacts.v, assembled from the parts of ARMainKit.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.api_reset.ARMainDefs.
Require Import Zlib.proof.harness.api_reset.ARMainKit.
Require Import Zlib.proof.harness.api_reset.ARMainHead0.
Require Import Zlib.proof.harness.api_reset.ARMainHead1.
Require Import Zlib.proof.harness.api_reset.ARMainTail.
Require Import Zlib.proof.harness.api_reset.ARMainChk.
Require Import Zlib.proof.harness.api_reset.ARMainRst.
Require Import Zlib.proof.harness.api_reset.ARMainOuter.
Require Import Zlib.proof.harness.api_reset.ARMainTop.

Lemma ar_main : ar_main_stmt.
Proof.
  exact (main_of (obody_of (body0_of (proj1 tails)) (body1_of (proj2 tails chk_proof)) rst_proof)).
Qed.
