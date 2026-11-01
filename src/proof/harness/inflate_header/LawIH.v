(* Law x_inflate_header (harness/x_inflate_header.c), from the inflate area's library bodies (LibStmt5.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Zlib.contracts.x_inflate_header.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.harness.inflate_header.IHLawAsm Zlib.proof.harness.inflate_header.IHMain
        Zlib.proof.harness.inflate_header.IHTheory Zlib.proof.harness.inflate_header.IHHelpersBody.

Lemma law5_inflate_header : inflate_lib5_stmt -> harness_safe Zlib.contracts.x_inflate_header.whole_prog.
Proof.
  intros H.
  exact (Zlib.proof.harness.inflate_header.IHLawAsm.ih_law_core H
           Zlib.proof.harness.inflate_header.IHMain.ih_body_main
           Zlib.proof.harness.inflate_header.IHTheory.ih_theory
           Zlib.proof.harness.inflate_header.IHHelpersBody.ih_helpers_bodies).
Qed.
