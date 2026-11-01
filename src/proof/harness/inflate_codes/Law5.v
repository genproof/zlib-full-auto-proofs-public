(* Law x_inflate_codes (harness/x_inflate_codes.c), from the inflate area's library bodies (LibStmt5.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Zlib.contracts.x_inflate_codes.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.harness.inflate_codes.LawAsm Zlib.proof.harness.inflate_codes.ICStepMwf.

Lemma law5_inflate_codes : inflate_lib5_stmt -> harness_safe Zlib.contracts.x_inflate_codes.whole_prog.
Proof.
  intros H.
  exact (Zlib.proof.harness.inflate_codes.LawAsm.law5_core H
           Zlib.proof.harness.inflate_codes.ICStepMwf.ic_stepf2_mwf3).
Qed.
