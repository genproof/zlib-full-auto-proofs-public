(* Law x_inflate_check (harness/x_inflate_check.c), from the inflate area's library bodies (LibStmt5.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Zlib.contracts.x_inflate_check.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.harness.inflate_check.IKLawAsm.

Lemma law5_inflate_check : inflate_lib5_stmt -> harness_safe Zlib.contracts.x_inflate_check.whole_prog.
Proof.
  exact Zlib.proof.harness.inflate_check.IKLawAsm.ik_law_core.
Qed.
