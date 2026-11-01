(* Law x_inflate_reset (harness/x_inflate_reset.c), from the inflate area's library bodies (LibStmt5.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Zlib.contracts.x_inflate_reset.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.harness.inflate_reset.IRLawAsm Zlib.proof.harness.inflate_reset.IRMain
        Zlib.proof.harness.inflate_reset.IRGlobals Zlib.proof.harness.inflate_reset.IRTheory.

Lemma law5_inflate_reset : inflate_lib5_stmt -> harness_safe Zlib.contracts.x_inflate_reset.whole_prog.
Proof.
  intros H.
  exact (Zlib.proof.harness.inflate_reset.IRLawAsm.law5_core H
           Zlib.proof.harness.inflate_reset.IRMain.body_main
           Zlib.proof.harness.inflate_reset.IRGlobals.globals_ok
           Zlib.proof.harness.inflate_reset.IRTheory.ir_theory).
Qed.
