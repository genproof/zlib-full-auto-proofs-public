(* Law x_inflate_buffers (harness/x_inflate_buffers.c), from the inflate area's library bodies (LibStmt5.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Zlib.contracts.x_inflate_buffers.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.harness.inflate_buffers.IBLawAsm Zlib.proof.harness.inflate_buffers.IBWbits.

Lemma law5_inflate_buffers : inflate_lib5_stmt -> harness_safe Zlib.contracts.x_inflate_buffers.whole_prog.
Proof.
  intros H. exact (Zlib.proof.harness.inflate_buffers.IBLawAsm.law5_core H
                     Zlib.proof.harness.inflate_buffers.IBWbits.ib_wbits).
Qed.
