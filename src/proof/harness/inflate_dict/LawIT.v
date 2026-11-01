(* Law x_inflate_dict (harness/x_inflate_dict.c), from the inflate area's library bodies (LibStmt5.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Zlib.contracts.x_inflate_dict.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.harness.inflate_dict.ITLawAsm Zlib.proof.harness.inflate_common.DRefBw
        Zlib.proof.harness.inflate_common.DRefCodes.

Lemma law5_inflate_dict : inflate_lib5_stmt -> harness_safe Zlib.contracts.x_inflate_dict.whole_prog.
Proof.
  intros H.
  exact (Zlib.proof.harness.inflate_dict.ITLawAsm.law_core H
           (conj Zlib.proof.harness.inflate_common.DRefBw.dref_bw_bodies_proof
                 Zlib.proof.harness.inflate_common.DRefCodes.body_bw_fixed)).
Qed.
