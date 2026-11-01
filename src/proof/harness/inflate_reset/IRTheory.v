(* Law inflate_reset: the pure theory (IRFacts.v's interface), from its parts. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Require Zlib.proof.harness.inflate_reset.IRTabDet Zlib.proof.harness.inflate_reset.IRSimHead
        Zlib.proof.harness.inflate_reset.IRSimHdr Zlib.proof.harness.inflate_reset.IRSimDict
        Zlib.proof.harness.inflate_reset.IRSimBlock Zlib.proof.harness.inflate_reset.IRSimFast
        Zlib.proof.harness.inflate_reset.IRSimDec Zlib.proof.harness.inflate_reset.IRSimTab
        Zlib.proof.harness.inflate_reset.IRRun.

Lemma ir_theory : ir_theory_stmt.
Proof.
  exact (Zlib.proof.harness.inflate_reset.IRRun.ir_run
           Zlib.proof.harness.inflate_reset.IRSimHead.head_sim
           Zlib.proof.harness.inflate_reset.IRSimHdr.hdr_sim
           Zlib.proof.harness.inflate_reset.IRSimDict.dict_sim
           Zlib.proof.harness.inflate_reset.IRSimBlock.block_sim
           Zlib.proof.harness.inflate_reset.IRSimFast.fast_sim
           Zlib.proof.harness.inflate_reset.IRSimDec.dec_sim
           Zlib.proof.harness.inflate_reset.IRSimTab.tab_sim
           Zlib.proof.harness.inflate_reset.IRTabDet.tabdet_proof).
Qed.
