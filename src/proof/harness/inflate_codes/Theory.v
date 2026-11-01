(* Law inflate_codes: the pure theory (Facts.v's interface): an invariant I of the harness's loop with the facts
   main needs, from the intra-call invariant of the model (stepf2_mwf3_stmt).  Helper files: Theory*.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_codes.Facts.
Require Import Zlib.proof.harness.inflate_codes.TheoryDefs.
Require Import Zlib.proof.harness.inflate_codes.TheoryHead.
Require Import Zlib.proof.harness.inflate_codes.TheoryHdr.
Require Import Zlib.proof.harness.inflate_codes.TheoryDict.
Require Import Zlib.proof.harness.inflate_codes.TheoryBlock.
Require Import Zlib.proof.harness.inflate_codes.TheoryFast.
Require Import Zlib.proof.harness.inflate_codes.TheoryDec.
Require Import Zlib.proof.harness.inflate_codes.TheoryTab.
Require Import Zlib.proof.harness.inflate_codes.TheoryNoDict.
Require Import Zlib.proof.harness.inflate_codes.TheoryRun.
Require Import Zlib.proof.harness.inflate_codes.TheoryCall.
Require Import Zlib.proof.harness.inflate_codes.TheoryApi.

Lemma codes_theory : codes_theory_stmt.
Proof.
  intros SM. exists inv.
  pose proof (rn_step SM th_head th_hdr th_dict th_block th_fast th_dec th_tab) as ST.
  constructor.
  - intros w src z sp W _ _ M _ _ _ _. apply ap_init; auto.
  - intros w src pos final indict z L (_ & _ & H & _). exact H.
  - intros w src pos final indict z L (_ & _ & _ & _ & F & _ & _ & _ & _ & _ & I). split.
    + destruct F as [(-> & _)|[(-> & _)|[(-> & _)|(-> & _)]]]; auto.
    + destruct I as [(-> & _)|(-> & _)]; auto.
  - intros w src pos final indict z L dict alloc_ok winp IV _ _ _ _. apply ap_setdict; auto.
  - intros. eapply cl_inflate; eauto. exact th_nodict.
Qed.
