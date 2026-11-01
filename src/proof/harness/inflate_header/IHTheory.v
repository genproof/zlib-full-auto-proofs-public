(* Law inflate_header: the theory over the model (Model2.run2): an invariant I with the facts of IHFacts.v.
   The invariant (IHTCall.ih_I) and the per-mode state (IHTDefs.J) are described in IHTDefs.v; the cases are
   IHTCase*.v, the facts about the member and the model's helpers IHTKit*.v, the loop and the call IHTCall.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_header.IHFacts.
Require Import Zlib.proof.harness.inflate_header.IHTDefs.
Require Import Zlib.proof.harness.inflate_header.IHTKitLay.
Require Import Zlib.proof.harness.inflate_header.IHTKitMisc.
Require Import Zlib.proof.harness.inflate_header.IHTKitNb.
Require Import Zlib.proof.harness.inflate_header.IHTKitStr.
Require Import Zlib.proof.harness.inflate_header.IHTCaseHF.
Require Import Zlib.proof.harness.inflate_header.IHTCaseTOE.
Require Import Zlib.proof.harness.inflate_header.IHTCaseEx.
Require Import Zlib.proof.harness.inflate_header.IHTCaseNC.
Require Import Zlib.proof.harness.inflate_header.IHTCaseHc.
Require Import Zlib.proof.harness.inflate_header.IHTCaseBlk.
Require Import Zlib.proof.harness.inflate_header.IHTCall.

Lemma ih_theory : ih_theory_stmt.
Proof.
  exists ih_I.
  assert (K : ih_kit).
  { destruct ih_misc_proof as (B & C & I). destruct ih_str_proof as (Z & P).
    constructor; auto using ih_lay_proof, ih_nb_proof. }
  apply (ih_call K).
  destruct ihc_hf as [HE FL]. destruct ihc_toe as (TI & OSc & EL). destruct ihc_nc as [NA CO].
  pose proof (ihc_hc K) as HC. pose proof (ihc_ex K) as EXc. pose proof (ihc_blk K) as BL.
  pose proof (CO K HC) as CO'. pose proof (NA K CO') as NA'. pose proof (EXc NA') as EX'.
  pose proof (EL K EX') as EL'. pose proof (OSc K EL') as OS1. pose proof (TI K OS1) as TI'.
  pose proof (FL K TI') as FL'. pose proof (HE K) as HE'.
  unfold ih_cases. tauto.
Qed.
