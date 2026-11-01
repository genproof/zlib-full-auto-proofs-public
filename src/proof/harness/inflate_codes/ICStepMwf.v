(* Law inflate_codes: the intra-call invariant of the model (CaseHyps5.stepf2_mwf3_stmt: one pass of the switch
   keeps mwf3), from Cover3.v's covering fact (Cover2.cover2_proof and Cover3Len.cover3_len_inv2) and the mwf3
   half of StepMwf5.stepf2_inv.  The files IC*.v of this directory are copies of src/proof/inflate/Step3*.v,
   Step5Header.v and Step5Mwf.v under their own module names, unchanged otherwise. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Inv3.
Require Zlib.proof.inflate.Cover2 Zlib.proof.inflate.Cover3 Zlib.proof.inflate.Cover3Len.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Zlib.proof.harness.inflate_codes.ICStep5Mwf.
Local Open Scope Z_scope.

Lemma ic_cover3 : Zlib.proof.inflate.Cover3.cover3_stmt.
Proof.
  intros type lens req old root used t A B C D E.
  destruct (Zlib.proof.inflate.Cover2.cover2_proof type lens req old root used t A B C D E) as [T U].
  split; [exact T|]. split; [exact U|].
  intros ->. eapply Zlib.proof.inflate.Cover3Len.cover3_len_inv2; eauto.
Qed.

Lemma ic_stepf2_mwf3 : stepf2_mwf3_stmt.
Proof. exact (Zlib.proof.harness.inflate_codes.ICStep5Mwf.stepf2_mwf3_x ic_cover3). Qed.
