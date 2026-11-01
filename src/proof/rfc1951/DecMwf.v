(* One pass of Model2's switch keeps mwf3 (= InvQ5.stepf2_mwf3_proof, restated here: InvQ5.v does not build on
   this base because of its fixed_ok5 part). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Inv3.
Require Zlib.proof.inflate.Cover2 Zlib.proof.inflate.Cover3 Zlib.proof.inflate.Cover3Len.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Zlib.proof.inflate.StepMwf5.
Local Open Scope Z_scope.

Lemma dm_cover3 : Zlib.proof.inflate.Cover3.cover3_stmt.
Proof.
  intros type lens req old root used t A B C D E.
  destruct (Zlib.proof.inflate.Cover2.cover2_proof type lens req old root used t A B C D E) as [T U].
  split; [exact T|]. split; [exact U|].
  intros ->. eapply Zlib.proof.inflate.Cover3Len.cover3_len_inv2; eauto.
Qed.

Lemma dm_stepf2_mwf3 : stepf2_mwf3_stmt.
Proof. exact (proj1 (Zlib.proof.inflate.StepMwf5.stepf2_inv dm_cover3)). Qed.
