(* The inflate machine's pure facts used by the v5 layer, Qed: the covering fact of inflate_table's tables
   (Cover3.cover3_stmt, from Cover2 and Cover3Len), one pass of Model2.v's switch keeps mwf3 (CaseHyps5's
   stepf2_mwf3_stmt, from StepMwf5.stepf2_inv), and the fixed tables are valid (fixed_ok5). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Inv3.
Require Zlib.proof.inflate.Cover2 Zlib.proof.inflate.Cover3 Zlib.proof.inflate.Cover3Len.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Zlib.proof.inflate.StepMwf5 Zlib.proof.inflate.FixedValid2.
Local Open Scope Z_scope.

Lemma cover3_proof : Zlib.proof.inflate.Cover3.cover3_stmt.
Proof.
  intros type lens req old root used t A B C D E.
  destruct (Zlib.proof.inflate.Cover2.cover2_proof type lens req old root used t A B C D E) as [T U].
  split; [exact T|]. split; [exact U|].
  intros ->. eapply Zlib.proof.inflate.Cover3Len.cover3_len_inv2; eauto.
Qed.

Lemma stepf2_mwf3_proof : stepf2_mwf3_stmt.
Proof. exact (proj1 (Zlib.proof.inflate.StepMwf5.stepf2_inv cover3_proof)). Qed.

Lemma fixed_ok5_proof : fixed_ok5.
Proof.
  intros s. split; [ | apply (Zlib.proof.inflate.FixedValid2.tvalid_fixed2 s)].
  destruct (Zlib.proof.inflate.FixedValid2.lvalid_fixed s) as (sz & A & B & C).
  exists sz. split; [exact A | split; [exact B | ]].
  intros i Hi. specialize (C i Hi). unfold Zlib.proof.inflate.Inv2.len_ok. intros Hop. specialize (C Hop). lia.
Qed.
