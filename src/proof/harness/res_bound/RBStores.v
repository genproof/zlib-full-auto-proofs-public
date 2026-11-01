(* Law res_bound, main: part_stores (RBKit.v): the eight stores into the local gz_header head (text, time, os,
   hcrc from nondet_u32; extra, name, comment selected by bits 1-3 of choice; extra_len), msuf 17 -> msuf 25, from
   the five segments of RBStKit.v. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.res_bound.RBKit Zlib.proof.harness.res_bound.RBStKit.
Require Zlib.proof.harness.res_bound.RBSt1 Zlib.proof.harness.res_bound.RBSt2 Zlib.proof.harness.res_bound.RBSt3.
Require Zlib.proof.harness.res_bound.RBSt4 Zlib.proof.harness.res_bound.RBSt5.

Lemma part_stores : part_stores_stmt.
Proof.
  intros Espec gv vh vs rs HB.
  apply Zlib.proof.harness.res_bound.RBSt1.st1; intros text time.
  apply Zlib.proof.harness.res_bound.RBSt2.st2; intros hv.
  apply Zlib.proof.harness.res_bound.RBSt3.st3.
  apply Zlib.proof.harness.res_bound.RBSt4.st4.
  apply Zlib.proof.harness.res_bound.RBSt5.st5.
  apply HB.
Qed.
