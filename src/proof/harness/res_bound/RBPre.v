(* Law res_bound, main: part_pre (RBKit.v): the four parameters, data_len, data, choice, the four lengths, dict,
   extra (any_bytes), name, comment (any_string) and the NULL test (msuf 0 -> msuf 17), from the two segments of
   RBPreKit.v. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.res_bound.RBKit Zlib.proof.harness.res_bound.RBPreKit.
Require Zlib.proof.harness.res_bound.RBPreA Zlib.proof.harness.res_bound.RBPreB.

Lemma part_pre : part_pre_stmt.
Proof.
  intros Espec gv vh vs HA1.
  apply Zlib.proof.harness.res_bound.RBPreA.part_preA; intros rs.
  apply Zlib.proof.harness.res_bound.RBPreB.part_preB.
  exact HA1.
Qed.
