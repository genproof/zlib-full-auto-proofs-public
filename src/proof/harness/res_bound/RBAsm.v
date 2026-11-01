(* Law res_bound (harness/res_bound.c): after deflateInit2 with any parameters in zlib.h's ranges and, or not,
   deflateSetDictionary (up to 2^32-1 bytes) or deflateSetHeader (any int text / hcrc / os, an extra field of
   up to 65535 bytes, a name and a comment of up to 2^32-2 bytes), one deflate(Z_FINISH) offered all the data and
   exactly deflateBound bytes of output space (both below 2^32) returns Z_STREAM_END, having read all of the data
   (avail_in 0, next_in at its end, total_in up by its length) and written at most deflateBound bytes (total_out as
   many).  harness_safe of its program from the body of main (with the harness's own any_string), the laws_common.h
   helpers (laws_common_ok), laws_session.h's deflate_params_ok (laws_session/Bodies.v), the deflate.c / trees.c
   bodies (DSpec / DSpec9: Obligations.trees_bodies_ok, Obligations9.deflate_bodies_ok9) and the model facts:
   LawFactsW.bound_facts_w (bw_init, bw_dict, bw_head, bw_bound, bw_once) with LTWBOnce.once_acct_w (the stream's
   fields after the one deflate() call), both from LTWBOnce.bound_theory_acct (the wide core LTWCore, the header
   stages LTWHdr and lemma (ii)), and LawFacts.api_facts (af_init: deflateInit2_ with any parameters). *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.deflate.LawFactsW.
Require Zlib.contracts.res_bound.
Require Zlib.proof.huffman.Lemmas Zlib.proof.deflate.LawTheory.
Require Zlib.proof.trees.Body_bits Zlib.proof.trees.Body_build Zlib.proof.trees.Body_scan Zlib.proof.trees.Body_send Zlib.proof.trees.Body_flush.
Require Zlib.proof.deflate.Body_leaf Zlib.proof.deflate.Body_window Zlib.proof.deflate.Body_stored Zlib.proof.deflate.Body_compress Zlib.proof.deflate.Body_api Zlib.proof.deflate.Body_api9 Zlib.proof.deflate.Body_deflate.
Require Zlib.proof.harness.res_bound.RBLaw Zlib.proof.harness.res_bound.RBMain Zlib.proof.harness.res_bound.RBStringBody.
Require Zlib.proof.deflate.LTWCore Zlib.proof.deflate.LTWHdr Zlib.proof.deflate.LTWBOnce.
Require Zlib.proof.harness.laws_session.Bodies.

(* the bodies of trees.c and deflate.c (as src/contracts/suite.v proves them for the x_ laws) *)
Lemma res_trees_bodies : Zlib.proof.deflate.Obligations.trees_bodies_ok.
Proof.
  unfold Zlib.proof.deflate.Obligations.trees_bodies_ok.
  destruct Zlib.proof.trees.Body_bits.trees_bits as (? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_build.trees_build as (? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_scan.trees_scan as (? & ? & ? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_send.trees_send as (? & ? & ? & ? & ?).
  pose proof Zlib.proof.trees.Body_flush.trees_flush.
  repeat (split; [assumption | ]); assumption.
Qed.

Lemma res_deflate_bodies9 : Zlib.proof.deflate.Obligations9.deflate_bodies_ok9.
Proof.
  unfold Zlib.proof.deflate.Obligations9.deflate_bodies_ok9.
  destruct Zlib.proof.deflate.Body_leaf.deflate_leaf as (? & ? & ? & ? & ? & ?).
  destruct Zlib.proof.deflate.Body_window.deflate_window as (? & ?).
  pose proof Zlib.proof.deflate.Body_stored.deflate_stored_body.
  destruct Zlib.proof.deflate.Body_compress.deflate_compress as (? & ? & ? & ?).
  destruct Zlib.proof.deflate.Body_api.deflate_api_bodies as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
  destruct Zlib.proof.deflate.Body_api9.deflate_api_bodies9 as (? & ? & ?).
  destruct Zlib.proof.deflate.Body_deflate.deflate_main_bodies as (? & ?).
  repeat (split; [assumption | ]); assumption.
Qed.

(* [RBKit.part_pre_stmt] (statements 0-16 of main, RBPre.part_pre) is taken as a hypothesis, as in RBMain. *)
Theorem res_bound_ok : Zlib.proof.harness.res_bound.RBKit.part_pre_stmt -> laws_common_ok ->
  harness_safe Zlib.contracts.res_bound.whole_prog.
Proof.
  intros PP LC.
  destruct Zlib.proof.huffman.Lemmas.huffman_lemmas as [Hi Hii].
  destruct (Zlib.proof.deflate.LawTheory.law_theory Hi Hii) as [AF _].
  exact (Zlib.proof.harness.res_bound.RBLaw.law_of_main (Zlib.proof.harness.res_bound.RBMain.body_main_of_pre PP)
    Zlib.proof.harness.res_bound.RBStringBody.body_any_string LC Zlib.proof.harness.laws_session.Bodies.laws_session_bodies
    (Zlib.proof.deflate.LTWBOnce.bound_theory_acct Hii (Zlib.proof.deflate.LTWCore.core_theory_w Hi)
       Zlib.proof.deflate.LTWHdr.hdr_theory_w)
    AF res_trees_bodies res_deflate_bodies9).
Qed.
