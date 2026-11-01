(* Law rt_session: the entries of trees.c and deflate.c in the assembly's context (SAsmG.G): the bodies of
   src/proof/trees/ and src/proof/deflate/ (deflate() against DSpecV.deflate_specV: DSpecVBody), moved into the
   law's program. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.Obligations9.
Require Zlib.proof.deflate.DSpecV Zlib.proof.deflate.DSpecVBody.
Require Zlib.proof.trees.Body_bits.
Require Zlib.proof.trees.Body_build.
Require Zlib.proof.trees.Body_scan.
Require Zlib.proof.trees.Body_send.
Require Zlib.proof.trees.Body_flush.
Require Zlib.proof.deflate.Body_leaf.
Require Zlib.proof.deflate.Body_window.
Require Zlib.proof.deflate.Body_stored.
Require Zlib.proof.deflate.Body_compress.
Require Zlib.proof.deflate.Body_api.
Require Zlib.proof.deflate.Body_api9.
Require Zlib.proof.deflate.Body_deflate.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SAsmG.
#[local] Existing Instance Zlib.proof.harness.rt_session.SCS.CS.

(* The bodies of trees.c, proved in src/proof/trees/. *)
Lemma ses_trees_bodies : trees_bodies_ok.
Proof.
  unfold trees_bodies_ok.
  destruct Zlib.proof.trees.Body_bits.trees_bits as (? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_build.trees_build as (? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_scan.trees_scan as (? & ? & ? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_send.trees_send as (? & ? & ? & ? & ?).
  pose proof Zlib.proof.trees.Body_flush.trees_flush.
  repeat (split; [assumption | ]); assumption.
Qed.

(* The bodies of deflate.c (deflateInit2_ / deflateReset with their v9 specifications), proved in
   src/proof/deflate/. *)
Lemma ses_deflate_bodies9 : deflate_bodies_ok9.
Proof.
  unfold deflate_bodies_ok9.
  destruct Zlib.proof.deflate.Body_leaf.deflate_leaf as (? & ? & ? & ? & ? & ?).
  destruct Zlib.proof.deflate.Body_window.deflate_window as (? & ?).
  pose proof Zlib.proof.deflate.Body_stored.deflate_stored_body.
  destruct Zlib.proof.deflate.Body_compress.deflate_compress as (? & ? & ? & ?).
  destruct Zlib.proof.deflate.Body_api.deflate_api_bodies as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
  destruct Zlib.proof.deflate.Body_api9.deflate_api_bodies9 as (? & ? & ?).
  destruct Zlib.proof.deflate.Body_deflate.deflate_main_bodies as (? & ?).
  repeat (split; [assumption | ]); assumption.
Qed.

Lemma ses_entries_trees : entries G_trees.
Proof.
  pose proof ses_trees_bodies as TB.
  destruct TB as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 &
                  T15 & T16 & T17 & T18 & T19 & T20).
  unfold ob_bi_reverse, ob_bi_flush, ob_bi_windup, ob_tr_flush_bits, ob_tr_align, ob_tr_stored_block,
    ob_gen_codes, ob_pqdownheap, ob_gen_bitlen, ob_build_tree, ob_scan_tree, ob_build_bl_tree,
    ob_detect_data_type, ob_init_block, ob_send_tree, ob_send_all_trees, ob_compress_block, ob_tr_static_init,
    ob_tr_init, ob_tr_flush_block in *.
  unfold entries, G_trees.
  ses_entry T1. ses_entry T2. ses_entry T3. ses_entry T4. ses_entry T5. ses_entry T6. ses_entry T7.
  ses_entry T8. ses_entry T9. ses_entry T10. ses_entry T11. ses_entry T12. ses_entry T13. ses_entry T14.
  ses_entry T15. ses_entry T16. ses_entry T17. ses_entry T18. ses_entry T19. ses_entry T20.
  apply Forall_nil.
Qed.

Lemma ses_entries_defl : entries G_defl.
Proof.
  pose proof ses_deflate_bodies9 as DB.
  destruct DB as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 &
                  D17 & D18 & D19 & D20 & D21 & D22 & D23 & _).
  pose proof Zlib.proof.deflate.DSpecVBody.deflate_bodyV as BV.
  unfold Zlib.proof.deflate.DSpecV.deflate_bodyV_stmt in BV.
  unfold ob_read_buf, ob_putShortMSB, ob_flush_pending, ob_slide_hash, ob_longest_match, ob_lm_init,
    ob_fill_window, ob_deflate_stored, ob_deflate_fast, ob_deflate_slow, ob_deflate_rle, ob_deflate_huff,
    ob_deflateStateCheck, ob_deflateResetKeep9, ob_deflateReset9, ob_deflateSetHeader, ob_deflateTune,
    ob_deflatePrime, ob_deflateBound_z, ob_deflateBound, ob_deflateSetDictionary, ob_deflateEnd,
    ob_deflateInit2_9 in *.
  unfold entries, G_defl.
  ses_entry D1. ses_entry D2. ses_entry D3. ses_entry D4. ses_entry D5. ses_entry D6. ses_entry D7.
  ses_entry D8. ses_entry D9. ses_entry D10. ses_entry D11. ses_entry D12. ses_entry D13. ses_entry D14.
  ses_entry D15. ses_entry D16. ses_entry D21. ses_entry D22. ses_entry D23. ses_entry BV.
  apply Forall_nil.
Qed.
