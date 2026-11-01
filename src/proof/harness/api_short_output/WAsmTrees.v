(* Law api_short_output (data of any length): the entries of WAsmKit.G_trees, from the bodies of trees.c
   (Obligations.trees_bodies_ok). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.harness.api_short_output.WLawCS Zlib.proof.harness.api_short_output.WAsmKit.
#[local] Existing Instance Zlib.proof.harness.api_short_output.WLawCS.CS.

Lemma w_entries_trees : Zlib.proof.inflate_api.SpecWLib.specw_bridge_stmt -> trees_bodies_ok ->
  w_entries G_trees.
Proof.
  intros BR TB. unfold w_entries, G_trees.
  destruct TB as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 &
                  T17 & T18 & T19 & T20).
  unfold ob_bi_reverse, ob_bi_flush, ob_bi_windup, ob_tr_flush_bits, ob_tr_align, ob_tr_stored_block,
    ob_gen_codes, ob_pqdownheap, ob_gen_bitlen, ob_build_tree, ob_scan_tree, ob_build_bl_tree,
    ob_detect_data_type, ob_init_block, ob_send_tree, ob_send_all_trees, ob_compress_block, ob_tr_static_init,
    ob_tr_init, ob_tr_flush_block in *.
  w_entry T1 BR. w_entry T2 BR. w_entry T3 BR. w_entry T4 BR. w_entry T5 BR. w_entry T6 BR.
  w_entry T7 BR. w_entry T8 BR. w_entry T9 BR. w_entry T10 BR. w_entry T11 BR. w_entry T12 BR.
  w_entry T13 BR. w_entry T14 BR. w_entry T15 BR. w_entry T16 BR. w_entry T17 BR. w_entry T18 BR.
  w_entry T19 BR. w_entry T20 BR.
  apply Forall_nil.
Qed.
