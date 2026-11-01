(* Laws rt_dictionary and api_dict_id, main (DWKit.v): statement 21 (rt_dictionary's numbers; 20 in api_dict_id), the do-while of deflate() calls (LI -> LB, DWFacts.dw_call), in each program's context (the temporaries of the loads of next_in / next_out differ). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
Require Zlib.proof.harness.dictionary_w.DWSegLoopDrt.
Require Zlib.proof.harness.dictionary_w.DWSegLoopDai.
#[local] Existing Instance CS.CS.

Lemma seg_loop_ok : seg_loop_drt_stmt /\ seg_loop_dai_stmt.
Proof.
  split; [ exact DWSegLoopDrt.seg_loop_drt_ok | exact DWSegLoopDai.seg_loop_dai_ok ].
Qed.
