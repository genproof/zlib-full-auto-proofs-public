(* Laws rt_dictionary and api_dict_id, main (DWKit.v): statements 0-12 (rt_dictionary; 0-11 in api_dict_id), the
   draws of dict_len, data_len, dict, data, their NULL test, the copies (copy_of), out and the four ints, and the
   second NULL test (PRE0 -> A10 with the copies, DWKit.F_drt / F_dai), in each program's context. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
Require Import Zlib.proof.harness.dictionary_w.DWSegIn1.
Require Import Zlib.proof.harness.dictionary_w.DWSegInDrt.
Require Import Zlib.proof.harness.dictionary_w.DWSegInDai.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

Lemma seg_in_ok : seg_in_drt_stmt /\ seg_in_dai_stmt.
(* each program's segment is proved in its own file (DWSegInDrt.v, DWSegInDai.v) *)
Proof.
  split; [exact seg_in_drt_ok | exact seg_in_dai_ok].
Qed.
