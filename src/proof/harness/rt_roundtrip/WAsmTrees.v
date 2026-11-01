(* Law rt_roundtrip (data of any length): the entries of WAsmKit.G_trees, from the bodies of trees.c
   (Obligations.trees_bodies_ok), by clip_streams/Asm.v's entry tactic for them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.Obligations9.
Require Zlib.proof.inflate_api.SpecWLib.
Require Zlib.proof.harness.clip_streams.Asm.
Require Import Zlib.proof.harness.rt_roundtrip.WCS.
Require Import Zlib.proof.harness.rt_roundtrip.WAsmKit.
#[local] Existing Instance Zlib.proof.harness.rt_roundtrip.WCS.CS.

Lemma w_entries_trees : Zlib.proof.inflate_api.SpecWLib.specw_bridge_stmt -> trees_bodies_ok ->
  w_entries G_trees.
Proof.
  intros BR TB. unfold w_entries, G_trees.
  Zlib.proof.harness.clip_streams.Asm.clip_trees_entries BR TB.
  apply Forall_nil.
Qed.
