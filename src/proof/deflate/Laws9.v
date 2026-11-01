(** * The three laws of the deflate area from the v9 body obligations

    As Laws.deflate_laws, with Obligations9.deflate_bodies_ok9 (deflateResetKeep, deflateReset, deflateInit2_
    against the v9 specs of DSpec9.v; the laws' main contexts use those specs). *)
Require Import QuickProof.Contract.
Require Zlib.contracts.x_deflate_api Zlib.contracts.x_deflate_bound Zlib.contracts.x_deflate_bound_split.
Require Import Zlib.proof.deflate.Obligations9.
Require Zlib.proof.huffman.Overlay Zlib.proof.huffman.BlockBound.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LawTheory.
Require Import Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.MainApi Zlib.proof.deflate.MainBound Zlib.proof.deflate.MainSplit.

Theorem deflate_laws9 :
  trees_bodies_ok -> deflate_bodies_ok9 ->
  Zlib.proof.huffman.Overlay.overlay_statement -> Zlib.proof.huffman.BlockBound.block_bound_statement ->
  harness_safe Zlib.contracts.x_deflate_api.whole_prog /\
  harness_safe Zlib.contracts.x_deflate_bound.whole_prog /\
  harness_safe Zlib.contracts.x_deflate_bound_split.whole_prog.
Proof.
  intros T D O B.
  destruct (law_theory O B) as [A Bd].
  pose proof harness_lib_bodies as H. pose proof deflate_globals_init as G.
  split; [|split].
  - apply deflate_api_law; assumption.
  - apply deflate_bound_law; assumption.
  - apply deflate_bound_split_law; assumption.
Qed.
