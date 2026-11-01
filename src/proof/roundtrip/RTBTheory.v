(* Round-trip laws, part RT-B: what compress2 needs from the deflate laws' theory (RTDIface
   rt_init_facts, rt_bound_once), pure Coq over the model, from the huffman lemmas (i) and (ii) (as
   LawTheory.law_theory). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTDIface.
Require Zlib.proof.huffman.Overlay Zlib.proof.huffman.BlockBound.
Require Zlib.proof.roundtrip.RTBProof.
Import ListNotations.
Local Open Scope Z_scope.

Theorem rt_b_facts :
  Zlib.proof.huffman.Overlay.overlay_statement -> Zlib.proof.huffman.BlockBound.block_bound_statement ->
  rt_init_facts /\ rt_bound_once.
Proof.
  exact Zlib.proof.roundtrip.RTBProof.rtb_facts.
Qed.
