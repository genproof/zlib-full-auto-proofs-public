(** * Body proofs: gen_codes, pqdownheap, gen_bitlen, build_tree (trees.c's Huffman tree construction).

    The target: every function's body satisfies its shared specification (see Obligations.v: ob_X =
    semax_body Vprog Gprog_X f_X X_spec; specs in src/proof/trees/TSpec.v, src/proof/deflate/DSpec.v,
    src/proof/compress/CSpec.v; checked models in src/proof/trees/CModel.v, src/proof/deflate/DModel*.v).
    Prove each body as its own lemma (in this file or in new files it imports) and conclude. *)
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.trees.Body_gen_codes Zlib.proof.trees.Body_pqdownheap Zlib.proof.trees.Body_gen_bitlen
  Zlib.proof.trees.Body_build_tree.

Theorem trees_build : ob_gen_codes /\ ob_pqdownheap /\ ob_gen_bitlen /\ ob_build_tree.
Proof.
  unfold ob_gen_codes, ob_pqdownheap, ob_gen_bitlen, ob_build_tree.
  split; [exact Body_gen_codes.body_gen_codes|]. split; [exact Body_pqdownheap.body_pqdownheap|].
  split; [exact Body_gen_bitlen.body_gen_bitlen|]. exact Body_build_tree.body_build_tree.
Qed.
