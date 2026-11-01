(** * Body proofs: send_tree, send_all_trees, compress_block, _tr_align, _tr_stored_block (bit output; the send_bits macro).

    The target: every function's body satisfies its shared specification (see Obligations.v: ob_X =
    semax_body Vprog Gprog_X f_X X_spec; specs in src/proof/trees/TSpec.v, src/proof/deflate/DSpec.v,
    src/proof/compress/CSpec.v; checked models in src/proof/trees/CModel.v, src/proof/deflate/DModel*.v).
    Prove each body as its own lemma (in this file or in new files it imports) and conclude. *)
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.trees.Body_send_tree Zlib.proof.trees.Body_send_all_trees Zlib.proof.trees.Body_compress_block
  Zlib.proof.trees.Body_tr_align Zlib.proof.trees.Body_tr_stored_block.

Theorem trees_send : ob_send_tree /\ ob_send_all_trees /\ ob_compress_block /\ ob_tr_align /\ ob_tr_stored_block.
Proof.
  unfold ob_send_tree, ob_send_all_trees, ob_compress_block, ob_tr_align, ob_tr_stored_block.
  split; [exact Body_send_tree.body_send_tree|].
  split; [exact Body_send_all_trees.body_send_all_trees|].
  split; [exact Body_compress_block.body_compress_block|].
  split; [exact Body_tr_align.body_tr_align|].
  exact Body_tr_stored_block.body_tr_stored_block.
Qed.
