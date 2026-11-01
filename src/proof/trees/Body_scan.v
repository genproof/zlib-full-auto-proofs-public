(** * Body proofs: scan_tree, build_bl_tree, detect_data_type, init_block, tr_static_init, _tr_init.

    The target: every function's body satisfies its shared specification (see Obligations.v: ob_X =
    semax_body Vprog Gprog_X f_X X_spec; specs in src/proof/trees/TSpec.v, src/proof/deflate/DSpec.v,
    src/proof/compress/CSpec.v; checked models in src/proof/trees/CModel.v, src/proof/deflate/DModel*.v).
    Prove each body as its own lemma (in this file or in new files it imports) and conclude. *)
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.trees.Body_scan_tree Zlib.proof.trees.Body_build_bl_tree Zlib.proof.trees.Body_detect
  Zlib.proof.trees.Body_init.

Theorem trees_scan : ob_scan_tree /\ ob_build_bl_tree /\ ob_detect_data_type /\ ob_init_block /\ ob_tr_static_init /\ ob_tr_init.
Proof.
  unfold ob_scan_tree, ob_build_bl_tree, ob_detect_data_type, ob_init_block, ob_tr_static_init, ob_tr_init.
  split; [exact Body_scan_tree.body_scan_tree|].
  split; [exact Body_build_bl_tree.body_build_bl_tree|].
  split; [exact Body_detect.body_detect_data_type|].
  split; [exact Body_init.body_init_block|].
  split; [exact Body_init.body_tr_static_init|].
  exact Body_init.body_tr_init.
Qed.
