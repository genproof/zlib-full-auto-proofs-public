(** * Body proofs: fill_window, longest_match.

    The target: every function's body satisfies its shared specification (see Obligations.v: ob_X =
    semax_body Vprog Gprog_X f_X X_spec; specs in src/proof/trees/TSpec.v, src/proof/deflate/DSpec.v,
    src/proof/compress/CSpec.v; checked models in src/proof/trees/CModel.v, src/proof/deflate/DModel*.v).
    Prove each body as its own lemma (in this file or in new files it imports) and conclude. *)
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.Body_fill_window.
Require Import Zlib.proof.deflate.Body_longest_match.

Theorem deflate_window : ob_fill_window /\ ob_longest_match.
Proof.
  split; [exact body_fill_window | exact body_longest_match].
Qed.
