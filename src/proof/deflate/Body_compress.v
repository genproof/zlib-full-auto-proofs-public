(** * Body proofs: deflate_fast, deflate_slow, deflate_rle, deflate_huff.

    The target: every function's body satisfies its shared specification (see Obligations.v: ob_X =
    semax_body Vprog Gprog_X f_X X_spec; specs in src/proof/trees/TSpec.v, src/proof/deflate/DSpec.v,
    src/proof/compress/CSpec.v; checked models in src/proof/trees/CModel.v, src/proof/deflate/DModel*.v).
    Prove each body as its own lemma (in this file or in new files it imports) and conclude. *)
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.Body_fast Zlib.proof.deflate.Body_slow Zlib.proof.deflate.Body_rle
  Zlib.proof.deflate.Body_huff.

Theorem deflate_compress : ob_deflate_fast /\ ob_deflate_slow /\ ob_deflate_rle /\ ob_deflate_huff.
Proof.
  split; [exact body_deflate_fast|]. split; [exact body_deflate_slow|]. split; [exact body_deflate_rle|].
  exact body_deflate_huff.
Qed.
