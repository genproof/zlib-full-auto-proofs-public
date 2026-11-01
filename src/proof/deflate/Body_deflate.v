(** * Body proofs: deflate (the state machine), deflateParams.

    The target: every function's body satisfies its shared specification (see Obligations.v: ob_X =
    semax_body Vprog Gprog_X f_X X_spec; specs in src/proof/trees/TSpec.v, src/proof/deflate/DSpec.v,
    src/proof/compress/CSpec.v; checked models in src/proof/trees/CModel.v, src/proof/deflate/DModel*.v).
    Prove each body as its own lemma (in this file or in new files it imports) and conclude. *)
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.MainDeflate Zlib.proof.deflate.DeflateParams8.

Theorem deflate_main_bodies : ob_deflate /\ ob_deflateParams.
Proof.
  exact (conj body_deflate body_deflateParams).
Qed.
