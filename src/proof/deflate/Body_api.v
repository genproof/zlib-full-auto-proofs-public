(** * Body proofs: deflateResetKeep, deflateReset, deflateSetHeader, deflateTune, deflatePrime, deflateBound_z, deflateBound, deflateSetDictionary, deflateEnd, deflateInit2_, and compress.c's compressBound_z, compressBound; and the conversion ob_dstream_to_end.

    The target: every function's body satisfies its shared specification (see Obligations.v: ob_X =
    semax_body Vprog Gprog_X f_X X_spec; specs in src/proof/trees/TSpec.v, src/proof/deflate/DSpec.v,
    src/proof/compress/CSpec.v; checked models in src/proof/trees/CModel.v, src/proof/deflate/DModel*.v).
    Prove each body as its own lemma (in this file or in new files it imports) and conclude. *)
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.Api_bound Zlib.proof.deflate.Api_simple Zlib.proof.deflate.Api_prime
  Zlib.proof.deflate.Api_boundz Zlib.proof.deflate.Api_resetkeep Zlib.proof.deflate.Api_reset
  Zlib.proof.deflate.Api_end Zlib.proof.deflate.Api_dict Zlib.proof.deflate.Api_init Zlib.proof.deflate.Api_toend.

Theorem deflate_api_bodies : ob_deflateResetKeep /\ ob_deflateReset /\ ob_deflateSetHeader /\ ob_deflateTune /\ ob_deflatePrime /\ ob_deflateBound_z /\ ob_deflateBound /\ ob_deflateSetDictionary /\ ob_deflateEnd /\ ob_deflateInit2_ /\ ob_compressBound_z /\ ob_compressBound /\ ob_dstream_to_end.
Proof.
  repeat match goal with |- _ /\ _ => split end.
  - exact body_deflateResetKeep.
  - exact body_deflateReset.
  - exact body_deflateSetHeader.
  - exact body_deflateTune.
  - exact body_deflatePrime.
  - exact body_deflateBound_z.
  - exact body_deflateBound.
  - exact body_deflateSetDictionary.
  - exact body_deflateEnd.
  - exact body_deflateInit2_.
  - exact body_compressBound_z.
  - exact body_compressBound.
  - exact dstream_to_end.
Qed.
