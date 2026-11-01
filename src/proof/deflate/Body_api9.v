(** * The v9 bodies of deflateResetKeep, deflateReset, deflateInit2_ (specs DSpec9.v; the v8 proofs are in
      Api_resetkeep.v, Api_reset.v, Api_init.v against DSpec's specs) *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.Obligations9.
Require Zlib.proof.deflate.Api_resetkeep9 Zlib.proof.deflate.Api_reset9 Zlib.proof.deflate.Api_init9.

Theorem deflate_api_bodies9 : ob_deflateResetKeep9 /\ ob_deflateReset9 /\ ob_deflateInit2_9.
Proof.
  exact (conj Api_resetkeep9.body_deflateResetKeep9
          (conj Api_reset9.body_deflateReset9 Api_init9.body_deflateInit2_9)).
Qed.
