(* The bodies of updatewindow, inflateStateCheck, inflateSetDictionary, inflateInit2_, inflateResetKeep,
   inflateReset, inflateReset2 and inflateEnd in the allocator-generic port (src/proof/za/inflate_api/Stmt.v,
   za_api_stmt), for every allocator and adler cell. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.inflate_api.Stmt.
Require Zlib.proof.za.inflate.BodySmall.
Require Zlib.proof.za.inflate_api.UwZ Zlib.proof.za.inflate_api.DictZ Zlib.proof.za.inflate_api.InitZ
  Zlib.proof.za.inflate_api.EndZ Zlib.proof.za.inflate_api.ResetZ.

Lemma za_api_proof : za_api_stmt.
Proof.
  intros ZA ZAV Espec.
  destruct (@Zlib.proof.za.inflate_api.ResetZ.za_reset_proof ZA ZAV Espec) as (Hk & Hr & Hr2).
  split; [apply Zlib.proof.za.inflate_api.UwZ.za_uw_proof |].
  split; [apply Zlib.proof.za.inflate.BodySmall.body_inflateStateCheck_za |].
  split; [apply Zlib.proof.za.inflate_api.DictZ.za_dict_proof |].
  split; [apply Zlib.proof.za.inflate_api.InitZ.za_init_proof |].
  split; [exact Hk |]. split; [exact Hr |]. split; [exact Hr2 |].
  apply Zlib.proof.za.inflate_api.EndZ.za_end_proof.
Qed.
