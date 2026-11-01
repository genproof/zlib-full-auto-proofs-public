(* inflate()'s body in the allocator-generic port (src/proof/za/inflate_api/Stmt.v, za_body_inflate_stmt):
   from the switch cases and the preservation of the two invariants, for every allocator and adler cell. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.inflate_api.Stmt.
(* the generated port of Body5_inflate.v (docs/port-za/inflate/body.py) *)
Require Zlib.proof.za.inflate_api.Body5_inflate.

Lemma za_body_inflate_proof : za_body_inflate_stmt.
Proof.
  intros ZA ZAV. exact (@Zlib.proof.za.inflate_api.Body5_inflate.body_inflate_proof5_za ZA ZAV).
Qed.
