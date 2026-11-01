(* inflate_fast's body in the allocator-generic port (src/proof/za/inflate_api/Stmt.v, za_fast_stmt), for
   every allocator and adler cell: the generated body_inflate_fast5_za (src/proof/za/inffast/BodyF5.v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.inflate_api.Stmt.
Require Zlib.proof.za.inffast.BodyF5.

Lemma za_fast_proof : za_fast_stmt.
Proof.
  intros ZA ZAV Espec.
  exact (@Zlib.proof.za.inffast.BodyF5.body_inflate_fast5_za ZA ZAV Espec).
Qed.
