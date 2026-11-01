(* deflateInit2_ and deflateEnd with a caller-supplied allocator (ZSpec.v), and the conversion of a live
   stream into what deflateEnd needs. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.deflate.Stmt.
Require Zlib.proof.za.deflate.InitZ Zlib.proof.za.deflate.EndZ.

(* The bodies are proved in InitZ.v (deflateInit2_) and EndZ.v (deflateEnd, and a live stream as deflateEnd's
   precondition). *)
Lemma za_deflate_api : za_deflate_api_stmt /\ za_dstream_end_stmt.
Proof.
  split.
  - intros ZA. split.
    + apply Zlib.proof.za.deflate.InitZ.body_za_deflateInit2_.
    + apply Zlib.proof.za.deflate.EndZ.body_za_deflateEnd.
  - apply Zlib.proof.za.deflate.EndZ.za_dstream_end_proof.
Qed.
