(** * deflate's body against DSpecV.deflate_specV ([DSpecV.deflate_bodyV_stmt]) *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DSpecV.
Require Import Zlib.proof.deflate.MainDeflateV.

(** MainDeflate's assembly of the stages with DSpecV's witness (MainDeflateV, StageEntryV). *)
Theorem deflate_bodyV : deflate_bodyV_stmt.
Proof.
  exact body_deflateV.
Qed.
