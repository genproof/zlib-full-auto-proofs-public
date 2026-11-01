(** * Core part of the deflate law theory: deflate_huff, against the corrected specs of RTDLTCSpecs2.v.
    With RTDLTCSpecs2.tally_spec_2 / fpend_spec_2 it also holds under the original specifications of
    RTDLTCSpecs.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCSpecs2.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Require Zlib.proof.roundtrip.RTDLTCHuffLoop Zlib.proof.roundtrip.RTDLTCHuffFbw Zlib.proof.roundtrip.RTDLTCHuffLit Zlib.proof.roundtrip.RTDLTCHuffRefill Zlib.proof.roundtrip.RTDLTCHuffBflush Zlib.proof.roundtrip.RTDLTCHuffTail.
Import Zlib.proof.roundtrip.RTDLTCHuffKit.

(** deflate_huff over [W /\ huff_extra]: [huff_spec] over [W] alone is not provable, see RTDLTCHuffKit.v
    (a huff state of [W] may hold pending matches; a block then reaches 65536 bytes with block_start >= 0). *)
Theorem huff_okX : fill_spec -> tally_spec2 -> fbo_spec -> huff_specX.
Proof.
  intros Hfill Htally Hfbo.
  assert (Hfbw := RTDLTCHuffFbw.hfbw_ok Hfbo).
  exact (RTDLTCHuffLoop.huff_assembly (RTDLTCHuffLit.hlit_ok Htally) (RTDLTCHuffRefill.hrefill_ok Hfill)
           (RTDLTCHuffBflush.hbflush_ok Hfbw) (RTDLTCHuffTail.htail_ok Hfbw)).
Qed.
