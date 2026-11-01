(** * Core part of the deflate law theory: deflate_huff, against the corrected specs of LTCSpecs2.v.
    With LTCSpecs2.tally_spec_2 / fpend_spec_2 it also holds under the original specifications of
    LTCSpecs.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCSpecs2.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Require Zlib.proof.deflate.LTCHuffLoop Zlib.proof.deflate.LTCHuffFbw Zlib.proof.deflate.LTCHuffLit
  Zlib.proof.deflate.LTCHuffRefill Zlib.proof.deflate.LTCHuffBflush Zlib.proof.deflate.LTCHuffTail.
Import Zlib.proof.deflate.LTCHuffKit.

(** deflate_huff over [W /\ huff_extra]: [huff_spec] over [W] alone is not provable, see LTCHuffKit.v
    (a huff state of [W] may hold pending matches; a block then reaches 65536 bytes with block_start >= 0). *)
Theorem huff_okX : fill_spec -> tally_spec2 -> fbo_spec -> huff_specX.
Proof.
  intros Hfill Htally Hfbo.
  assert (Hfbw := LTCHuffFbw.hfbw_ok Hfbo).
  exact (LTCHuffLoop.huff_assembly (LTCHuffLit.hlit_ok Htally) (LTCHuffRefill.hrefill_ok Hfill)
           (LTCHuffBflush.hbflush_ok Hfbw) (LTCHuffTail.htail_ok Hfbw)).
Qed.
