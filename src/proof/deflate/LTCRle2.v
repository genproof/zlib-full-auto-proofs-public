(** * Core part of the deflate law theory: deflate_rle, against the corrected specs of LTCSpecs2.v.
    With LTCSpecs2.tally_spec_2 / fpend_spec_2 it also holds under the original specifications of
    LTCSpecs.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCSpecs2.
Require Import Zlib.proof.deflate.LTCRleGlue Zlib.proof.deflate.LTCRleRefill Zlib.proof.deflate.LTCRleScan
  Zlib.proof.deflate.LTCRleLit Zlib.proof.deflate.LTCRleDist Zlib.proof.deflate.LTCRleFbw
  Zlib.proof.deflate.LTCRleBflush Zlib.proof.deflate.LTCRleTail.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem rle_ok2 : fill_spec -> tally_spec2 -> fbo_spec -> fpend_spec2 -> rle_spec.
Proof.
  intros Hfill Htal Hfbo _.
  pose proof (rfbw_ok Hfbo) as Hfbw.
  apply rle_from_parts.
  - exact (rrefill_ok Hfill).
  - exact rscan_ok.
  - exact (rlit_ok Htal).
  - exact (rdist_ok Htal).
  - exact (rbflush_ok Hfbw).
  - exact (rtail_ok Hfbw).
Qed.
