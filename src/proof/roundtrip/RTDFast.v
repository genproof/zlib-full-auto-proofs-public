(* RT-D part FAST: deflate_fast (specs: RTDSpecs.v / RTDK.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSpecs.
Require Import Zlib.proof.roundtrip.RTDFix Zlib.proof.roundtrip.RTDFastGlue.
Require Import Zlib.proof.roundtrip.RTDFastRefill Zlib.proof.roundtrip.RTDFastSearch Zlib.proof.roundtrip.RTDFastLit Zlib.proof.roundtrip.RTDFastMatch Zlib.proof.roundtrip.RTDFastBflush Zlib.proof.roundtrip.RTDFastTail.
Import ListNotations.
Local Open Scope Z_scope.

(* interface v2 (RTDFix.v): the corrected ins_fspec2 / fpend_fspec2 *)
Theorem rtd_fast_ok2 : Zlib.proof.huffman.Overlay.overlay_statement -> fill_fspec -> ins_fspec2 -> lm_fspec ->
  fpend_fspec2 -> fbo_fspec -> comp_fspec 1 c_deflate_fast.
Proof.
  intros Hov Hfill Hins Hlm _ Hfbo.
  exact (fast_from_fparts Hov Hfill Hins Hlm Hfbo frefill_ok fsearch_ok flit_ok fmatch_ok fbflush_ok ftail_ok).
Qed.

Theorem rtd_fast_ok : Zlib.proof.huffman.Overlay.overlay_statement -> fill_fspec -> ins_fspec -> lm_fspec -> fpend_fspec -> fbo_fspec -> comp_fspec 1 c_deflate_fast.
Proof.
  intros Hov Hfill Hins Hlm Hfp Hfbo.
  exact (rtd_fast_ok2 Hov Hfill (ins_fix Hins) Hlm (fpend_fix Hfp) Hfbo).
Qed.
