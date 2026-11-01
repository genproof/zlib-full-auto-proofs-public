(* RT-D part RLE: deflate_rle (specs: RTDSpecs.v / RTDK.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSpecs.
Require Import Zlib.proof.roundtrip.RTDFix Zlib.proof.roundtrip.RTDRleKit Zlib.proof.roundtrip.RTDRleGlue Zlib.proof.roundtrip.RTDRleScan Zlib.proof.roundtrip.RTDRleRefill Zlib.proof.roundtrip.RTDRleLit Zlib.proof.roundtrip.RTDRleDist Zlib.proof.roundtrip.RTDRleFbo Zlib.proof.roundtrip.RTDRleBflush Zlib.proof.roundtrip.RTDRleTail Zlib.proof.roundtrip.RTDLTCRle2.
Import ListNotations.
Local Open Scope Z_scope.

(** Interface v2 (RTDFix.v); the parts and the glue: RTDRleKit.v, RTDRleGlue.v and the RTDRle*.v part files. *)
Theorem rtd_rle_ok2 : Zlib.proof.huffman.Overlay.overlay_statement -> fill_fspec -> ins_fspec2 -> lm_fspec ->
  fpend_fspec2 -> fbo_fspec -> comp_fspec 4 c_deflate_rle.
Proof.
  intros Hov Hfill _ _ _ Hfbo.
  destruct (trees_ok2 Hov) as (Htal & Htf & Hroom).
  pose proof (fbo_ok Htf Hroom) as Hfbo0.
  pose proof (rffbo_ok Hfbo0 Hfbo) as Hfb.
  apply rle_assembly.
  - exact (rfrefill_ok Hfill).
  - exact rfscan_ok.
  - exact (rflit_ok Htal).
  - exact (rfdist_ok Htal).
  - exact (rfbflush_ok Hfbo0 Hfb).
  - exact (rftail_ok Hfbo0 Hfb).
  - exact (rrefill_ok fill_ok).
  - exact rscan_ok.
  - exact (rlit_ok Htal).
  - exact (rdist_ok Htal).
  - exact (rbflush_ok (rfbw_ok Hfbo0)).
  - exact (rle_ok2 fill_ok Htal Hfbo0 fpend2_ok).
Qed.

Theorem rtd_rle_ok : Zlib.proof.huffman.Overlay.overlay_statement -> fill_fspec -> ins_fspec -> lm_fspec -> fpend_fspec -> fbo_fspec -> comp_fspec 4 c_deflate_rle.
Proof.
  intros Hov Hfill Hins Hlm Hfp Hfbo.
  exact (rtd_rle_ok2 Hov Hfill (ins_fix Hins) Hlm (fpend_fix Hfp) Hfbo).
Qed.
