(* RT-D part HUFF: deflate_huff (specs: RTDSpecs.v / RTDK.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSpecs.
Import ListNotations.
Local Open Scope Z_scope.

Require Zlib.proof.roundtrip.RTDFix Zlib.proof.roundtrip.RTDHuffAsm Zlib.proof.roundtrip.RTDHuffLit Zlib.proof.roundtrip.RTDHuffFlush Zlib.proof.roundtrip.RTDHuffRefill Zlib.proof.roundtrip.RTDLTCTrees2 Zlib.proof.roundtrip.RTDLTCFlushKit Zlib.proof.roundtrip.RTDLTCFill Zlib.proof.roundtrip.RTDLTCHuffRefill Zlib.proof.roundtrip.RTDLTCHuffFbw Zlib.proof.roundtrip.RTDLTCHuffBflush Zlib.proof.roundtrip.RTDLTCHuffTail.

(* deflate_huff against the corrected interface v2 (RTDFix.v): the assembly RTDHuffAsm.huff_fasm of the
   functional parts (RTDHuffLit / RTDHuffFlush / RTDHuffRefill) and the deflate laws' safety parts *)
Theorem rtd_huff_ok2 : Zlib.proof.huffman.Overlay.overlay_statement -> fill_fspec ->
  Zlib.proof.roundtrip.RTDFix.ins_fspec2 -> lm_fspec -> Zlib.proof.roundtrip.RTDFix.fpend_fspec2 -> fbo_fspec ->
  comp_fspec 3 c_deflate_huff.
Proof.
  intros Hov Hfill _ _ _ Hfbo.
  destruct (Zlib.proof.roundtrip.RTDLTCTrees2.trees_ok2 Hov) as (Htal & Htf & Hroom).
  pose proof (Zlib.proof.roundtrip.RTDLTCFlushKit.fbo_ok Htf Hroom) as Hfbo0.
  pose proof Zlib.proof.roundtrip.RTDLTCFill.fill_ok as Hfill0.
  pose proof (Zlib.proof.roundtrip.RTDLTCHuffFbw.hfbw_ok Hfbo0) as Hfbw.
  exact (Zlib.proof.roundtrip.RTDHuffAsm.huff_fasm
           (Zlib.proof.roundtrip.RTDLTCHuffRefill.hrefill_ok Hfill0)
           (Zlib.proof.roundtrip.RTDLTCHuffBflush.hbflush_ok Hfbw)
           (Zlib.proof.roundtrip.RTDLTCHuffTail.htail_ok Hfbw)
           (Zlib.proof.roundtrip.RTDHuffLit.hflit_ok Htal)
           (Zlib.proof.roundtrip.RTDHuffFlush.hfflush_ok Hfbo0 Hfbo)
           (Zlib.proof.roundtrip.RTDHuffRefill.hfrefill_ok Hfill0 Hfill)).
Qed.

Theorem rtd_huff_ok : Zlib.proof.huffman.Overlay.overlay_statement -> fill_fspec -> ins_fspec -> lm_fspec -> fpend_fspec -> fbo_fspec -> comp_fspec 3 c_deflate_huff.
Proof.
  intros Hov Hfill Hins Hlm Hfp Hfbo.
  exact (rtd_huff_ok2 Hov Hfill (Zlib.proof.roundtrip.RTDFix.ins_fix Hins) Hlm
           (Zlib.proof.roundtrip.RTDFix.fpend_fix Hfp) Hfbo).
Qed.
