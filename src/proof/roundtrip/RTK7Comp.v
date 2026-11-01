(* deflate_stored, deflate_fast, deflate_slow, deflate_huff and deflate_rle on streams of any size
   (RTK7Defs.comp_fspec7 0 .. 4), from the generated wide port of the round-trip theory (src/proof/wide/roundtrip/, docs/port-wide/cfg_rtd.py). *)
From Coq Require Import ZArith.
Require Import Zlib.proof.roundtrip.RTK7Defs.
Require Zlib.proof.roundtrip.RTDWriter Zlib.proof.roundtrip.RTDFlush2.
Require Zlib.proof.wide.roundtrip.RTDV3 Zlib.proof.wide.roundtrip.RTDStored2 Zlib.proof.wide.roundtrip.RTDFill Zlib.proof.wide.roundtrip.RTDLm2
  Zlib.proof.wide.roundtrip.RTDFbo2 Zlib.proof.wide.roundtrip.RTDFast Zlib.proof.wide.roundtrip.RTDSlow3
  Zlib.proof.wide.roundtrip.RTDHuff Zlib.proof.wide.roundtrip.RTDRle.
Local Open Scope Z_scope.

(* the wide functional specification of a compression function (the stream of RTDLTDefs.zin_ok_w, the same as
   zin_ok7) is the left disjunct of comp_fspec7 *)
Lemma comp_fspec7_of_w f c : Zlib.proof.wide.roundtrip.RTDV3.comp_fspec3_w f c -> comp_fspec7 f c.
Proof.
  intros H s z flush s' z' bs dict D BS syms p HW Ho Hq Hfl Hz Hw Ha Hfn Hdi HD HK Hp Hp8 R.
  left. exact (H s z flush s' z' bs dict D BS syms p HW Ho Hq Hfl Hz Hw Ha Hfn Hdi HD HK Hp Hp8 R).
Qed.

Theorem rtk7_comp_ok : Zlib.proof.huffman.Overlay.overlay_statement ->
  comp_fspec7 0 c_deflate_stored /\ comp_fspec7 1 c_deflate_fast /\ comp_fspec7 2 c_deflate_slow /\ comp_fspec7 3 c_deflate_huff /\
  comp_fspec7 4 c_deflate_rle.
Proof.
  intros Hov.
  destruct Zlib.proof.roundtrip.RTDWriter.rtd_writer_ok as (Hw & Hst & _).
  pose proof (Zlib.proof.roundtrip.RTDFlush2.rtd_flush_ok2 Hov Hw Hst) as Hfb.
  pose proof Zlib.proof.wide.roundtrip.RTDFill.rtd_fill_ok_w as Hfill.
  destruct Zlib.proof.wide.roundtrip.RTDLm2.rtd_lm_ok2_w as [Hins Hlm].
  destruct (Zlib.proof.wide.roundtrip.RTDFbo2.rtd_fbo_ok2_w Hov Hw Hfb) as [Hfp Hfbo].
  pose proof (Zlib.proof.wide.roundtrip.RTDStored2.rtd_stored_ok2_w Hov Hw Hst Hfp) as C0.
  pose proof (Zlib.proof.wide.roundtrip.RTDFast.rtd_fast_ok2_w Hov Hfill Hins Hlm Hfp Hfbo) as C1.
  pose proof (Zlib.proof.wide.roundtrip.RTDSlow3.rtd_slow_ok3_w Hov Hfill Hins Hlm Hfp Hfbo) as C2.
  pose proof (Zlib.proof.wide.roundtrip.RTDHuff.rtd_huff_ok2_w Hov Hfill Hins Hlm Hfp Hfbo) as C3.
  pose proof (Zlib.proof.wide.roundtrip.RTDRle.rtd_rle_ok2_w Hov Hfill Hins Hlm Hfp Hfbo) as C4.
  destruct (Zlib.proof.wide.roundtrip.RTDV3.comp_fix3_all_w Hov C0 C1 C3 C4) as (D0 & D1 & D3 & D4).
  split; [|split; [|split; [|split]]]; apply comp_fspec7_of_w; assumption.
Qed.
