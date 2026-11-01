(* Round-trip laws, part RT-D: the deflate side.  An invariant K of the deflate runs of the
   harnesses, preserved by every call, giving RTFinal.dfinal at Z_STREAM_END (RTDIface.kfacts).  Hypothesis: the huffman area's lemma (i) (sym_buf / pending_buf overlay), proved separately
   and discharged by RoundTrips (it is a hypothesis of roundtrip_laws). *)
Require Import Zlib.proof.roundtrip.RTDIface.
Require Zlib.proof.huffman.Overlay.
Require Import Zlib.proof.roundtrip.RTDV3.
Require Import Zlib.proof.roundtrip.RTDWriter Zlib.proof.roundtrip.RTDFlush2 Zlib.proof.roundtrip.RTDFill Zlib.proof.roundtrip.RTDLm2 Zlib.proof.roundtrip.RTDFbo2 Zlib.proof.roundtrip.RTDStored2 Zlib.proof.roundtrip.RTDFast Zlib.proof.roundtrip.RTDSlow3 Zlib.proof.roundtrip.RTDHuff Zlib.proof.roundtrip.RTDRle Zlib.proof.roundtrip.RTDDeflate3 Zlib.proof.roundtrip.RTDDict3 Zlib.proof.roundtrip.RTDPM3.

Theorem rt_kfacts : Zlib.proof.huffman.Overlay.overlay_statement -> exists K, kfacts K.
Proof.
  intros Hov. exists Krt3.
  destruct rtd_writer_ok as (Hw & Hst & Hal).
  pose proof (rtd_flush_ok2 Hov Hw Hst) as Hfb.
  pose proof rtd_fill_ok as Hfill. destruct rtd_lm_ok2 as [Hins Hlm].
  destruct (rtd_fbo_ok2 Hov Hw Hfb) as [Hfp Hfbo].
  pose proof (rtd_stored_ok2 Hov Hw Hst Hfp) as C0.
  pose proof (rtd_fast_ok2 Hov Hfill Hins Hlm Hfp Hfbo) as C1.
  pose proof (rtd_slow_ok3 Hov Hfill Hins Hlm Hfp Hfbo) as C2.
  pose proof (rtd_huff_ok2 Hov Hfill Hins Hlm Hfp Hfbo) as C3.
  pose proof (rtd_rle_ok2 Hov Hfill Hins Hlm Hfp Hfbo) as C4.
  destruct (comp_fix3_all Hov C0 C1 C3 C4) as (D0 & D1 & D3 & D4).
  pose proof (rtd_deflate_ok3 Hov Hw Hst Hal Hfp D0 D1 C2 D3 D4) as Hd.
  destruct (rtd_pm3_ok Hov) as (Hp & Hi & Ht & Hh).
  apply kfacts_of; auto.
  exact (rtd_dict_ok3 Hov Hfill Hins).
Qed.
