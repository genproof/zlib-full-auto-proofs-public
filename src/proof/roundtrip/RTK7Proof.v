(* rt_kfacts7: the deflate side of the round trips without the size limits of deflate_roundtrip, for the
   invariant K7 of RTK7Defs.v, from its parts: deflateInit2 (RTK7Init), deflateSetHeader (RTK7Head),
   deflateSetDictionary (RTK7Dict), deflate (RTK7Deflate) over the wide core and header theory (RTK7Core,
   RTK7Hdr), flush_pending (RTK7Fpend) and the compression functions (RTK7Comp). *)
Require Import Zlib.proof.roundtrip.RTK7.
Require Import Zlib.proof.roundtrip.RTK7Defs.
Require Zlib.proof.huffman.Lemmas.
Require Import Zlib.proof.roundtrip.RTK7Init Zlib.proof.roundtrip.RTK7Head Zlib.proof.roundtrip.RTK7Dict Zlib.proof.roundtrip.RTK7Deflate Zlib.proof.roundtrip.RTK7Fpend Zlib.proof.roundtrip.RTK7Core Zlib.proof.roundtrip.RTK7Hdr.
Require Import Zlib.proof.roundtrip.RTK7Comp.

Theorem rt_kfacts7 : rt_k7_stmt.
Proof.
  pose proof (proj1 Zlib.proof.huffman.Lemmas.huffman_lemmas) as Hov.
  pose proof (rtk7_core_ok Hov) as Hc.
  destruct (rtk7_comp_ok Hov) as (Hst & H1 & H2 & H3 & H4).
  exists K7. apply kfacts7_of.
  - exact rtk7_init_ok.
  - exact (rtk7_dict_ok Hov Hc).
  - exact rtk7_head_ok.
  - exact (rtk7_deflate_ok Hov Hc rtk7_hdr_ok rtk7_fpend_ok Hst H1 H2 H3 H4).
Qed.
