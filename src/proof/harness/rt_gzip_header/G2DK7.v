(* Law rt_gzip_header on the round-2 harness: what the deflate side of the round trips (RTK7Defs.K7, the invariant
   of RTK7Proof.rt_kfacts7) says between two deflate() calls of a gzip stream with no data, needed to apply
   G2DAdler.g2_deflate_adler: the pending buffer holds bytes (and so does the gzip extra field), and in a header
   state strm->adler is the CRC-32 of header bytes so far (or 0), below 2^32. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTK7Defs.
Require Zlib.proof.huffman.Lemmas.
Require Import Zlib.proof.roundtrip.RTK7Init.
Require Import Zlib.proof.roundtrip.RTK7Head.
Require Import Zlib.proof.roundtrip.RTK7Dict.
Require Import Zlib.proof.roundtrip.RTK7Deflate.
Require Import Zlib.proof.roundtrip.RTK7Fpend.
Require Import Zlib.proof.roundtrip.RTK7Core.
Require Import Zlib.proof.roundtrip.RTK7Hdr.
Require Import Zlib.proof.roundtrip.RTK7Comp.
Require Zlib.proof.harness.rt_gzip_header.G2DAdler.
Require Zlib.proof.deflate.LTWHdrKit.
Require Zlib.proof.deflate.DetApiHdrSt.
Import ListNotations.
Local Open Scope Z_scope.

(* RTK7Proof.rt_kfacts7 for its invariant K7 itself (the theorem hides K7 behind an existential) *)
Lemma g2_kfacts7 : kfacts7 K7.
Proof.
  pose proof (proj1 Zlib.proof.huffman.Lemmas.huffman_lemmas) as Hov.
  pose proof (rtk7_core_ok Hov) as Hc.
  destruct (rtk7_comp_ok Hov) as (Hst & H1 & H2 & H3 & H4).
  apply kfacts7_of.
  - exact rtk7_init_ok.
  - exact (rtk7_dict_ok Hov Hc).
  - exact rtk7_head_ok.
  - exact (rtk7_deflate_ok Hov Hc rtk7_hdr_ok rtk7_fpend_ok Hst H1 H2 H3 H4).
Qed.

(* the header bytes of the round trips' copy of the theory are bytes *)
Lemma g2_hdr_bytes h xfl : rhdr_ok7 h -> bytes (gz_hdr_bytes (Some h) xfl).
Proof. intros H. exact (Zlib.proof.deflate.LTWHdrKit.gz_hdr_bytes_bytes_w h xfl H). Qed.

Lemma g2_k7_between O fin s tin tout adler :
  K7 [] 2 [] O fin s tin tout adler -> (forall R, fin = Some R -> R = []) ->
  Zlib.proof.deflate.DetApiHdrSt.pbq s /\
  (Zlib.proof.harness.rt_gzip_header.G2DAdler.hstat (d_status s) -> 0 <= adler < 4294967296).
Proof.
  intros [[HI _] | St] Hfin.
  2: { destruct St as (_ & R & E & NR). exfalso. exact (NR (Hfin R E)). }
  destruct HI as (_ & Out & _ & _ & _ & _ & _ & Hgz & _ & _ & _ & _ & _ & _ & _ & Ph).
  split.
  { split; [apply Out|]. intros h x E1 E2. destruct (Hgz h E1) as (_ & _ & _ & _ & _ & Hx & _).
    exact (proj2 (Hx x E2)). }
  unfold Zlib.proof.harness.rt_gzip_header.G2DAdler.hstat.
  intros Hh. destruct Ph as [P0 | (_ & [P1 | [P2 | P3]])].
  - destruct P0 as ([[Hs Hw] | [Hs _]] & _).
    + lia.
    + rewrite Hs in Hh. unfold INIT_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE, GZIP_STATE in *. lia.
  - destruct P1 as (_ & _ & _ & _ & _ & H & k & Hv & _).
    destruct Hv as (_ & h & xfl & _ & Hok & -> & _ & _ & _ & ->).
    unfold hadler. destruct (gz_hcrc h =? 0); [lia|].
    apply Zlib.proof.deflate.DetApiHdrSt.crc_adq. apply Forall_sublist. exact (g2_hdr_bytes h xfl Hok).
  - destruct P2 as (Hs & _). rewrite Hs in Hh.
    unfold INIT_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE, BUSY_STATE in *. lia.
  - destruct P3 as (Hs & _). rewrite Hs in Hh.
    unfold INIT_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE, FINISH_STATE in *. lia.
Qed.
