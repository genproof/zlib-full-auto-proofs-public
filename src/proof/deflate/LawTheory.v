(** * The model theory of the three deflate laws

    [law_theory]: from lemma (i) (the sym_buf / pending_buf overlay) and lemma (ii) (the per-block cost step at
    memLevel 8) of the huffman area, the facts the harness mains need (LawFacts.v), for invariants chosen
    here: [api_facts] (deflate_api: memory safety of every call (the checked runs are Some), return codes,
    counters, the Adler-32 / CRC-32 of the data, the zlib / gzip header and trailer, the behaviour after
    Z_STREAM_END) and [bound_facts] (deflate_bound, deflate_bound_split: deflateBound bounds the output for
    every accepted parameter set). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LawFacts.
Require Zlib.proof.huffman.Overlay Zlib.proof.huffman.BlockBound.
Require Zlib.proof.deflate.LTCore Zlib.proof.deflate.LTHdr Zlib.proof.deflate.LTApi Zlib.proof.deflate.LTBound.
Import ListNotations.
Local Open Scope Z_scope.

Theorem law_theory :
  Zlib.proof.huffman.Overlay.overlay_statement -> Zlib.proof.huffman.BlockBound.block_bound_statement ->
  (exists I Iend, api_facts I Iend) /\ (exists Bpre Brun, bound_facts Bpre Brun).
Proof.
  intros Hov Hbb.
  destruct (Zlib.proof.deflate.LTCore.core_theory Hov) as [W HW].
  destruct Zlib.proof.deflate.LTHdr.hdr_theory as [HI HH].
  split.
  - exact (Zlib.proof.deflate.LTApi.api_theory W HI HW HH).
  - exact (Zlib.proof.deflate.LTBound.bound_theory Hbb W HI HW HH).
Qed.
