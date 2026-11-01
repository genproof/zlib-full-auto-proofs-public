(** * The deflateBound accounting for compress2_z's loop, closed (LawFactsC2W.c2_facts_stmt)

    LTWC2.c2_facts_of for the core invariant LTCore.W3: the wide core theory (LTWCore.core_facts_w3: the
    compression call at every level and flush, deflate_stored on the 64-bit comparisons of fix F9), the wide
    header stages (LTWHdr.hdr_theory_w), lemma (ii) of the Huffman theory (BlockBound) and the progress of the
    compression functions (LTWC2Prog.compress_progress). *)
Require Zlib.proof.deflate.LawFactsC2W.
Require Zlib.proof.deflate.LTWC2.
Require Zlib.proof.deflate.LTWC2Prog.
Require Zlib.proof.deflate.LTWCore.
Require Zlib.proof.deflate.LTWHdr.
Require Zlib.proof.huffman.Lemmas.

Theorem c2_facts_thm : Zlib.proof.deflate.LawFactsC2W.c2_facts_stmt.
Proof.
  destruct Zlib.proof.huffman.Lemmas.huffman_lemmas as [Hi Hii].
  destruct Zlib.proof.deflate.LTWHdr.hdr_theory_w as [HI HF].
  pose proof (Zlib.proof.deflate.LTWCore.core_facts_w3 Hi) as CF.
  exists (Zlib.proof.deflate.LTWC2Defs.BpreC2 Zlib.proof.deflate.LTCore.W3),
    (Zlib.proof.deflate.LTWC2Defs.BrunC2 Zlib.proof.deflate.LTCore.W3 HI).
  exact (Zlib.proof.deflate.LTWC2.c2_facts_of Zlib.proof.deflate.LTCore.W3 HI CF HF Hii
           (Zlib.proof.deflate.LTWIface.cw_compress _ CF) Zlib.proof.deflate.LTWC2Prog.compress_progress).
Qed.
