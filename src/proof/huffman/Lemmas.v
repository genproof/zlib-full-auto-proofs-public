(** * The two lemmas of the huffman area, proved (statements in Overlay.v and BlockBound.v).

    - (i) [Overlay.overlay_statement]: at the compress_block call of _tr_flush_block the output never overtakes the
      symbols still to be read in the sym_buf overlay of pending_buf (CVE-2018-25032).
    - (ii) [BlockBound.block_bound_statement]: the per-block cost step behind the tight deflateBound / compressBound
      (memLevel 8). *)
Require Import Zlib.proof.huffman.Overlay Zlib.proof.huffman.BlockBound.
Require Zlib.proof.huffman.RepairBound Zlib.proof.huffman.TreeDD Zlib.proof.huffman.FlushDyn
        Zlib.proof.huffman.DynSum Zlib.proof.huffman.OverlayDyn Zlib.proof.huffman.BlockBoundProof.

Theorem huffman_lemmas : Overlay.overlay_statement /\ BlockBound.block_bound_statement.
Proof.
  assert (Hds : DynSum.dyn_sum_statement)
    by exact (DynSum.dyn_sum_holds FlushDyn.dyn_prep (TreeDD.tree_dd RepairBound.repair15_bound)).
  assert (Hov : Overlay.overlay_statement) by exact (OverlayDyn.overlay_proof Hds).
  split; [exact Hov|exact (BlockBoundProof.block_bound_proof Hds Hov)].
Qed.
