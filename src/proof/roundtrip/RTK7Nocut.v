(* The compression stage on the round trips' wide streams never ends in deflate_stored's old defect
   ([RTK7Api.comp_nocut7_stmt]): with fix F9 deflate_stored compares len with the 64-bit sum left + avail_in, so
   the wide port of the round trips' core theory (wide/roundtrip/RTDLTCore.core_compress3_w, for W3) holds
   without a guard at level 0 and the run ends as cpost says (as in RTK7Core.rtk7_core_ok). *)
From Coq Require Import ZArith List Lia.
Require Import Zlib.proof.roundtrip.RTK7Api.
Require Import Zlib.proof.wide.roundtrip.RTDLTCore.
Require Import Zlib.proof.wide.roundtrip.RTDLTCFill Zlib.proof.wide.roundtrip.RTDLTCTrees2.
Require Import Zlib.proof.wide.roundtrip.RTDLTCLm Zlib.proof.wide.roundtrip.RTDLTCSpecs2.
Require Zlib.proof.huffman.Lemmas.
Local Open Scope Z_scope.

Theorem comp_nocut7 : comp_nocut7_stmt.
Proof.
  pose proof (proj1 Zlib.proof.huffman.Lemmas.huffman_lemmas) as Hov.
  destruct (trees_ok2 Hov) as (Htal & Htf & Hroom).
  pose proof (fbo_ok_w Htf Hroom) as Hfbo. pose proof fpend2_ok_w as Hfp.
  pose proof fill_ok_w as Hfill. destruct lm_ok as [Hins Hlm].
  intros s z flush HW Ho Hq Hf Hz Hw Ha.
  exact (core_compress3_w Hfill Hins Hlm Htal Hfbo Hfp s z flush HW Ho Hq Hf Hz Hw Ha).
Qed.
