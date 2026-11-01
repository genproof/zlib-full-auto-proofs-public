(* RTK7Defs.core_facts7 W3 when the compression functions end as LTDefs.cpost says (RTK7Api.comp_nocut7_stmt,
   which fix F9 makes true): RTK7Core.rtk7_core_ok without its case of deflate_stored's old 32-bit sum, so
   without the proofs of deflate_stored over that sum (RTK7Stored). *)
Require Import Zlib.proof.roundtrip.RTK7Defs.
From Coq Require Import ZArith List Lia.
Require Import Zlib.proof.roundtrip.RTK7Core.
Require Import Zlib.proof.wide.roundtrip.RTDLTCore.
Require Import Zlib.proof.wide.roundtrip.RTDLTCFill Zlib.proof.wide.roundtrip.RTDLTCTrees2.
Require Import Zlib.proof.wide.roundtrip.RTDLTCLm Zlib.proof.wide.roundtrip.RTDLTCSpecs2.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rtk7_core_nocut : Zlib.proof.huffman.Overlay.overlay_statement ->
  (forall s z flush,
    W3 s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_ok7 z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W3 s z flush s' z' bs evs) ->
  core_facts7 W3.
Proof.
  intros Hov CN.
  destruct (trees_ok2 Hov) as (Htal & Htf & Hroom).
  pose proof (fbo_ok_w Htf Hroom) as Hfbo. pose proof fpend2_ok_w as Hfp.
  pose proof fill_ok_w as Hfill. destruct lm_ok as [Hins Hlm].
  constructor.
  - exact W3_prm.
  - exact W3_pos.
  - exact W3_frame.
  - exact rtk7_dict.
  - intros s z flush HW Ho Hq Hf Hz Hw Ha.
    destruct (CN s z flush HW Ho Hq Hf Hz Hw Ha) as (s' & z' & bs & evs & E & P).
    exists s', z', bs, evs. split; [exact E|left; exact P].
  - exact (W3_still_w Hfill Hins Hlm Htal Hfbo Hfp).
  - exact W3_full.
Qed.
