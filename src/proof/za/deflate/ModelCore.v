(** * The compression stage of deflate() for calls of up to 2^32 - 1 bytes in and out

    The model theory of the deflate laws (LTIface.core_facts, proved by LTCore.core_theory) runs the compression
    function on streams offering at most 2^30 bytes of input and of output space ([LTDefs.zin_ok]).  One
    deflate() call of the res_* laws offers up to 2^32 - 1 bytes of both.  [first_core_stmt] is
    [core_facts W] together with [cf_compress] for such calls ([zin_w1]), for the same invariant [W].

    The extra hypothesis [ub s + z_avail_in z <= 2^32 - 1] keeps deflate_stored's 32-bit sum
    [left + strm->avail_in] (deflate.c, [left] <= [ub s]) from wrapping: when it wraps, deflate_stored may end
    the stream with input left, which [cpost] excludes.  It holds in the first call after deflateInit2_
    (nothing in the window).

    Proof: [W] is LTCore's invariant [W3]; the compressors for such streams are the generated ports of the core
    theory (src/proof/wide/deflate/, docs/port-wide/port.py), assembled in LTWCore.core_compress3_w. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTIface.
Require Zlib.proof.huffman.Overlay.
Require Import Zlib.proof.deflate.LTCore Zlib.proof.deflate.LTCMisc Zlib.proof.deflate.LTCTrees2
  Zlib.proof.deflate.LTCFlushKit Zlib.proof.deflate.LTCLm.
Require Import Zlib.proof.wide.deflate.LTCSpecs2 Zlib.proof.wide.deflate.LTCFill Zlib.proof.wide.deflate.LTCStored2
  Zlib.proof.wide.deflate.LTCFast2 Zlib.proof.wide.deflate.LTCSlow2 Zlib.proof.wide.deflate.LTCHuff2
  Zlib.proof.wide.deflate.LTCRle2.
Require Zlib.proof.wide.deflate.LTCFlushKit.
Require Import Zlib.proof.deflate.LTWCore.
Import ListNotations.
Local Open Scope Z_scope.

(** A stream offering up to 2^32 - 1 bytes of input and of output space; total_in and total_out small. *)
Definition zin_w1 (z : strm) : Prop :=
  bytes (z_in z) /\ 0 <= z_next_in z /\ 0 <= z_avail_in z <= 4294967295 /\
  z_next_in z + z_avail_in z <= Zlength (z_in z) /\ 0 <= z_avail_out z <= 4294967295 /\
  0 <= z_total_in z <= 1099511627776 /\ 0 <= z_total_out z <= 1099511627776.

(** [cf_compress] of [core_facts] for such streams. *)
Definition cf_compress_w1 (W : dstate -> Prop) : Prop :=
  forall s z flush,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_w1 z -> ub s + z_avail_in z <= 4294967295 ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W s z flush s' z' bs evs.

Definition first_core_stmt : Prop :=
  Zlib.proof.huffman.Overlay.overlay_statement -> exists W, core_facts W /\ cf_compress_w1 W.

(** LTCore.core_compress3 for these streams: LTWCore.core_compress3_w, whose streams [zin_okw] include them. *)
Lemma core_compress3_w1 : fill_spec_w -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec_w -> fpend_spec2_w ->
  cf_compress_w1 W3.
Proof.
  intros Hfill Hins Hlm Htal Hfbo Hfp s z flush HW Ho Hq Hf Hz Hub Hw Ha.
  assert (Hzw : zin_okw z)
    by (destruct Hz as (B & H1 & H2 & H3 & H4 & H5 & H6); unfold zin_okw; repeat split; auto; lia).
  exact (core_compress3_w Hfill Hins Hlm Htal Hfbo Hfp s z flush HW Ho Hq Hf Hzw Hw Ha).
Qed.

Lemma first_core : first_core_stmt.
Proof.
  intros Hov. exists W3.
  destruct (trees_ok2 Hov) as (Htal & Htf & Hroom).
  pose proof (fbo_ok Htf Hroom) as Hfbo. pose proof fpend2_ok as Hfp.
  pose proof fill_ok as Hfill. destruct lm_ok as [Hins Hlm].
  split.
  - exact (Build_core_facts W3 W3_prm W3_pos W3_frame W3_init W3_tune W3_dict
             (core_compress3 Hfill Hins Hlm Htal Hfbo Hfp) (W3_still Hfill Hins Hlm Htal Hfbo Hfp)
             (core_live3 Hfp) W3_full W3_params).
  - exact (core_compress3_w1 fill_ok_w Hins Hlm Htal (Zlib.proof.wide.deflate.LTCFlushKit.fbo_ok_w Htf Hroom) fpend2_ok_w).
Qed.
