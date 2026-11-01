(** * deflate_slow with up to 2^32 - 1 bytes of output space

    LTCSlow2.slow_ok2 and LTCStillSlow.still_slow_ok for [compress_pre2w] (DetCoreKit.v) instead of
    [compress_pre2].  The port is DetCoreSlowInv.v (the invariant), DetCoreSlow<Part>.v (the parts),
    DetCoreSlowLoop.v (the loop) and DetCoreSlowStill.v (cf_still). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetCoreKit.
Require Import Zlib.proof.deflate.DetCoreSlowLoop Zlib.proof.deflate.DetCoreSlowStill.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem slow_wide_ok :
  (fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec -> fpend_spec2 -> slow_spec2w) /\
  (fill_idem_spec -> fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec -> fpend_spec2 ->
   forall s z flush, compress_pre2w s z flush -> still_at s -> fn_of s = 2 -> still_concl c_deflate_slow s z flush).
Proof.
  split.
  - exact slow_ok2w.
  - intros Hidem Hfill Hins Hlm Htally Hfbo Hfp.
    exact (still_slow_okw Hidem Hfill Hins Hlm Htally Hfbo Hfp (slow_ok2w Hfill Hins Hlm Htally Hfbo Hfp)).
Qed.
