(** * the compression functions with up to 2^32 - 1 bytes of output space ([core_wide_stmt], DetWide.v)

    The witness is the invariant [W3] of the core theory (LTCore.v), with the same [core_facts].  The wide
    facts [cf_compress_wide] / [cf_still_wide] are LTCore.core_compress3 / W3_still re-assembled from the wide
    compressors (DetCore{Stored,Fast,Slow,Huff,Rle}.v) with the same proofs. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetWide.
Require Import Zlib.proof.deflate.LTCore Zlib.proof.deflate.DetCoreKit Zlib.proof.deflate.DetCoreStored
  Zlib.proof.deflate.DetCoreFast Zlib.proof.deflate.DetCoreSlow Zlib.proof.deflate.DetCoreHuff
  Zlib.proof.deflate.DetCoreRle.
Require Import Zlib.proof.deflate.LTCHuffKit Zlib.proof.deflate.LTCMisc Zlib.proof.deflate.LTCSpecs2
  Zlib.proof.deflate.LTCFill Zlib.proof.deflate.LTCLm Zlib.proof.deflate.LTCTrees2 Zlib.proof.deflate.LTCStillFill.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** deflate_slow's wide facts (DetCoreSlow.v). *)
Definition slow_ok2w := proj1 slow_wide_ok.
Definition still_slow_okw := proj2 slow_wide_ok.

(** LTCore.core_compress3 for wide streams. *)
Lemma core_compress_wide3 : fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec -> fpend_spec2 ->
  forall s z flush,
    W3 s -> outok s -> quiet s -> 0 <= flush <= 5 -> zwide z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W3 s z flush s' z' bs evs.
Proof.
  intros Hfill Hins Hlm Htal Hfbo Hfp s z flush [HW2 Hx] Ho Hq Hf Hz Hw Ha.
  pose proof (proj1 HW2) as HW.
  assert (Hpre : compress_prew s z flush)
    by exact (conj HW (conj Ho (conj Hq (conj Hf (conj Hz (conj Hw (adler_pre_ok _ _ Ha))))))).
  assert (Hpre2 : compress_pre2w s z flush)
    by exact (conj HW2 (conj Ho (conj Hq (conj Hf (conj Hz (conj Hw (adler_pre_ok _ _ Ha))))))).
  assert (Lift : forall s' z' bs evs, fn_of s <> 2 -> fn_of s <> 3 ->
            cpost W s z flush s' z' bs evs -> cpost W3 s z flush s' z' bs evs).
  { intros s' z' bs evs N2 N3. apply cpost_imp. intros HW' Hsp. rewrite <- (fn_of_prm s s' Hsp) in N2, N3.
    split; [split; [exact HW'|exact (slow_extra_fn s' HW' N2)]|exact (huff_extra_fn s' N3)]. }
  rewrite (compress_dispatch s z flush (W_prm s HW)).
  destruct (fn_range s (W_prm s HW)) as [E|[E|[E|[E|E]]]]; rewrite E; cbn [Z.eqb Pos.eqb].
  - destruct (stored_ok2w Hfp s z flush Hpre E) as (s' & z' & bs & evs & Ec & Hc).
    exists s', z', bs, evs. split; [exact Ec|]. apply Lift; [rewrite E; discriminate|rewrite E; discriminate|exact Hc].
  - destruct (fast_ok2w Hfill Hins Hlm Htal Hfbo Hfp s z flush Hpre E) as (s' & z' & bs & evs & Ec & Hc).
    exists s', z', bs, evs. split; [exact Ec|]. apply Lift; [rewrite E; discriminate|rewrite E; discriminate|exact Hc].
  - destruct (slow_ok2w Hfill Hins Hlm Htal Hfbo Hfp s z flush Hpre2 E) as (s' & z' & bs & evs & Ec & Hc).
    exists s', z', bs, evs. split; [exact Ec|]. revert Hc. apply cpost_imp. intros HW' Hsp.
    split; [exact HW'|]. apply huff_extra_fn. rewrite (fn_of_prm s s' Hsp), E. discriminate.
  - destruct (huff_okXw Hfill Htal Hfbo s z flush Hpre Hx E) as (s' & z' & bs & evs & Ec & Hc & Hx').
    exists s', z', bs, evs. split; [exact Ec|]. revert Hc. apply cpost_imp. intros HW' Hsp.
    split; [|exact Hx']. split; [exact HW'|]. apply (slow_extra_fn s' HW'). rewrite (fn_of_prm s s' Hsp), E. discriminate.
  - destruct (rle_ok2w Hfill Htal Hfbo Hfp s z flush Hpre E) as (s' & z' & bs & evs & Ec & Hc).
    exists s', z', bs, evs. split; [exact Ec|]. apply Lift; [rewrite E; discriminate|rewrite E; discriminate|exact Hc].
Qed.

(** LTCore.W3_still for wide streams. *)
Lemma W3_still_wide : fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec -> fpend_spec2 ->
  forall s z flush s' z' bs,
    W3 s -> outok s -> quiet s -> 0 <= flush <= 5 -> zwide z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    c_compress_func s z flush = Some (s', z', bs) ->
    ub s = 0 -> d_strstart s = 0 -> z_next_in z' = z_next_in z -> d_strstart s' = 0.
Proof.
  intros Hfill Hins Hlm Htal Hfbo Hfp s z flush s' z' bs [HW2 Hx] Ho Hq Hf Hz Hw Ha E Hub Hss Hn.
  pose proof (proj1 HW2) as HW.
  assert (Hpre : compress_prew s z flush)
    by exact (conj HW (conj Ho (conj Hq (conj Hf (conj Hz (conj Hw (adler_pre_ok _ _ Ha))))))).
  assert (Hpre2 : compress_pre2w s z flush)
    by exact (conj HW2 (conj Ho (conj Hq (conj Hf (conj Hz (conj Hw (adler_pre_ok _ _ Ha))))))).
  assert (Hat : still_at s).
  { destruct (W3_pos s (conj HW2 Hx)) as (P1 & P2 & P3 & P4). unfold ub in Hub. unfold still_at. lia. }
  revert E. rewrite (compress_dispatch s z flush (W_prm s HW)).
  destruct (fn_range s (W_prm s HW)) as [F|[F|[F|[F|F]]]]; rewrite F; cbn [Z.eqb Pos.eqb]; intros E.
  - exact (still_stored_okw Hfill Hfp (stored_ok2w Hfp) s z flush Hpre Hat F s' z' bs E Hn).
  - exact (still_fast_okw fill_idem_ok Hfill Hins Hlm Htal Hfbo Hfp (fast_ok2w Hfill Hins Hlm Htal Hfbo Hfp)
             s z flush Hpre Hat F s' z' bs E Hn).
  - exact (still_slow_okw fill_idem_ok Hfill Hins Hlm Htal Hfbo Hfp
             s z flush Hpre2 Hat F s' z' bs E Hn).
  - exact (still_huff_okw fill_idem_ok Hfill Htal Hfbo Hfp (huff_okXw Hfill Htal Hfbo)
             s z flush Hpre Hx Hat F s' z' bs E Hn).
  - exact (still_rle_okw fill_idem_ok Hfill Htal Hfbo Hfp (rle_ok2w Hfill Htal Hfbo Hfp)
             s z flush Hpre Hat F s' z' bs E Hn).
Qed.

Theorem core_wide : core_wide_stmt.
Proof.
  intros Hov. exists W3.
  destruct (trees_ok2 Hov) as (Htal & Htf & Hroom).
  pose proof (fbo_ok Htf Hroom) as Hfbo. pose proof fpend2_ok as Hfp.
  pose proof fill_ok as Hfill. destruct lm_ok as [Hins Hlm].
  split; [|split].
  - exact (Build_core_facts W3 W3_prm W3_pos W3_frame W3_init W3_tune W3_dict
             (core_compress3 Hfill Hins Hlm Htal Hfbo Hfp) (W3_still Hfill Hins Hlm Htal Hfbo Hfp)
             (core_live3 Hfp) W3_full W3_params).
  - exact (core_compress_wide3 Hfill Hins Hlm Htal Hfbo Hfp).
  - exact (W3_still_wide Hfill Hins Hlm Htal Hfbo Hfp).
Qed.
