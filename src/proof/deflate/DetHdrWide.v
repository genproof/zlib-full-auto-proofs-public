(** * the header stages of deflate() with up to 2^32 - 1 bytes of output space ([hdr_wide_stmt], DetWide.v)

    The invariant is the one of LTHdr.hdr_theory ([LTHdrKit.hinv]).  Its proof of [hf_run] uses the bound on
    avail_out only as [0 <= z_avail_out z]: the stage lemmas of LTHdrStages.v (and the loops of LTHdrExtra.v /
    LTHdrStrNN.v, whose measures count header bytes, not output space) need nothing more.  So the proof below is
    the [hf_run] case of [hdr_theory], run from [hdr_pre_wide]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetWide.
Require Import Zlib.proof.deflate.LTHdrKit Zlib.proof.deflate.LTHdrStages Zlib.proof.deflate.LTHdr.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** [hf_run] of LTHdr.hdr_theory for avail_out up to 2^32 - 1 (the same proof). *)
Lemma hinv_run_wide : hf_run_wide hinv.
Proof.
  intros s z H k [Hp [Ho [P0 [Hs [Hbv [Hav [Ht [Hok Hcase]]]]]]]].
  assert (Hav' : 0 <= z_avail_out z) by lia.
  rewrite hdr_stages_eq.
  destruct Hcase as [[Hst [Hw [EH ->]]] | [[Hst [Hw [EH ->]]] | Hi]].
  - (* INIT: zlib header or raw *)
    destruct (zlib_stage s z Hp Ho P0 Hs Hbv Hav' Ht Hst Hw) as [s1 [z1 [r1 [E [Es Hpost]]]]].
    rewrite E. subst H. destruct r1 as [c|].
    + exists s1, z1, (Some c). split; [reflexivity|exact Hpost].
    + cbn [then_stage bind]. rewrite (proj1 (busy_rest s1 z1 Es)).
      exists s1, z1, None. split; [reflexivity|exact Hpost].
  - (* GZIP *)
    rewrite zlib_id by (rewrite Hst; discriminate). cbn [then_stage bind].
    assert (EH' : H = gz_hdr_bytes (d_gzhead s) (xfl_byte s)) by (rewrite EH; unfold hdr_bytes; rewrite Hw; reflexivity).
    rewrite EH'.
    destruct (gzip_stage s z Hp Ho P0 Hs Hbv Hav' Ht Hst Hw Hok) as [s1 [z1 [r1 [E Hr]]]].
    rewrite E. destruct Hr as [[-> Hg] | [Es Hpost]].
    + cbn [then_stage bind]. apply chain_extra. exact Hg.
    + destruct r1 as [c|].
      * exists s1, z1, (Some c). split; [reflexivity|exact Hpost].
      * cbn [then_stage bind]. rewrite (proj2 (busy_rest s1 z1 Es)).
        exists s1, z1, None. split; [reflexivity|exact Hpost].
  - (* resume in the middle of a gzip header *)
    pose proof (hinv_gent s z H k Hp Ho P0 Hs Hbv Hav' Ht Hi) as Hg.
    destruct (hinv_status _ _ _ _ Hi) as [_ [_ [Hst _]]].
    assert (N1 : d_status s <> INIT_STATE) by (destruct Hst as [S|[S|[S|S]]]; rewrite S; discriminate).
    assert (N2 : d_status s <> GZIP_STATE) by (destruct Hst as [S|[S|[S|S]]]; rewrite S; discriminate).
    rewrite zlib_id by assumption. cbn [then_stage bind]. rewrite gzip_id by assumption. cbn [then_stage bind].
    destruct Hst as [S|[S|[S|S]]]; rewrite S in Hg.
    + apply chain_extra. exact Hg.
    + unfold from_extra. rewrite extra_id by (rewrite S; discriminate). cbn [then_stage bind].
      apply chain_name. exact Hg.
    + unfold from_extra. rewrite extra_id by (rewrite S; discriminate). cbn [then_stage bind].
      unfold from_name. rewrite name_id by (rewrite S; discriminate). cbn [then_stage bind].
      apply chain_comment. exact Hg.
    + unfold from_extra. rewrite extra_id by (rewrite S; discriminate). cbn [then_stage bind].
      unfold from_name. rewrite name_id by (rewrite S; discriminate). cbn [then_stage bind].
      unfold from_comment. rewrite comment_id by (rewrite S; discriminate). cbn [then_stage bind].
      apply hcrc_stage. exact Hg.
Qed.

Theorem hdr_wide : hdr_wide_stmt.
Proof.
  exists hinv. split.
  - split.
    + exact hinv_frame.
    + exact hinv_status.
    + intros s z H k Hpre. apply hinv_run_wide.
      destruct Hpre as [Hp [Ho [P0 [Hs [Hbv [Hav Hrest]]]]]].
      unfold hdr_pre_wide. repeat (split; [assumption|]). split; [lia|exact Hrest].
  - exact hinv_run_wide.
Qed.
