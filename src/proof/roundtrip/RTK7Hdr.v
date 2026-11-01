(* The wide header theory of the deflate laws for hinv7 (RTK7Defs.hdr_facts7).

   LTWHdr.hdr_theory_w proves [exists HI, hdr_facts_w HI] with HI = LTWHdrKit.hinv_w, the header invariant for the
   headers LawFactsW.hdr_ok_w.  The record for hinv_w itself is restated here ([hdr_facts_hinv_w], the proof of
   hdr_theory_w with its witness named) and carried over to the round-trip side: RTK7Defs is stated over the
   round-trip copies of the deflate laws' theory (RTDLT*.v), whose definitions are those of LT*.v, so
   rhdr_ok7 / hinv7 / hdr_stages / hdr_post are the wide ones by conversion; hdr_pre7 differs from hdr_pre_w only
   by its stronger bound on the output (total_out + avail_out < 2^64 instead of total_out < 2^64). *)
From Coq Require Import ZArith List Lia Bool.
Require Import Zlib.proof.roundtrip.RTK7Defs.
Require Zlib.proof.deflate.LTWHdr.
Local Open Scope Z_scope.

(** The facts of the wide header theory for its invariant hinv_w (the proof of LTWHdr.hdr_theory_w). *)
Module WideHdr.
Import Zlib.proof.deflate.LTWIface Zlib.proof.deflate.LTHdrKit Zlib.proof.deflate.LTHdrStages
  Zlib.proof.deflate.LTWHdrKit Zlib.proof.deflate.LTWHdrStages Zlib.proof.deflate.LTWHdr.
Open Scope cmodel_scope.

Lemma hdr_facts_hinv_w : hdr_facts_w hinv_w.
Proof.
  split.
  - exact hinv_frame_w.
  - exact hinv_status_w.
  - intros s z H k [Hp [Ho [P0 [Hs [Hbv [Hav [Ht [Hok Hcase]]]]]]]].
    assert (Hav' : 0 <= z_avail_out z) by lia.
    rewrite hdr_stages_eq.
    destruct Hcase as [[Hst [Hw [EH ->]]] | [[Hst [Hw [EH ->]]] | Hi]].
    + (* INIT: zlib header or raw *)
      destruct (zlib_stage_w s z Hp Ho P0 Hs Hbv Hav' Ht Hst Hw) as [s1 [z1 [r1 [E [Es Hpost]]]]].
      rewrite E. subst H. destruct r1 as [c|].
      * exists s1, z1, (Some c). split; [reflexivity|exact Hpost].
      * cbn [then_stage bind]. rewrite (proj1 (busy_rest s1 z1 Es)).
        exists s1, z1, None. split; [reflexivity|exact Hpost].
    + (* GZIP *)
      rewrite zlib_id by (rewrite Hst; discriminate). cbn [then_stage bind].
      assert (EH' : H = gz_hdr_bytes (d_gzhead s) (xfl_byte s)) by (rewrite EH; unfold hdr_bytes; rewrite Hw; reflexivity).
      rewrite EH'.
      destruct (gzip_stage_w s z Hp Ho P0 Hs Hbv Hav' Ht Hst Hw Hok) as [s1 [z1 [r1 [E Hr]]]].
      rewrite E. destruct Hr as [[-> Hg] | [Es Hpost]].
      * cbn [then_stage bind]. apply chain_extra_w. exact Hg.
      * destruct r1 as [c|].
        -- exists s1, z1, (Some c). split; [reflexivity|exact Hpost].
        -- cbn [then_stage bind]. rewrite (proj2 (busy_rest s1 z1 Es)).
           exists s1, z1, None. split; [reflexivity|exact Hpost].
    + (* resume in the middle of a gzip header *)
      pose proof (hinv_gent_w s z H k Hp Ho P0 Hs Hbv Hav' Ht Hi) as Hg.
      destruct (hinv_status_w _ _ _ _ Hi) as [_ [_ [Hst _]]].
      assert (N1 : d_status s <> INIT_STATE) by (destruct Hst as [S|[S|[S|S]]]; rewrite S; discriminate).
      assert (N2 : d_status s <> GZIP_STATE) by (destruct Hst as [S|[S|[S|S]]]; rewrite S; discriminate).
      rewrite zlib_id by assumption. cbn [then_stage bind]. rewrite gzip_id by assumption. cbn [then_stage bind].
      destruct Hst as [S|[S|[S|S]]]; rewrite S in Hg.
      * apply chain_extra_w. exact Hg.
      * unfold from_extra. rewrite extra_id by (rewrite S; discriminate). cbn [then_stage bind].
        apply chain_name_w. exact Hg.
      * unfold from_extra. rewrite extra_id by (rewrite S; discriminate). cbn [then_stage bind].
        unfold from_name. rewrite name_id by (rewrite S; discriminate). cbn [then_stage bind].
        apply chain_comment_w. exact Hg.
      * unfold from_extra. rewrite extra_id by (rewrite S; discriminate). cbn [then_stage bind].
        unfold from_name. rewrite name_id by (rewrite S; discriminate). cbn [then_stage bind].
        unfold from_comment. rewrite comment_id by (rewrite S; discriminate). cbn [then_stage bind].
        apply hcrc_stage_w. exact Hg.
Qed.

End WideHdr.

(** hinv7 is hinv_w, and hdr_pre7 implies hdr_pre_w; the rest is equal by conversion. *)
Theorem rtk7_hdr_ok : hdr7_stmt.
Proof.
  destruct WideHdr.hdr_facts_hinv_w as [F1 F2 F3]. split.
  - exact F1.
  - exact F2.
  - intros s z H k P.
    destruct P as [Hp [Ho [P0 [Hs [Hbv [Hav [Ht0 [Ht [Hok Hcase]]]]]]]]].
    apply (F3 s z H k).
    split; [exact Hp|]. split; [exact Ho|]. split; [exact P0|]. split; [exact Hs|].
    split; [exact Hbv|]. split; [exact Hav|]. split; [lia|]. split; [exact Hok|exact Hcase].
Qed.
