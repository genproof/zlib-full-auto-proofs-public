(* The level-0 facts of the wide core for the clip() loops (LTWIfaceClip.core_clip3_stmt) for the core's invariant
   LTCore.W3: deflate_stored with ub s <= 65535 and avail_out >= 65540 (any avail_in < 2^32), and ub s' <= 65535
   after every level-0 compression call.  core_facts_w W3 (LTWCore.core_facts_w3) gives the other compressors and the
   level-0 calls with ub s + avail_in < 2^32. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.LTWIfaceClip.
Require Import Zlib.proof.deflate.LTCore Zlib.proof.deflate.LTCMisc.
Require Import Zlib.proof.deflate.LTWClipKit Zlib.proof.deflate.LTWClipLoop Zlib.proof.deflate.LTWClipStored
  Zlib.proof.deflate.LTWClipUb Zlib.proof.deflate.LTWClipBlk2.
Require Zlib.proof.wide.deflate.LTCStoredSblk Zlib.proof.wide.deflate.LTCStoredWin
  Zlib.proof.wide.deflate.LTCStoredFill Zlib.proof.wide.deflate.LTCStoredBlk2b Zlib.proof.wide.deflate.LTCStoredChain.
Local Open Scope Z_scope.

(** deflate_stored's contract under [clip_ok], from the wide stored theory's parts and the clip loop. *)
Lemma stored_clip_ok : stored_clip_spec.
Proof.
  apply stored_clip_assembly.
  - exact (dsloop_clip_ok Zlib.proof.deflate.LTCStoredSblk.sblk_ok).
  - exact (Zlib.proof.wide.deflate.LTCStoredWin.dswin_ok_w Zlib.proof.deflate.LTCStoredChain.chain_parts_ok).
  - exact (Zlib.proof.wide.deflate.LTCStoredFill.fill2_ok_w Zlib.proof.deflate.LTCStoredChain.chain_parts_ok).
  - exact (Zlib.proof.wide.deflate.LTCStoredBlk2b.blk2_ok2_w Zlib.proof.deflate.LTCStoredSblk.sblk_ok).
Qed.

(** [ub <= 65535] at every return of deflate_stored. *)
Lemma stored_ub_ok : stored_ub_spec.
Proof.
  apply stored_ub_assembly.
  - exact (dsloop_clip_ok Zlib.proof.deflate.LTCStoredSblk.sblk_ok).
  - exact (Zlib.proof.wide.deflate.LTCStoredWin.dswin_ok_w Zlib.proof.deflate.LTCStoredChain.chain_parts_ok).
  - exact (Zlib.proof.wide.deflate.LTCStoredFill.fill2_ok_w Zlib.proof.deflate.LTCStoredChain.chain_parts_ok).
  - exact blk2_ub_ok.
Qed.

Theorem core_clip_facts : core_facts_w Zlib.proof.deflate.LTCore.W3 -> core_clip3_stmt.
Proof.
  intros H. split; [|split].
  - (* cw_compress_clip: the third case of clip_ok *)
    intros s z flush [HW2 Hx] Ho Hq Hf Hz Hw Ha Hl Hub Hao.
    pose proof (proj1 HW2) as HW.
    assert (Hpre : compress_pre_w s z flush)
      by exact (conj HW (conj Ho (conj Hq (conj Hf (conj Hz (conj Hw (adler_pre_ok _ _ Ha))))))).
    assert (E : fn_of s = 0) by (unfold fn_of; rewrite Hl; reflexivity).
    rewrite (dispatch_stored s z flush (W_prm s HW) E).
    destruct (stored_clip_ok s z flush Hpre ltac:(right; right; lia) E) as (s' & z' & bs & evs & Ec & Hc).
    exists s', z', bs, evs. split; [exact Ec|].
    revert Hc. apply cpost_imp. intros HW' Hsp.
    assert (E' : fn_of s' = 0) by (rewrite (fn_of_prm s s' Hsp); exact E).
    split; [split; [exact HW'|]|].
    + apply (slow_extra_fn s' HW'). rewrite E'. discriminate.
    + apply huff_extra_fn. rewrite E'. discriminate.
  - (* cw_still_clip: core_facts_w's cw_still *)
    intros s z flush s' z' bs HW Ho Hq Hf Hz Hw Ha Hl _ _ Ec Hub0 Hss Hn.
    exact (cw_still _ H s z flush s' z' bs HW Ho Hq Hf Hz Hw Ha Ec Hub0 Hss Hn).
  - (* cw_stored_ub *)
    intros s z flush s' z' bs [[HW _] _] Ho Hq Hf Hz Hw Ha Hl Hub Ec.
    assert (Hpre : compress_pre_w s z flush)
      by exact (conj HW (conj Ho (conj Hq (conj Hf (conj Hz (conj Hw (adler_pre_ok _ _ Ha))))))).
    assert (E : fn_of s = 0) by (unfold fn_of; rewrite Hl; reflexivity).
    rewrite (dispatch_stored s z flush (W_prm s HW) E) in Ec.
    exact (stored_ub_ok s z flush s' z' bs Hpre E Hub Ec).
Qed.
