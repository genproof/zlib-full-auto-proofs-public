(* inflate_fast's copy of a match from the window and the output (fcopy) against the output so far. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimFastKit.
Require Zlib.proof.rfc1951.DecFastCopy.
Import ListNotations.
Local Open Scope Z_scope.


(* the window's bytes, as swin_ok states them, in the form the copy lemmas of rfc1951/DecFastCopy.v read
   them (DecodeDefs.win_at has the body of swin_at) *)
Lemma sfc_wh: forall s O0 e,
  (forall d, 1 <= d <= i_whave s -> swin_at s d = Znth (Zlength O0 - d) O0) -> e <= i_whave s ->
  DecFastCopy.dfc_wh s O0 e.
Proof. intros s O0 e W E d Hd. apply W. lia. Qed.

Lemma sf_copy : fcopy_stmt.
Proof.
  intros s O0 m len dist WO SANE D L. unfold fcopy.
  pose proof (Zlength_nonneg (m_ow m)). pose proof (Zlength_nonneg O0).
  destruct (Z.ltb_spec (Zlength (m_ow m)) dist) as [C|C].
  2:{ right. split; [lia|].
      DecFastCopy.dfc_dst. eexists. split; [reflexivity|]. subst ow. apply DecFastCopy.dfc_o. lia. }
  rewrite SANE. simpl negb.
  destruct WO as [[W0 [HV ->]]|[W1 [WIN [W2 [WN [WF [WL W3]]]]]]].
  { left. rewrite Zlength_nil. split; [lia|]. rewrite HV.
    replace (0 <? dist - Zlength (m_ow m)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  pose proof (Z.min_spec (Zlength O0) 32768).
  destruct (Z.ltb_spec (i_whave s) (dist - Zlength (m_ow m))) as [F|F].
  { left. split; [lia|reflexivity]. }
  right. split; [lia|]. simpl andb. cbv iota.
  set (op := dist - Zlength (m_ow m)) in *.
  assert (OP: 1 <= op <= i_whave s) by (unfold op; lia).
  assert (WH: DecFastCopy.dfc_wh s O0 op) by (apply sfc_wh; auto).
  pose proof (DecFastCopy.dfc_blen (i_wdata s)) as BL.
  destruct (Z.eqb_spec (i_wnext s) 0) as [N0|N0].
  { assert (FULL: i_whave s = i_wsize s) by (destruct (Z.ltb_spec (i_whave s) 32768); [specialize (WF ltac:(assumption))|]; lia).
    destruct (Z.ltb_spec op len); cbv beta iota.
    - DecFastCopy.dfc_dst. DecFastCopy.dfc_dst. eexists. split; [reflexivity|].
      assert (Z1: O0 ++ ow = lz_copy (Z.to_nat op) dist (O0 ++ m_ow m))
        by (subst ow; apply DecFastCopy.dfc_whi; auto; lia).
      assert (L1: Zlength ow = dist) by (subst ow; rewrite BL; lia).
      subst ow0. rewrite DecFastCopy.dfc_o by lia. rewrite Z1, <- DecFastCopy.dfc_lz2 by lia. f_equal; f_equal; lia.
    - DecFastCopy.dfc_dst. eexists. split; [reflexivity|]. subst ow. apply DecFastCopy.dfc_whi; auto; lia. }
  destruct (Z.ltb_spec (i_wnext s) op) as [N1|N1].
  { assert (FULL: i_whave s = i_wsize s) by (destruct (Z.ltb_spec (i_whave s) 32768); [specialize (WF ltac:(assumption))|]; lia).
    destruct (Z.ltb_spec (op - i_wnext s) len); cbv beta iota.
    - DecFastCopy.dfc_dst.
      assert (Z1: O0 ++ ow = lz_copy (Z.to_nat (op - i_wnext s)) dist (O0 ++ m_ow m))
        by (subst ow; apply DecFastCopy.dfc_whi; auto; lia).
      assert (L1: Zlength ow = Zlength (m_ow m) + (op - i_wnext s)) by (subst ow; rewrite BL; lia).
      assert (WH1: DecFastCopy.dfc_wh s O0 (dist - Zlength ow)) by (intros d Hd; apply WH; lia).
      destruct (Z.ltb_spec (i_wnext s) (len - (op - i_wnext s))); cbv beta iota.
      + DecFastCopy.dfc_dst. DecFastCopy.dfc_dst. eexists. split; [reflexivity|].
        assert (Z2: O0 ++ ow0 = lz_copy (Z.to_nat (i_wnext s)) dist (O0 ++ ow))
          by (subst ow0; apply DecFastCopy.dfc_wlo; auto; lia).
        assert (L2: Zlength ow0 = dist) by (subst ow0; rewrite BL; lia).
        subst ow1. rewrite DecFastCopy.dfc_o by lia. rewrite Z2, Z1, <- !DecFastCopy.dfc_lz2 by lia.
        f_equal; f_equal; lia.
      + DecFastCopy.dfc_dst. eexists. split; [reflexivity|].
        subst ow0. rewrite DecFastCopy.dfc_wlo with (dist := dist); auto; try lia.
        rewrite Z1, <- DecFastCopy.dfc_lz2 by lia. f_equal; f_equal; lia.
    - DecFastCopy.dfc_dst. eexists. split; [reflexivity|]. subst ow. apply DecFastCopy.dfc_whi; auto; lia. }
  destruct (Z.ltb_spec op len); cbv beta iota.
  - DecFastCopy.dfc_dst. DecFastCopy.dfc_dst. eexists. split; [reflexivity|].
    assert (Z1: O0 ++ ow = lz_copy (Z.to_nat op) dist (O0 ++ m_ow m))
      by (subst ow; apply DecFastCopy.dfc_wlo; auto; lia).
    assert (L1: Zlength ow = dist) by (subst ow; rewrite BL; lia).
    subst ow0. rewrite DecFastCopy.dfc_o by lia. rewrite Z1, <- DecFastCopy.dfc_lz2 by lia. f_equal; f_equal; lia.
  - DecFastCopy.dfc_dst. eexists. split; [reflexivity|]. subst ow. apply DecFastCopy.dfc_wlo; auto; lia.
Qed.
