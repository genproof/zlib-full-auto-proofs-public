(** * deflate_stored at level 0: the hash chains
    Statement and design: LTCStoredKit.v and its header. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCStoredKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma chain_land_sub : forall k u, 0 <= k ->
  Z.land (u - 2 ^ k) (2 ^ k - 1) = Z.land u (2 ^ k - 1).
Proof.
  intros k u Hk.
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  rewrite !Z.land_ones by lia.
  replace (u - 2 ^ k) with (u + (-1) * 2 ^ k) by lia.
  apply Z.mod_add. pose proof (Z.pow_pos_nonneg 2 k). lia.
Qed.

Lemma chain_land_range : forall k u, 0 <= k ->
  0 <= Z.land u (2 ^ k - 1) < 2 ^ k.
Proof.
  intros k u Hk.
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  rewrite !Z.land_ones by lia.
  apply Z.mod_pos_bound. pose proof (Z.pow_pos_nonneg 2 k). lia.
Qed.

Lemma slide_hc_strstart : forall s, d_strstart (slide_hc s) = d_strstart s.
Proof. reflexivity. Qed.
Lemma slide_hc_w_size : forall s, d_w_size (slide_hc s) = d_w_size s.
Proof. reflexivity. Qed.
Lemma slide_hc_w_mask : forall s, d_w_mask (slide_hc s) = d_w_mask s.
Proof. reflexivity. Qed.
Lemma slide_hc_hash_size : forall s, d_hash_size (slide_hc s) = d_hash_size s.
Proof. reflexivity. Qed.
Lemma slide_hc_head : forall s, d_head (slide_hc s) = map (slide_entry (d_w_size s)) (d_head s).
Proof. reflexivity. Qed.
Lemma slide_hc_prev : forall s, d_prev (slide_hc s) = map (slide_entry (d_w_size s)) (d_prev s).
Proof. reflexivity. Qed.
Lemma slide_hc_lim : forall s, lim (slide_hc s) = lim s.
Proof. reflexivity. Qed.

Theorem chain_parts_ok : chain_stmt.
Proof.
  split.
  - intros s s' [G [HG1 [HG2 HG3]]] Hh Hp Hw Hm Hhs Hst.
    exists G. split; [|split].
    + intros v Hv. destruct (HG1 v Hv); [left; auto | right; lia].
    + intros h Hr. rewrite Hh. apply HG2. lia.
    + intros q Hq Hq0 Hl. rewrite Hm, Hp. apply HG3; auto.
      revert Hl. unfold lim, MAX_DIST. rewrite Hw.
      destruct (d_strstart s >? d_w_size s - MIN_LOOKAHEAD) eqn:E1;
      destruct (d_strstart s' >? d_w_size s - MIN_LOOKAHEAD) eqn:E2;
      rewrite ?Z.gtb_ltb, ?Z.ltb_lt, ?Z.ltb_ge in *; lia.
  - intros s s' Hprm Hws [G [HG1 [HG2 HG3]]] Hh Hp Hw Hm Hhs Hst.
    destruct Hprm as [Hwb [Hwsz [Hmask _]]].
    destruct Hws as [_ [_ [_ [Hlp Hlh]]]].
    assert (Hwpos : 0 < d_w_size s) by (rewrite Hwsz; apply Z.pow_pos_nonneg; lia).
    exists (fun v => exists u, G u /\ v = slide_entry (d_w_size s) u).
    split; [|split].
    + intros v [u [Hu ->]]. rewrite slide_hc_strstart. unfold slide_entry, NIL.
      destruct (u >=? d_w_size s) eqn:E; rewrite ?Z.geb_le, ?Z.geb_leb, ?Z.leb_le, ?Z.leb_gt in *.
      * destruct (HG1 u Hu); lia.
      * left; auto.
    + intros h Hr. rewrite slide_hc_hash_size in Hr. rewrite slide_hc_head, Hh, Hw.
      exists (Znth h (d_head s)). split.
      * apply HG2. lia.
      * rewrite Znth_map; auto. rewrite Hlh. lia.
    + intros q [u [Hu ->]] Hq0 Hl.
      rewrite slide_hc_lim in Hl. rewrite slide_hc_w_mask, slide_hc_prev, Hp, Hw, Hm.
      unfold slide_entry, NIL in *.
      destruct (u >=? d_w_size s) eqn:E; rewrite ?Z.geb_le, ?Z.geb_leb, ?Z.leb_le, ?Z.leb_gt in *; [|lia].
      rewrite Hmask, Hwsz, chain_land_sub by lia. rewrite <- Hwsz.
      assert (Hr : 0 <= Z.land u (d_w_size s - 1) < d_w_size s)
        by (rewrite Hwsz; apply chain_land_range; lia).
      exists (Znth (Z.land u (d_w_size s - 1)) (d_prev s)). split.
      * rewrite <- Hmask. apply HG3; auto; [lia|].
        revert Hl. unfold lim, MAX_DIST. rewrite Hw.
        destruct (d_strstart s >? d_w_size s - MIN_LOOKAHEAD) eqn:E1;
        destruct (d_strstart s' >? d_w_size s - MIN_LOOKAHEAD) eqn:E2;
        rewrite ?Z.gtb_ltb, ?Z.ltb_lt, ?Z.ltb_ge in *; lia.
      * rewrite Znth_map; auto. rewrite Hlp. lia.
Qed.
