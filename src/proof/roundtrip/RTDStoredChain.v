(* RT-D part STORED: hash chains at level 0 (statement: RTDStoredKit.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDStoredKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rtdsc_update_hash : forall s s' h c,
  d_hash_shift s' = d_hash_shift s -> d_hash_mask s' = d_hash_mask s ->
  update_hash s' h c = update_hash s h c.
Proof. intros s s' h c E1 E2. unfold update_hash. rewrite E1, E2. reflexivity. Qed.

Lemma rtdsc_h3 : forall s s' q q',
  d_hash_shift s' = d_hash_shift s -> d_hash_mask s' = d_hash_mask s ->
  Znth q' (mb_val (d_window s')) = Znth q (mb_val (d_window s)) ->
  Znth (q' + 1) (mb_val (d_window s')) = Znth (q + 1) (mb_val (d_window s)) ->
  Znth (q' + 2) (mb_val (d_window s')) = Znth (q + 2) (mb_val (d_window s)) ->
  h3 s' q' = h3 s q.
Proof.
  intros s s' q q' E1 E2 B0 B1 B2. unfold h3.
  rewrite B0, B1, B2, !(rtdsc_update_hash s s') by auto. reflexivity.
Qed.

Lemma rtdsc_land_sub : forall k u, 0 <= k ->
  Z.land (u - 2 ^ k) (2 ^ k - 1) = Z.land u (2 ^ k - 1).
Proof.
  intros k u Hk.
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  rewrite !Z.land_ones by lia.
  replace (u - 2 ^ k) with (u + (-1) * 2 ^ k) by lia.
  apply Z.mod_add. pose proof (Z.pow_pos_nonneg 2 k). lia.
Qed.

Lemma rtdsc_land_range : forall k u, 0 <= k ->
  0 <= Z.land u (2 ^ k - 1) < 2 ^ k.
Proof.
  intros k u Hk.
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  rewrite !Z.land_ones by lia.
  apply Z.mod_pos_bound. pose proof (Z.pow_pos_nonneg 2 k). lia.
Qed.

Lemma rtdsc_keep : forall s s', chain_hok s -> d_head s' = d_head s -> d_prev s' = d_prev s ->
     d_w_size s' = d_w_size s -> d_w_mask s' = d_w_mask s -> d_hash_size s' = d_hash_size s ->
     d_hash_shift s' = d_hash_shift s -> d_hash_mask s' = d_hash_mask s ->
     d_strstart s <= d_strstart s' -> d_strstart s + d_lookahead s <= d_strstart s' + d_lookahead s' ->
     (forall i, 0 <= i < d_strstart s + d_lookahead s ->
        Znth i (mb_val (d_window s')) = Znth i (mb_val (d_window s))) ->
     chain_hok s'.
Proof.
  intros s s' Hc Hh Hp Hw Hm Hhs Hsh Hhm Hss Hsl Hwin b Hb.
  rewrite Hhs in Hb. destruct (Hc b Hb) as [G [HG0 HG1]].
  exists G. split; [rewrite Hh; exact HG0|].
  intros q Hq Hq0 Hl.
  assert (Hl0 : lim s <= q).
  { revert Hl. unfold lim, MAX_DIST. rewrite Hw.
    destruct (d_strstart s >? d_w_size s - MIN_LOOKAHEAD) eqn:E1;
    destruct (d_strstart s' >? d_w_size s - MIN_LOOKAHEAD) eqn:E2;
    rewrite ?Z.gtb_ltb, ?Z.ltb_lt, ?Z.ltb_ge in *; lia. }
  destruct (HG1 q Hq Hq0 Hl0) as [H1 [H2 H3]].
  split; [lia|split].
  - rewrite (rtdsc_h3 s s' q q); auto; apply Hwin; lia.
  - rewrite Hm, Hp. exact H3.
Qed.

Theorem rtds_chain_ok : chainh_stmt.
Proof.
  split; [|split].
  - exact rtdsc_keep.
  - intros s s' Hc Hh Hp Hw Hm Hhs Hsh Hhm Hss Hsl Hwin.
    apply (rtdsc_keep (slide_hc s) (slide_hc s')); auto; cbn [slide_hc]; simpl; try congruence.
  - intros s s' Hprm Hws Hc Hh Hp Hw Hm Hhs Hsh Hhm Hss Hla Hwin b Hb.
    destruct Hprm as [Hwb [Hwsz [Hmask _]]].
    destruct Hws as [_ [_ [_ [Hlp Hlh]]]].
    assert (Hwpos : 0 < d_w_size s) by (rewrite Hwsz; apply Z.pow_pos_nonneg; lia).
    change (d_hash_size (slide_hc s')) with (d_hash_size s') in Hb. rewrite Hhs in Hb.
    destruct (Hc b Hb) as [G [HG0 HG1]].
    exists (fun v => exists u, G u /\ v = slide_entry (d_w_size s) u). split.
    + change (d_head (slide_hc s')) with (map (slide_entry (d_w_size s')) (d_head s')).
      rewrite Hh, Hw. exists (Znth b (d_head s)). split; auto.
      rewrite Znth_map; auto. rewrite Hlh. lia.
    + intros q' [q [Hq ->]] Hq0 Hl.
      change (lim (slide_hc s')) with (lim s') in Hl.
      unfold slide_entry, NIL in *.
      destruct (q >=? d_w_size s) eqn:E; rewrite ?Z.geb_le, ?Z.geb_leb, ?Z.leb_le, ?Z.leb_gt in *; [|lia].
      assert (Hl0 : lim s <= q).
      { revert Hl. unfold lim, MAX_DIST. rewrite Hw, Hss.
        destruct (d_strstart s >? d_w_size s - MIN_LOOKAHEAD) eqn:E1;
        destruct (d_strstart s - d_w_size s >? d_w_size s - MIN_LOOKAHEAD) eqn:E2;
        rewrite ?Z.gtb_ltb, ?Z.ltb_lt, ?Z.ltb_ge in *; lia. }
      destruct (HG1 q Hq ltac:(lia) Hl0) as [H1 [H2 H3]].
      change (d_strstart (slide_hc s')) with (d_strstart s').
      change (d_lookahead (slide_hc s')) with (d_lookahead s').
      split; [lia|split].
      * change (h3 (slide_hc s') (q - d_w_size s)) with (h3 s' (q - d_w_size s)).
        rewrite (rtdsc_h3 s s' q (q - d_w_size s)); auto;
          [| rewrite Hwin by lia; f_equal; lia ..].
        rewrite Hwin by lia. f_equal. lia.
      * change (d_w_mask (slide_hc s')) with (d_w_mask s').
        change (d_prev (slide_hc s')) with (map (slide_entry (d_w_size s')) (d_prev s')).
        rewrite Hm, Hp, Hw, Hmask, Hwsz, rtdsc_land_sub by lia. rewrite <- Hwsz.
        assert (Hr : 0 <= Z.land q (d_w_size s - 1) < d_w_size s)
          by (rewrite Hwsz; apply rtdsc_land_range; lia).
        exists (Znth (Z.land q (d_w_size s - 1)) (d_prev s)). split.
        -- rewrite <- Hmask. exact H3.
        -- rewrite Znth_map; auto. rewrite Hlp. lia.
Qed.
