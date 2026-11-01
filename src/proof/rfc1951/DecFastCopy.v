(* Part of inflate_fast's decode theory (DecFastKit.v): the copy of a reference. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.DecFastKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma dfc_lz_add: forall a b dist out,
  lz_copy (a + b) dist out = lz_copy b dist (lz_copy a dist out).
Proof. induction a; intros; simpl; auto. Qed.

Lemma dfc_len: forall k w sr ow, Zlength (fst (copy_f k w sr ow)) = Zlength ow + Z.of_nat k.
Proof.
  induction k; intros; simpl. lia.
  destruct sr; rewrite IHk, Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

(* bytes from the window: the window bytes at i.. are the bytes of ob at the distances being copied *)
Lemma dfc_win: forall k w i ob ow dist,
  Zlength ow + Z.of_nat k <= dist <= Zlength ob + Zlength ow ->
  (forall t, 0 <= t < Z.of_nat k -> Znth (i + t) w = Znth (Zlength ob + Zlength ow - dist + t) ob) ->
  ob ++ fst (copy_f k w (SWin i) ow) = lz_copy k dist (ob ++ ow).
Proof.
  induction k; intros w i ob ow dist B H; simpl. auto.
  rewrite Zlength_app.
  assert (E: Znth (Zlength ob + Zlength ow - dist) (ob ++ ow) = Znth i w).
  { rewrite app_Znth1 by lia. specialize (H 0 ltac:(lia)). rewrite !Z.add_0_r in H. symmetry; exact H. }
  rewrite E, <- app_assoc. apply IHk.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - intros t Ht. rewrite Zlength_app, Zlength_cons, Zlength_nil.
    specialize (H (t + 1) ltac:(lia)).
    replace (i + 1 + t) with (i + (t + 1)) by lia.
    rewrite H. f_equal. lia.
Qed.

(* bytes from the output *)
Lemma dfc_out: forall k w ob ow dist,
  1 <= dist <= Zlength ow ->
  ob ++ fst (copy_f k w (SOut (Zlength ow - dist)) ow) = lz_copy k dist (ob ++ ow).
Proof.
  induction k; intros w ob ow dist B; simpl. auto.
  rewrite Zlength_app.
  replace (Zlength ob + Zlength ow - dist) with (Zlength ob + (Zlength ow - dist)) by lia.
  rewrite app_Znth2 by lia.
  replace (Zlength ob + (Zlength ow - dist) - Zlength ob) with (Zlength ow - dist) by lia.
  rewrite <- app_assoc.
  replace (Zlength ow - dist + 1) with (Zlength (ow ++ [Znth (Zlength ow - dist) ow]) - dist)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  apply IHk. rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Definition dfc_wh (s: istate) (ob: list Z) (e: Z) : Prop :=
  forall d, 1 <= d <= e -> win_at s d = Znth (Zlength ob - d) ob.

(* a window segment above wnext (the older part of the window) *)
Lemma dfc_whi: forall s ob ow dist k i,
  dfc_wh s ob (dist - Zlength ow) -> 0 <= k -> Zlength ow + k <= dist <= Zlength ob + Zlength ow ->
  i_wnext s + k <= dist - Zlength ow -> i = i_wsize s + i_wnext s - (dist - Zlength ow) ->
  ob ++ fst (copy_bytes (i_wdata s) (SWin i) k ow) = lz_copy (Z.to_nat k) dist (ob ++ ow).
Proof.
  intros s ob ow dist k i WH K B W ->. unfold copy_bytes. apply dfc_win. lia.
  intros t Ht. specialize (WH (dist - Zlength ow - t) ltac:(lia)).
  unfold win_at in WH. destruct (Z.leb_spec (dist - Zlength ow - t) (i_wnext s)); [lia|].
  replace (i_wsize s + i_wnext s - (dist - Zlength ow) + t) with (i_wsize s - (dist - Zlength ow - t - i_wnext s)) by lia.
  rewrite WH. f_equal. lia.
Qed.

(* a window segment below wnext (the newer part of the window) *)
Lemma dfc_wlo: forall s ob ow dist k i,
  dfc_wh s ob (dist - Zlength ow) -> 0 <= k -> Zlength ow + k <= dist <= Zlength ob + Zlength ow ->
  dist - Zlength ow <= i_wnext s -> i = i_wnext s - (dist - Zlength ow) ->
  ob ++ fst (copy_bytes (i_wdata s) (SWin i) k ow) = lz_copy (Z.to_nat k) dist (ob ++ ow).
Proof.
  intros s ob ow dist k i WH K B W ->. unfold copy_bytes. apply dfc_win. lia.
  intros t Ht. specialize (WH (dist - Zlength ow - t) ltac:(lia)).
  unfold win_at in WH. destruct (Z.leb_spec (dist - Zlength ow - t) (i_wnext s)); [|lia].
  replace (i_wnext s - (dist - Zlength ow) + t) with (i_wnext s - (dist - Zlength ow - t)) by lia.
  rewrite WH. f_equal. lia.
Qed.

Lemma dfc_o: forall w ob ow dist n,
  1 <= dist <= Zlength ow ->
  ob ++ fst (copy_bytes w (SOut (Zlength ow - dist)) n ow) = lz_copy (Z.to_nat n) dist (ob ++ ow).
Proof. intros. apply dfc_out; auto. Qed.

Lemma dfc_blen: forall w sr n ow, 0 <= n -> Zlength (fst (copy_bytes w sr n ow)) = Zlength ow + n.
Proof. intros. unfold copy_bytes. rewrite dfc_len. lia. Qed.

Lemma dfc_lz2: forall a b dist out, 0 <= a -> 0 <= b ->
  lz_copy (Z.to_nat (a + b)) dist out = lz_copy (Z.to_nat b) dist (lz_copy (Z.to_nat a) dist out).
Proof. intros. rewrite Z2Nat.inj_add by lia. apply dfc_lz_add. Qed.

Ltac dfc_dst :=
  match goal with |- context[copy_bytes ?w ?sr ?n ?o] =>
    let E := fresh "E" in let a := fresh "ow" in let b := fresh "sr" in
    destruct (copy_bytes w sr n o) as [a b] eqn:E;
    assert (a = fst (copy_bytes w sr n o)) by (rewrite E; reflexivity); clear E
  end; cbv beta iota.

Lemma dfc : copy_stmt.
Proof.
  intros G s ob m len dist SW WO WB D1 D2 L. unfold fcopy.
  destruct (Z.ltb_spec (Zlength (m_ow m)) dist) as [C|C].
  2:{ destruct (copy_bytes _ _ _ _) as [ow' sr'] eqn:E. exists ow'. split; auto.
      replace ow' with (fst (copy_bytes (i_wdata s) (SOut (Zlength (m_ow m) - dist)) len (m_ow m))) by (rewrite E; auto).
      apply dfc_o. rewrite Zlength_app in D1. lia. }
  rewrite Zlength_app in D1.
  assert (WS: i_wsize s <> 0).
  { intro Z0. destruct WO as [[_ ->]|[W1 _]]; [rewrite Zlength_nil in D1; lia|].
    rewrite W1 in Z0. pose proof (sw_wbits _ SW). pose proof (Z.pow_pos_nonneg 2 (i_wbits s)). lia. }
  destruct WO as [[? _]|[W1 [W2 W3]]]; [contradiction|].
  assert (DB: dist <= i_wsize s).
  { rewrite W1. destruct (Z.ltb_spec (dc_wb G) 0). rewrite Z.pow_neg_r in D2 by lia. lia.
    pose proof (Z.pow_le_mono_r 2 (dc_wb G) (i_wbits s) ltac:(lia) ltac:(lia)). lia. }
  set (op := dist - Zlength (m_ow m)).
  pose proof (Zlength_nonneg (m_ow m)). pose proof (Zlength_nonneg ob).
  assert (OP: 1 <= op <= i_whave s) by (unfold op; rewrite W2; pose proof (Z.min_spec (Zlength ob) (i_wsize s)); lia).
  assert (WH: dfc_wh s ob op) by (intros d Hd; apply W3; lia).
  replace (i_whave s <? op) with false by (symmetry; apply Z.ltb_ge; lia). simpl andb. cbv iota.
  pose proof (sw_whave _ SW). pose proof (sw_wnext _ SW). pose proof (sw_wvalid _ SW).
  pose proof (dfc_blen (i_wdata s)) as BL.
  destruct (Z.eqb_spec (i_wnext s) 0) as [N0|N0].
  { assert (FULL: i_whave s = i_wsize s) by (destruct (Z.ltb_spec (i_whave s) (i_wsize s)); [specialize (H3 H4)|]; lia).
    destruct (Z.ltb_spec op len); cbv beta iota.
    - dfc_dst. dfc_dst. eexists. split; [reflexivity|].
      assert (Z1: ob ++ ow = lz_copy (Z.to_nat op) dist (ob ++ m_ow m))
        by (subst ow; apply dfc_whi; auto; lia).
      assert (L1: Zlength ow = dist) by (subst ow; rewrite BL; lia).
      subst ow0. rewrite dfc_o by lia. rewrite Z1, <- dfc_lz2 by lia. f_equal; f_equal; lia.
    - dfc_dst. eexists. split; [reflexivity|]. subst ow. apply dfc_whi; auto; lia. }
  destruct (Z.ltb_spec (i_wnext s) op) as [N1|N1].
  { assert (FULL: i_whave s = i_wsize s) by (destruct (Z.ltb_spec (i_whave s) (i_wsize s)); [specialize (H3 H4)|]; lia).
    destruct (Z.ltb_spec (op - i_wnext s) len); cbv beta iota.
    - dfc_dst.
      assert (Z1: ob ++ ow = lz_copy (Z.to_nat (op - i_wnext s)) dist (ob ++ m_ow m))
        by (subst ow; apply dfc_whi; auto; lia).
      assert (L1: Zlength ow = Zlength (m_ow m) + (op - i_wnext s)) by (subst ow; rewrite BL; lia).
      assert (WH1: dfc_wh s ob (dist - Zlength ow)) by (intros d Hd; apply WH; lia).
      destruct (Z.ltb_spec (i_wnext s) (len - (op - i_wnext s))); cbv beta iota.
      + dfc_dst. dfc_dst. eexists. split; [reflexivity|].
        assert (Z2: ob ++ ow0 = lz_copy (Z.to_nat (i_wnext s)) dist (ob ++ ow))
          by (subst ow0; apply dfc_wlo; auto; lia).
        assert (L2: Zlength ow0 = dist) by (subst ow0; rewrite BL; lia).
        subst ow1. rewrite dfc_o by lia. rewrite Z2, Z1, <- !dfc_lz2 by lia. f_equal; f_equal; lia.
      + dfc_dst. eexists. split; [reflexivity|].
        subst ow0. rewrite dfc_wlo with (dist := dist); auto; try lia. rewrite Z1, <- dfc_lz2 by lia.
        f_equal; f_equal; lia.
    - dfc_dst. eexists. split; [reflexivity|]. subst ow. apply dfc_whi; auto; lia. }
  destruct (Z.ltb_spec op len); cbv beta iota.
  - dfc_dst. dfc_dst. eexists. split; [reflexivity|].
    assert (Z1: ob ++ ow = lz_copy (Z.to_nat op) dist (ob ++ m_ow m))
      by (subst ow; apply dfc_wlo; auto; lia).
    assert (L1: Zlength ow = dist) by (subst ow; rewrite BL; lia).
    subst ow0. rewrite dfc_o by lia. rewrite Z1, <- dfc_lz2 by lia. f_equal; f_equal; lia.
  - dfc_dst. eexists. split; [reflexivity|]. subst ow. apply dfc_wlo; auto; lia.
Qed.
