(* inflate_fast's table walk (fwalk_f) with the whole code in the bit buffer reads adecode's entry. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimFastKit.
Require Import Zlib.proof.harness.api_split_invariant.SIKitBits.
Import ListNotations.
Local Open Scope Z_scope.

(* Tables.islink is the slow path's link test of the kind *)
Lemma sfw_islink kind lk :
  (kind = LENS /\ lk = len_islink) \/ (kind = DISTS /\ lk = dist_islink) -> forall op, islink kind op = lk op.
Proof. intros [[-> ->]|[-> ->]] op; reflexivity. Qed.

(* inflate_fast's link tests (len_link, dist_link) hold on the links of a valid table ... *)
Lemma sfw_link1 kind il op :
  (kind = LENS /\ il = len_link) \/ (kind = DISTS /\ il = dist_link) -> islink kind op = true -> il op = true.
Proof.
  intros [[-> ->]|[-> ->]]; unfold islink.
  - change (LENS =? DISTS) with false. cbv iota. unfold len_link.
    rewrite andb_true_iff, negb_true_iff, !Z.eqb_eq, Z.eqb_neq. intros [A B].
    assert (C: forall k, Z.land 240 k = k -> Z.land op k = 0).
    { intros k Hk. rewrite <- Hk, Z.land_assoc, B. apply Z.land_0_l. }
    rewrite (C 16 eq_refl), (C 64) by reflexivity.
    destruct (op =? 0) eqn:E; [apply Z.eqb_eq in E; lia|reflexivity].
  - change (DISTS =? DISTS) with true. cbv iota. unfold dist_link.
    rewrite andb_true_l, Z.eqb_eq. intros B.
    assert (C: forall k, Z.land 240 k = k -> Z.land op k = 0).
    { intros k Hk. rewrite <- Hk, Z.land_assoc, B. apply Z.land_0_l. }
    rewrite (C 16 eq_refl), (C 64) by reflexivity. reflexivity.
Qed.

(* ... and fail on its final entries *)
Lemma sfw_link2 kind il e :
  (kind = LENS /\ il = len_link) \/ (kind = DISTS /\ il = dist_link) -> final_ok kind e -> il (e_op e) = false.
Proof.
  intros [[-> ->]|[-> ->]].
  - unfold final_ok, len_link. change (LENS =? CODES) with false. change (LENS =? LENS) with true. cbv iota.
    intros [[-> _]|[[A _]|[A|[A _]]]].
    + reflexivity.
    + assert (e_op e = 16 \/ e_op e = 17 \/ e_op e = 18 \/ e_op e = 19 \/ e_op e = 20 \/ e_op e = 21) by lia.
      destruct H as [->|[->|[->|[->|[->| ->]]]]]; reflexivity.
    + rewrite A; reflexivity.
    + apply Z.eqb_neq in A. rewrite A. rewrite !orb_true_r. reflexivity.
  - unfold final_ok, dist_link. change (DISTS =? CODES) with false. change (DISTS =? LENS) with false.
    cbv iota. intros [[A _]|[A _]].
    + assert (e_op e = 16 \/ e_op e = 17 \/ e_op e = 18 \/ e_op e = 19 \/ e_op e = 20 \/ e_op e = 21 \/
        e_op e = 22 \/ e_op e = 23 \/ e_op e = 24 \/ e_op e = 25 \/ e_op e = 26 \/ e_op e = 27 \/
        e_op e = 28 \/ e_op e = 29) by lia.
      repeat (destruct H as [->|H]; [reflexivity|]). rewrite H; reflexivity.
    + apply Z.eqb_neq in A. rewrite A, orb_true_r. reflexivity.
Qed.

Lemma sfw_hb_s m h b : m_s (set_m_bits (set_m_hold m h) b) = m_s m.
Proof. destruct m; reflexivity. Qed.
Lemma sfw_hb_hold m h b : m_hold (set_m_bits (set_m_hold m h) b) = h.
Proof. destruct m; reflexivity. Qed.
Lemma sfw_hb_bits m h b : m_bits (set_m_bits (set_m_hold m h) b) = b.
Proof. destruct m; reflexivity. Qed.
Lemma sfw_hb_hb m h1 b1 h2 b2 :
  set_m_bits (set_m_hold (set_m_bits (set_m_hold m h1) b1) h2) b2 = set_m_bits (set_m_hold m h2) b2.
Proof. destruct m; reflexivity. Qed.

Lemma sfw_u32 x : 0 <= x <= 64 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

Lemma sf_walk : fwalk_stmt.
Proof.
  intros src P0 m kind t nb sz il lk BB TV KL B15.
  assert (IL: (kind = LENS /\ il = len_link) \/ (kind = DISTS /\ il = dist_link)) by (destruct KL; tauto).
  assert (LK: forall op, islink kind op = lk op) by (apply sfw_islink; destruct KL; tauto).
  destruct BB as [Bsrc BP0 _ _ [Bb Bb2] Bh].
  set (q := mq P0 m) in *. set (b := m_bits m) in *.
  assert (Q: 0 <= q) by (unfold q, mq; fold b; lia).
  destruct TV as [Hrb Hsz Hroot].
  assert (P: 0 < 2 ^ nb) by (apply Z.pow_pos_nonneg; lia).
  assert (Hm: m_hold m mod 2 ^ nb = sbits src q nb) by (rewrite Bh; apply sik_sbits_mod; auto; lia).
  rewrite Hm. unfold adecode.
  pose proof (sik_sbits_range src q nb ltac:(lia)) as Ri.
  destruct (Hroot _ Ri) as [Eok Hc]. cbv zeta in Hc.
  set (e := tab_entry lenfix_list distfix_list (m_s m) t (sbits src q nb)) in *.
  rewrite <- LK.
  destruct (islink kind (e_op e)) eqn:L.
  - destruct Hc as (B1 & O1 & O2 & Hsub).
    set (j := sbits src (q + e_bits e) (e_op e)).
    assert (Hj: 0 <= j < 2 ^ e_op e) by (apply sik_sbits_range; lia).
    destruct (Hsub j Hj) as (I2 & Eok2 & L2 & B2 & F2). cbv zeta in *.
    set (e2 := tab_entry lenfix_list distfix_list (m_s m) t (e_val e + j)) in *.
    destruct Eok as (_ & Eb & _). destruct Eok2 as (Eo2 & Eb2 & Ev2).
    cbn [fwalk_f]. rewrite (sfw_link1 _ _ _ IL L). rewrite sfw_hb_s, sfw_hb_hold, sfw_hb_bits, sfw_hb_hb.
    assert (Hm2: Z.shiftr (m_hold m) (e_bits e) mod 2 ^ e_op e = j).
    { rewrite Bh, sik_sbits_shiftr by (auto; lia). unfold j. apply sik_sbits_mod; auto; lia. }
    rewrite Hm2. fold e2. rewrite (sfw_link2 _ _ _ IL F2).
    split; [|split; [lia|split; [repeat split; lia|split; [exact F2|exists (e_val e + j); split; [lia|reflexivity]]]]].
    unfold dropbits. fold b. rewrite Z.shiftr_shiftr by lia.
    rewrite (sfw_u32 (b - e_bits e)) by lia.
    replace (b - e_bits e - e_bits e2) with (b - (e_bits e + e_bits e2)) by lia. reflexivity.
  - destruct Hc as [Bl F]. destruct Eok as (Eo & Eb & Ev).
    cbn [fwalk_f]. rewrite (sfw_link2 _ _ _ IL F).
    split; [reflexivity|]. split; [lia|]. split; [repeat split; lia|]. split; [exact F|].
    exists (sbits src q nb). split; [lia|reflexivity].
Qed.
