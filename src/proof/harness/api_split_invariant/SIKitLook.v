(* The slow path's table lookups (lookup1, then lookup2 after a link) on the input's bits.

   While fewer bits than the root (or sub-table) index are in the buffer, the lookup reads the entry at
   the zero-padded index.  Because inflate_table replicates every entry over all the indices that agree
   with it on its code bits (`trep`), the entry read at the padded index is the entry at the full index
   as soon as either of them has a code that fits in the bits available; otherwise neither fits and the
   lookup pulls a byte, or leaves when the input is exhausted. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SIKitBits.
Require Import Zlib.proof.harness.api_split_invariant.SIKitBuf.
Import ListNotations.
Local Open Scope Z_scope.

Lemma sik_pull_bits m : 0 <= m_bits m <= 31 -> m_bits (pull m) = m_bits m + 8.
Proof.
  intros. unfold pull. cbn [m_bits set_m_bits]. unfold u32. apply Z.mod_small.
  pose proof (sik_pow_le 6 32 ltac:(lia)). change (2 ^ 6) with 64 in *. lia.
Qed.

Lemma sik_mq_nonneg src P0 m : bitbuf src P0 m -> 0 <= mq P0 m.
Proof. intros Hb. pose proof (bb_bits _ _ _ Hb). unfold mq. lia. Qed.

Section Look.
Variables (src: list Z) (P0: Z) (kind: Z) (s: istate) (t: tref) (nb sz: Z) (lk: Z -> bool).
Hypothesis B : bytes_ok src.
Hypothesis TV : tvalid_g kind (tab_entry lenfix_list distfix_list s t) nb sz.
Hypothesis TR : trep (tab_entry lenfix_list distfix_list s t) nb lk.
Hypothesis LK : forall op, lk op = true -> islink kind op = true.

Local Notation get := (tab_entry lenfix_list distfix_list s t).

Lemma sik_nb : 1 <= nb <= 15.
Proof. exact (tv_rb _ _ _ _ TV). Qed.

(* a root entry: its code has at most nb bits, exactly nb when it is a link *)
Lemma sik_root i : 0 <= i < 2 ^ nb ->
  entry_ok (get i) /\ e_bits (get i) <= nb /\ (lk (e_op (get i)) = true -> e_bits (get i) = nb).
Proof.
  intros Hi. destruct TV as [R S T]. specialize (T i Hi). cbv zeta in T. destruct T as [E T].
  split; [exact E|]. destruct (islink kind (e_op (get i))) eqn:L.
  - destruct T as (A1 & _). split; lia.
  - destruct T as [T1 _]. split; [exact T1|]. intros Hl. apply LK in Hl. congruence.
Qed.

(* the entry at the index of the min(b, nb) bits at q against the entry at the full index *)
Lemma sik_key1 q b : 0 <= q -> 0 <= b ->
  let i := sbits src q (Z.min b nb) in let r := get (sbits src q nb) in
  (e_bits (get i) <= b <-> e_bits r <= b) /\ (e_bits (get i) <= b -> get i = r).
Proof.
  intros Q Hb. cbv zeta. pose proof sik_nb.
  destruct (Z_le_gt_dec nb b).
  { rewrite Z.min_r by lia. split; [tauto|auto]. }
  rewrite Z.min_l by lia.
  set (i := sbits src q b). set (j := sbits src q nb).
  assert (Ri: 0 <= i < 2 ^ nb).
  { pose proof (sik_sbits_range src q b Hb). pose proof (sik_pow_le b nb ltac:(lia)). unfold i. lia. }
  assert (Rj: 0 <= j < 2 ^ nb) by (apply sik_sbits_range; lia).
  assert (Ag: forall x, 0 <= x <= b -> i mod 2 ^ x = j mod 2 ^ x).
  { intros x Hx. unfold i, j. apply sik_sbits_agree; auto; lia. }
  destruct TR as [T1 _].
  assert (Fw: e_bits (get i) <= b -> get j = get i).
  { intros Hle. destruct (sik_root i Ri) as ((_ & Eb & _) & _ & Lk).
    destruct (lk (e_op (get i))) eqn:L; [specialize (Lk eq_refl); lia|].
    apply T1; auto. apply Ag; lia. }
  assert (Bw: e_bits (get j) <= b -> get i = get j).
  { intros Hle. destruct (sik_root j Rj) as ((_ & Eb & _) & _ & Lk).
    destruct (lk (e_op (get j))) eqn:L; [specialize (Lk eq_refl); lia|].
    apply T1; auto. symmetry. apply Ag; lia. }
  split.
  - split; intros H'; [rewrite (Fw H'); exact H'|rewrite (Bw H'); exact H'].
  - intros H'. symmetry. apply Fw; auto.
Qed.

Lemma sik_bitsn_min m q b : bitbuf src P0 m -> mq P0 m = q -> 0 <= b ->
  bitsn m b = sbits src q (Z.min (m_bits m) b).
Proof.
  intros Hb Hq Hb'. unfold bitsn. rewrite (bb_hold _ _ _ Hb), Hq.
  pose proof (bb_bits _ _ _ Hb). pose proof (sik_mq_nonneg _ _ _ Hb).
  apply sik_sbits_mod_min; auto; lia.
Qed.

Lemma sik_lk1_loop q : forall k m, bitbuf src P0 m -> m_leave m = 0 -> m_s m = s -> mq P0 m = q ->
  let root := get (sbits src q nb) in
  e_bits root <= m_bits m + 8 * Z.of_nat k ->
  let '(here, m', ok) := lookup1_f k lenfix_list distfix_list t nb m in
  shp m m' /\ bitbuf src P0 m' /\ mq P0 m' = q /\
  (ok = true -> m_leave m' = 0 /\ here = root /\ e_bits here <= m_bits m' /\
                m_bits m' <= Z.max (m_bits m) (e_bits root + 7)) /\
  (ok = false -> m_leave m' = 1 /\ m_have m' = 0 /\ m_bits m' < e_bits root).
Proof.
  pose proof sik_nb.
  induction k as [|k IH]; intros m Hb Hl Hs Hq root Hf.
  - cbn [lookup1_f]. rewrite Hs, (sik_bitsn_min m q nb Hb Hq) by lia.
    pose proof (bb_bits _ _ _ Hb).
    destruct (sik_key1 q (m_bits m) ltac:(subst q; apply (sik_mq_nonneg _ _ _ Hb)) ltac:(lia)) as [K1 K2].
    cbv zeta in K1, K2. fold root in K1, K2.
    assert (E: e_bits root <= m_bits m) by lia.
    split; [apply shp_refl|]. split; [exact Hb|]. split; [exact Hq|].
    split; [|intros; discriminate].
    intros _. split; [exact Hl|]. split; [apply K2, K1, E|]. split; [apply K1, E|]. lia.
  - cbn [lookup1_f]. rewrite Hs, (sik_bitsn_min m q nb Hb Hq) by lia.
    pose proof (bb_bits _ _ _ Hb). pose proof (sik_mq_nonneg _ _ _ Hb) as Q.
    rewrite Hq in Q.
    destruct (sik_key1 q (m_bits m) Q ltac:(lia)) as [K1 K2].
    cbv zeta in K1, K2. fold root in K1, K2.
    destruct (Z.leb_spec (e_bits (get (sbits src q (Z.min (m_bits m) nb)))) (m_bits m)) as [E|E].
    + split; [apply shp_refl|]. split; [exact Hb|]. split; [exact Hq|].
      split; [|intros; discriminate].
      intros _. split; [exact Hl|]. split; [apply K2, E|]. split; [exact E|]. lia.
    + assert (Er: m_bits m < e_bits root) by (destruct (Z_lt_le_dec (m_bits m) (e_bits root)); [auto|];
                                                apply K1 in l; lia).
      assert (Rr: e_bits root <= nb).
      { apply (sik_root (sbits src q nb)). apply sik_sbits_range; lia. }
      destruct (Z.eqb_spec (m_have m) 0).
      * split; [apply shp_leave|]. split; [apply sik_bitbuf_leave; auto|].
        split; [rewrite sik_mq_leave; auto|]. split; [intros; discriminate|].
        intros _. split; [reflexivity|]. split; [destruct m; auto|]. destruct m; simpl in *; lia.
      * pose proof (bb_nx _ _ _ Hb). unfold m_have in n.
        destruct (sik_pull src P0 m Hb ltac:(unfold m_have; lia) ltac:(lia)) as [Pb Pq].
        pose proof (sik_pull_bits m ltac:(lia)) as Pbits.
        rewrite Nat2Z.inj_succ in Hf.
        specialize (IH (pull m) Pb ltac:(destruct m; auto) ltac:(destruct m; auto) ltac:(congruence)
                       ltac:(fold root; rewrite Pbits; lia)).
        destruct (lookup1_f k lenfix_list distfix_list t nb (pull m)) as [[h m'] ok].
        destruct IH as (R1 & R2 & R3 & R4 & R5).
        split; [eapply shp_trans; [apply shp_pull|exact R1]|]. split; [exact R2|]. split; [exact R3|].
        split; [|exact R5].
        intros O. destruct (R4 O) as (A1 & A2 & A3 & A4). rewrite Pbits in A4. unfold root in *. subst h. repeat split; auto; lia.
Qed.

Lemma sik_lookup1 m : bitbuf src P0 m -> m_leave m = 0 -> m_s m = s ->
  let q := mq P0 m in
  let root := get (sbits src q nb) in
  let '(here, m', ok) := lookup1 lenfix_list distfix_list t nb m in
  m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m (m_nx m')) (m_hold m')) (m_bits m')) (m_leave m') /\
  bitbuf src P0 m' /\ mq P0 m' = q /\
  (ok = true -> m_leave m' = 0 /\ here = root /\ e_bits here <= m_bits m' /\
                m_bits m' <= Z.max (m_bits m) (e_bits here + 7)) /\
  (ok = false -> m_leave m' = 1 /\ m_have m' = 0 /\ 8 * (P0 + Zlength (m_inp m)) < q + e_bits root).
Proof.
  intros Hb Hl Hs q root. pose proof sik_nb. pose proof (bb_bits _ _ _ Hb).
  pose proof (sik_mq_nonneg _ _ _ Hb).
  assert (Rr: e_bits root <= nb).
  { apply (sik_root (sbits src q nb)). apply sik_sbits_range; lia. }
  pose proof (sik_lk1_loop q 3 m Hb Hl Hs eq_refl ltac:(fold root; simpl; lia)) as L.
  unfold lookup1. destruct (lookup1_f 3 lenfix_list distfix_list t nb m) as [[h m'] ok].
  destruct L as (R1 & R2 & R3 & R4 & R5).
  destruct (shp_s _ _ R1) as [Es Ei].
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split.
  - intros O. destruct (R4 O) as (A1 & A2 & A3 & A4). subst h. repeat split; auto.
  - intros O. destruct (R5 O) as (A1 & A2 & A3). split; [auto|]. split; [auto|].
    unfold m_have in A2. rewrite Ei in A2. unfold root in *. subst q. unfold mq in *. lia.
Qed.

(* after a link: the sub-table entry *)
Section Sub.
Variable (jr: Z).
Hypothesis Rjr : 0 <= jr < 2 ^ nb.
Hypothesis Ljr : lk (e_op (get jr)) = true.

Local Notation r := (get jr).

Lemma sik_sub : e_bits r = nb /\ 1 <= e_op r /\ nb + e_op r <= 15 /\
  forall j, 0 <= j < 2 ^ e_op r -> entry_ok (get (e_val r + j)) /\ nb + e_bits (get (e_val r + j)) <= 15.
Proof.
  destruct TV as [R S T]. specialize (T jr Rjr). cbv zeta in T. destruct T as [E T].
  rewrite (LK _ Ljr) in T. destruct T as (A1 & A2 & A3 & A4).
  split; [auto|]. split; [auto|]. split; [auto|].
  intros j Hj. destruct (A4 j Hj) as (C1 & C2 & C3 & C4 & C5). auto.
Qed.

Lemma sik_key2 q' c : 0 <= q' -> 0 <= c ->
  let i := sbits src q' (Z.min c (e_op r)) in let J := sbits src q' (e_op r) in
  (e_bits (get (e_val r + i)) <= c <-> e_bits (get (e_val r + J)) <= c) /\
  (e_bits (get (e_val r + i)) <= c -> get (e_val r + i) = get (e_val r + J)).
Proof.
  intros Q Hc. cbv zeta. destruct sik_sub as (S1 & S2 & S3 & S4).
  destruct (Z_le_gt_dec (e_op r) c).
  { rewrite Z.min_r by lia. split; [tauto|auto]. }
  rewrite Z.min_l by lia.
  set (op := e_op r) in *. set (i := sbits src q' c). set (J := sbits src q' op).
  assert (Ri: 0 <= i < 2 ^ op).
  { pose proof (sik_sbits_range src q' c Hc). pose proof (sik_pow_le c op ltac:(lia)). unfold i. lia. }
  assert (RJ: 0 <= J < 2 ^ op) by (apply sik_sbits_range; lia).
  assert (Ag: forall x, 0 <= x <= c -> i mod 2 ^ x = J mod 2 ^ x).
  { intros x Hx. unfold i, J. apply sik_sbits_agree; auto; lia. }
  destruct TR as [_ T2].
  assert (Fw: e_bits (get (e_val r + i)) <= c -> get (e_val r + J) = get (e_val r + i)).
  { intros Hle. destruct (S4 i Ri) as ((_ & Eb & _) & _).
    apply (T2 jr Rjr Ljr i J Ri RJ). apply Ag; lia. }
  assert (Bw: e_bits (get (e_val r + J)) <= c -> get (e_val r + i) = get (e_val r + J)).
  { intros Hle. destruct (S4 J RJ) as ((_ & Eb & _) & _).
    apply (T2 jr Rjr Ljr J i RJ Ri). symmetry. apply Ag; lia. }
  split.
  - split; intros H'; [rewrite (Fw H'); exact H'|rewrite (Bw H'); exact H'].
  - intros H'. symmetry. apply Fw; auto.
Qed.

Lemma sik_lk2_loop q : forall k m, bitbuf src P0 m -> m_leave m = 0 -> m_s m = s -> mq P0 m = q ->
  e_bits r <= m_bits m ->
  let h2 := get (e_val r + sbits src (q + e_bits r) (e_op r)) in
  e_bits r + e_bits h2 <= m_bits m + 8 * Z.of_nat k ->
  let '(here, m', ok) := lookup2_f k lenfix_list distfix_list t r m in
  shp m m' /\ bitbuf src P0 m' /\ mq P0 m' = q /\
  (ok = true -> m_leave m' = 0 /\ here = h2 /\ e_bits r + e_bits here <= m_bits m' /\
                m_bits m' <= Z.max (m_bits m) (e_bits r + e_bits here + 7)) /\
  (ok = false -> m_leave m' = 1 /\ m_have m' = 0 /\ m_bits m' < e_bits r + e_bits h2).
Proof.
  pose proof sik_nb. destruct sik_sub as (S1 & S2 & S3 & S4).
  induction k as [|k IH]; intros m Hb Hl Hs Hq Hr h2 Hf;
    pose proof (bb_bits _ _ _ Hb) as Bb; pose proof (sik_mq_nonneg _ _ _ Hb) as Q; rewrite Hq in Q;
    destruct (sik_key2 (q + e_bits r) (m_bits m - e_bits r) ltac:(lia) ltac:(lia)) as [K1 K2];
    cbv zeta in K1, K2; fold h2 in K1, K2;
    (assert (Ei: e_val r + Z.shiftr (bitsn m (e_bits r + e_op r)) (e_bits r) =
                 e_val r + sbits src (q + e_bits r) (Z.min (m_bits m - e_bits r) (e_op r)))
      by (rewrite (sik_bitsn_min m q) by (auto; lia);
          rewrite sik_sbits_shiftr by (auto; lia); f_equal; f_equal; lia));
    cbn [lookup2_f]; rewrite Hs, Ei.
  - assert (E: e_bits h2 <= m_bits m - e_bits r) by (simpl in Hf; lia).
    split; [apply shp_refl|]. split; [exact Hb|]. split; [exact Hq|].
    split; [|intros; discriminate].
    intros _. split; [exact Hl|]. rewrite (K2 (proj2 K1 E)). split; [auto|]. split; lia.
  - destruct (Z.leb_spec (e_bits r + e_bits (get (e_val r + sbits src (q + e_bits r)
               (Z.min (m_bits m - e_bits r) (e_op r))))) (m_bits m)) as [E|E].
    + split; [apply shp_refl|]. split; [exact Hb|]. split; [exact Hq|].
      split; [|intros; discriminate].
      intros _. split; [exact Hl|]. rewrite (K2 ltac:(lia)). rewrite (K2 ltac:(lia)) in E.
      split; [auto|]. split; lia.
    + assert (Er: m_bits m < e_bits r + e_bits h2).
      { destruct (Z_lt_le_dec (m_bits m) (e_bits r + e_bits h2)) as [l|l]; [auto|].
        assert (e_bits h2 <= m_bits m - e_bits r) by lia. apply K1 in H0. lia. }
      assert (Rh: e_bits r + e_bits h2 <= 15).
      { unfold h2. rewrite S1. refine (proj2 (S4 _ _)). apply sik_sbits_range; lia. }
      destruct (Z.eqb_spec (m_have m) 0).
      * split; [apply shp_leave|]. split; [apply sik_bitbuf_leave; auto|].
        split; [rewrite sik_mq_leave; auto|]. split; [intros; discriminate|].
        intros _. split; [reflexivity|]. split; [destruct m; auto|]. destruct m; simpl in *; lia.
      * pose proof (bb_nx _ _ _ Hb). unfold m_have in n.
        destruct (sik_pull src P0 m Hb ltac:(unfold m_have; lia) ltac:(lia)) as [Pb Pq].
        pose proof (sik_pull_bits m ltac:(lia)) as Pbits.
        rewrite Nat2Z.inj_succ in Hf.
        specialize (IH (pull m) Pb ltac:(destruct m; auto) ltac:(destruct m; auto) ltac:(congruence)
                       ltac:(rewrite Pbits; lia) ltac:(fold h2; rewrite Pbits; lia)).
        destruct (lookup2_f k lenfix_list distfix_list t r (pull m)) as [[h m'] ok].
        destruct IH as (R1 & R2 & R3 & R4 & R5).
        split; [eapply shp_trans; [apply shp_pull|exact R1]|]. split; [exact R2|]. split; [exact R3|].
        split; [|exact R5].
        intros O. destruct (R4 O) as (A1 & A2 & A3 & A4). rewrite Pbits in A4. subst h.
        unfold h2 in *. repeat split; auto. clear - A4 Er. lia.
Qed.

End Sub.

Lemma sik_lookup2 m : bitbuf src P0 m -> m_leave m = 0 -> m_s m = s ->
  let q := mq P0 m in
  let root := get (sbits src q nb) in
  lk (e_op root) = true ->
  forall m1, bitbuf src P0 m1 -> m_leave m1 = 0 -> m_s m1 = m_s m -> m_inp m1 = m_inp m ->
  mq P0 m1 = q -> e_bits root <= m_bits m1 ->
  let h2 := get (e_val root + sbits src (q + e_bits root) (e_op root)) in
  let '(here, m', ok) := lookup2 lenfix_list distfix_list t root m1 in
  m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m1 (m_nx m')) (m_hold m')) (m_bits m')) (m_leave m') /\
  bitbuf src P0 m' /\ mq P0 m' = q /\
  (ok = true -> m_leave m' = 0 /\ here = h2 /\ e_bits root + e_bits here <= m_bits m' /\
                m_bits m' <= Z.max (m_bits m1) (e_bits root + e_bits here + 7)) /\
  (ok = false -> m_leave m' = 1 /\ m_have m' = 0 /\
                 8 * (P0 + Zlength (m_inp m)) < q + e_bits root + e_bits h2).
Proof.
  intros Hb Hl Hs q root Lr m1 Hb1 Hl1 Hs1 Inp Hq1 Hr1 h2.
  pose proof (sik_mq_nonneg _ _ _ Hb).
  assert (Rj: 0 <= sbits src q nb < 2 ^ nb) by (apply sik_sbits_range; pose proof sik_nb; lia).
  destruct (sik_sub _ Rj Lr) as (S1 & S2 & S3 & S4).
  pose proof (bb_bits _ _ _ Hb1).
  assert (Rh: e_bits root + e_bits h2 <= 15).
  { unfold h2, root. rewrite S1. refine (proj2 (S4 _ _)). apply sik_sbits_range; lia. }
  pose proof (sik_lk2_loop (sbits src q nb) Rj Lr q 3 m1 Hb1 Hl1 ltac:(congruence) Hq1 Hr1
                ltac:(fold root h2; simpl; lia)) as L.
  fold root h2 in L.
  unfold lookup2. destruct (lookup2_f 3 lenfix_list distfix_list t root m1) as [[h m'] ok].
  destruct L as (R1 & R2 & R3 & R4 & R5).
  destruct (shp_s _ _ R1) as [Es Ei].
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split.
  - intros O. destruct (R4 O) as (A1 & A2 & A3 & A4). repeat split; auto.
  - intros O. destruct (R5 O) as (A1 & A2 & A3). split; [auto|]. split; [auto|].
    unfold m_have in A2. rewrite Ei, Inp in A2. unfold h2, root in *. subst q. unfold mq in *. lia.
Qed.

End Look.
