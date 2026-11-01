(* Copy of the Qed proof of src/proof/inftrees/part_subbits.v, under another module name, so that loop_facts is
   proved without hypotheses. *)
(* Part: subbits_stmt of fact_result.v (the sub-table look-ahead = gmax - root). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
Import ListNotations.
Local Open Scope Z_scope.

(* F l: the Kraft sum of the lengths <= l in a list. *)
Definition sb_F (xs: list Z) (l: Z) : Z := ksum (filter (fun x => x <=? l) xs).

Lemma sb_F_step : forall xs l,
  sb_F xs l = sb_F xs (l - 1) + count_len xs l * 2 ^ (MAXBITS - l).
Proof.
  induction xs as [|x xs IH]; intros l; unfold sb_F in *.
  - reflexivity.
  - rewrite count_len_cons. cbn [filter].
    destruct (x <=? l) eqn:E1, (x <=? l - 1) eqn:E2, (l =? x) eqn:E3;
      rewrite ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq, ?Z.eqb_neq in *; try lia;
      unfold ksum in *; cbn [fold_right]; rewrite IH; try lia.
    subst. lia.
Qed.

Lemma sb_filter_all : forall (f: Z -> bool) xs, Forall (fun x => f x = true) xs -> filter f xs = xs.
Proof.
  induction xs; intros H; [reflexivity|]. inversion H; subst. cbn [filter]. rewrite H2, IHxs; auto.
Qed.

Lemma sb_filter_none : forall (f: Z -> bool) xs, Forall (fun x => f x = false) xs -> filter f xs = [].
Proof.
  induction xs; intros H; [reflexivity|]. inversion H; subst. cbn [filter]. rewrite H2, IHxs; auto.
Qed.

Lemma sb_ksum_filter_le : forall (f: Z -> bool) xs, ksum (filter f xs) <= ksum xs.
Proof.
  induction xs; [reflexivity|]. cbn [filter]. unfold ksum in *; cbn [fold_right].
  assert (0 <= 2 ^ (MAXBITS - a)) by (apply Z.pow_nonneg; lia).
  destruct (f a); cbn [fold_right]; lia.
Qed.

Lemma sb_Forall_sublist : forall (P: Z -> Prop) (ls: list Z) a b, 0 <= a <= b -> b <= Zlength ls ->
  (forall p, a <= p < b -> P (Znth p ls)) -> Forall P (sublist a b ls).
Proof.
  intros. apply Forall_forall. intros x Hx. apply In_Znth in Hx. destruct Hx as [k [Hk Hx]].
  rewrite Zlength_sublist in Hk by lia. rewrite Znth_sublist in Hx by lia. subst. apply H1. lia.
Qed.

Lemma sb_mod_step : forall a b u, 0 < u -> a mod u = 0 -> b mod u = 0 -> a < b -> a + u <= b.
Proof.
  intros. pose proof (Z_div_mod_eq_full a u). pose proof (Z_div_mod_eq_full b u).
  rewrite H0 in H3. rewrite H1 in H4.
  assert (a / u < b / u) by nia. nia.
Qed.

Section SubBits.
Variables (ls: list Z) (root i: Z) (cnt: list Z).
Context (Hrange : Forall (fun l => 1 <= l <= MAXBITS) ls).
Context (Hsorted : forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls).
Context (Hk : ksum ls = 2 ^ MAXBITS).
Context (Hroot : 0 <= root <= MAXBITS).
Context (Hi : 0 <= i < Zlength ls).
Context (Hlong : root < Znth i ls).
Context (Hmod : kpre ls i mod 2 ^ (MAXBITS - root) = 0).
Context (Hcnt : forall l, 1 <= l <= MAXBITS -> Znth l cnt = count_len (sublist i (Zlength ls) ls) l).

Let N := Zlength ls.
Let D := 2 ^ (MAXBITS - root).
Let L := Znth i ls.
Let mx := Znth (N - 1) ls.
Let suf := sublist i N ls.

Lemma sb_lr : forall p, 0 <= p < N -> 1 <= Znth p ls <= MAXBITS.
Proof. intros. eapply Forall_forall in Hrange; [exact Hrange|]. apply Znth_In; lia. Qed.

Lemma sb_Dpos : 0 < D.
Proof. apply Z.pow_pos_nonneg; lia. Qed.

Lemma sb_pow_split : forall a b, 0 <= a -> 0 <= b -> 2 ^ (a + b) = 2 ^ a * 2 ^ b.
Proof. intros. apply Z.pow_add_r; lia. Qed.

Lemma sb_T_mod : forall p, i <= p < N -> (kpre ls i + D) mod 2 ^ (MAXBITS - Znth p ls) = 0.
Proof.
  intros. pose proof (sb_lr p ltac:(lia)). assert (L <= Znth p ls) by (apply Hsorted; lia).
  unfold D. rewrite (Z_div_mod_eq_full (kpre ls i) (2 ^ (MAXBITS - root))), Hmod.
  replace (MAXBITS - root) with ((Znth p ls - root) + (MAXBITS - Znth p ls)) by lia.
  rewrite sb_pow_split by (unfold L in *; lia).
  replace (2 ^ (Znth p ls - root) * 2 ^ (MAXBITS - Znth p ls) *
     (kpre ls i / (2 ^ (Znth p ls - root) * 2 ^ (MAXBITS - Znth p ls))) + 0 +
     2 ^ (Znth p ls - root) * 2 ^ (MAXBITS - Znth p ls))
    with ((2 ^ (Znth p ls - root) * (kpre ls i / (2 ^ (Znth p ls - root) * 2 ^ (MAXBITS - Znth p ls)) + 1))
          * 2 ^ (MAXBITS - Znth p ls)) by ring.
  apply Z.mod_mul. apply Z.pow_nonzero; lia.
Qed.

Lemma sb_T_le : kpre ls i + D <= kpre ls N.
Proof.
  rewrite kpre_full, Hk.
  pose proof (kpre_next_le ls i Hi). pose proof (sb_lr i Hi). fold L in H0.
  assert (kpre ls i mod D = 0) by exact Hmod.
  assert (kpre ls i < 2 ^ MAXBITS). { pose proof (Z.pow_pos_nonneg 2 (MAXBITS - L)). lia. }
  apply sb_mod_step; auto. apply sb_Dpos.
  unfold D. assert (E: 2 ^ MAXBITS = 2 ^ root * 2 ^ (MAXBITS - root))
    by (rewrite <- sb_pow_split by lia; f_equal; lia).
  rewrite E. apply Z.mod_mul. apply Z.pow_nonzero; lia.
Qed.

Lemma sb_climb : forall n k, (Z.to_nat (N - k) <= n)%nat -> i <= k <= N -> kpre ls k <= kpre ls i + D ->
  exists j, k <= j <= N /\ kpre ls j = kpre ls i + D.
Proof.
  pose proof sb_T_le.
  induction n; intros k Hn Hk1 Hk2.
  - assert (k = N) by lia. subst k. exists N. split; [lia|]. lia.
  - destruct (Z.eq_dec (kpre ls k) (kpre ls i + D)) as [E|E]; [exists k; split; [lia|auto]|].
    destruct (Z.eq_dec k N) as [EN|EN]; [subst k; lia|].
    assert (Hkp: kpre ls (k + 1) <= kpre ls i + D).
    { rewrite kpre_S by lia. pose proof (sb_lr k ltac:(lia)).
      apply sb_mod_step; [apply Z.pow_pos_nonneg; lia | apply (kpre_div_self ls Hrange Hsorted k) | |]; try lia.
      apply sb_T_mod. lia. }
    destruct (IHn (k + 1) ltac:(lia) ltac:(lia) Hkp) as [j Hj]. exists j. split; [lia|tauto].
Qed.

Lemma sb_j : exists j, i < j <= N /\ kpre ls j = kpre ls i + D.
Proof.
  destruct (sb_climb (Z.to_nat (N - i)) i ltac:(lia) ltac:(lia)) as [j [Hj1 Hj2]].
  - pose proof sb_Dpos. lia.
  - exists j. split; auto. assert (j <> i) by (intro; subst; pose proof sb_Dpos; lia). lia.
Qed.

Lemma sb_div_eq : forall x q, D * q <= x < D * q + D -> x / D = q.
Proof. intros. symmetry. apply Z.div_unique with (x - D * q); [left|]; lia. Qed.

Section WithJ.
Variable j : Z.
Context (Hj : i < j <= N).
Context (HjK : kpre ls j = kpre ls i + D).

Let q := kpre ls i / D.
Let G := gmax ls root q.

Lemma sb_Ki : kpre ls i = D * q.
Proof. unfold q. pose proof (Z_div_mod_eq_full (kpre ls i) D). fold D in Hmod. lia. Qed.

Lemma sb_lt_j : kpre ls (j - 1) < kpre ls j.
Proof.
  replace j with (j - 1 + 1) at 2 by lia. rewrite kpre_S by lia.
  pose proof (sb_lr (j - 1) ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 (MAXBITS - Znth (j - 1) ls)). lia.
Qed.

Lemma sb_G : G = Znth (j - 1) ls.
Proof.
  pose proof sb_Ki. pose proof sb_lt_j. pose proof sb_Dpos.
  destruct (gmax_props ls root q) as (G1 & G2 & G3). fold G in G1, G2, G3.
  assert (A: Znth (j - 1) ls <= G).
  { apply G2; [lia| |].
    - assert (L <= Znth (j - 1) ls) by (apply Hsorted; lia). unfold L in *; lia.
    - fold D. apply sb_div_eq. pose proof (kpre_mono ls i (j - 1) ltac:(lia) ltac:(lia)). lia. }
  pose proof (sb_lr (j - 1) ltac:(lia)).
  destruct G3 as [G3|(p & Hp & Hpr & Hpq & G3)]; [lia|].
  assert (p <= j - 1).
  { destruct (Z_lt_le_dec (j - 1) p); [|lia]. exfalso.
    pose proof (kpre_mono ls j p ltac:(lia) ltac:(lia)). fold D in Hpq.
    assert (q + 1 <= kpre ls p / D) by (apply Z.div_le_lower_bound; lia). lia. }
  assert (Znth p ls <= Znth (j - 1) ls) by (apply Hsorted; lia). lia.
Qed.

Lemma sb_suf_split : suf = sublist i j ls ++ sublist j N ls.
Proof. unfold suf. rewrite <- sublist_split by lia. reflexivity. Qed.

Lemma sb_key : forall l, D <= sb_F suf l <-> G <= l.
Proof.
  intros l. rewrite sb_G. split; intros H.
  - destruct (Z_lt_le_dec l (Znth (j - 1) ls)) as [Hl|Hl]; [|auto]. exfalso.
    unfold sb_F, suf in H. rewrite (sublist_split i (j - 1) N) in H by lia.
    rewrite filter_app, ksum_app in H.
    rewrite (sb_filter_none _ (sublist (j - 1) N ls)) in H.
    + pose proof (sb_ksum_filter_le (fun x => x <=? l) (sublist i (j - 1) ls)).
      pose proof (kpre_split ls i (j - 1) ltac:(lia) ltac:(lia)). pose proof sb_lt_j.
      unfold ksum at 2 in H. cbn [fold_right] in H. lia.
    + apply sb_Forall_sublist; try lia. intros p Hp.
      assert (Znth (j - 1) ls <= Znth p ls) by (apply Hsorted; lia). apply Z.leb_gt. lia.
  - unfold sb_F. rewrite sb_suf_split, filter_app, ksum_app.
    rewrite (sb_filter_all _ (sublist i j ls)).
    + pose proof (kpre_split ls i j ltac:(lia) ltac:(lia)).
      pose proof (ksum_nonneg (filter (fun x => x <=? l) (sublist j N ls))). lia.
    + apply sb_Forall_sublist; try lia. intros p Hp.
      assert (Znth p ls <= Znth (j - 1) ls) by (apply Hsorted; lia). apply Z.leb_le. lia.
Qed.

Lemma sb_F0 : sb_F suf (L - 1) = 0.
Proof.
  unfold sb_F. rewrite sb_filter_none; [reflexivity|].
  apply sb_Forall_sublist; try lia. intros p Hp.
  assert (L <= Znth p ls) by (apply Hsorted; lia). apply Z.leb_gt. lia.
Qed.

Lemma sb_G_range : L <= G <= mx /\ G <= MAXBITS.
Proof.
  rewrite sb_G. pose proof (sb_lr (j - 1) ltac:(lia)).
  assert (L <= Znth (j - 1) ls) by (apply Hsorted; lia).
  assert (Znth (j - 1) ls <= mx) by (apply Hsorted; lia). lia.
Qed.

Lemma sb_loop : forall k curr left,
  L <= curr + root <= G -> mx - (curr + root) <= Z.of_nat k ->
  left * 2 ^ (MAXBITS - (curr + root)) = D - sb_F suf (curr + root - 1) ->
  sub_loop k curr root mx left cnt = G - root.
Proof.
  pose proof sb_G_range. pose proof sb_Dpos.
  induction k as [|k IH]; intros curr left H1 H2 H3; cbn [sub_loop].
  - lia.
  - destruct (curr + root <? mx) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E; lia].
    assert (HL1: 1 <= L) by (apply (sb_lr i Hi)).
    rewrite Hcnt by lia. fold N. fold suf.
    pose proof (sb_F_step suf (curr + root)).
    assert (P: 0 < 2 ^ (MAXBITS - (curr + root))) by (apply Z.pow_pos_nonneg; lia).
    destruct (left - count_len suf (curr + root) <=? 0) eqn:E2.
    + apply Z.leb_le in E2.
      assert (HF: D <= sb_F suf (curr + root)) by nia.
      apply sb_key in HF. lia.
    + apply Z.leb_gt in E2.
      assert (sb_F suf (curr + root) < D) by nia.
      assert (curr + root < G) by (destruct (Z_lt_le_dec (curr + root) G); auto;
                                   apply sb_key in l; lia).
      apply IH; try lia.
      replace (curr + 1 + root - 1) with (curr + root) by lia.
      assert (EP: 2 ^ (MAXBITS - (curr + root)) = 2 * 2 ^ (MAXBITS - (curr + 1 + root))).
      { replace (MAXBITS - (curr + root)) with (1 + (MAXBITS - (curr + 1 + root))) by lia.
        rewrite sb_pow_split by lia. reflexivity. }
      rewrite EP in *. nia.
Qed.

End WithJ.

Lemma sb_main : sub_bits L root mx cnt = gmax ls root (kpre ls i / D) - root.
Proof.
  destruct sb_j as [j [Hj HjK]].
  unfold sub_bits. rewrite pow2_shiftl by lia.
  pose proof (sb_G_range j Hj HjK). pose proof (sb_lr i Hi). pose proof (sb_lr (N - 1) ltac:(lia)).
  apply (sb_loop j Hj HjK).
  - unfold L in *; lia.
  - unfold mx, L, MAXBITS in *; change (Z.of_nat 16) with 16; lia.
  - replace (L - root + root) with L by lia. rewrite sb_F0.
    unfold D. replace (MAXBITS - root) with ((L - root) + (MAXBITS - L)) by lia.
    rewrite sb_pow_split by (unfold L in *; lia). lia.
Qed.

End SubBits.

Lemma subbits_ok2 : subbits_stmt.
Proof.
  unfold subbits_stmt. intros ls root i cnt Hr Hs Hk Hroot Hi Hl Hm Hlen Hc.
  apply sb_main; auto.
Qed.
