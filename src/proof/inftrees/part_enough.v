(* Part: fact_enough (facts.v): ENOUGH_LENS / ENOUGH_DISTS suffice (verified enough.c search). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
Require Import Zlib.proof.inftrees.model_inv.
Require Import Zlib.proof.inftrees.senough_dp.
Import ListNotations.
Local Open Scope Z_scope.

(* The proof: by size_stmt the size is 2^root + sumf over the sorted lengths ls.  Every root
   entry q whose longest code g is longer than root contributes 2^(g - root) = the sum of wgt l for
   root < l <= g; and the root entries holding a code of length >= l are at most
   2^root - P l / 2^(15 - root), P l the Kraft sum of the codes shorter than l (the codes are
   sorted).  That bound is the sum of `term` over the states (A l, K l) of the code, which the
   verified search of senough_dp.v bounds by ENOUGH - 2^root. *)

(* ---------------------------------------------------------------------------------------------- *)
(* Sums.                                                                                           *)

Lemma lsum_plus : forall f g xs, lsum (fun x => f x + g x) xs = lsum f xs + lsum g xs.
Proof. induction xs; simpl; [lia|]. unfold lsum in *; simpl. lia. Qed.

Lemma lsum_scale : forall c f xs, lsum (fun x => c * f x) xs = c * lsum f xs.
Proof. induction xs; unfold lsum in *; simpl; [lia|]. rewrite IHxs. lia. Qed.

Lemma lsum_ext : forall f g xs, (forall x, In x xs -> f x = g x) -> lsum f xs = lsum g xs.
Proof.
  induction xs; intros H; unfold lsum in *; simpl; [lia|].
  rewrite H by (left; auto). rewrite IHxs by (intros; apply H; right; auto). lia.
Qed.

Lemma lsum_le : forall f g xs, (forall x, In x xs -> f x <= g x) -> lsum f xs <= lsum g xs.
Proof.
  intros f g xs. induction xs as [|y xs IH]; intros H; unfold lsum in *; simpl; [lia|].
  assert (H1 := H y (or_introl eq_refl)).
  assert (H2 : fold_right (fun x s => f x + s) 0 xs <= fold_right (fun x s => g x + s) 0 xs)
    by (apply IH; intros; apply H; right; auto).
  lia.
Qed.

Lemma lsum_zero : forall f xs, (forall x, In x xs -> f x = 0) -> lsum f xs = 0.
Proof.
  intros. rewrite (lsum_ext f (fun _ => 0)) by auto. clear. induction xs as [|y xs IH]; [reflexivity|].
  change (lsum (fun _ => 0) (y :: xs)) with (0 + lsum (fun _ => 0) xs). rewrite IH. reflexivity.
Qed.

Lemma lsum_swap : forall (h: Z -> Z -> Z) xs ys,
  lsum (fun x => lsum (fun y => h x y) ys) xs = lsum (fun y => lsum (fun x => h x y) xs) ys.
Proof.
  intros h xs ys. induction xs as [|x xs IH]; unfold lsum in *; simpl.
  - symmetry. apply (lsum_zero (fun _ => 0)). auto.
  - rewrite IH. fold (lsum (fun y => h x y) ys).
    fold (lsum (fun y => fold_right (fun x0 s => h x0 y + s) 0 xs) ys).
    rewrite <- lsum_plus. reflexivity.
Qed.

Lemma fold_plus_lsum : forall f xs a, fold_left (fun t q => t + f q) xs a = a + lsum f xs.
Proof.
  intros f xs. induction xs as [|x xs IH]; intros a; simpl; [lia|].
  rewrite IH. unfold lsum; simpl. lia.
Qed.

Lemma sumf_lsum : forall ls root n, sumf ls root n = lsum (fq ls root) (zseq 0 n).
Proof. intros. unfold sumf. rewrite fold_plus_lsum. lia. Qed.

Lemma lsum_ge_ind : forall m n lo,
  lsum (fun q => if m <=? q then 1 else 0) (zseq lo n) = lo + Z.of_nat n - Z.max lo (Z.min m (lo + Z.of_nat n)).
Proof.
  intros m n. induction n as [|n IH]; intros lo; unfold lsum in *; cbn [zseq fold_right]; [lia|].
  rewrite IH. destruct (m <=? lo) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E]; lia.
Qed.

Lemma lsum_eq_ind : forall x n lo,
  lsum (fun l => if l =? x then 1 else 0) (zseq lo n) =
  if (lo <=? x) && (x <? lo + Z.of_nat n) then 1 else 0.
Proof.
  intros x n. induction n as [|n IH]; intros lo; unfold lsum in *; cbn [zseq fold_right].
  - destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x (lo + Z.of_nat 0)); simpl; lia.
  - rewrite IH.
    destruct (Z.eqb_spec lo x); destruct (Z.leb_spec lo x); destruct (Z.leb_spec (lo + 1) x);
    destruct (Z.ltb_spec x (lo + Z.of_nat (S n))); destruct (Z.ltb_spec x (lo + 1 + Z.of_nat n));
    simpl; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Kraft sums of filtered lists.                                                                   *)

Lemma ksum_cons : forall x xs, ksum (x :: xs) = 2 ^ (MAXBITS - x) + ksum xs.
Proof. reflexivity. Qed.

Lemma ksum_filter_split : forall f xs,
  ksum xs = ksum (filter f xs) + ksum (filter (fun x => negb (f x)) xs).
Proof.
  intros f xs. induction xs as [|x xs IH]; [reflexivity|].
  cbn [filter]. destruct (f x); cbn [filter negb]; rewrite !ksum_cons; lia.
Qed.

Lemma len_filter_split : forall (f: Z -> bool) xs,
  Zlength xs = Zlength (filter f xs) + Zlength (filter (fun x => negb (f x)) xs).
Proof.
  intros f xs. induction xs as [|x xs IH]; [reflexivity|].
  cbn [filter]. destruct (f x); cbn [filter negb]; rewrite !Zlength_cons; lia.
Qed.

Lemma ksum_filter_le : forall f xs, ksum (filter f xs) <= ksum xs.
Proof.
  intros. rewrite (ksum_filter_split f xs). pose proof (ksum_nonneg (filter (fun x => negb (f x)) xs)). lia.
Qed.

Lemma ksum_filter_none : forall (f: Z -> bool) xs, (forall x, In x xs -> f x = false) -> ksum (filter f xs) = 0.
Proof.
  intros f xs. induction xs as [|x xs IH]; intros H; [reflexivity|].
  cbn [filter]. rewrite (H x (or_introl eq_refl)). apply IH. intros; apply H; right; auto.
Qed.

Lemma filter_all : forall (f: Z -> bool) xs, (forall x, In x xs -> f x = true) -> filter f xs = xs.
Proof.
  intros f xs. induction xs as [|x xs IH]; intros H; [reflexivity|].
  cbn [filter]. rewrite (H x (or_introl eq_refl)). f_equal. apply IH. intros; apply H; right; auto.
Qed.

Lemma ksum_filter_succ : forall l xs,
  ksum (filter (fun x => x <? l + 1) xs) =
  ksum (filter (fun x => x <? l) xs) + Zlength (filter (fun x => x =? l) xs) * 2 ^ (MAXBITS - l).
Proof.
  intros l xs. induction xs as [|x xs IH]; [reflexivity|].
  cbn [filter]. destruct (x <? l + 1) eqn:E1; destruct (x <? l) eqn:E2; destruct (x =? l) eqn:E3;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge, ?Z.eqb_eq, ?Z.eqb_neq in *; try lia;
    rewrite ?ksum_cons, ?Zlength_cons, IH; try lia.
  subst. lia.
Qed.

Lemma len_filter_succ : forall l xs,
  Zlength (filter (fun x => x <? l + 1) xs) =
  Zlength (filter (fun x => x <? l) xs) + Zlength (filter (fun x => x =? l) xs).
Proof.
  intros l xs. induction xs as [|x xs IH]; [reflexivity|].
  cbn [filter]. destruct (x <? l + 1) eqn:E1; destruct (x <? l) eqn:E2; destruct (x =? l) eqn:E3;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge, ?Z.eqb_eq, ?Z.eqb_neq in *; try lia;
    rewrite ?Zlength_cons, IH; lia.
Qed.

Lemma ksum_ge_bound : forall l xs, Forall (fun x => l <= x <= MAXBITS) xs ->
  ksum xs <= Zlength xs * 2 ^ (MAXBITS - l).
Proof.
  intros l xs. induction xs as [|x xs IH]; intros H; [simpl; lia|].
  inversion H; subst. rewrite ksum_cons, Zlength_cons. specialize (IH H3).
  assert (2 ^ (MAXBITS - x) <= 2 ^ (MAXBITS - l)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma Forall_filter_In : forall (P: Z -> Prop) (f: Z -> bool) xs,
  (forall x, In x xs -> f x = true -> P x) -> Forall P (filter f xs).
Proof.
  intros. apply Forall_forall. intros x Hx. apply filter_In in Hx. destruct Hx. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The states of a complete sorted code.                                                           *)

Section Code.
Context (ls : list Z).
Context (Hrange : Forall (fun l => 1 <= l <= MAXBITS) ls).
Context (Hsorted : forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls).
Context (Hk : ksum ls = 2 ^ MAXBITS).

Definition sP (l: Z) : Z := ksum (filter (fun x => x <? l) ls).
Definition sK (l: Z) : Z := Zlength (filter (fun x => x <? l) ls).
Definition sA (l: Z) : Z := (2 ^ MAXBITS - sP l) / 2 ^ (MAXBITS - l).
Definition sC (l: Z) : Z := Zlength (filter (fun x => x =? l) ls).

Lemma In_range : forall x, In x ls -> 1 <= x <= MAXBITS.
Proof. intros. eapply Forall_forall in Hrange; eauto. Qed.

Lemma sP_rest : forall l, 2 ^ MAXBITS - sP l = ksum (filter (fun x => negb (x <? l)) ls).
Proof. intros. unfold sP. rewrite <- Hk. rewrite (ksum_filter_split (fun x => x <? l) ls) at 1. lia. Qed.

Lemma sP_div : forall l, 1 <= l <= 15 -> 2 ^ MAXBITS - sP l = sA l * 2 ^ (MAXBITS - l).
Proof.
  intros l Hl. unfold sA.
  assert (Hm: sP l mod 2 ^ (MAXBITS - l) = 0).
  { unfold sP. apply ksum_div; [unfold MAXBITS; lia|].
    apply Forall_filter_In. intros x _ Hx. apply Z.ltb_lt in Hx. lia. }
  assert (Hpos: 0 < 2 ^ (MAXBITS - l)) by (apply Z.pow_pos_nonneg; unfold MAXBITS; lia).
  assert (H2: 2 ^ MAXBITS = 2 ^ l * 2 ^ (MAXBITS - l)) by (rewrite <- Z.pow_add_r by (unfold MAXBITS; lia); f_equal; lia).
  pose proof (Z.div_mod (sP l) (2 ^ (MAXBITS - l)) ltac:(lia)) as Hd. rewrite Hm in Hd.
  set (p := sP l / 2 ^ (MAXBITS - l)) in *.
  replace (2 ^ MAXBITS - sP l) with ((2 ^ l - p) * 2 ^ (MAXBITS - l)) by lia.
  rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma state_ok : forall N, Zlength ls <= N -> forall l, 1 <= l <= 15 ->
  0 <= sK l <= N /\ 0 <= sA l <= Z.min (2 ^ l) (N - sK l).
Proof.
  intros N HN l Hl.
  assert (Hpos: 0 < 2 ^ (MAXBITS - l)) by (apply Z.pow_pos_nonneg; unfold MAXBITS; lia).
  assert (H2: 2 ^ MAXBITS = 2 ^ l * 2 ^ (MAXBITS - l)) by (rewrite <- Z.pow_add_r by (unfold MAXBITS; lia); f_equal; lia).
  pose proof (sP_div l Hl) as Hd. pose proof (sP_rest l) as Hr.
  pose proof (len_filter_split (fun x => x <? l) ls) as Hlen. cbv beta in Hlen.
  assert (Hge := ksum_ge_bound l (filter (fun x => negb (x <? l)) ls)
                   ltac:(apply Forall_filter_In; intros x Hx Hf; apply In_range in Hx;
                         apply negb_true_iff, Z.ltb_ge in Hf; lia)).
  assert (HP: 0 <= sP l) by apply ksum_nonneg.
  assert (HR: 0 <= ksum (filter (fun x => negb (x <? l)) ls)) by apply ksum_nonneg.
  pose proof (Zlength_nonneg (filter (fun x => x <? l) ls)).
  pose proof (Zlength_nonneg (filter (fun x => negb (x <? l)) ls)).
  unfold sK. split; [lia|].
  assert (0 <= sA l) by nia.
  assert (sA l <= 2 ^ l) by nia.
  assert (sA l <= Zlength (filter (fun x => negb (x <? l)) ls)) by nia.
  lia.
Qed.

Lemma trans_ok : forall l, 1 <= l <= 14 ->
  sA (l + 1) = 2 * (sA l - sC l) /\ sK (l + 1) = sK l + sC l /\ 0 <= sC l.
Proof.
  intros l Hl. split; [|split].
  - pose proof (sP_div l ltac:(lia)) as H0. pose proof (sP_div (l + 1) ltac:(lia)) as H1.
    unfold sP in H0, H1. rewrite ksum_filter_succ in H1. fold (sP l) in H0, H1. fold (sC l) in H1.
    assert (Hpos: 0 < 2 ^ (MAXBITS - (l + 1))) by (apply Z.pow_pos_nonneg; unfold MAXBITS; lia).
    assert (E: 2 ^ (MAXBITS - l) = 2 * 2 ^ (MAXBITS - (l + 1)))
      by (rewrite <- Z.pow_succ_r by (unfold MAXBITS; lia); f_equal; lia).
    rewrite E in H0, H1.
    apply (Z.mul_reg_r _ _ (2 ^ (MAXBITS - (l + 1)))); [lia|]. nia.
  - unfold sK, sC. apply len_filter_succ.
  - apply Zlength_nonneg.
Qed.

Lemma state_1 : sA 1 = 2 /\ sK 1 = 0.
Proof.
  assert (Hf: filter (fun x => x <? 1) ls = []).
  { pose proof (filter_all (fun x => negb (x <? 1)) ls) as H.
    destruct (filter (fun x => x <? 1) ls) eqn:E; [reflexivity|].
    assert (In z (filter (fun x => x <? 1) ls)) by (rewrite E; left; auto).
    apply filter_In in H0. destruct H0 as [H0 H1]. apply In_range in H0. apply Z.ltb_lt in H1. lia. }
  unfold sA, sK, sP. rewrite Hf. split; reflexivity.
Qed.

Lemma kpre_ge_sP : forall j l, 0 <= j < Zlength ls -> l <= Znth j ls -> sP l <= kpre ls j.
Proof.
  intros j l Hj Hl. unfold sP, kpre.
  rewrite <- (sublist_same 0 (Zlength ls) ls) at 1 by lia.
  rewrite (sublist_split 0 j (Zlength ls)) by lia.
  rewrite filter_app, ksum_app.
  rewrite (ksum_filter_none _ (sublist j (Zlength ls) ls)).
  - pose proof (ksum_filter_le (fun x => x <? l) (sublist 0 j ls)). lia.
  - intros x Hx. apply In_Znth in Hx. destruct Hx as [i [Hi Hx]].
    rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist in Hx by lia. subst x.
    apply Z.ltb_ge. specialize (Hsorted j (i + j) ltac:(lia) ltac:(lia)). lia.
Qed.

Section Root.
Context (R : Z).
Context (HR : R = 6 \/ R = 9).

Definition bnd (l: Z) : Z := if l <=? R then 0 else wgt R l * (2 ^ R - sP l / 2 ^ (MAXBITS - R)).

Lemma fq_split : forall q, fq ls R q =
  lsum (fun l => if l <=? R then 0 else wgt R l * (if l <=? gmax ls R q then 1 else 0)) (zseq 1 15).
Proof.
  intros q. unfold fq.
  destruct (gmax_props ls R q) as [_ [_ Hg]].
  assert (Hg': gmax ls R q = 0 \/ R < gmax ls R q <= 15).
  { destruct Hg as [Hg|[j [Hj [HRj [_ Hg]]]]]; [left; auto|right].
    rewrite Hg. split; [lia|]. apply (In_range (Znth j ls)). apply Znth_In; lia. }
  clear Hg. revert Hg'. generalize (gmax ls R q). intros g Hg2.
  destruct HR as [-> | ->].
  - assert (g = 0 \/ g = 7 \/ g = 8 \/ g = 9 \/ g = 10 \/ g = 11 \/ g = 12 \/ g = 13 \/ g = 14 \/ g = 15) by lia; clear Hg2.
    repeat match goal with H: _ \/ _ |- _ => destruct H as [->|H] end; try (subst; reflexivity).
  - assert (g = 0 \/ g = 10 \/ g = 11 \/ g = 12 \/ g = 13 \/ g = 14 \/ g = 15) by lia; clear Hg2.
    repeat match goal with H: _ \/ _ |- _ => destruct H as [->|H] end; try (subst; reflexivity).
Qed.

Lemma count_bound : forall l, R < l <= 15 ->
  lsum (fun q => if l <=? gmax ls R q then 1 else 0) (zseq 0 (Z.to_nat (2 ^ R)))
    <= 2 ^ R - sP l / 2 ^ (MAXBITS - R).
Proof.
  intros l Hl.
  set (m := sP l / 2 ^ (MAXBITS - R)).
  assert (Hpos: 0 < 2 ^ (MAXBITS - R)) by (apply Z.pow_pos_nonneg; unfold MAXBITS; lia).
  assert (Hm0: 0 <= m) by (apply Z.div_pos; [apply ksum_nonneg | lia]).
  assert (Hm1: m <= 2 ^ R).
  { assert (sP l <= 2 ^ MAXBITS) by (rewrite <- Hk; apply ksum_filter_le).
    assert (m <= 2 ^ MAXBITS / 2 ^ (MAXBITS - R)) by (apply Z.div_le_mono; lia).
    destruct HR as [-> | ->]; exact H0. }
  eapply Z.le_trans.
  - apply (lsum_le _ (fun q => if m <=? q then 1 else 0)).
    intros q _. destruct (l <=? gmax ls R q) eqn:E; [apply Z.leb_le in E|destruct (m <=? q); lia].
    destruct (gmax_props ls R q) as [_ [_ [Hg|[j [Hj [HRj [Hq Hg]]]]]]]; [lia|].
    rewrite Hg in E. assert (sP l <= kpre ls j) by (apply kpre_ge_sP; lia).
    assert (m <= q) by (rewrite <- Hq; apply Z.div_le_mono; lia).
    apply Z.leb_le in H0. rewrite H0. lia.
  - rewrite lsum_ge_ind. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma sumf_bound : sumf ls R (Z.to_nat (2 ^ R)) <= lsum bnd (zseq 1 15).
Proof.
  rewrite sumf_lsum.
  rewrite (lsum_ext _ _ _ (fun q _ => fq_split q)).
  rewrite lsum_swap.
  apply lsum_le. intros l Hl. apply In_zseq' in Hl. simpl in Hl. unfold bnd.
  destruct (l <=? R) eqn:E.
  - rewrite lsum_zero by auto. lia.
  - apply Z.leb_gt in E. rewrite lsum_scale.
    assert (0 <= wgt R l) by (unfold wgt; destruct (l =? R + 1); [lia | apply Z.pow_nonneg; lia]).
    apply Z.mul_le_mono_nonneg_l; [lia|]. apply count_bound. lia.
Qed.

Lemma bnd_term : forall l, 1 <= l <= 15 -> bnd l = term R l (sA l).
Proof.
  intros l Hl. unfold bnd, term. pose proof (sP_div l Hl) as H. unfold MAXBITS in *.
  replace (2 ^ 15 - sA l * 2 ^ (15 - l)) with (sP l) by lia. reflexivity.
Qed.

Lemma code_bound : forall N E, chkb R N E = true -> Zlength ls <= N ->
  2 ^ R + sumf ls R (Z.to_nat (2 ^ R)) <= E.
Proof.
  intros N E Hc HN. unfold chkb in Hc. cbv zeta in Hc.
  destruct (chk_parts _ _ _ _ _ Hc) as [_ [_ [_ Htop]]].
  pose proof sumf_bound as H1.
  rewrite (lsum_ext _ (fun l => term R l (sA l))) in H1
    by (intros l Hl; apply In_zseq' in Hl; simpl in Hl; apply bnd_term; lia).
  pose proof (dp_sound R N E _ _ Hc sA sK sC (state_ok N HN) trans_ok) as H2.
  destruct state_1 as [-> ->] in H2. lia.
Qed.

End Root.
End Code.

(* ---------------------------------------------------------------------------------------------- *)
(* The assembly.                                                                                   *)

Lemma sumf_zero : forall ls root n, Forall (fun l => l <= root) ls -> sumf ls root n = 0.
Proof.
  intros. rewrite sumf_lsum. apply lsum_zero. intros q _. unfold fq.
  destruct (gmax_props ls root q) as [_ [_ [Hg|[j [Hj [HRj [_ Hg]]]]]]].
  - rewrite Hg. reflexivity.
  - eapply Forall_forall in H; [|apply Znth_In; exact Hj]. lia.
Qed.

Lemma count_sum : forall xs,
  lsum (count_len xs) (zseq 1 15) = Zlength (filter (fun x => (1 <=? x) && (x <? 16)) xs).
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  rewrite (lsum_ext _ (fun l => (if l =? x then 1 else 0) + count_len xs l))
    by (intros; apply count_len_cons).
  rewrite lsum_plus, IH, lsum_eq_ind. simpl.
  destruct ((1 <=? x) && (x <? 16)); rewrite ?Zlength_cons; lia.
Qed.

Lemma enough_gen : sorted_stmt -> size_stmt -> forall R N E type lens,
  (R = 6 /\ N = 30 /\ E = 592 \/ R = 9 /\ N = 286 /\ E = 852) -> type <> CODES ->
  Zlength lens <= N -> Forall (fun l => 0 <= l <= MAXBITS) lens -> expected_valid type lens = 0 ->
  two_level_size lens (expected_root R lens) <= E.
Proof.
  intros Hs Hz R N E type lens HRNE Ht HN Hr Hv.
  assert (Hc: chkb R N E = true)
    by (destruct HRNE as [[-> [-> ->]]|[-> [-> ->]]]; [exact chk_dists | exact chk_lens]).
  assert (HR: R = 6 \/ R = 9) by lia.
  destruct (Hs lens Hr) as (Hsy & Hlr & Hso & Hin & Hcnt & Hclen & Hks & Hnil & Hmm).
  assert (Hlen: Zlength (sl lens) <= Zlength lens).
  { assert (E1: Zlength (sl lens) = lsum (count_len (sl lens)) (zseq 1 15)).
    { rewrite count_sum, filter_all; [reflexivity|]. intros x Hx.
      eapply Forall_forall in Hlr; [|exact Hx]. unfold MAXBITS in Hlr.
      apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite E1, (lsum_ext _ (count_len lens)).
    - rewrite count_sum. pose proof (len_filter_split (fun x => (1 <=? x) && (x <? 16)) lens) as Hlf.
      cbv beta in Hlf.
      pose proof (Zlength_nonneg (filter (fun x => negb ((1 <=? x) && (x <? 16))) lens)). lia.
    - intros l Hl. apply In_zseq' in Hl. simpl in Hl.
      rewrite <- Hcnt by (unfold MAXBITS; lia). apply Znth_counts. lia. }
  set (ls := sl lens) in *.
  unfold expected_valid in Hv. unfold expected_root.
  rewrite <- !maxlen_longest in *. rewrite <- Hks in Hv.
  assert (HE: 2 ^ R <= E) by (destruct HRNE as [[-> [-> ->]]|[-> [-> ->]]]; simpl; lia).
  assert (Hpos: 0 < 2 ^ R) by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.eq_dec (maxlen lens) 0) as [H0|H0].
  - rewrite H0 in *. simpl.
    assert (ls = []) by (apply Hnil; auto).
    rewrite Hz; [|auto| rewrite <- Hks; fold ls; rewrite H; unfold ksum, MAXBITS; simpl; lia | unfold MAXBITS; lia].
    fold ls. rewrite H. simpl. lia.
  - rewrite <- (minlen_shortest lens Hr H0).
    destruct (Hmm ltac:(intro H; apply H0, Hnil, H)) as [Hmin Hmax].
    assert (Hne: 0 < Zlength ls).
    { destruct ls eqn:El; [exfalso; apply H0, Hnil; auto|]. rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia. }
    assert (Hall: forall i, 0 <= i < Zlength ls -> minlen lens <= Znth i ls <= maxlen lens).
    { intros i Hi. rewrite <- Hmin, <- Hmax. split; apply Hso; lia. }
    assert (Hmm2: 1 <= minlen lens /\ minlen lens <= maxlen lens /\ maxlen lens <= MAXBITS).
    { rewrite <- Hmin, <- Hmax. assert (Hx := Hso 0 (Zlength ls - 1) ltac:(lia) ltac:(lia)).
      pose proof (proj1 (Forall_forall _ _) Hlr (Znth 0 ls) ltac:(apply Znth_In; lia)) as Hy.
      pose proof (proj1 (Forall_forall _ _) Hlr (Znth (Zlength ls - 1) ls) ltac:(apply Znth_In; lia)) as Hy2.
      cbv beta in Hy, Hy2.
      lia. }
    destruct (maxlen lens =? 0) eqn:Em; [apply Z.eqb_eq in Em; lia|].
    destruct (GP_KRAFT_ONE <? ksum ls) eqn:Ek; [discriminate|]. apply Z.ltb_ge in Ek.
    unfold GP_KRAFT_ONE in Ek.
    assert (Hk15: 2 ^ MAXBITS = 32768) by reflexivity.
    destruct (Z_le_gt_dec (maxlen lens) R) as [Hle|Hgt].
    + (* all codes at most R long: one-level table of 2^max entries *)
      replace (if (if maxlen lens <? R then maxlen lens else R) <? minlen lens then minlen lens
               else if maxlen lens <? R then maxlen lens else R) with (maxlen lens)
        by (destruct (maxlen lens <? R) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1];
            destruct (_ <? minlen lens) eqn:E2; [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2|
              apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]; lia).
      rewrite Hz by (auto; unfold MAXBITS in *; try lia; rewrite <- Hks; fold ls; lia).
      fold ls. rewrite sumf_zero.
      * assert (2 ^ maxlen lens <= 2 ^ R) by (apply Z.pow_le_mono_r; lia). lia.
      * apply Forall_forall. intros x Hx. apply In_Znth in Hx. destruct Hx as [i [Hi <-]].
        specialize (Hall i Hi). lia.
    + (* a complete code with root R *)
      assert (Hcomp: ksum ls = 2 ^ MAXBITS).
      { destruct (Z.ltb_spec (ksum ls) 32768) as [E2|E2]; [|unfold MAXBITS; lia].
        exfalso. unfold GP_KRAFT_ONE in Hv.
        assert (E3: (type =? CODES) = false) by (apply Z.eqb_neq; auto).
        assert (E4: (maxlen lens =? 1) = false) by (apply Z.eqb_neq; lia).
        assert (E5: (ksum ls <? 32768) = true) by (apply Z.ltb_lt; lia).
        rewrite E3, E4, E5 in Hv. simpl in Hv. discriminate. }
      destruct (maxlen lens <? R) eqn:E1; [apply Z.ltb_lt in E1; lia|].
      destruct (R <? minlen lens) eqn:E2.
      * (* impossible: all codes longer than R, too few symbols *)
        apply Z.ltb_lt in E2. exfalso.
        assert (Hb := ksum_ge_bound (R + 1) ls).
        assert (Forall (fun x => R + 1 <= x <= MAXBITS) ls).
        { apply Forall_forall. intros x Hx. apply In_Znth in Hx. destruct Hx as [i [Hi <-]].
          specialize (Hall i Hi). lia. }
        specialize (Hb H). rewrite Hcomp in Hb.
        destruct HRNE as [[-> [-> ->]]|[-> [-> ->]]]; simpl in Hb; lia.
      * apply Z.ltb_ge in E2.
        rewrite Hz by (auto; unfold MAXBITS in *; try lia; rewrite <- Hks; fold ls; lia).
        fold ls. apply (code_bound ls Hlr Hso Hcomp R HR N E Hc). lia.
Qed.

Lemma fact_enough_ok : sorted_stmt -> rfc_stmt -> bits_stmt -> size_stmt -> fact_enough.
Proof.
  intros Hs _ _ Hz type lens Ht Hr Hv.
  destruct Ht as [[-> HN]|[-> HN]]; simpl.
  - apply (enough_gen Hs Hz 9 286 852 LENS lens); auto. unfold LENS, CODES. lia.
  - apply (enough_gen Hs Hz 6 30 592 DISTS lens); auto. unfold DISTS, CODES. lia.
Qed.
