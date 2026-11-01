(** * The length-limit repair of gen_bitlen

    When the Huffman tree is deeper than [max_length] (M), gen_bitlen's first pass clamps every depth to M and
    counts [overflow] = the number of nodes deeper than M = 2 * I, where I is the number of internal nodes at
    depth >= M.  The clamped counts c (c_l leaves at clamped length l) then satisfy the Kraft sum
    sum_l c_l 2^(M-l) = 2^M + I.  The repair loop runs I times: it takes the deepest nonempty level b < M, moves
    one leaf from b to b+1, moves one leaf from M to b+1 (so c_b--, c_{b+1} += 2, c_M--); each iteration lowers
    the Kraft sum by exactly one unit 2^-M.  The reassignment then hands the lengths out, longest first, to the
    leaves in the order the heap stores them from [HEAP_SIZE - 1] down.

    This file proves:
    - [repair_correct]: on counts with Kraft sum 2^M + I and c_M >= I + 1 ([rinv]), [gen_bitlen_repair] with
      overflow 2 * I runs I iterations of [rstep], each well defined (a level b in [1, M-1] with c_b > 0 exists,
      no u16 wrap), and ends with Kraft sum exactly 2^M, all counts >= 0, the same number of leaves, c'_M >= 1;
      [repaired_lens]: the lengths [lens M c'] handed out are all in [1, M] and have Kraft sum 1;
    - [clamp_rinv]: the clamped counts [clampc M d] of a complete code d with a leaf deeper than M satisfy
      [rinv M I] with I = (their Kraft sum) - 2^M >= 1; [repl_model]: the model's repair on them gives
      [repl M d];
    - [reassign_correct], [apply_lens_spec]: [gen_bitlen_reassign] gives the k-th leaf of the heap scan (from
      [HEAP_SIZE - 1] down, internal nodes skipped) the k-th length of [lens], leaves the other entries alone,
      and adds sum_k (L'_k - Len_k) * Freq_k to opt_len (mod 2^64);
    - [bl_repair_cost_scan]: on the bit-length tree (M = 7, n <= 19 leaves, total weight W <= 320) the repaired
      code costs at most [dblt e n] bits more than the Huffman code: 101 / 128 / 260 for n <= 13 / 15 / 19 with
      the caps f * fib (d + 1) <= W of [HuffAbs.huff_fib] (e = 0), 59 / 71 / 147 with caps f * fib (d + 2) <= W
      (e = 1); by enumerating all depth profiles ([enum], [vm_compute]);
    - [cex_no_shifted_cap]: on the literal/length tree (M = 15) a cap f * fib (L + 1 - s) <= W on the repaired
      lengths fails for every shift s <= 5 (a concrete table run through the model's build_tree). *)

From Coq Require Import ZArith List Lia Bool Permutation Sorted.
From Coq Require Mergesort Orders.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Sums over the levels 1..k *)

Fixpoint lsum (g : Z -> Z) (k : nat) : Z :=
  match k with O => 0 | S k' => lsum g k' + g (Z.of_nat (S k')) end.

Lemma lsum_S : forall g k, lsum g (S k) = lsum g k + g (Z.of_nat (S k)).
Proof. reflexivity. Qed.

Lemma lsum_ext : forall g h k, (forall l, 1 <= l <= Z.of_nat k -> g l = h l) -> lsum g k = lsum h k.
Proof.
  intros g h k; induction k as [|k IH]; intros H; [reflexivity|].
  rewrite !lsum_S, IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma lsum_add : forall g h k, lsum (fun l => g l + h l) k = lsum g k + lsum h k.
Proof. intros g h k; induction k as [|k IH]; [reflexivity|]. rewrite !lsum_S, IH. ring. Qed.

Lemma lsum_point : forall i v k,
  lsum (fun l => if l =? i then v else 0) k = if (1 <=? i) && (i <=? Z.of_nat k) then v else 0.
Proof.
  intros i v k; induction k as [|k IH].
  - simpl. destruct (1 <=? i) eqn:E1, (i <=? 0) eqn:E2; simpl; auto; lia.
  - rewrite lsum_S, IH.
    destruct (Z.eqb_spec (Z.of_nat (S k)) i), (Z.leb_spec 1 i), (Z.leb_spec i (Z.of_nat k)),
      (Z.leb_spec i (Z.of_nat (S k))); simpl; lia.
Qed.

Lemma lsum_le : forall g h k, (forall l, 1 <= l <= Z.of_nat k -> g l <= h l) -> lsum g k <= lsum h k.
Proof.
  intros g h k; induction k as [|k IH]; intros H; [simpl; lia|].
  rewrite !lsum_S. specialize (IH (fun l Hl => H l ltac:(lia))). specialize (H (Z.of_nat (S k)) ltac:(lia)). lia.
Qed.

Lemma lsum_zero : forall k, lsum (fun _ => 0) k = 0.
Proof. induction k as [|k IH]; [reflexivity|]. rewrite lsum_S, IH. reflexivity. Qed.

Lemma lsum_nonneg : forall g k, (forall l, 1 <= l <= Z.of_nat k -> 0 <= g l) -> 0 <= lsum g k.
Proof. intros g k H. rewrite <- (lsum_zero k). apply lsum_le; auto. Qed.

Lemma lsum_one : forall g k l, 1 <= l <= Z.of_nat k -> (forall l', 1 <= l' <= Z.of_nat k -> 0 <= g l') ->
  g l <= lsum g k.
Proof.
  intros g k; induction k as [|k IH]; intros l Hl H; [lia|].
  rewrite lsum_S. destruct (Z.eq_dec l (Z.of_nat (S k))) as [->|Hne].
  - assert (0 <= lsum g k) by (apply lsum_nonneg; intros; apply H; lia). lia.
  - assert (g l <= lsum g k) by (apply IH; [lia|intros; apply H; lia]).
    assert (0 <= g (Z.of_nat (S k))) by (apply H; lia). lia.
Qed.

(** ** Counts: Kraft sum and number of leaves *)

(** [c] is bl_count: [Znth l c] codes of length [l], for [1 <= l <= M]. *)
Definition kraftc (M : Z) (c : list Z) : Z := lsum (fun l => Znth l c * 2 ^ (M - l)) (Z.to_nat M).
Definition tot (M : Z) (c : list Z) : Z := lsum (fun l => Znth l c) (Z.to_nat M).

Lemma u16_small : forall x, 0 <= x < 65536 -> u16 x = x.
Proof. intros; unfold u16; apply Z.mod_small; auto. Qed.

Lemma Znth_upd : forall (c : list Z) i v l, 0 <= i < Zlength c -> 0 <= l < Zlength c ->
  Znth l (upd_Znth i c v) = if l =? i then v else Znth l c.
Proof.
  intros. destruct (Z.eqb_spec l i) as [->|].
  - apply upd_Znth_same; auto.
  - apply upd_Znth_diff; auto.
Qed.

(** ** One iteration of the repair loop *)

Definition rstep_at (M : Z) (c : list Z) (b : Z) : list Z :=
  let c := upd_Znth b c (u16 (Znth b c - 1)) in
  let c := upd_Znth (b + 1) c (u16 (Znth (b + 1) c + 2)) in
  upd_Znth M c (u16 (Znth M c - 1)).

Definition rstep (M : Z) (c : list Z) : list Z := rstep_at M c (find_nonzero_down 20 c (M - 1)).

Lemma repair_unfold : forall f M c ovf,
  gen_bitlen_repair (S f) M c ovf =
  if ovf - 2 >? 0 then gen_bitlen_repair f M (rstep M c) (ovf - 2) else rstep M c.
Proof. reflexivity. Qed.

Lemma find_nonzero_down_spec : forall fuel c x,
  (exists y, 1 <= y <= x /\ Znth y c <> 0) -> x <= Z.of_nat fuel ->
  let b := find_nonzero_down fuel c x in
  1 <= b <= x /\ Znth b c <> 0 /\ (forall l, b < l <= x -> Znth l c = 0).
Proof.
  induction fuel as [|f IH]; intros c x [y [Hy Hny]] Hx; [lia|].
  simpl. destruct (Znth x c =? 0) eqn:E.
  - apply Z.eqb_eq in E. assert (y <> x) by (intro; subst; contradiction).
    destruct (IH c (x - 1)) as [H1 [H2 H3]]; [exists y; split; [lia|auto]|lia|].
    split; [lia|split; auto]. intros l Hl. destruct (Z.eq_dec l x) as [->|]; auto. apply H3; lia.
  - apply Z.eqb_neq in E. split; [lia|split; auto]. intros; lia.
Qed.

Lemma nonzero_dec : forall (c : list Z) (k : nat),
  (exists y, 1 <= y <= Z.of_nat k /\ Znth y c <> 0) \/ (forall y, 1 <= y <= Z.of_nat k -> Znth y c = 0).
Proof.
  intros c k; induction k as [|k [IH|IH]].
  - right; intros; lia.
  - left. destruct IH as [y Hy]; exists y; lia.
  - destruct (Z.eq_dec (Znth (Z.of_nat (S k)) c) 0) as [E|E].
    + right. intros y Hy. destruct (Z.eq_dec y (Z.of_nat (S k))) as [->|]; auto. apply IH; lia.
    + left. exists (Z.of_nat (S k)); split; [lia|auto].
Qed.

(** The loop invariant with [J] iterations to go. *)
Definition rinv (M J : Z) (c : list Z) : Prop :=
  Zlength c = 16 /\ (forall l, 1 <= l <= M -> 0 <= Znth l c) /\
  tot M c <= 2 ^ M /\ tot M c <= 573 /\
  kraftc M c = 2 ^ M + J /\ J + 1 <= Znth M c.

Lemma count_le_tot : forall M c l, 1 <= M -> 1 <= l <= M -> (forall l, 1 <= l <= M -> 0 <= Znth l c) ->
  Znth l c <= tot M c.
Proof.
  intros M c l HM Hl H. unfold tot. apply (lsum_one (fun l => Znth l c)); [lia|]. intros; apply H; lia.
Qed.

Section Step.
Variables (M J : Z) (c : list Z).
Hypothesis HM : 1 <= M <= 15.
Hypothesis HJ : 0 <= J.
Hypothesis Hinv : rinv M (J + 1) c.

Lemma step_level : exists b, find_nonzero_down 20 c (M - 1) = b /\ 1 <= b <= M - 1 /\ 0 < Znth b c /\
  (forall l, b < l <= M - 1 -> Znth l c = 0).
Proof.
  destruct Hinv as [Hlen [Hnn [Htot [Htot' [Hk HcM]]]]].
  destruct (nonzero_dec c (Z.to_nat (M - 1))) as [Hex|Hall].
  - destruct (find_nonzero_down_spec 20 c (M - 1)) as [H1 [H2 H3]];
      [destruct Hex as [y Hy]; exists y; lia|lia|].
    eexists; split; [reflexivity|]. split; [lia|]. split; [|exact H3].
    assert (0 <= Znth (find_nonzero_down 20 c (M - 1)) c) by (apply Hnn; lia). lia.
  - exfalso. assert (E : kraftc M c = tot M c).
    { unfold kraftc, tot. apply lsum_ext. intros l Hl.
      destruct (Z.eq_dec l M) as [->|]; [rewrite Z.sub_diag; simpl; lia|].
      rewrite Hall by lia. lia. }
    lia.
Qed.

Variable b : Z.
Hypothesis Hb : 1 <= b <= M - 1.
Hypothesis Hcb : 0 < Znth b c.

Let c1 := upd_Znth b c (u16 (Znth b c - 1)).
Let c2 := upd_Znth (b + 1) c1 (u16 (Znth (b + 1) c1 + 2)).

Lemma rstep_at_Znth : Zlength (rstep_at M c b) = 16 /\ forall l, 0 <= l < 16 ->
  Znth l (rstep_at M c b) =
  Znth l c - (if l =? b then 1 else 0) + (if l =? b + 1 then 2 else 0) - (if l =? M then 1 else 0).
Proof.
  destruct Hinv as [Hlen [Hnn [Htot [Htot' [Hk HcM]]]]].
  assert (Hle : forall l, 1 <= l <= M -> Znth l c <= 573)
    by (intros; assert (Znth l c <= tot M c) by (apply count_le_tot; auto; lia); lia).
  assert (L1 : Zlength c1 = 16) by (unfold c1; rewrite upd_Znth_Zlength; lia).
  assert (Z1 : forall l, 0 <= l < 16 -> Znth l c1 = if l =? b then Znth b c - 1 else Znth l c).
  { intros l Hl. unfold c1. rewrite Znth_upd by lia.
    rewrite u16_small; [auto|]. specialize (Hle b ltac:(lia)). lia. }
  assert (L2 : Zlength c2 = 16) by (unfold c2; rewrite upd_Znth_Zlength; lia).
  assert (Z2 : forall l, 0 <= l < 16 -> Znth l c2 =
            if l =? b + 1 then Znth (b + 1) c + 2 else if l =? b then Znth b c - 1 else Znth l c).
  { intros l Hl. unfold c2. rewrite Znth_upd by lia.
    destruct (Z.eqb_spec l (b + 1)) as [->|]; rewrite !Z1 by lia.
    - destruct (Z.eqb_spec (b + 1) b); [lia|].
      assert (0 <= Znth (b + 1) c) by (apply Hnn; lia).
      specialize (Hle (b + 1) ltac:(lia)). apply u16_small; lia.
    - reflexivity. }
  unfold rstep_at; cbv zeta. fold c1. fold c2.
  split; [rewrite upd_Znth_Zlength; lia|].
  intros l Hl. rewrite Znth_upd by lia.
  specialize (Hle M ltac:(lia)).
  destruct (Z.eqb_spec l M) as [->|Hne].
  - rewrite Z2 by lia.
    destruct (Z.eqb_spec M (b + 1)) as [E|]; destruct (Z.eqb_spec M b); try lia;
      [rewrite <- E|]; rewrite u16_small; lia.
  - rewrite Z2 by lia. destruct (Z.eqb_spec l (b + 1)) as [E1|]; destruct (Z.eqb_spec l b) as [E2|]; subst; lia.
Qed.

Lemma rstep_at_kraft : kraftc M (rstep_at M c b) = kraftc M c - 1.
Proof.
  destruct rstep_at_Znth as [_ HZ].
  unfold kraftc.
  rewrite (lsum_ext _ (fun l => Znth l c * 2 ^ (M - l) +
             ((if l =? b then - 2 ^ (M - b) else 0) +
              ((if l =? b + 1 then 2 ^ (M - b) else 0) + (if l =? M then -1 else 0))))).
  2:{ intros l Hl. rewrite HZ by lia.
      destruct (Z.eqb_spec l b) as [E1|E1].
      { subst l. destruct (Z.eqb_spec b (b + 1)); [lia|]. destruct (Z.eqb_spec b M); [lia|]. ring. }
      destruct (Z.eqb_spec l (b + 1)) as [E2|E2].
      { subst l. destruct (Z.eqb_spec (b + 1) M) as [E3|E3].
        - rewrite E3, Z.sub_diag. replace (M - b) with 1 by lia. simpl. ring.
        - replace (M - b) with (Z.succ (M - (b + 1))) by lia. rewrite Z.pow_succ_r by lia. ring. }
      destruct (Z.eqb_spec l M) as [E3|E3].
      { subst l. rewrite Z.sub_diag. simpl. ring. }
      ring. }
  rewrite !lsum_add, !lsum_point.
  destruct (Z.leb_spec 1 b), (Z.leb_spec b (Z.of_nat (Z.to_nat M))), (Z.leb_spec 1 (b + 1)),
    (Z.leb_spec (b + 1) (Z.of_nat (Z.to_nat M))), (Z.leb_spec 1 M), (Z.leb_spec M (Z.of_nat (Z.to_nat M)));
    simpl; lia.
Qed.

Lemma rstep_at_tot : tot M (rstep_at M c b) = tot M c.
Proof.
  destruct rstep_at_Znth as [_ HZ].
  unfold tot.
  rewrite (lsum_ext _ (fun l => Znth l c +
             ((if l =? b then -1 else 0) + ((if l =? b + 1 then 2 else 0) + (if l =? M then -1 else 0))))).
  2:{ intros l Hl. rewrite HZ by lia.
      destruct (Z.eqb_spec l b); destruct (Z.eqb_spec l (b + 1)); destruct (Z.eqb_spec l M); lia. }
  rewrite !lsum_add, !lsum_point.
  destruct (Z.leb_spec 1 b), (Z.leb_spec b (Z.of_nat (Z.to_nat M))), (Z.leb_spec 1 (b + 1)),
    (Z.leb_spec (b + 1) (Z.of_nat (Z.to_nat M))), (Z.leb_spec 1 M), (Z.leb_spec M (Z.of_nat (Z.to_nat M)));
    simpl; lia.
Qed.

Lemma rstep_at_inv : rinv M J (rstep_at M c b).
Proof.
  destruct rstep_at_Znth as [Hlen' HZ].
  assert (Hk := rstep_at_kraft). assert (Ht := rstep_at_tot).
  destruct Hinv as [Hlen [Hnn [Htot [Htot' [Hk0 HcM]]]]].
  split; [auto|]. split; [|split; [lia|split; [lia|split; [lia|]]]].
  - intros l Hl. rewrite HZ by lia. specialize (Hnn l Hl).
    destruct (Z.eqb_spec l b); destruct (Z.eqb_spec l (b + 1)); destruct (Z.eqb_spec l M); subst; lia.
  - rewrite HZ by lia. destruct (Z.eqb_spec M b); destruct (Z.eqb_spec M (b + 1)); rewrite Z.eqb_refl; lia.
Qed.

End Step.

Lemma rstep_inv : forall M J c, 1 <= M <= 15 -> 0 <= J -> rinv M (J + 1) c ->
  rinv M J (rstep M c) /\ tot M (rstep M c) = tot M c /\
  (forall l, 0 <= l < 16 -> (l < 1 \/ M < l) -> Znth l (rstep M c) = Znth l c).
Proof.
  intros M J c HM HJ Hinv.
  destruct (step_level M J c HM HJ Hinv) as [b [Hb [Hb1 [Hcb _]]]].
  unfold rstep. rewrite Hb.
  split; [apply (rstep_at_inv M J c); auto|]. split; [apply (rstep_at_tot M J c); auto|].
  intros l Hl Hout. destruct (rstep_at_Znth M J c HM HJ Hinv b Hb1 Hcb) as [_ HZ].
  rewrite HZ by lia. destruct (Z.eqb_spec l b); destruct (Z.eqb_spec l (b + 1)); destruct (Z.eqb_spec l M); lia.
Qed.

Lemma iter_inv : forall M (J : nat) K c, 1 <= M <= 15 -> 0 <= K -> rinv M (Z.of_nat J + K) c ->
  rinv M K (Nat.iter J (rstep M) c) /\ tot M (Nat.iter J (rstep M) c) = tot M c /\
  (forall l, 0 <= l < 16 -> (l < 1 \/ M < l) -> Znth l (Nat.iter J (rstep M) c) = Znth l c).
Proof.
  intros M J; induction J as [|J IH]; intros K c HM HK Hinv.
  - simpl. split; [exact Hinv|split; auto].
  - destruct (IH (K + 1) c HM ltac:(lia)) as [H1 [H2 H3]]; [replace (Z.of_nat J + (K + 1)) with
      (Z.of_nat (S J) + K) by lia; exact Hinv|].
    destruct (rstep_inv M K _ HM HK H1) as [H4 [H5 H6]].
    simpl. split; [exact H4|split; [lia|]]. intros; rewrite H6, H3; auto.
Qed.

Lemma repair_iter : forall M (J f : nat) c, 1 <= M <= 15 -> rinv M (Z.of_nat (S J)) c -> (J <= f)%nat ->
  gen_bitlen_repair (S f) M c (2 * Z.of_nat (S J)) = Nat.iter (S J) (rstep M) c.
Proof.
  intros M J; induction J as [|J IH]; intros f c HM Hinv Hf.
  - rewrite repair_unfold. simpl. reflexivity.
  - rewrite repair_unfold. destruct f as [|f]; [lia|].
    replace (2 * Z.of_nat (S (S J)) - 2 >? 0) with true by (symmetry; apply Z.gtb_lt; lia).
    replace (2 * Z.of_nat (S (S J)) - 2) with (2 * Z.of_nat (S J)) by lia.
    destruct (rstep_inv M (Z.of_nat (S J)) c HM ltac:(lia)) as [H1 _];
      [replace (Z.of_nat (S J) + 1) with (Z.of_nat (S (S J))) by lia; exact Hinv|].
    rewrite (IH f (rstep M c) HM H1 ltac:(lia)).
    rewrite <- Nat.iter_succ_r. reflexivity.
Qed.

(** The repair loop, from overflow = 2 * I: I iterations, Kraft sum 2^M, counts nonnegative, c'_M >= 1. *)
Theorem repair_correct : forall M c I, 1 <= M <= 15 -> 1 <= I -> rinv M I c ->
  let c' := gen_bitlen_repair (Z.to_nat HEAP_SIZE) M c (2 * I) in
  c' = Nat.iter (Z.to_nat I) (rstep M) c /\
  Zlength c' = 16 /\ (forall l, 1 <= l <= M -> 0 <= Znth l c') /\
  kraftc M c' = 2 ^ M /\ 1 <= Znth M c' /\ tot M c' = tot M c /\
  (forall l, 0 <= l < 16 -> (l < 1 \/ M < l) -> Znth l c' = Znth l c).
Proof.
  intros M c I HM HI Hinv c'.
  assert (Hfuel : (Z.to_nat I - 1 <= 572)%nat).
  { destruct Hinv as [_ [Hnn [_ [Ht [_ HcM]]]]].
    assert (Znth M c <= tot M c) by (apply count_le_tot; auto; lia). lia. }
  assert (E : c' = Nat.iter (Z.to_nat I) (rstep M) c).
  { unfold c'. replace (Z.to_nat HEAP_SIZE) with (S 572) by reflexivity.
    replace (Z.to_nat I) with (S (Z.to_nat I - 1)) by lia.
    replace I with (Z.of_nat (S (Z.to_nat I - 1))) at 1 by lia.
    apply repair_iter; [exact HM| |lia].
    replace (Z.of_nat (S (Z.to_nat I - 1))) with I by lia. exact Hinv. }
  destruct (iter_inv M (Z.to_nat I) 0 c HM ltac:(lia)) as [[H1 [H2 [_ [_ [H5 H6]]]]] [H7 H8]];
    [rewrite Z2Nat.id by lia; rewrite Z.add_0_r; exact Hinv|].
  rewrite <- E in H1, H2, H5, H6, H7, H8.
  split; [exact E|]. split; [auto|]. split; [auto|]. split; [lia|]. split; [lia|]. auto.
Qed.

(** ** The repaired lengths in handout order *)

(** [lseq c k]: c_k copies of k, then c_{k-1} copies of k-1, ..., then c_1 copies of 1. *)
Fixpoint lseq (c : list Z) (k : nat) : list Z :=
  match k with
  | O => []
  | S k' => repeat (Z.of_nat (S k')) (Z.to_nat (Znth (Z.of_nat (S k')) c)) ++ lseq c k'
  end.

Definition lens (M : Z) (c : list Z) : list Z := lseq c (Z.to_nat M).

Fixpoint sumz (l : list Z) : Z := match l with [] => 0 | x :: r => x + sumz r end.

Lemma sumz_app : forall a b, sumz (a ++ b) = sumz a + sumz b.
Proof. induction a; simpl; intros; [lia|]. rewrite IHa; lia. Qed.

Lemma sumz_repeat : forall x n, sumz (repeat x n) = Z.of_nat n * x.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat sumz]. rewrite IH, Nat2Z.inj_succ. ring. Qed.

Lemma lseq_length : forall c k, (forall l, 1 <= l <= Z.of_nat k -> 0 <= Znth l c) ->
  Zlength (lseq c k) = lsum (fun l => Znth l c) k.
Proof.
  intros c k; induction k as [|k IH]; intros H; [reflexivity|].
  cbn [lseq]. rewrite Zlength_app, lsum_S, Zlength_repeat'. rewrite IH by (intros; apply H; lia).
  rewrite Z2Nat.id by (apply H; lia). lia.
Qed.

Lemma lseq_kraft : forall M c k, (forall l, 1 <= l <= Z.of_nat k -> 0 <= Znth l c) ->
  sumz (map (fun x => 2 ^ (M - x)) (lseq c k)) = lsum (fun l => Znth l c * 2 ^ (M - l)) k.
Proof.
  intros M c k; induction k as [|k IH]; intros H; [reflexivity|].
  cbn [lseq]. rewrite map_app, sumz_app, lsum_S, map_repeat, sumz_repeat. rewrite IH by (intros; apply H; lia).
  rewrite Z2Nat.id by (apply H; lia). lia.
Qed.

Lemma lseq_range : forall c k x, In x (lseq c k) -> 1 <= x <= Z.of_nat k.
Proof.
  intros c k; induction k as [|k IH]; intros x Hx; [destruct Hx|].
  cbn [lseq] in Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx].
  - apply repeat_spec in Hx. lia.
  - specialize (IH x Hx). lia.
Qed.

(** The repaired code: [tot] lengths, each in [1, M], Kraft sum exactly 1. *)
Theorem repaired_lens : forall M c I, 1 <= M <= 15 -> 1 <= I -> rinv M I c ->
  let L := lens M (gen_bitlen_repair (Z.to_nat HEAP_SIZE) M c (2 * I)) in
  Zlength L = tot M c /\ (forall x, In x L -> 1 <= x <= M) /\ sumz (map (fun x => 2 ^ (M - x)) L) = 2 ^ M.
Proof.
  intros M c I HM HI Hinv L.
  destruct (repair_correct M c I HM HI Hinv) as [_ [_ [Hnn [Hk [_ [Ht _]]]]]].
  split; [|split].
  - unfold L, lens. rewrite lseq_length; [exact Ht|]. intros; apply Hnn; lia.
  - intros x Hx. apply lseq_range in Hx. lia.
  - unfold L, lens. rewrite lseq_kraft; [exact Hk|]. intros; apply Hnn; lia.
Qed.

(** ** The reassignment: lengths handed out along the heap scan *)

(** One step of the inner loop, on leaf [m]. *)
Definition lstep (m bits : Z) (t : tree) (opt : Z) : tree * Z :=
  if negb (Znth m (dl t) =? bits) then
    (set_dl t m (u16 bits), u64 (opt + u64 (bits - Znth m (dl t)) * Znth m (fc t)))
  else (t, opt).

Fixpoint apply_lens (ms ls : list Z) (t : tree) (opt : Z) : tree * Z :=
  match ms, ls with
  | m :: ms', l :: ls' => let '(t', opt') := lstep m l t opt in apply_lens ms' ls' t' opt'
  | _, _ => (t, opt)
  end.

(** The leaves ([<= mc]) among the heap positions [h-1], [h-2], ..., [h-k], in that order. *)
Fixpoint scan (heap : list Z) (mc h : Z) (k : nat) : list Z :=
  match k with
  | O => []
  | S k' => let m := Znth (h - 1) heap in
            if m >? mc then scan heap mc (h - 1) k' else m :: scan heap mc (h - 1) k'
  end.

Lemma inner_unfold : forall f mc bits heap t opt h n,
  gen_bitlen_reassign_inner (S f) mc bits heap t opt h n =
  if n =? 0 then (t, opt, h)
  else if Znth (h - 1) heap >? mc then gen_bitlen_reassign_inner f mc bits heap t opt (h - 1) n
  else let '(t', opt') := lstep (Znth (h - 1) heap) bits t opt in
       gen_bitlen_reassign_inner f mc bits heap t' opt' (h - 1) (n - 1).
Proof. reflexivity. Qed.

Lemma outer_unfold : forall f mc heap c t opt h bits,
  gen_bitlen_reassign (S f) mc heap c t opt h bits =
  if bits =? 0 then (t, opt)
  else let '(t', opt', h') := gen_bitlen_reassign_inner (Z.to_nat HEAP_SIZE) mc bits heap t opt h (Znth bits c) in
       gen_bitlen_reassign f mc heap c t' opt' h' (bits - 1).
Proof. reflexivity. Qed.

Lemma inner_spec : forall mc bits heap f k h n t opt,
  (k <= f)%nat -> (n <= length (scan heap mc h k))%nat ->
  exists k', (k' <= k)%nat /\
    gen_bitlen_reassign_inner f mc bits heap t opt h (Z.of_nat n) =
      (fst (apply_lens (firstn n (scan heap mc h k)) (repeat bits n) t opt),
       snd (apply_lens (firstn n (scan heap mc h k)) (repeat bits n) t opt),
       h - Z.of_nat (k - k')) /\
    scan heap mc (h - Z.of_nat (k - k')) k' = skipn n (scan heap mc h k).
Proof.
  intros mc bits heap f; induction f as [|f IH]; intros k h n t opt Hk Hn.
  - assert (k = O) by lia; subst k. simpl in Hn. assert (n = O) by lia; subst n.
    exists O. simpl. rewrite Z.sub_0_r. auto.
  - rewrite inner_unfold. destruct n as [|n].
    + exists k. simpl. rewrite Nat.sub_diag, Z.sub_0_r. auto.
    + destruct k as [|k]; [simpl in Hn; lia|].
      replace (Z.of_nat (S n) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [scan] in *. destruct (Znth (h - 1) heap >? mc).
      * destruct (IH k (h - 1) (S n) t opt ltac:(lia) Hn) as [k' [Hk' [E1 E2]]].
        exists k'. split; [lia|]. rewrite E1.
        replace (h - 1 - Z.of_nat (k - k')) with (h - Z.of_nat (S k - k')) in * by lia. auto.
      * cbn [length] in Hn. cbn [firstn repeat apply_lens].
        destruct (lstep (Znth (h - 1) heap) bits t opt) as [t1 o1].
        replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
        destruct (IH k (h - 1) n t1 o1 ltac:(lia) ltac:(lia)) as [k' [Hk' [E1 E2]]].
        exists k'. split; [lia|]. rewrite E1. cbn [skipn].
        replace (h - 1 - Z.of_nat (k - k')) with (h - Z.of_nat (S k - k')) in * by lia. auto.
Qed.

Lemma apply_lens_app : forall ms1 ls1 ms2 ls2 t opt, length ms1 = length ls1 ->
  apply_lens (ms1 ++ ms2) (ls1 ++ ls2) t opt =
  apply_lens ms2 ls2 (fst (apply_lens ms1 ls1 t opt)) (snd (apply_lens ms1 ls1 t opt)).
Proof.
  induction ms1 as [|m ms1 IH]; intros [|l ls1] ms2 ls2 t opt Hl; try discriminate; [reflexivity|].
  cbn [app apply_lens]. destruct (lstep m l t opt) as [t1 o1]. apply IH. simpl in Hl; lia.
Qed.

Lemma firstn_add : forall {A} (n m : nat) (l : list A), firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  intros A n; induction n as [|n IH]; intros m [|x l]; simpl; auto. destruct m; auto.
  rewrite IH. reflexivity.
Qed.

Lemma lseq_length_nat : forall c k, (forall l, 1 <= l <= Z.of_nat k -> 0 <= Znth l c) ->
  length (lseq c k) = Z.to_nat (lsum (fun l => Znth l c) k).
Proof.
  intros c k H. rewrite <- lseq_length by auto. rewrite Zlength_correct, Nat2Z.id. reflexivity.
Qed.

Lemma outer_spec : forall mc heap c (kb f : nat) k h t opt,
  (kb < f)%nat -> (k <= Z.to_nat HEAP_SIZE)%nat -> (forall l, 1 <= l <= Z.of_nat kb -> 0 <= Znth l c) ->
  (length (lseq c kb) <= length (scan heap mc h k))%nat ->
  gen_bitlen_reassign f mc heap c t opt h (Z.of_nat kb) =
  apply_lens (firstn (length (lseq c kb)) (scan heap mc h k)) (lseq c kb) t opt.
Proof.
  intros mc heap c kb; induction kb as [|kb IH]; intros f k h t opt Hf Hk Hnn Hlen.
  - destruct f as [|f]; [lia|]. rewrite outer_unfold. reflexivity.
  - destruct f as [|f]; [lia|]. rewrite outer_unfold.
    replace (Z.of_nat (S kb) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    set (nn := Z.to_nat (Znth (Z.of_nat (S kb)) c)).
    assert (Hc : Znth (Z.of_nat (S kb)) c = Z.of_nat nn) by (unfold nn; rewrite Z2Nat.id; auto; apply Hnn; lia).
    rewrite Hc.
    assert (Hl : length (lseq c (S kb)) = (nn + length (lseq c kb))%nat).
    { cbn [lseq]. rewrite length_app, repeat_length. reflexivity. }
    rewrite Hl in *.
    destruct (inner_spec mc (Z.of_nat (S kb)) heap (Z.to_nat HEAP_SIZE) k h nn t opt Hk ltac:(lia))
      as [k' [Hk' [E1 E2]]].
    rewrite E1. cbv beta iota. replace (Z.of_nat (S kb) - 1) with (Z.of_nat kb) by lia.
    rewrite (IH f k' (h - Z.of_nat (k - k'))); [| lia | lia | intros; apply Hnn; lia |].
    2:{ rewrite E2, length_skipn. lia. }
    rewrite E2. cbn [lseq]. rewrite firstn_add, apply_lens_app.
    + reflexivity.
    + rewrite length_firstn, repeat_length. lia.
Qed.

(** [gen_bitlen_reassign] = the lengths [lens M c], in order, on the first [tot M c] leaves of the scan from
    [HEAP_SIZE - 1] down. *)
Theorem reassign_correct : forall mc heap c t opt M k,
  1 <= M <= 15 -> (forall l, 1 <= l <= M -> 0 <= Znth l c) -> (k <= Z.to_nat HEAP_SIZE)%nat ->
  (Z.to_nat (tot M c) <= length (scan heap mc HEAP_SIZE k))%nat ->
  gen_bitlen_reassign 20 mc heap c t opt HEAP_SIZE M =
  apply_lens (firstn (Z.to_nat (tot M c)) (scan heap mc HEAP_SIZE k)) (lens M c) t opt.
Proof.
  intros mc heap c t opt M k HM Hnn Hk Hlen.
  assert (Hl : length (lens M c) = Z.to_nat (tot M c)).
  { unfold lens, tot. apply lseq_length_nat. intros; apply Hnn; lia. }
  replace M with (Z.of_nat (Z.to_nat M)) at 1 by lia.
  rewrite (outer_spec mc heap c (Z.to_nat M) 20 k); [| lia | auto | intros; apply Hnn; lia |].
  - fold (lens M c). rewrite Hl. reflexivity.
  - fold (lens M c). lia.
Qed.

(** The effect of [apply_lens] on distinct leaves. *)
Fixpoint dsum (ms ls D F : list Z) : Z :=
  match ms, ls with
  | m :: ms', l :: ls' => (l - Znth m D) * Znth m F + dsum ms' ls' D F
  | _, _ => 0
  end.

Lemma dsum_ext : forall ms ls D1 F1 D2 F2, (forall m, In m ms -> Znth m D1 = Znth m D2 /\ Znth m F1 = Znth m F2) ->
  dsum ms ls D1 F1 = dsum ms ls D2 F2.
Proof.
  induction ms as [|m ms IH]; intros [|l ls] D1 F1 D2 F2 H; auto. cbn [dsum].
  destruct (H m (or_introl eq_refl)) as [-> ->]. rewrite (IH ls D1 F1 D2 F2); auto.
  intros; apply H; right; auto.
Qed.

Lemma u64_add_mul : forall a x y, u64 (a + u64 x * y) = u64 (a + x * y).
Proof.
  intros. unfold u64. rewrite Z.add_mod, Z.mul_mod, Z.mod_mod, <- Z.mul_mod, <- Z.add_mod by lia. reflexivity.
Qed.

Lemma u64_u64_add : forall a b, u64 (u64 a + b) = u64 (a + b).
Proof. intros. unfold u64. rewrite Z.add_mod_idemp_l by lia. reflexivity. Qed.

Theorem apply_lens_spec : forall ms ls t opt,
  NoDup ms -> length ms = length ls -> (forall m, In m ms -> 0 <= m < Zlength (dl t)) ->
  (forall l, In l ls -> 0 <= l < 65536) -> 0 <= opt < 18446744073709551616 ->
  let r := apply_lens ms ls t opt in
  fc (fst r) = fc t /\ Zlength (dl (fst r)) = Zlength (dl t) /\
  (forall i, 0 <= i < Zlength ms -> Znth (Znth i ms) (dl (fst r)) = Znth i ls) /\
  (forall m, ~ In m ms -> Znth m (dl (fst r)) = Znth m (dl t)) /\
  snd r = u64 (opt + dsum ms ls (dl t) (fc t)).
Proof.
  induction ms as [|m ms IH]; intros [|l ls] t opt Hnd Hlen Hm Hl Hopt; try discriminate.
  - simpl. split; [auto|split; [auto|split; [intros i Hi; rewrite Zlength_nil in Hi; lia|split; [auto|]]]].
    unfold u64. rewrite Z.add_0_r, Z.mod_small; auto.
  - inversion Hnd as [|? ? Hnin Hnd']; subst.
    assert (Hm0 := Hm m (or_introl eq_refl)). assert (Hl0 := Hl l (or_introl eq_refl)).
    (* the step on m *)
    assert (Hst : exists t1 o1, lstep m l t opt = (t1, o1) /\ fc t1 = fc t /\ Zlength (dl t1) = Zlength (dl t) /\
              Znth m (dl t1) = l /\ (forall m', m' <> m -> Znth m' (dl t1) = Znth m' (dl t)) /\
              o1 = u64 (opt + (l - Znth m (dl t)) * Znth m (fc t))).
    { unfold lstep. destruct (Znth m (dl t) =? l) eqn:E; simpl.
      - apply Z.eqb_eq in E. exists t, opt. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
        split; [auto|]. rewrite E, Z.sub_diag, Z.mul_0_l, Z.add_0_r. unfold u64. rewrite Z.mod_small; auto.
      - eexists _, _. split; [reflexivity|]. unfold set_dl; simpl.
        split; [auto|]. split; [rewrite upd_Znth_Zlength; lia|].
        split; [rewrite upd_Znth_same by lia; apply u16_small; lia|].
        split; [|apply u64_add_mul].
        intros m' Hne. apply upd_Znth_diff'; lia. }
    destruct Hst as [t1 [o1 [Est [Hfc [Hlen1 [Hmm [Hoth Ho1]]]]]]].
    cbn [apply_lens]. rewrite Est.
    assert (Ho1r : 0 <= o1 < 18446744073709551616) by (rewrite Ho1; unfold u64; apply Z.mod_pos_bound; lia).
    destruct (IH ls t1 o1 Hnd' ltac:(simpl in Hlen; lia)) as [H1 [H2 [H3 [H4 H5]]]]; auto.
    { intros m' Hm'. rewrite Hlen1. apply Hm; right; auto. }
    { intros; apply Hl; right; auto. }
    split; [congruence|]. split; [congruence|]. split; [|split].
    + intros i Hi. rewrite Zlength_cons in Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
      * rewrite !Znth_0_cons. rewrite H4 by auto. exact Hmm.
      * rewrite !Znth_pos_cons by lia. apply H3. lia.
    + intros m' Hm'. rewrite H4 by (intro; apply Hm'; right; auto). apply Hoth. intro; apply Hm'; left; auto.
    + rewrite H5, Ho1, u64_u64_add. cbn [dsum].
      rewrite (dsum_ext ms ls (dl t1) (fc t1) (dl t) (fc t)).
      * f_equal. ring.
      * intros m' Hm'. split; [apply Hoth; intro; subst; contradiction|congruence].
Qed.


(** ** Clamped counts of a depth list *)

Definition levels16 : list Z := map Z.of_nat (seq 0 16).

Definition cntz (P : Z -> bool) (d : list Z) : Z := Z.of_nat (length (filter P d)).

(** bl_count after the first pass, from the depths [d] of the leaves: c_l = #{x in d : min x M = l}, l >= 1. *)
Definition clampc (M : Z) (d : list Z) : list Z :=
  map (fun l => if l =? 0 then 0 else cntz (fun x => Z.min x M =? l) d) levels16.

(** The repaired lengths, in handout order. *)
Definition repl (M : Z) (d : list Z) : list Z :=
  let c := clampc M d in lens M (Nat.iter (Z.to_nat (kraftc M c - 2 ^ M)) (rstep M) c).

Lemma levels16_len : Zlength levels16 = 16.
Proof. reflexivity. Qed.

Lemma Znth_levels16 : forall l, 0 <= l < 16 -> Znth l levels16 = l.
Proof.
  intros l Hl. unfold levels16. rewrite Znth_map by (rewrite Zlength_correct, length_seq; lia).
  unfold Znth. destruct (Z_lt_dec l 0); [lia|]. rewrite seq_nth by lia. lia.
Qed.

Lemma clampc_len : forall M d, Zlength (clampc M d) = 16.
Proof. intros. unfold clampc. rewrite Zlength_map. reflexivity. Qed.

Lemma Znth_clampc : forall M d l, 0 <= l < 16 ->
  Znth l (clampc M d) = if l =? 0 then 0 else cntz (fun x => Z.min x M =? l) d.
Proof.
  intros M d l Hl. unfold clampc. rewrite Znth_map by (rewrite levels16_len; lia).
  rewrite Znth_levels16 by lia. reflexivity.
Qed.

Lemma cntz_cons : forall P x d, cntz P (x :: d) = (if P x then 1 else 0) + cntz P d.
Proof. intros. unfold cntz. simpl. destruct (P x); simpl length; lia. Qed.

Lemma clamp_sums : forall M d, 1 <= M <= 15 -> (forall x, In x d -> 1 <= x) ->
  kraftc M (clampc M d) = sumz (map (fun x => 2 ^ (M - Z.min x M)) d) /\
  tot M (clampc M d) = Zlength d.
Proof.
  intros M d HM; induction d as [|x d IH]; intros Hd.
  - unfold kraftc, tot. split.
    + rewrite (lsum_ext _ (fun _ => 0)); [apply lsum_zero|]. intros l Hl.
      rewrite Znth_clampc by lia. destruct (l =? 0); reflexivity.
    + rewrite (lsum_ext _ (fun _ => 0)); [apply lsum_zero|]. intros l Hl.
      rewrite Znth_clampc by lia. destruct (l =? 0); reflexivity.
  - destruct IH as [IH1 IH2]; [intros; apply Hd; right; auto|].
    assert (Hx := Hd x (or_introl eq_refl)).
    assert (Hpt : forall l, 1 <= l <= M ->
              Znth l (clampc M (x :: d)) = Znth l (clampc M d) + (if l =? Z.min x M then 1 else 0)).
    { intros l Hl. rewrite !Znth_clampc by lia. destruct (Z.eqb_spec l 0); [lia|].
      rewrite cntz_cons. destruct (Z.eqb_spec (Z.min x M) l); destruct (Z.eqb_spec l (Z.min x M)); lia. }
    split.
    + unfold kraftc in *. cbn [map sumz].
      rewrite (lsum_ext _ (fun l => Znth l (clampc M d) * 2 ^ (M - l) +
                                (if l =? Z.min x M then 2 ^ (M - Z.min x M) else 0))).
      2:{ intros l Hl. rewrite Hpt by lia. destruct (Z.eqb_spec l (Z.min x M)) as [->|]; ring. }
      rewrite lsum_add, lsum_point, IH1.
      destruct (Z.leb_spec 1 (Z.min x M)), (Z.leb_spec (Z.min x M) (Z.of_nat (Z.to_nat M))); simpl; lia.
    + unfold tot in *. rewrite Zlength_cons.
      rewrite (lsum_ext _ (fun l => Znth l (clampc M d) + (if l =? Z.min x M then 1 else 0))).
      2:{ intros l Hl. rewrite Hpt by lia. reflexivity. }
      rewrite lsum_add, lsum_point, IH2.
      destruct (Z.leb_spec 1 (Z.min x M)), (Z.leb_spec (Z.min x M) (Z.of_nat (Z.to_nat M))); simpl; lia.
Qed.

Lemma sumz_scale : forall {A} (g : A -> Z) a l, sumz (map (fun x => a * g x) l) = a * sumz (map g l).
Proof. intros A g a l; induction l as [|x l IH]; simpl; [lia|]. rewrite IH. ring. Qed.

Lemma sumz_le : forall {A} (g h : A -> Z) l, (forall x, In x l -> g x <= h x) -> sumz (map g l) <= sumz (map h l).
Proof.
  intros A g h l; induction l as [|x l IH]; intros H; simpl; [lia|].
  specialize (IH (fun y Hy => H y (or_intror Hy))). specialize (H x (or_introl eq_refl)). lia.
Qed.

Lemma sumz_nonneg : forall {A} (g : A -> Z) l, (forall x, In x l -> 0 <= g x) -> 0 <= sumz (map g l).
Proof.
  intros A g l H. replace 0 with (sumz (map (fun _ : A => 0) l)) at 1.
  - apply sumz_le; auto.
  - clear H. induction l; simpl; auto.
Qed.

(** The clamped counts of a complete code with a leaf deeper than M satisfy the loop invariant, with
    I = (Kraft sum of the clamped counts) - 2^M >= 1 iterations to go. *)
Theorem clamp_rinv : forall M D d, 1 <= M <= 15 -> M <= D ->
  (forall x, In x d -> 1 <= x <= D) -> sumz (map (fun x => 2 ^ (D - x)) d) = 2 ^ D ->
  Zlength d <= 2 ^ M -> Zlength d <= 573 -> (exists x, In x d /\ M < x) ->
  let I := kraftc M (clampc M d) - 2 ^ M in 1 <= I /\ rinv M I (clampc M d).
Proof.
  intros M D d HM HD Hd Hk Hn1 Hn2 [x0 [Hx0 Hx0M]] I.
  destruct (clamp_sums M d HM) as [Hkc Htc]; [intros; apply Hd; auto|].
  assert (Hsc : 2 ^ (D - M) * kraftc M (clampc M d) = sumz (map (fun x => 2 ^ (D - Z.min x M)) d)).
  { rewrite Hkc, <- sumz_scale. f_equal. apply map_ext_in. intros x Hx. rewrite <- Z.pow_add_r by lia.
    f_equal. lia. }
  set (deep := filter (fun x => M <? x) d).
  set (shal := filter (fun x => negb (M <? x)) d).
  assert (Hsplit : forall g : Z -> Z, sumz (map g d) = sumz (map g deep) + sumz (map g shal)).
  { intro g. unfold deep, shal. clear. induction d as [|x d IH]; simpl; [lia|].
    destruct (M <? x); simpl; rewrite IH; lia. }
  assert (Hshallow : forall x, In x shal -> Z.min x M = x).
  { intros x Hx. apply filter_In in Hx. destruct Hx as [_ Hx]. apply negb_true_iff, Z.ltb_ge in Hx. lia. }
  assert (Hdeep : forall x, In x deep -> In x d /\ M < x).
  { intros x Hx. apply filter_In in Hx. destruct Hx as [Hx1 Hx]. apply Z.ltb_lt in Hx. auto. }
  set (T := sumz (map (fun x => 2 ^ (D - x)) deep)).
  assert (HT : 0 < T).
  { unfold T. assert (Hin : In x0 deep) by (apply filter_In; split; auto; apply Z.ltb_lt; lia).
    clear -Hin Hd Hdeep. induction deep as [|y r IH]; [destruct Hin|]. simpl.
    assert (0 <= sumz (map (fun x => 2 ^ (D - x)) r)) by (apply sumz_nonneg; intros; apply Z.pow_nonneg; lia).
    assert (0 < 2 ^ (D - y)) by (apply Z.pow_pos_nonneg; [lia|]; destruct (Hdeep y (or_introl eq_refl)) as [Hy _];
      specialize (Hd y Hy); lia).
    lia. }
  assert (Hmass : sumz (map (fun x => 2 ^ (D - Z.min x M)) deep) = Z.of_nat (length deep) * 2 ^ (D - M)).
  { clear -Hdeep. induction deep as [|y r IH]; cbn [map sumz length]; [lia|].
    destruct (Hdeep y (or_introl eq_refl)) as [_ Hy]. replace (Z.min y M) with M by lia.
    rewrite IH by (intros; apply Hdeep; right; auto). rewrite Nat2Z.inj_succ. ring. }
  assert (Hsh : sumz (map (fun x => 2 ^ (D - Z.min x M)) shal) = sumz (map (fun x => 2 ^ (D - x)) shal)).
  { f_equal. apply map_ext_in. intros x Hx. rewrite Hshallow; auto. }
  assert (HI : 2 ^ (D - M) * I = Z.of_nat (length deep) * 2 ^ (D - M) - T).
  { unfold I. rewrite Z.mul_sub_distr_l, Hsc, Hsplit, Hmass, Hsh.
    rewrite <- Z.pow_add_r by lia. replace (D - M + M) with D by lia.
    rewrite <- Hk, (Hsplit (fun x => 2 ^ (D - x))). unfold T. lia. }
  assert (Hpos : 0 < 2 ^ (D - M)) by (apply Z.pow_pos_nonneg; lia).
  assert (HT2 : 2 * T <= Z.of_nat (length deep) * 2 ^ (D - M)).
  { unfold T. clear -Hdeep HM HD Hd. induction deep as [|y r IH]; cbn [map sumz length]; [lia|].
    rewrite Nat2Z.inj_succ.
    destruct (Hdeep y (or_introl eq_refl)) as [Hyin Hy]. assert (Hyd := Hd y Hyin).
    assert (2 * 2 ^ (D - y) <= 2 ^ (D - M)).
    { rewrite <- Z.pow_succ_r by lia. apply Z.pow_le_mono_r; lia. }
    assert (2 * sumz (map (fun x => 2 ^ (D - x)) r) <= Z.of_nat (length r) * 2 ^ (D - M))
      by (apply IH; intros; apply Hdeep; right; auto). lia. }
  assert (HIlt : I < Z.of_nat (length deep)) by nia.
  assert (HIge : 1 <= I) by nia.
  split; [exact HIge|].
  assert (Hcm : Z.of_nat (length deep) <= Znth M (clampc M d)).
  { rewrite Znth_clampc by lia. destruct (Z.eqb_spec M 0); [lia|]. unfold cntz, deep.
    apply Nat2Z.inj_le. clear -HM. induction d as [|x d IH]; simpl; [lia|].
    destruct (Z.ltb_spec M x); simpl.
    - replace (Z.min x M =? M) with true by (symmetry; apply Z.eqb_eq; lia). simpl. lia.
    - destruct (Z.min x M =? M); simpl; lia. }
  split; [apply clampc_len|]. split.
  { intros l Hl. rewrite Znth_clampc by lia. destruct (l =? 0); [lia|]. unfold cntz; lia. }
  split; [lia|]. split; [lia|]. split; [unfold I; lia|]. lia.
Qed.

(** The model's repair, on the clamped counts of [d], gives [repl M d]. *)
Lemma repl_model : forall M d I, 1 <= M <= 15 -> I = kraftc M (clampc M d) - 2 ^ M -> 1 <= I ->
  rinv M I (clampc M d) ->
  lens M (gen_bitlen_repair (Z.to_nat HEAP_SIZE) M (clampc M d) (2 * I)) = repl M d.
Proof.
  intros M d I HM HI HI1 Hinv. destruct (repair_correct M (clampc M d) I HM HI1 Hinv) as [E _].
  rewrite E. unfold repl. rewrite <- HI. reflexivity.
Qed.

(** ** The cost of the repair against the Huffman depths *)

(** [dlt f L d] = sum_k f_k * (L_k - d_k): the cost increase when the k-th leaf of the scan (frequency f_k,
    Huffman depth d_k) gets length L_k. *)
Fixpoint dlt (f L d : list Z) : Z :=
  match f, L, d with x :: f', y :: L', z :: d' => x * (y - z) + dlt f' L' d' | _, _, _ => 0 end.

(** Nonincreasing lists. *)
Fixpoint dsorted (l : list Z) : Prop :=
  match l with [] => True | x :: r => (forall y, In y r -> y <= x) /\ dsorted r end.

Lemma dsorted_nth : forall d, (forall k, (S k < length d)%nat -> nth (S k) d 0 <= nth k d 0) -> dsorted d.
Proof.
  induction d as [|x d IH]; intros H; simpl; auto. split.
  - intros y Hy. destruct (In_nth d y 0 Hy) as [k [Hk <-]].
    clear Hy. induction k as [|k IHk].
    + apply (H 0%nat). simpl; lia.
    + assert (nth (S k) d 0 <= nth k d 0) by (apply (H (S k)); simpl; lia). specialize (IHk ltac:(lia)). lia.
  - apply IH. intros k Hk. apply (H (S k)). simpl; lia.
Qed.

Lemma fibn_succ_ge : forall n, fibn n <= fibn (S n).
Proof.
  destruct n as [|n]; [simpl; lia|]. change (fibn (S (S n))) with (fibn (S n) + fibn n).
  assert (0 <= fibn n) by apply fibn_nonneg. lia.
Qed.

Lemma fibn_mono : forall n m, (n <= m)%nat -> fibn n <= fibn m.
Proof.
  intros n m H; induction H as [|m H IH]; [lia|]. assert (Hs := fibn_succ_ge m). lia.
Qed.

Lemma fib_mono : forall a b, 0 <= a <= b -> fib a <= fib b.
Proof. intros a b H. unfold fib. apply fibn_mono. lia. Qed.

Lemma fib_pos : forall a, 1 <= a -> 1 <= fib a.
Proof. intros a H. assert (fib 1 <= fib a) by (apply fib_mono; lia). change (fib 1) with 1 in H0. lia. Qed.

(** A cost bound per position: f in [1, cap] gives f * dl <= bnd cap dl. *)
Definition bnd (cap dl : Z) : Z := if 0 <? dl then dl * cap else dl.

(** [bsum e Wm L d]: the bound with the caps f_k <= Wm / fib (d_k + 1 + e). *)
Fixpoint bsum (e Wm : Z) (L d : list Z) : Z :=
  match L, d with y :: L', z :: d' => bnd (Wm / fib (z + 1 + e)) (y - z) + bsum e Wm L' d' | _, _ => 0 end.

Lemma dlt_le_bsum : forall e Wm f L d, 0 <= e -> length f = length d -> length L = length d ->
  (forall k, (k < length d)%nat ->
     1 <= nth k f 0 /\ 0 <= nth k d 0 /\ fib (nth k d 0 + 1 + e) * nth k f 0 <= Wm) ->
  dlt f L d <= bsum e Wm L d.
Proof.
  intros e Wm f L d He; revert f L; induction d as [|z d IH]; intros [|x f] [|y L] Hf HL H;
    simpl in Hf, HL; try lia; [simpl; lia|]. cbn [dlt bsum].
  assert (IH' := IH f L ltac:(simpl in *; lia) ltac:(simpl in *; lia)
                   (fun k Hk => H (S k) ltac:(simpl; lia))).
  destruct (H 0%nat ltac:(simpl; lia)) as [Hx [Hz Hc]]. simpl in Hx, Hz, Hc.
  assert (Hfp : 1 <= fib (z + 1 + e)) by (apply fib_pos; lia).
  assert (Hcap : x <= Wm / fib (z + 1 + e)) by (apply Z.div_le_lower_bound; lia).
  unfold bnd. destruct (Z.ltb_spec 0 (y - z)); nia.
Qed.

(** ** The bit-length tree: M = 7, at most 19 leaves, total weight at most 320 *)

Fixpoint forall_le (m : nat) (P : nat -> bool) : bool :=
  match m with O => P O | S m' => P (S m') && forall_le m' P end.

Lemma forall_le_spec : forall m P, forall_le m P = true -> forall i, (i <= m)%nat -> P i = true.
Proof.
  induction m as [|m IH]; intros P H i Hi; simpl in H.
  - assert (i = O) by lia; subst; auto.
  - apply andb_true_iff in H. destruct H as [H1 H2]. destruct (Nat.eq_dec i (S m)) as [->|]; auto.
    apply IH; auto; lia.
Qed.

(** The bounds on the cost increase, by alphabet size n: [dbl] with the caps f * fib (d + 1) <= W
    ([HuffAbs.huff_fib]), [dbl2] with the caps f * fib (d + 2) <= W. *)
Definition dbl (n : nat) : Z :=
  if (n <=? 8)%nat then 0 else nth (n - 9) [22; 37; 57; 94; 101; 101; 128; 164; 164; 200; 260] 260.

Definition dbl2 (n : nat) : Z :=
  if (n <=? 8)%nat then 0 else nth (n - 9) [13; 21; 32; 53; 59; 59; 71; 91; 91; 111; 147] 147.

Definition dblt (e : Z) (n : nat) : Z := if e =? 0 then dbl n else dbl2 n.

Definition leaf_ok (e : Z) (d : list Z) : bool :=
  Nat.eqb (length (repl 7 d)) (length d) && (bsum e 320 (repl 7 d) d <=? dblt e (length d)).

(** [chk] on all nonincreasing depth lists with values in [1, 12], at most 19 entries and Kraft sum 1: [acc]
    holds the entries shallower than [l] chosen so far, [rem] the Kraft mass (in units 2^-12) still to place. *)
Fixpoint enum (chk : list Z -> bool) (fuel : nat) (l rem : Z) (nl : nat) (acc : list Z) : bool :=
  match fuel with
  | O => if rem =? 0 then chk acc else true
  | S fuel' =>
    if Z.of_nat nl * 2 ^ (12 - l) <? rem then true
    else forall_le (Nat.min (Z.to_nat (rem / 2 ^ (12 - l))) nl)
           (fun x => enum chk fuel' (l + 1) (rem - Z.of_nat x * 2 ^ (12 - l)) (nl - x) (repeat l x ++ acc))
  end.

Lemma enum_ok0 : enum (leaf_ok 0) 12 1 4096 19 [] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma enum_ok1 : enum (leaf_ok 1) 12 1 4096 19 [] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dsorted_app_l : forall a b, dsorted (a ++ b) -> dsorted a.
Proof.
  induction a as [|x a IH]; intros b H; simpl in *; auto. destruct H as [H1 H2]. split; eauto.
  intros y Hy; apply H1, in_or_app; auto.
Qed.

Lemma split_last : forall pre l, dsorted pre -> (forall y, In y pre -> l <= y) ->
  exists pre' x, pre = pre' ++ repeat l x /\ (forall y, In y pre' -> l < y) /\ dsorted pre'.
Proof.
  induction pre as [|y r IH]; intros l Hs Hl.
  - exists [], O. simpl. split; [auto|split; [intros _ []|exact I]].
  - destruct Hs as [Hhd Hs]. destruct (IH l Hs (fun z Hz => Hl z (or_intror Hz))) as [r' [x [Er [Hgt Hs']]]].
    assert (Hyl := Hl y (or_introl eq_refl)).
    destruct (Z.eq_dec y l) as [->|Hne].
    + destruct r' as [|z r''].
      * exists [], (S x). simpl. rewrite Er. split; [auto|split; [intros _ []|exact I]].
      * exfalso. assert (In z r) by (rewrite Er; left; auto).
        specialize (Hhd z H). specialize (Hgt z (or_introl eq_refl)). lia.
    + exists (y :: r'), x. split; [rewrite Er; reflexivity|]. split.
      * intros z [<-|Hz]; [lia|auto].
      * split; auto. intros z Hz. apply Hhd. rewrite Er. apply in_or_app; auto.
Qed.

Lemma sumz_le_const : forall {A} (g : A -> Z) c l, (forall x, In x l -> g x <= c) ->
  sumz (map g l) <= Z.of_nat (length l) * c.
Proof.
  intros A g c l; induction l as [|x l IH]; intros H; cbn [map sumz length]; [lia|].
  rewrite Nat2Z.inj_succ. specialize (IH (fun y Hy => H y (or_intror Hy))). specialize (H x (or_introl eq_refl)).
  lia.
Qed.

Lemma enum_complete : forall chk fuel l rem nl acc pre,
  enum chk fuel l rem nl acc = true -> l + Z.of_nat fuel = 13 -> 1 <= l ->
  dsorted pre -> (forall y, In y pre -> l <= y <= 12) ->
  sumz (map (fun x => 2 ^ (12 - x)) pre) = rem -> (length pre <= nl)%nat ->
  chk (pre ++ acc) = true.
Proof.
  intros chk; induction fuel as [|f IH]; intros l rem nl acc pre He Hl Hl1 Hs Hr Hk Hn.
  - destruct pre as [|y pre]; [|specialize (Hr y (or_introl eq_refl)); lia].
    simpl in Hk. subst rem. exact He.
  - cbn [enum] in He.
    assert (Hu : 0 < 2 ^ (12 - l)) by (apply Z.pow_pos_nonneg; lia).
    destruct (Z.ltb_spec (Z.of_nat nl * 2 ^ (12 - l)) rem) as [Hlt|Hge].
    + exfalso. assert (sumz (map (fun x => 2 ^ (12 - x)) pre) <= Z.of_nat (length pre) * 2 ^ (12 - l)).
      { apply sumz_le_const. intros x Hx. apply Z.pow_le_mono_r; [lia|]. specialize (Hr x Hx). lia. }
      nia.
    + destruct (split_last pre l Hs (fun y Hy => proj1 (Hr y Hy))) as [pre' [x [Ep [Hgt Hs']]]].
      subst pre. rewrite map_app, sumz_app, map_repeat, sumz_repeat in Hk.
      rewrite length_app, repeat_length in Hn.
      assert (H0 : 0 <= sumz (map (fun x => 2 ^ (12 - x)) pre'))
        by (apply sumz_nonneg; intros; apply Z.pow_nonneg; lia).
      assert (Hx1 : Z.of_nat x <= rem / 2 ^ (12 - l)) by (apply Z.div_le_lower_bound; lia).
      assert (Hx : (x <= Nat.min (Z.to_nat (rem / 2 ^ (12 - l))) nl)%nat) by lia.
      assert (He' := forall_le_spec _ _ He x Hx). cbv beta in He'.
      rewrite <- app_assoc.
      apply (IH (l + 1) (rem - Z.of_nat x * 2 ^ (12 - l)) (nl - x)%nat); auto; try lia.
      intros y Hy. specialize (Hgt y Hy). assert (In y (pre' ++ repeat l x)) by (apply in_or_app; auto).
      specialize (Hr y H). lia.
Qed.

Lemma kraft_rescale : forall d D K, (forall x, In x d -> x <= D /\ x <= K) -> 0 <= D -> 0 <= K ->
  sumz (map (fun x => 2 ^ (D - x)) d) = 2 ^ D -> sumz (map (fun x => 2 ^ (K - x)) d) = 2 ^ K.
Proof.
  intros d D K Hd HD HK Hk. destruct (Z.le_ge_cases K D) as [HKD|HKD].
  - assert (E : sumz (map (fun x => 2 ^ (D - x)) d) = 2 ^ (D - K) * sumz (map (fun x => 2 ^ (K - x)) d)).
    { rewrite <- sumz_scale. f_equal. apply map_ext_in. intros x Hx. specialize (Hd x Hx).
      rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    rewrite E in Hk. replace (2 ^ D) with (2 ^ (D - K) * 2 ^ K) in Hk by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (0 < 2 ^ (D - K)) by (apply Z.pow_pos_nonneg; lia).
    apply Z.mul_reg_l in Hk; lia.
  - rewrite (map_ext_in _ (fun x => 2 ^ (K - D) * 2 ^ (D - x))).
    + rewrite sumz_scale, Hk, <- Z.pow_add_r by lia. f_equal. lia.
    + intros x Hx. specialize (Hd x Hx). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma bl_leaf_ok : forall e d D, e = 0 \/ e = 1 -> (length d <= 19)%nat -> dsorted d ->
  (forall x, In x d -> 1 <= x <= D) -> sumz (map (fun x => 2 ^ (D - x)) d) = 2 ^ D ->
  (forall x, In x d -> x <= 12) -> d <> [] -> leaf_ok e d = true.
Proof.
  intros e d D He Hn Hs Hd Hk H12 Hne.
  destruct d as [|x0 d0] eqn:Ed; [congruence|].
  assert (HD1 : 1 <= D) by (specialize (Hd x0 (or_introl eq_refl)); lia).
  rewrite <- Ed in *.
  assert (Hk12 : sumz (map (fun x => 2 ^ (12 - x)) d) = 4096).
  { apply (kraft_rescale d D 12); auto; [intros x Hx; split; [apply Hd|apply H12]; auto|lia|lia]. }
  rewrite <- (app_nil_r d).
  assert (Hen : enum (leaf_ok e) 12 1 4096 19 [] = true) by (destruct He; subst; [apply enum_ok0|apply enum_ok1]).
  exact (enum_complete _ 12 1 4096 19 [] d Hen ltac:(reflexivity) ltac:(lia) Hs
           ltac:(intros y Hy; split; [apply Hd|apply H12]; auto) Hk12 Hn).
Qed.

Lemma caps_depth12 : forall e f d W, 0 <= e -> W <= 320 ->
  (forall k, (k < length d)%nat -> 1 <= nth k f 0 /\ fib (nth k d 0 + 1 + e) * nth k f 0 <= W) ->
  (forall x, In x d -> 0 <= x) -> forall x, In x d -> x <= 12.
Proof.
  intros e f d W He HW Hc H0 x Hx. destruct (In_nth d x 0 Hx) as [k [Hkl Hkx]]. destruct (Hc k Hkl) as [Hf1 Hfc].
  rewrite Hkx in Hfc. specialize (H0 x Hx). destruct (Z.le_gt_cases x 12) as [|Hgt]; auto. exfalso.
  assert (fib 14 <= fib (x + 1 + e)) by (apply fib_mono; lia). change (fib 14) with 377 in H. nia.
Qed.

(** The cost of the repair on the bit-length tree, for depths sorted along the scan.  [d]: the Huffman depths
    of the leaves in the order of the heap scan, [f]: their frequencies, [W] the total weight.  The caps on [f]
    are the Fibonacci bound of [HuffAbs.huff_fib] (e = 0) or its sharper form with fib (d + 2) (e = 1). *)
Theorem bl_repair_cost : forall (e : Z) (f d : list Z) (W D : Z), e = 0 \/ e = 1 ->
  length f = length d -> (length d <= 19)%nat -> dsorted d ->
  (forall x, In x d -> 1 <= x <= D) -> sumz (map (fun x => 2 ^ (D - x)) d) = 2 ^ D ->
  W <= 320 -> (forall k, (k < length d)%nat -> 1 <= nth k f 0 /\ fib (nth k d 0 + 1 + e) * nth k f 0 <= W) ->
  dlt f (repl 7 d) d <= dblt e (length d).
Proof.
  intros e f d W D He Hf Hn Hs Hd Hk HW Hc.
  destruct d as [|x0 d0] eqn:Ed; [destruct (repl 7 []), f; cbn [dlt length]; unfold dblt, dbl, dbl2; simpl;
                                  destruct (e =? 0); lia|].
  rewrite <- Ed in *.
  assert (H12 := caps_depth12 e f d W ltac:(lia) HW Hc ltac:(intros x Hx; specialize (Hd x Hx); lia)).
  assert (Hleaf := bl_leaf_ok e d D He Hn Hs Hd Hk H12 ltac:(congruence)).
  unfold leaf_ok in Hleaf. apply andb_true_iff in Hleaf.
  destruct Hleaf as [Hlen Hb]. apply Nat.eqb_eq in Hlen. apply Z.leb_le in Hb.
  eapply Z.le_trans; [|exact Hb].
  apply dlt_le_bsum; auto; [lia|].
  intros k Hkl. destruct (Hc k Hkl) as [H1 H2]. split; [auto|split; [|lia]].
  assert (In (nth k d 0) d) by (apply nth_In; auto). specialize (Hd _ H). lia.
Qed.

(** ** Ties: the depths along the heap scan need not be sorted *)

(** zlib's heap scan visits the leaves by nondecreasing frequency, but among leaves of equal frequency the
    depths can come in any order (zlib's [smaller] breaks ties by subtree height, not by depth).  The cost only
    depends on the (frequency, depth) pairs, so the depths can be sorted within each block of equal
    frequency; between blocks they are already sorted when a more frequent leaf is never deeper. *)

Module PairLe <: Orders.TotalLeBool.
  Definition t := (Z * Z)%type.
  Definition leb (p q : t) : bool := (fst p <? fst q) || ((fst p =? fst q) && (snd q <=? snd p)).
  Theorem leb_total : forall p q, leb p q = true \/ leb q p = true.
  Proof.
    intros [a x] [b y]. unfold leb; simpl.
    destruct (Z.ltb_spec a b); [auto|]. destruct (Z.ltb_spec b a); [auto|].
    assert (a = b) by lia. subst. rewrite Z.eqb_refl. simpl.
    destruct (Z.leb_spec y x); [auto|]. right. apply Z.leb_le. lia.
  Qed.
End PairLe.

Module PairSort := Mergesort.Sort PairLe.

Lemma PairLe_spec : forall p q, PairLe.leb p q = true -> fst p < fst q \/ (fst p = fst q /\ snd q <= snd p).
Proof.
  intros [a x] [b y] H. unfold PairLe.leb in H; simpl in *.
  apply orb_true_iff in H. destruct H as [H|H]; [left; apply Z.ltb_lt; auto|].
  apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. auto.
Qed.

Lemma ss_le_unique : forall l1 l2 : list Z, StronglySorted Z.le l1 -> StronglySorted Z.le l2 ->
  Permutation l1 l2 -> l1 = l2.
Proof.
  induction l1 as [|a r IH]; intros l2 H1 H2 Hp.
  - symmetry. apply Permutation_nil; auto.
  - destruct l2 as [|b r'].
    + apply Permutation_sym, Permutation_nil in Hp. discriminate.
    + apply StronglySorted_inv in H1. apply StronglySorted_inv in H2.
      destruct H1 as [H1 Ha]. destruct H2 as [H2 Hb].
      assert (Hab : a = b).
      { assert (Ha2 : In a (b :: r')) by (eapply Permutation_in; eauto; left; auto).
        assert (Hb1 : In b (a :: r)) by (eapply Permutation_in; [apply Permutation_sym; eauto|left; auto]).
        destruct Ha2 as [->|Ha2]; auto. destruct Hb1 as [->|Hb1]; auto.
        rewrite Forall_forall in Ha, Hb. specialize (Ha b Hb1). specialize (Hb a Ha2). lia. }
      subst b. f_equal. apply IH; auto. eapply Permutation_cons_inv; eauto.
Qed.

Lemma adj_mono : forall f, (forall k, (S k < length f)%nat -> nth k f 0 <= nth (S k) f 0) ->
  forall i j, (i <= j < length f)%nat -> nth i f 0 <= nth j f 0.
Proof.
  intros f H i j [Hij Hj]. induction Hij as [|j Hij IH]; [lia|].
  assert (nth j f 0 <= nth (S j) f 0) by (apply H; lia). specialize (IH ltac:(lia)). lia.
Qed.

Lemma ss_of_adj : forall f, (forall k, (S k < length f)%nat -> nth k f 0 <= nth (S k) f 0) ->
  StronglySorted Z.le f.
Proof.
  induction f as [|a f IH]; intros H; constructor.
  - apply IH. intros k Hk. apply (H (S k)). simpl; lia.
  - apply Forall_forall. intros y Hy. destruct (In_nth f y 0 Hy) as [j [Hj <-]].
    apply (adj_mono (a :: f) H 0 (S j)). simpl; lia.
Qed.

Lemma map_fst_combine : forall (l l' : list Z), length l = length l' -> map fst (combine l l') = l.
Proof. induction l as [|x l IH]; intros [|y l'] H; simpl in *; try lia; auto. rewrite IH; auto. Qed.

Lemma map_snd_combine : forall (l l' : list Z), length l = length l' -> map snd (combine l l') = l'.
Proof. induction l as [|x l IH]; intros [|y l'] H; simpl in *; try lia; auto. rewrite IH; auto. Qed.

Lemma combine_fst_snd : forall (l : list (Z * Z)), combine (map fst l) (map snd l) = l.
Proof. induction l as [|[x y] l IH]; simpl; auto. rewrite IH; auto. Qed.

Lemma in_combine_nth : forall f d a x, length f = length d -> In (a, x) (combine f d) ->
  exists i, (i < length f)%nat /\ nth i f 0 = a /\ nth i d 0 = x.
Proof.
  intros f d a x Hl Hin. destruct (In_nth _ _ (0, 0) Hin) as [i [Hi Hn]].
  rewrite length_combine in Hi. rewrite combine_nth in Hn by auto. injection Hn as <- <-.
  exists i. split; [lia|auto].
Qed.

Lemma ss_snd_dsorted : forall (l : list (Z * Z)),
  StronglySorted (fun p q => PairLe.leb p q = true) l ->
  (forall p q, In p l -> In q l -> fst p < fst q -> snd q <= snd p) -> dsorted (map snd l).
Proof.
  induction l as [|p l IH]; intros Hs H; simpl; auto.
  apply StronglySorted_inv in Hs. destruct Hs as [Hs Hf]. split.
  - intros y Hy. apply in_map_iff in Hy. destruct Hy as [q [<- Hq]].
    rewrite Forall_forall in Hf. destruct (PairLe_spec p q (Hf q Hq)) as [Hlt|[_ Hle]]; auto.
    apply H; simpl; auto.
  - apply IH; auto. intros; apply H; simpl; auto.
Qed.

Lemma rearrange : forall f d, length f = length d ->
  (forall k, (S k < length f)%nat -> nth k f 0 <= nth (S k) f 0) ->
  (forall i j, (i < length f)%nat -> (j < length f)%nat -> nth i f 0 < nth j f 0 -> nth j d 0 <= nth i d 0) ->
  exists d', Permutation d d' /\ dsorted d' /\ length d' = length d /\ Permutation (combine f d) (combine f d').
Proof.
  intros f d Hl Hf Hx.
  set (s := PairSort.sort (combine f d)).
  assert (Hp : Permutation (combine f d) s) by apply PairSort.Permuted_sort.
  assert (Hss : StronglySorted (fun p q => PairLe.leb p q = true) s).
  { apply PairSort.StronglySorted_sort. intros [a x] [b y] [c z] H1 H2.
    apply PairLe_spec in H1, H2. simpl in *. unfold PairLe.leb; simpl.
    apply orb_true_iff. destruct H1 as [H1|[H1 H1']]; destruct H2 as [H2|[H2 H2']].
    - left; apply Z.ltb_lt; lia.
    - left; apply Z.ltb_lt; lia.
    - left; apply Z.ltb_lt; lia.
    - right. apply andb_true_iff. split; [apply Z.eqb_eq; lia|apply Z.leb_le; lia]. }
  assert (Hfs : map fst s = f).
  { symmetry. apply ss_le_unique.
    - apply ss_of_adj; auto.
    - clear -Hss. induction Hss as [|p l Hs IH Hf]; constructor; auto.
      rewrite Forall_forall in *. intros y Hy. apply in_map_iff in Hy. destruct Hy as [q [<- Hq]].
      destruct (PairLe_spec p q (Hf q Hq)) as [|[]]; lia.
    - rewrite <- (map_fst_combine f d Hl) at 1. apply Permutation_map; auto. }
  exists (map snd s). split; [|split; [|split]].
  - rewrite <- (map_snd_combine f d Hl) at 1. apply Permutation_map; auto.
  - apply ss_snd_dsorted; auto. intros [a x] [b y] Hp1 Hq1 Hlt. simpl in *.
    apply (Permutation_in _ (Permutation_sym Hp)) in Hp1. apply (Permutation_in _ (Permutation_sym Hp)) in Hq1.
    destruct (in_combine_nth f d a x Hl Hp1) as [i [Hi [Hfi Hdi]]].
    destruct (in_combine_nth f d b y Hl Hq1) as [j [Hj [Hfj Hdj]]].
    rewrite <- Hdi, <- Hdj. apply Hx; auto. rewrite Hfi, Hfj. exact Hlt.
  - rewrite length_map. rewrite <- (Permutation_length Hp), length_combine. lia.
  - rewrite <- Hfs at 2. rewrite combine_fst_snd. exact Hp.
Qed.

Lemma sumz_perm : forall l l', Permutation l l' -> sumz l = sumz l'.
Proof. intros l l' H; induction H; simpl; lia. Qed.

Lemma cntz_perm : forall P d d', Permutation d d' -> cntz P d = cntz P d'.
Proof. intros P d d' H; induction H; rewrite ?cntz_cons; lia. Qed.

Lemma repl_perm : forall M d d', Permutation d d' -> repl M d = repl M d'.
Proof.
  intros M d d' H. unfold repl.
  replace (clampc M d) with (clampc M d'); [reflexivity|].
  unfold clampc. apply map_ext. intros l. rewrite (cntz_perm _ d d' H). reflexivity.
Qed.

Lemma dlt_split : forall f L d, length f = length d -> length L = length d ->
  dlt f L d = sumz (map (fun p => fst p * snd p) (combine f L)) - sumz (map (fun p => fst p * snd p) (combine f d)).
Proof.
  induction f as [|x f IH]; intros [|y L] [|z d] Hf HL; simpl in *; try lia.
  rewrite IH by lia. ring.
Qed.

(** The cost of the repair on the bit-length tree, on the lists in heap-scan order: [f] nondecreasing (the
    removal order of the heap), a more frequent leaf never deeper (Huffman optimality); the depths of equally
    frequent leaves may come in any order. *)
Theorem bl_repair_cost_scan : forall (e : Z) (f d : list Z) (W D : Z), e = 0 \/ e = 1 ->
  length f = length d -> (length d <= 19)%nat ->
  (forall k, (S k < length f)%nat -> nth k f 0 <= nth (S k) f 0) ->
  (forall i j, (i < length f)%nat -> (j < length f)%nat -> nth i f 0 < nth j f 0 -> nth j d 0 <= nth i d 0) ->
  (forall x, In x d -> 1 <= x <= D) -> sumz (map (fun x => 2 ^ (D - x)) d) = 2 ^ D ->
  W <= 320 -> (forall k, (k < length d)%nat -> 1 <= nth k f 0 /\ fib (nth k d 0 + 1 + e) * nth k f 0 <= W) ->
  dlt f (repl 7 d) d <= dblt e (length d).
Proof.
  intros e f d W D He Hl Hn Hf Hx Hd Hk HW Hc.
  destruct (rearrange f d Hl Hf Hx) as [d' [Hp [Hs [Hl' Hpc]]]].
  assert (Hin : forall x, In x d' -> In x d) by (intros; eapply Permutation_in; [apply Permutation_sym|]; eauto).
  assert (Hd' : forall x, In x d' -> 1 <= x <= D) by (intros x Hx'; apply Hd, Hin; auto).
  assert (Hk' : sumz (map (fun x => 2 ^ (D - x)) d') = 2 ^ D)
    by (rewrite <- Hk; apply sumz_perm, Permutation_map, Permutation_sym; auto).
  assert (Hc' : forall k, (k < length d')%nat -> 1 <= nth k f 0 /\ fib (nth k d' 0 + 1 + e) * nth k f 0 <= W).
  { intros k Hk'' . assert (Hin2 : In (nth k f 0, nth k d' 0) (combine f d')).
    { rewrite <- combine_nth by lia. apply nth_In. rewrite length_combine. lia. }
    apply (Permutation_in _ (Permutation_sym Hpc)) in Hin2.
    destruct (in_combine_nth f d _ _ Hl Hin2) as [i [Hi [Hfi Hdi]]].
    rewrite <- Hfi, <- Hdi. apply Hc. lia. }
  assert (H12 : forall x, In x d' -> x <= 12)
    by (apply (caps_depth12 e f d' W); [lia|auto|auto|intros x Hx'; specialize (Hd' x Hx'); lia]).
  assert (Hlen : length (repl 7 d') = length d').
  { destruct d' as [|x0 d0] eqn:Ed'; [reflexivity|].
    rewrite <- Ed' in *.
    assert (Hleaf := bl_leaf_ok e d' D He ltac:(lia) Hs Hd' Hk' H12 ltac:(congruence)).
    unfold leaf_ok in Hleaf. apply andb_true_iff in Hleaf. destruct Hleaf as [Hlen _].
    apply Nat.eqb_eq in Hlen. exact Hlen. }
  rewrite (repl_perm 7 d d' Hp).
  assert (E : dlt f (repl 7 d') d = dlt f (repl 7 d') d').
  { rewrite !dlt_split by lia. f_equal. apply sumz_perm, Permutation_map; auto. }
  rewrite E, <- Hl'.
  apply (bl_repair_cost e f d' W D); auto; lia.
Qed.

(** The bound for the alphabet sizes of memLevel 1 (n <= 13), memLevel 2 (n <= 15) and in general (n <= 19). *)
Lemma dblt_13 : forall e n, (n <= 13)%nat -> dblt e n <= (if e =? 0 then 101 else 59).
Proof.
  intros e n Hn. unfold dblt. destruct (e =? 0);
    do 14 (destruct n as [|n]; [unfold dbl, dbl2; cbn; lia|]); lia.
Qed.

Lemma dblt_15 : forall e n, (n <= 15)%nat -> dblt e n <= (if e =? 0 then 128 else 71).
Proof.
  intros e n Hn. unfold dblt. destruct (e =? 0);
    do 16 (destruct n as [|n]; [unfold dbl, dbl2; cbn; lia|]); lia.
Qed.

Lemma dblt_19 : forall e n, (n <= 19)%nat -> dblt e n <= (if e =? 0 then 260 else 147).
Proof.
  intros e n Hn. unfold dblt. destruct (e =? 0);
    do 20 (destruct n as [|n]; [unfold dbl, dbl2; cbn; lia|]); lia.
Qed.

(** ** The literal/length tree: no per-rank cap with a small shift *)

(** A frequency table on which zlib's build_tree (the model, run by [vm_compute]) gives a code the length 15
    although f * fib (15 + 1 - s) > W for every shift s <= 5: 263 used literal/length codes, 226 of frequency 1,
    28 of frequency 2, and 227 * fib k for k = 2..10 (total W = 32516).  Code 255 (frequency 454) has Huffman
    depth 8 and gets length 15.  The code costs sum f * L = 89128 bits; the Huffman tree built by the model
    costs the sum of its internal node weights, 85148, so the repair adds 3980 = 0.122 W. *)
Definition cex_freq : list Z :=
  [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1;
   1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1;
   1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1;
   1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1;
   1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1;
   1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1;
   1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2;
   2; 2; 227; 454; 681; 1135; 1816; 2951; 4767; 7718; 12485].

Definition cex_out : tree * Z * work :=
  build_tree static_l_desc (mkTree (cex_freq ++ repeat 0 310) (repeat 0 573))
    (mkWork (repeat 0 573) 0 0 (repeat 0 573) (repeat 0 16) 0 0).

Definition cex_len : list Z := sublist 0 263 (dl (fst (fst cex_out))).

Lemma cex_facts :
  Zlength cex_freq = 263 /\ sumz cex_freq = 32516 /\ snd (fst cex_out) = 262 /\
  Znth 255 cex_freq = 454 /\ Znth 255 cex_len = 15 /\
  sumz (map (fun p => fst p * snd p) (combine cex_freq cex_len)) = 89128 /\
  sumz (sublist 286 548 (fc (fst (fst cex_out)))) = 85148 /\ Znth 547 (fc (fst (fst cex_out))) = 32516.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem cex_no_shifted_cap : forall s, s <= 5 ->
  sumz cex_freq < Znth 255 cex_freq * fib (Znth 255 cex_len + 1 - s).
Proof.
  intros s Hs. destruct cex_facts as [_ [E1 [_ [E2 [E3 _]]]]]. rewrite E1, E2, E3.
  assert (fib 11 <= fib (15 + 1 - s)) by (apply fib_mono; lia). change (fib 11) with 89 in H. lia.
Qed.

(** ** The bit-length tree with Huffman optimality: at most 75 bits for n <= 15, W <= 316 *)

(** A certificate (Q, alpha, beta, gamma, sigma, alts) for a depth profile d proves Q * sum_k a_k f_k <= Q * T for
    every f with 1 <= f_k, fib (d_k + 1) f_k <= 316, f nondecreasing, sum f <= 316, and
    sum_k f_k d_k <= sum_k f_k e_k for every alternative code e in alts (Huffman optimality): Q * a_k is at most
    the coefficient of f_k in the nonnegative combination of these constraints with the multipliers alpha (caps),
    beta (f_k >= 1), gamma (f_k <= f_(k+1)), sigma (the total) and the first components of alts (LP duality,
    the multipliers found by an LP solver and checked here). *)
Definition cert : Type := (Z * list Z * list Z * list Z * Z * list (Z * list Z))%type.

Fixpoint sumk (n : nat) (g : nat -> Z) : Z := match n with O => 0 | S n' => sumk n' g + g n' end.

Definition dotn (n : nat) (f a : list Z) : Z := sumk n (fun k => nth k f 0 * nth k a 0).

Definition gprev (g : list Z) (k : nat) : Z := match k with O => 0 | S k' => nth k' g 0 end.

Definition coefk (d : list Z) (c : cert) (k : nat) : Z :=
  let '(Q, al, be, ga, si, alts) := c in
  nth k al 0 * fib (nth k d 0 + 1) - nth k be 0 + (nth k ga 0 - gprev ga k) + si +
  sumz (map (fun p => fst p * (nth k d 0 - nth k (snd p) 0)) alts).

Definition alt_ok (n : nat) (p : Z * list Z) : bool :=
  (0 <=? fst p) && Nat.eqb (length (snd p)) n &&
  forallb (fun x => (0 <=? x) && (x <=? 12)) (snd p) && (sumz (map (fun x => 2 ^ (12 - x)) (snd p)) <=? 4096).

Definition cert_ok (T : Z) (d a : list Z) (c : cert) : bool :=
  let '(Q, al, be, ga, si, alts) := c in
  let n := length d in
  (0 <? Q) && Nat.eqb (length al) n && Nat.eqb (length be) n && Nat.eqb (length ga) (n - 1) &&
  forallb (fun x => 0 <=? x) al && forallb (fun x => 0 <=? x) be && forallb (fun x => 0 <=? x) ga &&
  (0 <=? si) && forallb (alt_ok n) alts &&
  forallb (fun k => Q * nth k a 0 <=? coefk d c k) (seq 0 n) &&
  (316 * sumz al - sumz be + 316 * si <=? Q * T).

Lemma sumk_ext : forall n g h, (forall k, (k < n)%nat -> g k = h k) -> sumk n g = sumk n h.
Proof. induction n as [|n IH]; intros g h H; simpl; auto. rewrite (IH g h), H; auto. Qed.

Lemma sumk_le : forall n g h, (forall k, (k < n)%nat -> g k <= h k) -> sumk n g <= sumk n h.
Proof.
  induction n as [|n IH]; intros g h H; simpl; [lia|].
  specialize (IH g h (fun k Hk => H k ltac:(lia))). specialize (H n ltac:(lia)). lia.
Qed.

Lemma sumk_add : forall n g h, sumk n (fun k => g k + h k) = sumk n g + sumk n h.
Proof. induction n as [|n IH]; intros; simpl; [lia|]. rewrite IH; lia. Qed.

Lemma sumk_scale : forall n c g, sumk n (fun k => c * g k) = c * sumk n g.
Proof. induction n as [|n IH]; intros; simpl; [lia|]. rewrite IH; ring. Qed.

Lemma sumk_shift : forall n g, sumk (S n) g = g O + sumk n (fun k => g (S k)).
Proof.
  induction n as [|n IH]; intros g; [simpl; lia|].
  change (sumk (S (S n)) g) with (sumk (S n) g + g (S n)). rewrite IH. simpl. lia.
Qed.

Lemma sumz_sumk : forall l, sumz l = sumk (length l) (fun k => nth k l 0).
Proof.
  induction l as [|x l IH]; [reflexivity|]. cbn [length]. rewrite sumk_shift. simpl. rewrite IH. reflexivity.
Qed.

Lemma nth_nonneg : forall l k, forallb (fun x => 0 <=? x) l = true -> 0 <= nth k l 0.
Proof.
  intros l k H. destruct (Nat.lt_ge_cases k (length l)) as [Hk|Hk].
  - rewrite forallb_forall in H. specialize (H _ (nth_In l 0 Hk)). apply Z.leb_le in H. auto.
  - rewrite nth_overflow by auto. lia.
Qed.

Lemma abel : forall n f g, (1 <= n)%nat ->
  sumk n (fun k => nth k f 0 * (nth k g 0 - gprev g k)) =
  sumk (n - 1) (fun k => nth k g 0 * (nth k f 0 - nth (S k) f 0)) + nth (n - 1) g 0 * nth (n - 1) f 0.
Proof.
  intros n f g Hn. induction n as [|n IH]; [lia|].
  destruct n as [|n]; [simpl; ring|].
  change (sumk (S (S n)) (fun k => nth k f 0 * (nth k g 0 - gprev g k))) with
    (sumk (S n) (fun k => nth k f 0 * (nth k g 0 - gprev g k)) + nth (S n) f 0 * (nth (S n) g 0 - gprev g (S n))).
  rewrite IH by lia. replace (S (S n) - 1)%nat with (S n) by lia. replace (S n - 1)%nat with n by lia.
  change (sumk (S n) (fun k => nth k g 0 * (nth k f 0 - nth (S k) f 0))) with
    (sumk n (fun k => nth k g 0 * (nth k f 0 - nth (S k) f 0)) + nth n g 0 * (nth n f 0 - nth (S n) f 0)).
  simpl gprev. ring.
Qed.

Lemma alts_exchange : forall n f d (alts : list (Z * list Z)),
  sumk n (fun k => nth k f 0 * sumz (map (fun p => fst p * (nth k d 0 - nth k (snd p) 0)) alts)) =
  sumz (map (fun p => fst p * (dotn n f d - dotn n f (snd p))) alts).
Proof.
  intros n f d alts. induction alts as [|p alts IH].
  - simpl. rewrite (sumk_ext n _ (fun _ => 0)); [|intros; ring]. clear. induction n; simpl; lia.
  - cbn [map sumz]. rewrite <- IH.
    rewrite (sumk_ext n _ (fun k => fst p * (nth k f 0 * nth k d 0) + (- fst p) * (nth k f 0 * nth k (snd p) 0) +
                 nth k f 0 * sumz (map (fun p0 => fst p0 * (nth k d 0 - nth k (snd p0) 0)) alts)));
      [|intros; ring].
    rewrite !sumk_add, !sumk_scale. unfold dotn. ring.
Qed.

Lemma cert_sound : forall T d a c f,
  cert_ok T d a c = true -> length f = length d ->
  (forall k, (k < length d)%nat -> 1 <= nth k f 0 /\ fib (nth k d 0 + 1) * nth k f 0 <= 316) ->
  (forall k, (S k < length d)%nat -> nth k f 0 <= nth (S k) f 0) ->
  sumz f <= 316 ->
  (forall e, length e = length d -> (forall x, In x e -> 0 <= x <= 12) ->
     sumz (map (fun x => 2 ^ (12 - x)) e) <= 4096 -> dotn (length d) f d <= dotn (length d) f e) ->
  dotn (length d) f a <= T.
Proof.
  intros T d a c f Hc Hlf Hcap Hmono Hsum Hopt.
  destruct c as [[[[[Q al] be] ga] si] alts].
  unfold cert_ok in Hc. cbv beta iota zeta in Hc. rewrite !andb_true_iff in Hc.
  destruct Hc as [[[[[[[[[[HQ Hal] Hbe] Hga] Hal0] Hbe0] Hga0] Hsi] Halts] Hco] Hb].
  apply Z.ltb_lt in HQ. apply Nat.eqb_eq in Hal, Hbe, Hga. apply Z.leb_le in Hsi, Hb.
  set (n := length d) in *.
  assert (Hf0 : forall k, (k < n)%nat -> 0 <= nth k f 0) by (intros k Hk; destruct (Hcap k Hk); lia).
  assert (Hco' : forall k, (k < n)%nat -> Q * nth k a 0 <= coefk d (Q, al, be, ga, si, alts) k).
  { intros k Hk. rewrite forallb_forall in Hco. apply Z.leb_le, Hco, in_seq. lia. }
  (* Q * dot <= sum of f_k * coef_k *)
  assert (H1 : Q * dotn n f a <= sumk n (fun k => nth k f 0 * coefk d (Q, al, be, ga, si, alts) k)).
  { unfold dotn. rewrite <- sumk_scale. apply sumk_le. intros k Hk.
    specialize (Hco' k Hk). specialize (Hf0 k Hk). nia. }
  unfold coefk in H1. cbv beta iota in H1.
  rewrite (sumk_ext n _ (fun k => nth k f 0 * (nth k al 0 * fib (nth k d 0 + 1)) + (- 1) * (nth k f 0 * nth k be 0) +
             nth k f 0 * (nth k ga 0 - gprev ga k) + si * nth k f 0 +
             nth k f 0 * sumz (map (fun p => fst p * (nth k d 0 - nth k (snd p) 0)) alts))) in H1 by (intros; ring).
  rewrite !sumk_add, !sumk_scale, alts_exchange in H1.
  (* the five parts *)
  assert (P1 : sumk n (fun k => nth k f 0 * (nth k al 0 * fib (nth k d 0 + 1))) <= 316 * sumz al).
  { rewrite sumz_sumk, Hal, <- sumk_scale. apply sumk_le. intros k Hk.
    assert (0 <= nth k al 0) by (apply nth_nonneg; auto). destruct (Hcap k Hk). nia. }
  assert (P2 : sumz be <= sumk n (fun k => nth k f 0 * nth k be 0)).
  { rewrite sumz_sumk, Hbe. apply sumk_le. intros k Hk.
    assert (0 <= nth k be 0) by (apply nth_nonneg; auto). destruct (Hcap k Hk). nia. }
  assert (P3 : sumk n (fun k => nth k f 0 * (nth k ga 0 - gprev ga k)) <= 0).
  { destruct n as [|m] eqn:En; [simpl; lia|]. rewrite abel by lia.
    replace (S m - 1)%nat with m by lia. rewrite (nth_overflow ga) by lia.
    assert (sumk m (fun k => nth k ga 0 * (nth k f 0 - nth (S k) f 0)) <= sumk m (fun _ => 0)).
    { apply sumk_le. intros k Hk. assert (0 <= nth k ga 0) by (apply nth_nonneg; auto).
      assert (nth k f 0 <= nth (S k) f 0) by (apply Hmono; lia). nia. }
    assert (sumk m (fun _ : nat => 0) = 0) by (clear; induction m; simpl; lia). lia. }
  assert (P4 : si * sumk n (fun k => nth k f 0) <= 316 * si).
  { rewrite <- Hlf, <- sumz_sumk. nia. }
  assert (P5 : sumz (map (fun p => fst p * (dotn n f d - dotn n f (snd p))) alts) <= 0).
  { assert (Hall : forall p, In p alts -> fst p * (dotn n f d - dotn n f (snd p)) <= 0).
    { intros p Hp. rewrite forallb_forall in Halts. specialize (Halts p Hp). unfold alt_ok in Halts.
      rewrite !andb_true_iff in Halts. destruct Halts as [[[Hp0 Hpl] Hpr] Hpk].
      apply Z.leb_le in Hp0, Hpk. apply Nat.eqb_eq in Hpl.
      assert (dotn n f d <= dotn n f (snd p)).
      { apply Hopt; auto. intros x Hx. rewrite forallb_forall in Hpr. specialize (Hpr x Hx).
        apply andb_true_iff in Hpr. destruct Hpr as [Hx1 Hx2]. apply Z.leb_le in Hx1, Hx2. lia. }
      nia. }
    clear -Hall. induction alts as [|p alts IH]; simpl; [lia|].
    specialize (IH (fun q Hq => Hall q (or_intror Hq))). specialize (Hall p (or_introl eq_refl)). lia. }
  assert (Q * dotn n f a <= Q * T) by lia.
  apply Z.mul_le_mono_pos_l in H; auto.
Qed.

(** The certificates, for the 408 profiles where the per-position caps bound exceeds 75 (68 of them cannot
    occur at all: their certificates combine the constraints into 0 <= -1), generated by
    docs/huffman-gen/certs.py (repair_cert.py). *)
Definition cert_table : list (list Z * cert) := [
  ([9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [14; 14; 14; 14; 9; 9; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 3; 0; 0; 0], 1, [(1, [7; 7; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [7; 7; 7; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [46; 46; 14; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 18; 9; 0; 0; 3; 0; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (1, [8; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (23, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [23; 23; 14; 14; 19; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 3; 0; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (1, [9; 9; 8; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [23; 23; 33; 33; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 3; 0; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (1, [9; 9; 8; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1]); (9, [10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 2; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [56; 56; 33; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 3; 0; 0; 0], 1, [(1, [7; 7; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (1, [8; 8; 7; 7; 7; 6; 6; 4; 4; 4; 2; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1]); (9, [10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 2; 1]); (14, [10; 10; 10; 10; 8; 7; 6; 5; 4; 3; 2; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [29; 29; 29; 29; 19; 19; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 8; 0; 0; 4; 2], 2, [(6, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [96; 96; 29; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 38; 19; 0; 0; 8; 0; 0; 4; 2], 2, [(6, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (49, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 2; 2])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [48; 48; 29; 29; 39; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 8; 0; 0; 4; 2], 2, [(6, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 2; 2])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [48; 48; 68; 68; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 8; 0; 0; 4; 2], 2, [(6, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 2; 2]); (19, [10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 2; 2; 2])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [116; 116; 68; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 8; 0; 0; 4; 2], 2, [(6, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 7; 7; 7; 5; 4; 3; 2; 2; 2]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 2; 2]); (20, [10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 2; 2; 2]); (28, [10; 10; 10; 10; 8; 7; 6; 5; 4; 3; 2; 2; 2])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [16; 16; 16; 16; 10; 10; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 2; 0; 2; 1; 0], 1, [(1, [7; 7; 7; 7; 6; 6; 4; 3; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (2, [8; 8; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [52; 52; 16; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 20; 10; 0; 0; 2; 0; 2; 1; 0], 1, [(1, [7; 7; 7; 7; 6; 6; 4; 3; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (2, [8; 8; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (26, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [26; 26; 16; 16; 22; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 2; 0; 2; 1; 0], 1, [(1, [7; 7; 7; 7; 6; 6; 4; 3; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (2, [9; 9; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [26; 26; 38; 38; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 2; 0; 2; 1; 0], 1, [(1, [8; 8; 8; 8; 6; 5; 4; 3; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (2, [9; 9; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1]); (10, [10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [64; 64; 38; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 2; 0; 2; 1; 0], 1, [(1, [7; 7; 7; 7; 6; 6; 4; 3; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (2, [9; 9; 9; 9; 7; 7; 7; 5; 4; 3; 3; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1]); (12, [10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 1]); (14, [10; 10; 10; 10; 8; 7; 6; 5; 4; 3; 3; 3; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [39; 39; 39; 39; 26; 26; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 17; 12; 6; 0; 0], 3, [(1, [7; 7; 7; 7; 6; 6; 4; 4; 4; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (3, [7; 7; 7; 7; 6; 6; 4; 4; 4; 4; 4; 3; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 4; 4; 4; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [130; 130; 39; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 52; 26; 0; 0; 17; 15; 9; 0; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (4, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (68, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [65; 65; 39; 39; 52; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 17; 15; 9; 0; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (4, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [65; 65; 91; 91; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 17; 15; 9; 0; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (4, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1]); (26, [10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 2; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 4; 4; 4; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [156; 156; 91; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 17; 15; 9; 0; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (4, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1]); (26, [10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 2; 1]); (39, [10; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 2; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [47; 47; 47; 47; 31; 31; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 1; 24; 15; 0; 0; 0], 3, [(3, [7; 7; 7; 7; 6; 6; 4; 4; 4; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [156; 156; 47; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 62; 31; 0; 1; 24; 15; 0; 0; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (6, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (81, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [78; 78; 47; 47; 62; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 1; 24; 15; 0; 0; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (6, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [78; 78; 109; 109; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 1; 24; 15; 0; 0; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (6, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (31, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 5; 5; 3; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [187; 187; 109; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 1; 24; 15; 0; 0; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (6, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (31, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1]); (47, [10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 1])]));
  ([8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [8; 8; 11; 11; 11; 11; 3; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 5; 0; 2; 0; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 2; 2; 2]); (1, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 1]); (3, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 2; 1])]));
  ([9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [25; 25; 8; 8; 14; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 3; 0; 8; 0; 2; 0; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 2; 2; 2]); (1, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 1]); (6, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 1]); (4, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 1])]));
  ([9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 2; 1], (10, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [47; 47; 47; 47; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 3; 6; 0; 16; 0; 4; 0; 0], 2, [(2, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 2; 2; 2]); (2, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 1]); (12, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 1]); (5, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 1])]));
  ([10; 10; 9; 8; 7; 7; 7; 6; 6; 4; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [47; 47; 28; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 6; 3; 0; 8; 0; 2; 0; 0], 1, [(1, [8; 8; 7; 7; 7; 6; 6; 5; 5; 3; 2; 2; 2]); (1, [8; 8; 7; 7; 7; 6; 6; 5; 5; 3; 3; 3; 1]); (6, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 1]); (7, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 2; 1]); (8, [9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 2; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [17; 17; 17; 17; 8; 8; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 6; 8; 0; 2; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 1]); (4, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 6; 6; 4; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [50; 50; 17; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 16; 8; 0; 6; 8; 0; 2; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 1]); (4, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 1]); (22, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [25; 25; 17; 17; 20; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 6; 8; 0; 2; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 1]); (4, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 6; 6; 4; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [25; 25; 37; 37; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 6; 8; 0; 2; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1]); (4, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 2; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1]); (6, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 2; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [62; 62; 37; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 6; 8; 0; 2; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1]); (4, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 2; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1]); (6, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 2; 1]); (17, [10; 10; 10; 10; 8; 7; 6; 6; 6; 4; 3; 2; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [33; 33; 33; 33; 21; 21; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 6; 0; 4; 2; 0; 2], 2, [(3, [7; 7; 7; 7; 7; 7; 6; 4; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (6, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 4; 3; 3; 3; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [108; 108; 33; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 42; 21; 0; 0; 6; 0; 4; 2; 0; 2], 2, [(4, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (6, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 2; 2]); (53, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 2; 2])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [54; 54; 33; 33; 45; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 6; 0; 4; 2; 0; 2], 2, [(3, [8; 8; 7; 7; 7; 6; 6; 4; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (6, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (5, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 2; 2])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 4; 3; 3; 3; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [54; 54; 78; 78; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 6; 0; 4; 2; 0; 2], 2, [(4, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (6, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (3, [9; 9; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 2; 2]); (21, [10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 2; 2])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 4; 3; 3; 3; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [132; 132; 78; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 6; 0; 4; 2; 0; 2], 2, [(4, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (6, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (3, [9; 9; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 2; 2]); (21, [10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 2; 2]); (33, [10; 10; 10; 10; 8; 7; 6; 5; 4; 3; 3; 3; 2; 2])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 2; 2], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [42; 42; 42; 42; 28; 28; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 16; 13; 10; 0; 6; 3], 3, [(2, [7; 7; 7; 7; 6; 6; 4; 4; 4; 4; 4; 3; 2; 2]); (7, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 4; 4; 4; 2; 2; 2], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [140; 140; 42; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 56; 28; 0; 0; 16; 15; 12; 0; 6; 3], 3, [(9, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (73, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 2; 2])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 2; 2; 2], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [70; 70; 42; 42; 56; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 16; 15; 12; 0; 6; 3], 3, [(9, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 2; 2])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 2; 2; 2], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [70; 70; 98; 98; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 16; 15; 12; 0; 6; 3], 3, [(9, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 2; 2]); (28, [10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 2; 2; 2])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 4; 4; 4; 2; 2; 2], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [168; 168; 98; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 16; 13; 10; 0; 6; 3], 3, [(2, [8; 8; 8; 8; 6; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (7, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (7, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 2; 2]); (28, [10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 2; 2; 2]); (40, [10; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 2; 2; 2])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [17; 17; 17; 17; 11; 11; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 1; 9; 5; 0; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 2; 2])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [56; 56; 17; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 22; 11; 0; 1; 9; 5; 0; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (29, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [28; 28; 17; 17; 22; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 1; 9; 5; 0; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [28; 28; 39; 39; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 1; 9; 5; 0; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2]); (11, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 2; 2])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 5; 5; 3; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [67; 67; 39; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 1; 9; 5; 0; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2]); (11, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 2; 2]); (17, [10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 2; 2])]));
  ([8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [9; 9; 13; 13; 13; 13; 4; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 5; 0; 1; 0; 2; 1], 1, [(3, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 2; 2]); (4, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 2; 2; 2])]));
  ([9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 2; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [30; 30; 9; 9; 17; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 4; 0; 9; 0; 1; 0; 2; 1], 1, [(3, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 2; 2]); (8, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (5, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 2; 2])]));
  ([9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 2; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [28; 28; 28; 28; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 2; 4; 0; 9; 0; 1; 0; 2; 1], 1, [(3, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 2; 2]); (8, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 2; 2])]));
  ([10; 10; 9; 8; 7; 7; 7; 6; 6; 4; 3; 2; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [56; 56; 34; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 8; 4; 0; 9; 0; 1; 0; 2; 1], 1, [(3, [8; 8; 7; 7; 7; 6; 6; 5; 5; 3; 3; 3; 2; 2]); (8, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (9, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 2; 2; 2]); (9, [9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 2; 2; 2])]));
  ([9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [21; 21; 21; 21; 9; 9; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 8; 9; 0; 1; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 2; 2]); (7, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 2; 2])]));
  ([10; 10; 9; 8; 8; 8; 6; 6; 6; 4; 3; 2; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [60; 60; 21; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 18; 9; 0; 8; 9; 0; 1; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 2; 2]); (7, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 2; 2]); (24, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 2; 2])]));
  ([10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 2; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [30; 30; 21; 21; 25; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 8; 9; 0; 1; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 2; 2]); (7, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 2; 2])]));
  ([10; 10; 10; 10; 8; 7; 6; 6; 6; 4; 3; 2; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [30; 30; 46; 46; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 8; 9; 0; 1; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 2; 2]); (7, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 2; 2]); (9, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 2; 2; 2])]));
  ([11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 3; 2; 2; 2], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [86; 86; 53; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 10; 9; 0; 0; 0; 2; 1], 1, [(3, [9; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 6; 6; 6; 5; 5; 4; 4; 2; 2; 2]); (10, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 2; 2; 2]); (5, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 2; 2]); (10, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 2; 2; 2]); (20, [10; 10; 10; 10; 8; 7; 6; 6; 6; 4; 3; 2; 2; 2])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 3; 3; 1], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [42; 42; 42; 42; 28; 28; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 15; 10; 5; 0; 4; 0], 3, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (1, [7; 7; 7; 7; 6; 6; 4; 4; 4; 4; 4; 3; 2; 2]); (7, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 4; 4; 4; 3; 3; 1], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [140; 140; 42; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 56; 28; 0; 0; 14; 10; 6; 0; 5; 0], 3, [(1, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (8, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (73, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 3; 3; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 3; 3; 1], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [70; 70; 42; 42; 56; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 14; 10; 6; 0; 5; 0], 3, [(1, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (8, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 3; 3; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 3; 3; 1], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [70; 70; 98; 98; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 15; 10; 5; 0; 4; 0], 3, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 8; 8; 6; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (7, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (5, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 3; 3; 1]); (28, [10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 3; 3; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 4; 4; 4; 3; 3; 1], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [168; 168; 98; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 14; 10; 6; 0; 5; 0], 3, [(1, [9; 9; 8; 8; 8; 6; 5; 4; 3; 3; 3; 3; 3; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (8, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (4, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 3; 3; 1]); (27, [10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 3; 3; 1]); (42, [10; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 3; 3; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [48; 48; 48; 48; 32; 32; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 26; 18; 0; 9; 6; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (10, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 3; 3; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [160; 160; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 64; 32; 0; 0; 24; 16; 0; 7; 6; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (8, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (83, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [80; 80; 48; 48; 64; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 24; 16; 0; 7; 6; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (8, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 3; 3; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [80; 80; 112; 112; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 24; 16; 0; 7; 6; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (8, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1]); (32, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 5; 5; 3; 3; 3; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [68; 68; 40; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 8; 6; 0; 3; 2; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 6; 6; 6; 5; 5; 4; 4; 3; 3; 1]); (3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1]); (12, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 1]); (16, [10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 3; 3; 1])]));
  ([8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [8; 8; 10; 10; 10; 10; 2; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 6; 0; 4; 3; 2; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 2; 2]); (2, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 1])]));
  ([9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [22; 22; 8; 8; 12; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 2; 0; 8; 0; 4; 3; 2; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 2; 2]); (4, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (3, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 1])]));
  ([9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 3; 3; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [21; 21; 21; 21; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 1; 2; 0; 8; 0; 4; 3; 2; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 2; 2]); (4, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (2, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 1])]));
  ([10; 10; 9; 8; 7; 7; 7; 6; 6; 4; 3; 3; 3; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [42; 42; 24; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 4; 2; 0; 8; 0; 4; 3; 2; 0], 1, [(1, [8; 8; 7; 7; 7; 6; 6; 5; 5; 3; 3; 3; 2; 2]); (4, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (5, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 1]); (8, [9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 3; 3; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [14; 14; 14; 14; 8; 8; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 4; 8; 0; 4; 3; 2; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 2; 2])]));
  ([10; 10; 9; 8; 8; 8; 6; 6; 6; 4; 3; 3; 3; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [44; 44; 14; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 16; 8; 0; 4; 8; 0; 4; 3; 2; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 2; 2]); (23, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 3; 3; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [22; 22; 14; 14; 16; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 4; 8; 0; 4; 3; 2; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 6; 6; 4; 3; 3; 3; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [22; 22; 30; 30; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 4; 8; 0; 4; 3; 2; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 1]); (8, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 3; 3; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 3; 3; 3; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [52; 52; 30; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 4; 8; 0; 4; 3; 2; 0], 1, [(1, [9; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 2; 2]); (2, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 1]); (8, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 3; 3; 1]); (13, [10; 10; 10; 10; 8; 7; 6; 6; 6; 4; 3; 3; 3; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [48; 48; 48; 48; 32; 32; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 23; 14; 5; 6; 0; 0], 3, [(3, [7; 7; 7; 7; 6; 6; 4; 4; 4; 4; 4; 3; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (4, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [160; 160; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 64; 32; 0; 0; 23; 14; 5; 6; 0; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (7, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (83, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [80; 80; 48; 48; 64; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 23; 14; 5; 6; 0; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (7, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 4; 4; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [80; 80; 112; 112; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 23; 14; 5; 6; 0; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (7, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (32, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 5; 5; 4; 4; 2; 1], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [148; 148; 88; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 12; 6; 0; 4; 0; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (8, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (5, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (23, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 1]); (37, [10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 4; 4; 2; 1])]));
  ([8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 2; 1], (8, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [10; 10; 12; 12; 12; 12; 2; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 8; 0; 6; 3; 0; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 1]); (2, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 2; 1])]));
  ([9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 2; 1], (8, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [26; 26; 10; 10; 14; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 2; 0; 10; 0; 6; 3; 0; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 1]); (4, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 1]); (2, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 2; 1])]));
  ([9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 4; 4; 2; 1], (8, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [25; 25; 25; 25; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 1; 2; 0; 10; 0; 6; 3; 0; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 1]); (4, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 1]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 2; 1])]));
  ([10; 10; 9; 8; 7; 7; 7; 6; 6; 4; 4; 4; 2; 1], (8, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [50; 50; 28; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 4; 2; 0; 10; 0; 6; 3; 0; 0], 1, [(1, [8; 8; 7; 7; 7; 6; 6; 5; 5; 3; 3; 3; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 1]); (4, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 1]); (4, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 2; 1]); (10, [9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 4; 4; 2; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 2; 1], (15, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [35; 35; 35; 35; 20; 20; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 10; 20; 0; 11; 6; 0; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 6; 6; 4; 4; 4; 2; 1], (15, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [110; 110; 35; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 40; 20; 0; 10; 20; 0; 11; 6; 0; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 1]); (56, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 2; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 4; 4; 2; 1], (15, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [55; 55; 35; 35; 40; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 10; 20; 0; 11; 6; 0; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 2; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 6; 6; 4; 4; 4; 2; 1], (15, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [55; 55; 75; 75; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 10; 20; 0; 11; 6; 0; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 2; 1]); (20, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 4; 4; 2; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 4; 4; 2; 1], (7, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [70; 70; 41; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 6; 10; 0; 5; 3; 0; 0], 1, [(1, [9; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 3; 3; 1]); (2, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 2; 1]); (3, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 2; 1]); (10, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 4; 4; 2; 1]); (17, [10; 10; 10; 10; 8; 7; 6; 6; 6; 4; 4; 4; 2; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 3; 2; 1], (7, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [18; 18; 18; 18; 11; 11; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 3; 5; 0; 4; 0; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 6; 6; 5; 5; 3; 2; 1], (7, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [58; 58; 18; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 22; 11; 0; 3; 5; 0; 4; 0; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (29, [9; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 3; 2; 1])]));
  ([9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [47; 47; 47; 47; 47; 47; 31; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 1; 8; 15; 0; 0; 0], 3, [(3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 2; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 1]); (6, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 1])]));
  ([10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [125; 125; 47; 47; 47; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 31; 0; 1; 8; 15; 0; 0; 0], 3, [(3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 2; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 1]); (6, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 1]); (50, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 1])]));
  ([10; 10; 10; 10; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1], (32, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [219; 219; 219; 219; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 31; 62; 0; 2; 16; 30; 0; 0; 0], 6, [(6, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 2; 2]); (6, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 1]); (12, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 1]); (69, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [219; 219; 156; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 62; 31; 0; 1; 8; 15; 0; 0; 0], 3, [(3, [9; 9; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (3, [9; 9; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (6, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (81, [10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (47, [10; 10; 10; 10; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1])]));
  ([10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [78; 78; 78; 78; 47; 47; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 1; 8; 15; 0; 0; 0], 3, [(3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 2; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 1]); (6, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 1]); (3, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [250; 250; 78; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 94; 47; 0; 0; 1; 8; 15; 0; 0; 0], 3, [(3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 2; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 1]); (6, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 1]); (3, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 1]); (141, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [125; 125; 78; 78; 109; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 1; 8; 15; 0; 0; 0], 3, [(3, [9; 9; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (3, [9; 9; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (6, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (3, [10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (31, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 11; 11; 9; 8; 7; 6; 5; 5; 5; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [43; 43; 65; 65; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 3; 5; 0; 0; 0], 1, [(1, [10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (2, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 3; 2; 1]); (5, [10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (10, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1]); (13, [11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 1])]));
  ([12; 12; 11; 10; 9; 8; 7; 6; 5; 5; 5; 3; 2; 1], (85, [0; 0; 0; 0; 0; 0; 0; 85; 85; 85; 0; 0; 0; 0], [133722; 133722; 83030; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 5244; 2622; 0; 0; 0], 874, [(874, [11; 11; 10; 9; 8; 7; 6; 5; 4; 4; 4; 2; 2; 2]); (874, [11; 11; 10; 9; 8; 7; 6; 5; 4; 4; 4; 3; 3; 1]); (1748, [10; 10; 9; 8; 7; 6; 5; 5; 5; 5; 5; 4; 2; 1]); (7866, [11; 11; 10; 9; 8; 7; 6; 6; 6; 5; 5; 3; 2; 1]); (4370, [11; 11; 10; 9; 8; 7; 7; 7; 5; 5; 5; 3; 2; 1]); (13984, [11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (18354, [11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1]); (32338, [11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 1]); (50692, [11; 11; 11; 11; 9; 8; 7; 6; 5; 5; 5; 3; 2; 1])]));
  ([9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [12; 12; 8; 8; 8; 8; 8; 8; 12; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [7; 7; 6; 6; 6; 6; 6; 6; 6; 3; 3; 3; 2; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 1])]));
  ([9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [12; 12; 20; 20; 8; 8; 8; 8; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [7; 7; 6; 6; 6; 6; 6; 6; 6; 3; 3; 3; 2; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 1]); (6, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 1])]));
  ([10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [64; 64; 20; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 32; 24; 16; 8; 0; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 2; 2; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 1]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 2; 1]); (5, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 1]); (40, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1])]));
  ([9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [12; 12; 18; 18; 18; 18; 8; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 1; 0; 0], 1, [(1, [7; 7; 6; 6; 6; 6; 6; 6; 6; 3; 3; 3; 2; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 1]); (4, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 1])]));
  ([10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [44; 44; 12; 12; 24; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 8; 0; 8; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 1]); (9, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (16, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1])]));
  ([10; 10; 10; 10; 8; 8; 8; 7; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [40; 40; 40; 40; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 4; 8; 0; 8; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 1]); (9, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (12, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1])]));
  ([11; 11; 10; 9; 8; 8; 8; 7; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [80; 80; 52; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 16; 8; 0; 8; 0; 0; 1; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 1]); (1, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 2; 1]); (12, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (21, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (12, [10; 10; 10; 10; 8; 8; 8; 7; 7; 5; 4; 3; 2; 1])]));
  ([10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [32; 32; 32; 32; 12; 12; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 12; 8; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 2; 1]); (13, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1])]));
  ([11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [88; 88; 32; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 24; 12; 0; 12; 8; 0; 0; 1; 0; 0], 1, [(1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 2; 1]); (16, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1]); (33, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1])]));
  ([11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [44; 44; 32; 32; 40; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 12; 8; 0; 0; 1; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 1]); (1, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 2; 1]); (13, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (8, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1])]));
  ([11; 11; 11; 11; 9; 8; 7; 7; 7; 5; 4; 3; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [49; 49; 82; 82; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 13; 8; 0; 0; 0; 0; 0], 1, [(1, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 2; 2; 2]); (1, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 3; 3; 1]); (2, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 4; 4; 2; 1]); (2, [9; 9; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 1]); (18, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (10, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1]); (9, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 10; 9; 8; 7; 7; 7; 5; 4; 3; 2; 1], (49, [0; 0; 0; 0; 0; 0; 0; 0; 0; 49; 49; 0; 0; 0], [78120; 78120; 47430; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 2232; 4464; 0; 0; 0; 0; 0], 558, [(558, [11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 3; 2; 2; 2]); (558, [11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 3; 3; 3; 1]); (1116, [11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 4; 4; 2; 1]); (1674, [11; 11; 10; 9; 8; 7; 6; 6; 6; 5; 5; 3; 2; 1]); (2790, [10; 10; 9; 8; 7; 7; 7; 7; 7; 6; 4; 3; 2; 1]); (6696, [10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (7254, [11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1]); (16740, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 3; 2; 1]); (30690, [11; 11; 11; 11; 9; 8; 7; 7; 7; 5; 4; 3; 2; 1])]));
  ([9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [12; 12; 12; 12; 16; 16; 16; 16; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1])]));
  ([10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [28; 28; 12; 12; 16; 16; 16; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (3, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (7, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 3; 2; 1])]));
  ([10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [28; 28; 28; 28; 16; 16; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 3; 3; 1]); (4, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (6, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 3; 2; 1])]));
  ([11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [88; 88; 36; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 32; 16; 0; 8; 0; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (16, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1]); (44, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1])]));
  ([11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [52; 52; 20; 20; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 16; 8; 0; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (24, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1])]));
  ([11; 11; 11; 11; 9; 8; 8; 8; 6; 5; 4; 3; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [59; 59; 77; 77; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 20; 10; 0; 0; 0; 0; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (2, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 1]); (2, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 3; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (28, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1]); (18, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 10; 9; 8; 8; 8; 6; 5; 4; 3; 2; 1], (35, [0; 0; 0; 0; 0; 0; 0; 0; 0; 35; 35; 0; 0; 0], [73098; 73098; 42408; 0; 0; 0; 0; 7254; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 7254; 0; 0; 0; 0; 0; 0; 0], 558, [(558, [11; 11; 10; 9; 8; 7; 7; 7; 5; 4; 3; 2; 2; 2]); (558, [7; 7; 7; 7; 6; 6; 6; 6; 5; 4; 4; 3; 3; 1]); (1116, [11; 11; 10; 9; 8; 7; 7; 7; 5; 4; 4; 4; 2; 1]); (1116, [11; 11; 10; 9; 8; 7; 7; 7; 5; 5; 5; 3; 2; 1]); (2790, [11; 11; 10; 9; 8; 7; 7; 7; 6; 6; 4; 3; 2; 1]); (3906, [10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (14508, [11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1]); (11718, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 2; 1]); (30132, [11; 11; 11; 11; 9; 8; 8; 8; 6; 5; 4; 3; 2; 1])]));
  ([10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [20; 20; 24; 24; 24; 24; 16; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 2; 1]); (1, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1]); (4, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1])]));
  ([11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [60; 60; 24; 24; 24; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 16; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (1, [9; 9; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1]); (4, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1]); (1, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1]); (28, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 1])]));
  ([11; 11; 11; 11; 9; 9; 9; 7; 6; 5; 4; 3; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [58; 58; 65; 65; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 9; 18; 0; 0; 0; 0; 0; 0; 0], 1, [(1, [9; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 3; 3; 1]); (2, [9; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 2; 1]); (2, [9; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 3; 2; 1]); (5, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1]); (7, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1]); (16, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 10; 9; 9; 9; 7; 6; 5; 4; 3; 2; 1], (19, [0; 0; 0; 0; 0; 0; 0; 0; 0; 19; 19; 0; 0; 0], [68634; 68634; 37944; 0; 0; 0; 11718; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 558, [(558, [10; 10; 9; 8; 7; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (558, [11; 11; 10; 9; 8; 8; 8; 6; 5; 4; 3; 3; 3; 1]); (558, [11; 11; 10; 9; 8; 8; 8; 6; 5; 4; 4; 4; 2; 1]); (1674, [11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (2790, [11; 11; 10; 9; 8; 8; 8; 6; 6; 6; 4; 3; 2; 1]); (4464, [11; 11; 10; 9; 8; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (7254, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1]); (11718, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 1]); (18972, [11; 11; 11; 11; 9; 9; 9; 7; 6; 5; 4; 3; 2; 1])]));
  ([11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 3; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [46; 46; 46; 46; 28; 28; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 1, [(1, [7; 7; 7; 7; 6; 6; 5; 5; 4; 4; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 1]); (4, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1]); (6, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1]); (10, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 10; 10; 10; 8; 7; 6; 5; 4; 3; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 3; 3; 0; 0; 0], [6820; 6820; 3410; 0; 2108; 2108; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 62, [(62, [11; 11; 10; 9; 9; 9; 7; 6; 5; 4; 3; 2; 2; 2]); (62, [11; 11; 10; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 1]); (124, [11; 11; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 2; 1]); (186, [11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1]); (310, [11; 11; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 2; 1]); (496, [11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1]); (806, [11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1]); (1302, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 1]); (2108, [11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 11; 11; 9; 8; 7; 6; 5; 4; 3; 2; 1], (61, [0; 0; 0; 0; 0; 0; 0; 0; 0; 61; 61; 0; 0; 0], [49662; 49662; 30690; 30690; 49662; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 558, [(558, [11; 11; 10; 10; 10; 8; 7; 6; 5; 4; 3; 2; 2; 2]); (558, [11; 11; 10; 10; 10; 8; 7; 6; 5; 4; 3; 3; 3; 1]); (1116, [11; 11; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 2; 1]); (1674, [11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 1]); (2790, [11; 11; 10; 10; 10; 8; 7; 6; 6; 6; 4; 3; 2; 1]); (4464, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 3; 2; 1]); (7254, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 2; 1]); (11718, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 2; 1]); (18972, [11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 12; 12; 10; 9; 8; 7; 6; 5; 4; 3; 2; 1], (8, [0; 0; 0; 0; 0; 0; 0; 0; 0; 8; 8; 0; 0; 0], [6417; 6417; 9579; 9579; 0; 0; 1860; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 93, [(93, [10; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 2; 2; 2]); (93, [10; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 3; 3; 1]); (186, [10; 10; 10; 10; 9; 9; 7; 6; 5; 4; 4; 4; 2; 1]); (279, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1]); (465, [10; 10; 10; 10; 9; 9; 7; 6; 6; 6; 4; 3; 2; 1]); (744, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1]); (1209, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1]); (93, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 1]); (3162, [12; 12; 11; 11; 11; 9; 8; 7; 6; 5; 4; 3; 2; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 3; 3; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [37; 37; 37; 37; 23; 23; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 4; 0; 8; 6; 4; 2; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 3; 3]); (5, [7; 7; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 3; 3; 2]); (5, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 4; 3; 3; 3; 3; 3; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [120; 120; 37; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 46; 23; 0; 0; 4; 0; 8; 6; 4; 2; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 3; 3]); (10, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (5, [8; 8; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (57, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 3; 3; 2])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 3; 3; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [60; 60; 37; 37; 51; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 4; 0; 8; 6; 4; 2; 0], 2, [(2, [8; 8; 7; 7; 7; 6; 6; 4; 3; 3; 3; 3; 3; 3; 3]); (10, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (3, [9; 9; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (4, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 3; 3; 2])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 4; 3; 3; 3; 3; 3; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [60; 60; 88; 88; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 4; 0; 8; 6; 4; 2; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 3; 3]); (10, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (5, [9; 9; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 3; 3; 2]); (23, [10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 3; 3; 2])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 4; 3; 3; 3; 3; 3; 2], (7, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [172; 172; 104; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 8; 6; 4; 2; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 3; 3]); (10, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (4, [9; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (11, [9; 9; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (6, [9; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 3; 3; 2]); (25, [10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 3; 3; 2]); (39, [10; 10; 10; 10; 8; 7; 6; 5; 4; 3; 3; 3; 3; 3; 2])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 3; 3; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [15; 15; 15; 15; 10; 10; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 5; 4; 3; 0; 1; 0; 1], 1, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 4; 4; 4; 3; 3; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [50; 50; 15; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 20; 10; 0; 0; 5; 4; 3; 0; 1; 0; 1], 1, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (26, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 3; 3; 2; 2])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 3; 3; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [25; 25; 15; 15; 20; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 5; 4; 3; 0; 1; 0; 1], 1, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 3; 3; 2; 2])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 3; 3; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [25; 25; 35; 35; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 5; 4; 3; 0; 1; 0; 1], 1, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 3; 3; 2; 2]); (10, [10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 3; 3; 2; 2])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 4; 4; 4; 3; 3; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [60; 60; 35; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 5; 4; 3; 0; 1; 0; 1], 1, [(2, [9; 9; 9; 9; 7; 6; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (2, [9; 9; 9; 9; 7; 6; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (5, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 3; 3; 2; 2]); (10, [10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 3; 3; 2; 2]); (11, [10; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 3; 3; 2; 2])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 3; 3; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [18; 18; 18; 18; 12; 12; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 9; 6; 0; 2; 1; 0; 1], 1, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 2; 2])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 3; 3; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [60; 60; 18; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 24; 12; 0; 0; 9; 6; 0; 2; 1; 0; 1], 1, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 2; 2]); (31, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 3; 3; 2; 2])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [30; 30; 18; 18; 24; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 9; 6; 0; 2; 1; 0; 1], 1, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 3; 3; 2; 2])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 3; 3; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [30; 30; 42; 42; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 9; 6; 0; 2; 1; 0; 1], 1, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 3; 3; 2; 2]); (12, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 2; 2])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 5; 5; 3; 3; 3; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [72; 72; 42; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 9; 6; 0; 2; 1; 0; 1], 1, [(2, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (3, [9; 9; 8; 8; 8; 6; 5; 5; 5; 4; 4; 3; 3; 2; 2]); (4, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 3; 3; 2; 2]); (9, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 2; 2]); (18, [10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 3; 3; 2; 2])]));
  ([8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [9; 9; 12; 12; 12; 12; 3; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 6; 0; 3; 2; 1; 0; 1], 1, [(2, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 3; 3; 2]); (3, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2])]));
  ([9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [27; 27; 9; 9; 15; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 3; 0; 9; 0; 3; 2; 1; 0; 1], 1, [(2, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 3; 3; 2]); (6, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (4, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2])]));
  ([9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2], (12, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [51; 51; 51; 51; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 3; 6; 0; 18; 0; 6; 4; 2; 0; 2], 2, [(4, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 3; 3; 2]); (12, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (5, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2])]));
  ([10; 10; 9; 8; 7; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [51; 51; 30; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 6; 3; 0; 9; 0; 3; 2; 1; 0; 1], 1, [(2, [8; 8; 7; 7; 7; 6; 6; 5; 5; 3; 3; 3; 3; 3; 2]); (6, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (7, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (9, [9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2])]));
  ([9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [18; 18; 18; 18; 9; 9; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 6; 9; 0; 3; 2; 1; 0; 1], 1, [(2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2])]));
  ([10; 10; 9; 8; 8; 8; 6; 6; 6; 4; 3; 3; 3; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [54; 54; 18; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 18; 9; 0; 6; 9; 0; 3; 2; 1; 0; 1], 1, [(2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (25, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 2; 2])]));
  ([10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 3; 3; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [27; 27; 18; 18; 21; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 6; 9; 0; 3; 2; 1; 0; 1], 1, [(2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (3, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 2; 2])]));
  ([10; 10; 10; 10; 8; 7; 6; 6; 6; 4; 3; 3; 3; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [27; 27; 39; 39; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 6; 9; 0; 3; 2; 1; 0; 1], 1, [(2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (3, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 2; 2]); (9, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 3; 3; 2; 2])]));
  ([11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 3; 3; 3; 2; 2], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [96; 96; 60; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 12; 9; 0; 0; 2; 1; 0; 1], 1, [(2, [9; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 6; 6; 6; 5; 5; 4; 4; 3; 3; 2; 2]); (12, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (6, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 2; 2]); (12, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 3; 3; 2; 2]); (22, [10; 10; 10; 10; 8; 7; 6; 6; 6; 4; 3; 3; 3; 2; 2])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [18; 18; 18; 18; 12; 12; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 8; 4; 0; 1; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 2; 2])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 5; 5; 4; 4; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [60; 60; 18; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 24; 12; 0; 0; 8; 4; 0; 1; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 2; 2]); (31, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 2; 2])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [30; 30; 18; 18; 24; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 8; 4; 0; 1; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 2; 2])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 4; 4; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [30; 30; 42; 42; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 8; 4; 0; 1; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 2; 2]); (12, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 2; 2])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 5; 5; 4; 4; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [72; 72; 42; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 8; 4; 0; 1; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 2; 2]); (12, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 2; 2]); (18, [10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 4; 4; 2; 2; 2])]));
  ([8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [10; 10; 11; 11; 11; 11; 1; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 9; 0; 8; 4; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 2; 2; 2])]));
  ([9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [23; 23; 10; 10; 12; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 1; 0; 10; 0; 8; 4; 0; 2; 1], 1, [(2, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 2; 2])]));
  ([9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 4; 4; 2; 2; 2], (18, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [45; 45; 45; 45; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 1; 2; 0; 20; 0; 16; 8; 0; 4; 2], 2, [(3, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (3, [9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (4, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 2; 2])]));
  ([10; 10; 9; 8; 7; 7; 7; 6; 6; 4; 4; 4; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [45; 45; 24; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 2; 1; 0; 10; 0; 8; 4; 0; 2; 1], 1, [(3, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 2; 2]); (10, [9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 4; 4; 2; 2; 2])]));
  ([9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 2; 2; 2], (15, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [35; 35; 35; 35; 20; 20; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 10; 20; 0; 10; 5; 0; 1; 2], 2, [(3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 3; 3; 2])]));
  ([10; 10; 9; 8; 8; 8; 6; 6; 6; 4; 4; 4; 2; 2; 2], (15, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [110; 110; 35; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 40; 20; 0; 10; 20; 0; 10; 5; 0; 1; 2], 2, [(3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (57, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 2; 2; 2])]));
  ([10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 4; 4; 2; 2; 2], (15, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [55; 55; 35; 35; 40; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 10; 20; 0; 10; 5; 0; 1; 2], 2, [(3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (2, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 2; 2; 2])]));
  ([10; 10; 10; 10; 8; 7; 6; 6; 6; 4; 4; 4; 2; 2; 2], (15, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [55; 55; 75; 75; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 10; 20; 0; 10; 5; 0; 1; 2], 2, [(3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (2, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 2; 2; 2]); (20, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 4; 4; 2; 2; 2])]));
  ([11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 4; 4; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [80; 80; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 8; 10; 0; 5; 4; 0; 2; 1], 1, [(3, [9; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 3; 3; 2; 2]); (6, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 2; 2; 2]); (4, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 2; 2; 2]); (10, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 4; 4; 2; 2; 2]); (19, [10; 10; 10; 10; 8; 7; 6; 6; 6; 4; 4; 4; 2; 2; 2])]));
  ([9; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 3; 2; 2; 2], (23, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [61; 61; 61; 61; 38; 38; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 8; 16; 1; 12; 0; 0; 6; 3], 3, [(9, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 2; 2])]));
  ([10; 10; 9; 8; 8; 8; 6; 6; 6; 5; 5; 3; 2; 2; 2], (23, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [198; 198; 61; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 76; 38; 0; 8; 16; 1; 12; 0; 0; 6; 3], 3, [(9, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 2; 2]); (102, [9; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 3; 2; 2; 2])]));
  ([9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [17; 17; 17; 17; 17; 17; 11; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 1; 3; 5; 0; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 2; 2])]));
  ([10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [45; 45; 17; 17; 17; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 11; 0; 1; 3; 5; 0; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (18, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 2; 2])]));
  ([10; 10; 10; 10; 8; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2], (12, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [79; 79; 79; 79; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 11; 22; 0; 2; 6; 10; 0; 0; 4; 2], 2, [(6, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (25, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 2; 2])]));
  ([11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [85; 85; 62; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 26; 13; 0; 0; 4; 5; 0; 0; 2; 1], 1, [(3, [9; 9; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (3, [9; 9; 8; 8; 8; 7; 7; 6; 6; 5; 5; 3; 2; 2; 2]); (32, [10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2]); (18, [10; 10; 10; 10; 8; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2])]));
  ([10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [28; 28; 28; 28; 17; 17; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 1; 3; 5; 0; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 2; 2])]));
  ([11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 2; 2], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [98; 98; 31; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 36; 18; 0; 0; 0; 4; 5; 0; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (3, [9; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 3; 2; 2; 2]); (4, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 2; 2]); (51, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 2; 2])]));
  ([11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 2; 2], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [45; 45; 28; 28; 39; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 1; 3; 5; 0; 0; 2; 1], 1, [(3, [9; 9; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (1, [10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2]); (11, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 2; 2])]));
  ([11; 11; 11; 11; 9; 8; 7; 6; 5; 5; 5; 3; 2; 2; 2], (13, [0; 0; 0; 0; 0; 0; 0; 13; 13; 13; 0; 0; 0; 0; 0], [55936; 55936; 83904; 83904; 7866; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 7866; 4370; 0; 0; 1748; 874], 874, [(2622, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 3; 3; 2; 2]); (874, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 2; 2]); (11362, [10; 10; 9; 9; 9; 7; 6; 6; 6; 5; 5; 3; 2; 2; 2]); (4370, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 2; 2; 2]); (15732, [10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2]); (13110, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 2; 2])]));
  ([12; 12; 11; 10; 9; 8; 7; 6; 5; 5; 5; 3; 2; 2; 2], (79, [0; 0; 0; 0; 0; 0; 0; 79; 79; 79; 0; 0; 0; 0; 0], [131974; 131974; 81282; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 1748; 3496; 0; 0; 1748; 874], 874, [(2622, [11; 11; 10; 9; 8; 7; 6; 5; 4; 4; 4; 3; 3; 2; 2]); (874, [10; 10; 9; 8; 7; 6; 5; 5; 5; 5; 5; 4; 2; 2; 2]); (5244, [10; 10; 9; 8; 7; 6; 6; 6; 6; 6; 5; 3; 2; 2; 2]); (4370, [11; 11; 10; 9; 8; 7; 7; 7; 5; 5; 5; 3; 2; 2; 2]); (10488, [11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2]); (20102, [11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 2; 2]); (30590, [11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 2; 2]); (50692, [11; 11; 11; 11; 9; 8; 7; 6; 5; 5; 5; 3; 2; 2; 2])]));
  ([9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [27; 27; 18; 18; 18; 18; 18; 18; 27; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 4; 2], 2, [(6, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 2; 2; 2])]));
  ([9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [27; 27; 45; 45; 18; 18; 18; 18; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 4; 2], 2, [(6, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 2; 2; 2]); (11, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 2; 2])]));
  ([10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [144; 144; 45; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 72; 54; 36; 18; 0; 0; 0; 1; 0; 4; 2], 2, [(6, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 2; 2; 2]); (11, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 2; 2]); (90, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2])]));
  ([9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 2; 2], (18, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [54; 54; 81; 81; 81; 81; 36; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 9; 0; 0; 2; 0; 8; 4], 4, [(12, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 2; 2; 2]); (13, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 2; 2])]));
  ([10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [99; 99; 27; 27; 54; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 18; 0; 18; 0; 0; 1; 0; 4; 2], 2, [(6, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 2; 2]); (20, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (36, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 2; 2])]));
  ([10; 10; 10; 10; 8; 8; 8; 7; 7; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [90; 90; 90; 90; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 9; 18; 0; 18; 0; 0; 1; 0; 4; 2], 2, [(6, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 2; 2]); (20, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (27, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 2; 2])]));
  ([11; 11; 10; 9; 8; 8; 8; 7; 7; 5; 4; 3; 2; 2; 2], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [94; 94; 62; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 20; 10; 0; 9; 0; 0; 0; 0; 2; 1], 1, [(3, [9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 4; 4; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (14, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (29, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (10, [10; 10; 10; 10; 8; 8; 8; 7; 7; 5; 4; 3; 2; 2; 2])]));
  ([10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [72; 72; 72; 72; 27; 27; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 27; 18; 0; 0; 1; 0; 4; 2], 2, [(6, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 2; 2; 2]); (29, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 2; 2])]));
  ([11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 3; 2; 2; 2], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [104; 104; 38; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 28; 14; 0; 14; 9; 0; 0; 0; 0; 2; 1], 1, [(3, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 2; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (19, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (38, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 2; 2])]));
  ([11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 3; 2; 2; 2], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [52; 52; 38; 38; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 14; 9; 0; 0; 0; 0; 2; 1], 1, [(3, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (15, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (10, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 2; 2])]));
  ([11; 11; 11; 11; 9; 8; 7; 7; 7; 5; 4; 3; 2; 2; 2], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 4; 4; 0; 0; 0; 0], [16740; 16740; 27342; 27342; 2232; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 6417; 3906; 0; 0; 0; 0; 558; 279], 279, [(837, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 2; 2]); (279, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 4; 4; 2; 2; 2]); (1116, [9; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 3; 2; 2; 2]); (1395, [10; 10; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 2; 2; 2]); (8928, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (1953, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 2; 2])]));
  ([12; 12; 11; 10; 9; 8; 7; 7; 7; 5; 4; 3; 2; 2; 2], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 16; 16; 0; 0; 0; 0], [36270; 36270; 22041; 0; 0; 0; 0; 0; 2511; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 558; 279], 279, [(837, [11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 3; 3; 3; 2; 2]); (279, [11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 4; 4; 2; 2; 2]); (1116, [11; 11; 10; 9; 8; 7; 6; 6; 6; 5; 5; 3; 2; 2; 2]); (1395, [10; 10; 9; 8; 7; 7; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (2511, [10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (3906, [11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 3; 2; 2; 2]); (7812, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 3; 2; 2; 2]); (14229, [11; 11; 11; 11; 9; 8; 7; 7; 7; 5; 4; 3; 2; 2; 2])]));
  ([9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [27; 27; 27; 27; 36; 36; 36; 36; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 4; 2], 2, [(6, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 2; 2; 2]); (3, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2])]));
  ([10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [63; 63; 27; 27; 36; 36; 36; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 4; 2], 2, [(6, [8; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 2; 2]); (8, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (12, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 3; 2; 2; 2])]));
  ([10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [63; 63; 63; 63; 36; 36; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 4; 2], 2, [(6, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 2; 2]); (2, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (18, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 3; 2; 2; 2])]));
  ([11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 2; 2], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [104; 104; 43; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 38; 19; 0; 10; 0; 0; 0; 0; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (20, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 2; 2]); (51, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 2; 2])]));
  ([11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 2; 2; 2], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [62; 62; 23; 23; 58; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 20; 10; 0; 0; 0; 0; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (29, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 2; 2])]));
  ([11; 11; 11; 11; 9; 8; 8; 8; 6; 5; 4; 3; 2; 2; 2], (2, [0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 2; 0; 0; 0; 0], [6882; 6882; 7719; 7719; 1302; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 3441; 2139; 0; 0; 0; 0; 0; 186; 93], 93, [(279, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (93, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (372, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 2; 2; 2]); (465, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 3; 2; 2; 2]); (837, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (3534, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 2; 2])]));
  ([12; 12; 11; 10; 9; 8; 8; 8; 6; 5; 4; 3; 2; 2; 2], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 13; 13; 0; 0; 0; 0], [23994; 23994; 15438; 0; 0; 0; 0; 2604; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 372; 186], 186, [(558, [11; 11; 10; 9; 8; 7; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (186, [11; 11; 10; 9; 8; 7; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (744, [11; 11; 10; 9; 8; 7; 7; 7; 5; 5; 5; 3; 2; 2; 2]); (930, [11; 11; 10; 9; 8; 7; 7; 7; 6; 6; 4; 3; 2; 2; 2]); (1674, [10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (2604, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 2; 2]); (4278, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 2; 2; 2]); (8556, [11; 11; 11; 11; 9; 8; 8; 8; 6; 5; 4; 3; 2; 2; 2])]));
  ([10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 2; 2], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [45; 45; 54; 54; 54; 54; 36; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 4; 2], 2, [(6, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 2; 2; 2]); (2, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (9, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 2; 2])]));
  ([11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 2; 2; 2], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [71; 71; 29; 29; 29; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 19; 0; 0; 0; 0; 0; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (6, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 2; 2]); (32, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 2; 2])]));
  ([11; 11; 11; 11; 9; 9; 9; 7; 6; 5; 4; 3; 2; 2; 2], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [61; 61; 68; 68; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 10; 19; 0; 0; 0; 0; 0; 0; 2; 1], 1, [(3, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [9; 9; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 2; 2]); (1, [10; 10; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 2; 2]); (2, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (5, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 2; 2]); (23, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 2; 2])]));
  ([12; 12; 11; 10; 9; 9; 9; 7; 6; 5; 4; 3; 2; 2; 2], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 13; 13; 0; 0; 0; 0], [30969; 30969; 20646; 0; 0; 6417; 6417; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 558; 279], 279, [(837, [11; 11; 10; 9; 8; 8; 8; 6; 5; 4; 3; 3; 3; 2; 2]); (279, [10; 10; 9; 8; 7; 7; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (1116, [11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2]); (1116, [11; 11; 10; 9; 8; 8; 8; 6; 6; 6; 4; 3; 2; 2; 2]); (2511, [11; 11; 10; 9; 8; 8; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (3906, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 2; 2]); (6417, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 2; 2; 2]); (10323, [11; 11; 11; 11; 9; 9; 9; 7; 6; 5; 4; 3; 2; 2; 2])]));
  ([11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 3; 2; 2; 2], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [48; 48; 48; 48; 29; 29; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 1], 1, [(3, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 3; 2; 2; 2]); (5, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (2, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 2; 2]); (9, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 2; 2])]));
  ([12; 12; 11; 10; 10; 10; 8; 7; 6; 5; 4; 3; 2; 2; 2], (35, [0; 0; 0; 0; 0; 0; 0; 0; 0; 35; 35; 0; 0; 0; 0], [54126; 54126; 33480; 0; 20646; 33480; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1116; 558], 558, [(1674, [11; 11; 10; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 2; 2]); (558, [11; 11; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 2; 2; 2]); (2232, [11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 2; 2]); (2790, [11; 11; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 2; 2; 2]); (5022, [11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 3; 2; 2; 2]); (7812, [11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 2; 2]); (12834, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 2; 2; 2]); (20646, [11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 3; 2; 2; 2])]));
  ([12; 12; 11; 11; 11; 9; 8; 7; 6; 5; 4; 3; 2; 2; 2], (95, [0; 0; 0; 0; 0; 0; 0; 0; 0; 95; 95; 0; 0; 0; 0], [54126; 54126; 33480; 33480; 54126; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1116; 558], 558, [(1674, [11; 11; 10; 10; 10; 8; 7; 6; 5; 4; 3; 3; 3; 2; 2]); (558, [11; 11; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 2; 2; 2]); (2232, [11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 2; 2]); (2790, [11; 11; 10; 10; 10; 8; 7; 6; 6; 6; 4; 3; 2; 2; 2]); (5022, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 3; 2; 2; 2]); (7812, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 2; 2; 2]); (12834, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 2; 2; 2]); (20646, [11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 3; 2; 2; 2])]));
  ([12; 12; 12; 12; 10; 9; 8; 7; 6; 5; 4; 3; 2; 2; 2], (37, [0; 0; 0; 0; 0; 0; 0; 0; 0; 37; 37; 0; 0; 0; 0], [20367; 20367; 30690; 30690; 0; 279; 6417; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 558; 279], 279, [(837, [10; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 3; 3; 2; 2]); (279, [10; 10; 10; 10; 9; 9; 7; 6; 5; 4; 4; 4; 2; 2; 2]); (1116, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 2; 2]); (1395, [10; 10; 10; 10; 9; 9; 7; 6; 6; 6; 4; 3; 2; 2; 2]); (2511, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 2; 2]); (3906, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 2; 2]); (10323, [12; 12; 11; 11; 11; 9; 8; 7; 6; 5; 4; 3; 2; 2; 2])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 4; 4; 3; 1], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [42; 42; 42; 42; 28; 28; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 16; 13; 10; 7; 4; 0; 0], 3, [(2, [7; 7; 7; 7; 6; 6; 4; 4; 4; 4; 4; 4; 4; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (6, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 4; 4; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 4; 4; 4; 4; 4; 3; 1], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [140; 140; 42; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 56; 28; 0; 0; 16; 13; 10; 7; 4; 0; 0], 3, [(2, [8; 8; 7; 6; 6; 6; 4; 4; 4; 4; 4; 4; 4; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (6, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 4; 4; 1]); (77, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 4; 4; 3; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 4; 4; 3; 1], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [70; 70; 42; 42; 56; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 16; 13; 10; 7; 4; 0; 0], 3, [(2, [8; 8; 7; 7; 7; 5; 4; 4; 4; 4; 4; 4; 4; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (6, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 4; 4; 1]); (7, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 4; 4; 3; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 4; 4; 3; 1], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [70; 70; 98; 98; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 16; 13; 10; 7; 4; 0; 0], 3, [(2, [8; 8; 8; 8; 6; 5; 4; 4; 4; 4; 4; 4; 4; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (6, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 4; 4; 1]); (7, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 4; 4; 3; 1]); (28, [10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 4; 4; 3; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 4; 4; 4; 4; 4; 3; 1], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [168; 168; 98; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 16; 13; 10; 7; 4; 0; 0], 3, [(2, [8; 8; 8; 8; 6; 5; 4; 4; 4; 4; 4; 4; 4; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (6, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 4; 4; 1]); (7, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 4; 4; 3; 1]); (28, [10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 4; 4; 3; 1]); (40, [10; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 4; 4; 3; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 3; 3; 1], (32, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [96; 96; 96; 96; 64; 64; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 43; 22; 1; 6; 0; 3; 0], 6, [(6, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (9, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 4; 4; 1]); (11, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 3; 3; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 5; 5; 4; 4; 3; 3; 1], (32, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [320; 320; 96; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 128; 64; 0; 0; 43; 22; 1; 6; 0; 3; 0], 6, [(6, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (9, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 4; 4; 1]); (11, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 3; 3; 1]); (166, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 3; 3; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 3; 3; 1], (32, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [160; 160; 96; 96; 128; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 43; 22; 1; 6; 0; 3; 0], 6, [(6, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (9, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 4; 4; 1]); (11, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 3; 3; 1]); (6, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 3; 3; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 4; 4; 3; 3; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [80; 80; 112; 112; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 22; 11; 0; 3; 0; 2; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (4, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 4; 4; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 4; 4; 3; 1]); (6, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 3; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 3; 3; 1]); (32, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 3; 3; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 5; 5; 4; 4; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [80; 80; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 6; 4; 0; 2; 0; 1; 0], 1, [(1, [8; 8; 8; 8; 6; 5; 4; 4; 4; 4; 4; 3; 3; 3; 2]); (2, [9; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 4; 4; 3; 1]); (3, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 3; 3; 1]); (4, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (5, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 3; 3; 1]); (12, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 3; 3; 1]); (17, [10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 4; 4; 3; 3; 1])]));
  ([8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 3; 3; 1], (8, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [10; 10; 12; 12; 12; 12; 2; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 8; 0; 6; 4; 2; 1; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 3; 3; 2]); (2, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 1])]));
  ([9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 3; 3; 1], (8, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [26; 26; 10; 10; 14; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 2; 0; 10; 0; 6; 4; 2; 1; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 3; 3; 2]); (4, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (3, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 3; 3; 1])]));
  ([9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 4; 4; 3; 3; 1], (8, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [25; 25; 25; 25; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 1; 2; 0; 10; 0; 6; 4; 2; 1; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 3; 3; 2]); (4, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (2, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 3; 3; 1])]));
  ([10; 10; 9; 8; 7; 7; 7; 6; 6; 4; 4; 4; 3; 3; 1], (8, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [50; 50; 28; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 4; 2; 0; 10; 0; 6; 4; 2; 1; 0], 1, [(1, [8; 8; 7; 7; 7; 6; 6; 5; 5; 3; 3; 3; 3; 3; 2]); (4, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (5, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (10, [9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 4; 4; 3; 3; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 3; 3; 1], (15, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [35; 35; 35; 35; 20; 20; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 10; 20; 0; 11; 7; 3; 2; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 4; 4; 3; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 6; 6; 4; 4; 4; 3; 3; 1], (15, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [110; 110; 35; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 40; 20; 0; 10; 20; 0; 11; 7; 3; 2; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 4; 4; 3; 1]); (57, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 3; 3; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 4; 4; 3; 3; 1], (15, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [55; 55; 35; 35; 40; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 10; 20; 0; 11; 7; 3; 2; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 4; 4; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 3; 3; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 6; 6; 4; 4; 4; 3; 3; 1], (15, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [55; 55; 75; 75; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 10; 20; 0; 11; 7; 3; 2; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 4; 4; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 3; 3; 1]); (20, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 4; 4; 3; 3; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 4; 4; 3; 3; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [80; 80; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 8; 10; 0; 4; 2; 0; 1; 0], 1, [(1, [9; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (2, [9; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 4; 4; 3; 1]); (6, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (4, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 3; 3; 1]); (10, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 4; 4; 3; 3; 1]); (19, [10; 10; 10; 10; 8; 7; 6; 6; 6; 4; 4; 4; 3; 3; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 3; 3; 3; 1], (22, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [52; 52; 52; 52; 30; 30; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 14; 18; 0; 16; 0; 6; 3; 0], 3, [(2, [7; 7; 7; 7; 6; 6; 4; 4; 4; 4; 4; 3; 3; 3; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (9, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 3; 3; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 6; 6; 5; 5; 3; 3; 3; 1], (22, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [164; 164; 52; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 60; 30; 0; 14; 18; 0; 16; 0; 6; 3; 0], 3, [(2, [7; 7; 7; 7; 6; 6; 4; 4; 4; 4; 4; 3; 3; 3; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (9, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 3; 3; 1]); (78, [9; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 3; 3; 3; 1])]));
  ([9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 3; 3; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [48; 48; 48; 48; 48; 48; 32; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 10; 18; 0; 6; 3; 0], 3, [(1, [7; 7; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 3; 3; 2]); (2, [8; 8; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (9, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 3; 3; 1])]));
  ([10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [128; 128; 48; 48; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 32; 0; 0; 8; 16; 0; 7; 6; 0], 3, [(3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (8, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (51, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 3; 3; 1])]));
  ([10; 10; 10; 10; 8; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [112; 112; 112; 112; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 16; 32; 0; 0; 10; 18; 0; 9; 6; 0], 3, [(3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (10, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (2, [9; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 3; 3; 1]); (33, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 3; 3; 1])]));
  ([11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [78; 78; 56; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 22; 11; 0; 0; 3; 6; 0; 3; 2; 0], 1, [(1, [8; 8; 7; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 2; 2]); (4, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (29, [10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1]); (17, [10; 10; 10; 10; 8; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1])]));
  ([10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [80; 80; 80; 80; 48; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 10; 18; 0; 9; 6; 0], 3, [(3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (10, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (2, [9; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 3; 3; 1])]));
  ([11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [90; 90; 28; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 34; 17; 0; 0; 0; 3; 6; 0; 2; 1; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 1]); (3, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 3; 3; 1]); (49, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 1])]));
  ([11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 3; 3; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [45; 45; 28; 28; 40; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 3; 6; 0; 2; 1; 0], 1, [(1, [8; 8; 7; 7; 7; 6; 6; 4; 4; 4; 3; 3; 3; 3; 2]); (3, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 1]); (2, [10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1]); (11, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 1])]));
  ([11; 11; 11; 11; 9; 8; 7; 6; 5; 5; 5; 3; 3; 3; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [45; 45; 68; 68; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 3; 6; 0; 3; 2; 0], 1, [(1, [10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 3; 3; 2; 2]); (4, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (1, [10; 10; 9; 9; 9; 7; 7; 7; 5; 5; 5; 3; 3; 3; 1]); (2, [10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1]); (12, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 1]); (15, [11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 3; 3; 1])]));
  ([12; 12; 11; 10; 9; 8; 7; 6; 5; 5; 5; 3; 3; 3; 1], (37, [0; 0; 0; 0; 0; 0; 0; 37; 37; 37; 0; 0; 0; 0; 0], [65113; 65113; 40204; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 437; 874; 0; 1311; 874; 0], 437, [(437, [11; 11; 10; 9; 8; 7; 6; 5; 4; 4; 4; 3; 3; 2; 2]); (1748, [10; 10; 9; 8; 7; 6; 5; 5; 5; 5; 5; 4; 3; 3; 1]); (1311, [10; 10; 9; 8; 7; 6; 6; 6; 6; 6; 5; 3; 3; 3; 1]); (2622, [11; 11; 10; 9; 8; 7; 7; 7; 5; 5; 5; 3; 3; 3; 1]); (5681, [11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1]); (9614, [11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 1]); (15295, [11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 3; 3; 1]); (24909, [11; 11; 11; 11; 9; 8; 7; 6; 5; 5; 5; 3; 3; 3; 1])]));
  ([9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [12; 12; 8; 8; 8; 8; 8; 8; 12; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 2; 1; 0], 1, [(1, [7; 7; 6; 6; 6; 6; 6; 6; 6; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 1])]));
  ([9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [12; 12; 20; 20; 8; 8; 8; 8; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 2; 1; 0], 1, [(1, [7; 7; 6; 6; 6; 6; 6; 6; 6; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 1]); (6, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 3; 3; 1])]));
  ([10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [64; 64; 20; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 32; 24; 16; 8; 0; 0; 0; 2; 3; 2; 0], 1, [(1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 1]); (5, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 3; 3; 1]); (40, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1])]));
  ([9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [12; 12; 18; 18; 18; 18; 8; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 2; 2; 1; 0], 1, [(1, [7; 7; 6; 6; 6; 6; 6; 6; 6; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 1]); (4, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 3; 3; 1])]));
  ([10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [44; 44; 12; 12; 24; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 8; 0; 8; 0; 0; 2; 3; 2; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (9, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (16, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 3; 3; 1])]));
  ([10; 10; 10; 10; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [40; 40; 40; 40; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 4; 8; 0; 8; 0; 0; 2; 3; 2; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (9, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (12, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 3; 3; 1])]));
  ([11; 11; 10; 9; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [80; 80; 52; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 16; 8; 0; 8; 0; 0; 2; 3; 2; 0], 1, [(1, [9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (2, [9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (12, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (24, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (9, [10; 10; 10; 10; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1])]));
  ([10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [32; 32; 32; 32; 12; 12; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 12; 8; 0; 0; 2; 3; 2; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (13, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 3; 3; 1])]));
  ([11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [88; 88; 32; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 24; 12; 0; 12; 8; 0; 0; 2; 3; 2; 0], 1, [(1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 2; 2]); (2, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 3; 3; 1]); (16, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (33, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 3; 3; 1])]));
  ([11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [44; 44; 32; 32; 40; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 12; 8; 0; 0; 2; 3; 2; 0], 1, [(1, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (2, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (13, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (8, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 3; 3; 1])]));
  ([11; 11; 11; 11; 9; 8; 7; 7; 7; 5; 4; 3; 3; 3; 1], (2, [0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 2; 0; 0; 0; 0], [16182; 16182; 28458; 28458; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 6138; 3906; 0; 0; 0; 837; 558; 0], 279, [(279, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 3; 3; 2; 2]); (1116, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 4; 4; 3; 3; 1]); (558, [10; 10; 9; 9; 9; 7; 6; 6; 6; 5; 5; 3; 3; 3; 1]); (1674, [10; 10; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 3; 3; 1]); (8370, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (3906, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 3; 3; 1]); (279, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 3; 3; 3; 1])]));
  ([12; 12; 11; 10; 9; 8; 7; 7; 7; 5; 4; 3; 3; 3; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 13; 13; 0; 0; 0; 0], [35712; 35712; 21762; 0; 0; 0; 0; 0; 2232; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 558; 279; 0], 279, [(279, [10; 10; 9; 8; 7; 6; 5; 5; 5; 3; 3; 3; 3; 3; 2]); (837, [11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 4; 4; 3; 3; 1]); (558, [11; 11; 10; 9; 8; 7; 6; 6; 6; 5; 5; 3; 3; 3; 1]); (1674, [10; 10; 9; 8; 7; 7; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (2232, [10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (3906, [11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 3; 3; 3; 1]); (7812, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 3; 3; 3; 1]); (13950, [11; 11; 11; 11; 9; 8; 7; 7; 7; 5; 4; 3; 3; 3; 1])]));
  ([9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [12; 12; 12; 12; 16; 16; 16; 16; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 2; 1; 0], 1, [(1, [7; 7; 7; 7; 6; 6; 6; 6; 5; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1])]));
  ([10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [28; 28; 12; 12; 16; 16; 16; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 2; 1; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (3, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (7, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 3; 3; 3; 1])]));
  ([10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [28; 28; 28; 28; 16; 16; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 3; 2; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (8, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 3; 3; 3; 1])]));
  ([11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [88; 88; 36; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 32; 16; 0; 8; 0; 0; 0; 2; 2; 1; 0], 1, [(1, [8; 8; 7; 7; 7; 7; 7; 6; 4; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (3, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (15, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 3; 3; 1]); (44, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1])]));
  ([11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [52; 52; 20; 20; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 16; 8; 0; 0; 0; 2; 2; 1; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (3, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (23, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1])]));
  ([11; 11; 11; 11; 9; 8; 8; 8; 6; 5; 4; 3; 3; 3; 1], (1, [0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0], [4464; 4464; 5394; 5394; 434; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 2232; 1364; 0; 0; 0; 0; 186; 124; 0], 62, [(62, [10; 10; 9; 9; 9; 7; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (248, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (124, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 1]); (372, [10; 10; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 3; 3; 1]); (496, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (2728, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1])]));
  ([12; 12; 11; 10; 9; 8; 8; 8; 6; 5; 4; 3; 3; 3; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 3; 3; 0; 0; 0; 0], [4278; 4278; 2480; 0; 0; 0; 0; 434; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 434; 0; 0; 0; 0; 0; 62; 31; 0], 31, [(31, [10; 10; 9; 8; 7; 6; 6; 6; 4; 3; 3; 3; 3; 3; 2]); (93, [11; 11; 10; 9; 8; 7; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (62, [11; 11; 10; 9; 8; 7; 7; 7; 5; 5; 5; 3; 3; 3; 1]); (186, [11; 11; 10; 9; 8; 7; 7; 7; 6; 6; 4; 3; 3; 3; 1]); (248, [10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (868, [11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1]); (682, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 3; 3; 1]); (1798, [11; 11; 11; 11; 9; 8; 8; 8; 6; 5; 4; 3; 3; 3; 1])]));
  ([10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [20; 20; 24; 24; 24; 24; 16; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 3; 2; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (4, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 3; 3; 1])]));
  ([11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [60; 60; 24; 24; 24; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 16; 0; 0; 0; 0; 2; 2; 1; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (3, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (4, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 3; 3; 1]); (27, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 3; 3; 1])]));
  ([11; 11; 11; 11; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 1], (2, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [64; 64; 74; 74; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 10; 20; 0; 0; 0; 0; 0; 2; 1; 0], 1, [(1, [7; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (4, [9; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 3; 3; 3; 1]); (2, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (10, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 3; 3; 1]); (20, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 3; 3; 1])]));
  ([12; 12; 11; 10; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 1], (8, [0; 0; 0; 0; 0; 0; 0; 0; 0; 8; 8; 0; 0; 0; 0], [30132; 30132; 20088; 0; 0; 6138; 6138; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 558; 279; 0], 279, [(279, [10; 10; 9; 8; 7; 7; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (837, [11; 11; 10; 9; 8; 8; 8; 6; 5; 4; 4; 4; 3; 3; 1]); (558, [11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1]); (1674, [11; 11; 10; 9; 8; 8; 8; 6; 6; 6; 4; 3; 3; 3; 1]); (2232, [11; 11; 10; 9; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (3906, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 3; 3; 1]); (6138, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 3; 3; 1]); (10044, [11; 11; 11; 11; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 1])]));
  ([11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 3; 3; 3; 1], (2, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [52; 52; 52; 52; 32; 32; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 1; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 3; 3; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (4, [9; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 3; 3; 3; 1]); (3, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (9, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1]); (8, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 3; 3; 1])]));
  ([12; 12; 11; 10; 10; 10; 8; 7; 6; 5; 4; 3; 3; 3; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 4; 4; 0; 0; 0; 0], [8742; 8742; 5394; 0; 3348; 5394; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 186; 93; 0], 93, [(93, [10; 10; 9; 8; 8; 8; 6; 5; 4; 3; 3; 3; 3; 3; 2]); (279, [11; 11; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 3; 3; 1]); (186, [11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 1]); (558, [11; 11; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 3; 3; 1]); (744, [11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 3; 3; 3; 1]); (1302, [11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1]); (2046, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 3; 3; 1]); (3348, [11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 3; 3; 3; 1])]));
  ([12; 12; 11; 11; 11; 9; 8; 7; 6; 5; 4; 3; 3; 3; 1], (41, [0; 0; 0; 0; 0; 0; 0; 0; 0; 41; 41; 0; 0; 0; 0], [26226; 26226; 16182; 16182; 26226; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 558; 279; 0], 279, [(279, [10; 10; 9; 9; 9; 7; 6; 5; 4; 3; 3; 3; 3; 3; 2]); (837, [11; 11; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 3; 3; 1]); (558, [11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 3; 3; 1]); (1674, [11; 11; 10; 10; 10; 8; 7; 6; 6; 6; 4; 3; 3; 3; 1]); (2232, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 3; 3; 3; 1]); (3906, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 3; 3; 1]); (6138, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 3; 3; 1]); (10044, [11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 3; 3; 3; 1])]));
  ([12; 12; 12; 12; 10; 9; 8; 7; 6; 5; 4; 3; 3; 3; 1], (7, [0; 0; 0; 0; 0; 0; 0; 0; 0; 7; 7; 0; 0; 0; 0], [4402; 4402; 6634; 6634; 0; 124; 1302; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 124; 62; 0], 62, [(62, [8; 8; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 3; 3; 2]); (186, [10; 10; 10; 10; 9; 9; 7; 6; 5; 4; 4; 4; 3; 3; 1]); (124, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 1]); (372, [10; 10; 10; 10; 9; 9; 7; 6; 6; 6; 4; 3; 3; 3; 1]); (496, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 3; 3; 1]); (868, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1]); (2232, [12; 12; 11; 11; 11; 9; 8; 7; 6; 5; 4; 3; 3; 3; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [17; 17; 17; 17; 11; 11; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 1; 11; 9; 6; 3; 0; 0; 0], 1, [(1, [7; 7; 7; 7; 6; 6; 4; 4; 4; 4; 4; 4; 4; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 4; 4; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 5; 5; 2; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [56; 56; 17; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 22; 11; 0; 1; 11; 9; 6; 3; 0; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 4; 4; 3; 1]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 5; 5; 2; 1]); (29, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 5; 5; 4; 2; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [28; 28; 17; 17; 22; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 1; 11; 9; 6; 3; 0; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 4; 4; 3; 1]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 5; 5; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 5; 5; 4; 2; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [28; 28; 39; 39; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 1; 11; 9; 6; 3; 0; 0; 0], 1, [(1, [7; 7; 7; 7; 6; 6; 4; 4; 4; 4; 4; 4; 4; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 4; 4; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 5; 5; 2; 1]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1]); (11, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 5; 5; 4; 2; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 5; 5; 5; 5; 5; 4; 2; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [67; 67; 39; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 1; 11; 9; 6; 3; 0; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 4; 4; 3; 1]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 5; 5; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1]); (11, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 5; 5; 4; 2; 1]); (17, [10; 10; 10; 10; 8; 7; 6; 5; 5; 5; 5; 5; 4; 2; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 4; 4; 2; 1], (29, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [70; 70; 70; 70; 41; 41; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 17; 23; 0; 17; 5; 8; 0; 0], 4, [(4, [8; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (4, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 4; 4; 3; 1]); (7, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 6; 6; 5; 5; 4; 4; 2; 1], (29, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [222; 222; 70; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 82; 41; 0; 17; 23; 0; 17; 5; 8; 0; 0], 4, [(4, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 2; 2]); (4, [8; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 4; 4; 3; 1]); (11, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1]); (104, [9; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 4; 4; 2; 1])]));
  ([9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 4; 4; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [48; 48; 48; 48; 48; 48; 32; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 7; 14; 5; 6; 0; 0], 3, [(3, [7; 7; 7; 7; 7; 7; 6; 4; 4; 4; 4; 4; 3; 2; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (4, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 5; 5; 4; 2; 1])]));
  ([10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [128; 128; 48; 48; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 32; 0; 0; 7; 14; 5; 6; 0; 0], 3, [(3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (7, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (51, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 4; 4; 2; 1])]));
  ([10; 10; 10; 10; 8; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [112; 112; 112; 112; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 16; 32; 0; 0; 7; 14; 5; 6; 0; 0], 3, [(3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (7, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (35, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 4; 4; 2; 1])]));
  ([11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [166; 166; 120; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 46; 23; 0; 0; 3; 6; 0; 4; 0; 0], 2, [(2, [8; 8; 8; 8; 6; 6; 6; 4; 4; 4; 4; 4; 3; 2; 2]); (2, [9; 9; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (6, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (5, [9; 9; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 1]); (61, [10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (35, [10; 10; 10; 10; 8; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1])]));
  ([10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 1], (16, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [80; 80; 80; 80; 48; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 7; 14; 5; 6; 0; 0], 3, [(3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (7, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (3, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 4; 4; 2; 1])]));
  ([11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 1], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [194; 194; 60; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 74; 37; 0; 0; 0; 3; 6; 0; 4; 0; 0], 2, [(2, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 3; 3; 2; 2]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 4; 4; 3; 1]); (8, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1]); (5, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (14, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (94, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 1])]));
  ([11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 4; 4; 2; 1], (9, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [97; 97; 60; 60; 88; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 3; 6; 0; 4; 0; 0], 2, [(2, [9; 9; 8; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (2, [9; 9; 8; 8; 8; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (8, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (5, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (2, [10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (23, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 1])]));
  ([11; 11; 11; 11; 9; 8; 7; 6; 5; 5; 5; 4; 4; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 4; 4; 4; 0; 0; 0; 0; 0], [27094; 27094; 43263; 43263; 874; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 2622; 1311; 0; 874; 0; 0], 437, [(437, [10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 3; 3; 2; 2]); (437, [9; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 4; 4; 3; 1]); (1748, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 5; 5; 4; 2; 1]); (3933, [10; 10; 9; 9; 9; 7; 6; 6; 6; 5; 5; 4; 4; 2; 1]); (3059, [10; 10; 9; 9; 9; 7; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (6992, [10; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (9614, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 1])]));
  ([12; 12; 11; 10; 9; 8; 7; 6; 5; 5; 5; 4; 4; 2; 1], (79, [0; 0; 0; 0; 0; 0; 0; 79; 79; 79; 0; 0; 0; 0; 0], [131974; 131974; 81282; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 874; 1748; 0; 2622; 0; 0], 874, [(874, [11; 11; 10; 9; 8; 7; 6; 5; 4; 4; 4; 3; 3; 2; 2]); (874, [10; 10; 9; 8; 7; 6; 5; 5; 5; 5; 5; 4; 3; 3; 1]); (4370, [11; 11; 10; 9; 8; 7; 6; 5; 5; 5; 5; 5; 4; 2; 1]); (2622, [10; 10; 9; 8; 7; 6; 6; 6; 6; 6; 5; 4; 4; 2; 1]); (6992, [11; 11; 10; 9; 8; 7; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (10488, [11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (20102, [11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 1]); (30590, [11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 4; 4; 2; 1]); (50692, [11; 11; 11; 11; 9; 8; 7; 6; 5; 5; 5; 4; 4; 2; 1])]));
  ([9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [13; 13; 8; 8; 8; 8; 8; 8; 13; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 5; 3; 0; 0], 1, [(1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 1])]));
  ([9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [13; 13; 21; 21; 8; 8; 8; 8; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 5; 3; 0; 0], 1, [(1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 1]); (6, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 2; 1])]));
  ([10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [66; 66; 21; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 32; 24; 16; 8; 0; 0; 2; 5; 3; 0; 0], 1, [(1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 1]); (6, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 2; 1]); (40, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1])]));
  ([9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 4; 4; 2; 1], (10, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [26; 26; 37; 37; 37; 37; 16; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 5; 0; 4; 10; 6; 0; 0], 2, [(2, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (2, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 1]); (7, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 2; 1])]));
  ([10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [45; 45; 13; 13; 24; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 8; 0; 8; 0; 2; 5; 3; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (9, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1]); (16, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 4; 4; 2; 1])]));
  ([10; 10; 10; 10; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [41; 41; 41; 41; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 4; 8; 0; 8; 0; 2; 5; 3; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (9, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1]); (12, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 4; 4; 2; 1])]));
  ([11; 11; 10; 9; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [82; 82; 53; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 16; 8; 0; 8; 0; 2; 5; 3; 0; 0], 1, [(1, [9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 7; 7; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (11, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1]); (24, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (11, [10; 10; 10; 10; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 1])]));
  ([10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [32; 32; 32; 32; 13; 13; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 11; 8; 0; 2; 5; 3; 0; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (12, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 4; 4; 2; 1])]));
  ([11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [90; 90; 32; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 26; 13; 0; 11; 8; 0; 2; 5; 3; 0; 0], 1, [(1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 3; 3; 1]); (14, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (37, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 4; 4; 2; 1])]));
  ([11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [45; 45; 32; 32; 40; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 11; 8; 0; 2; 5; 3; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (12, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (8, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 4; 4; 2; 1])]));
  ([11; 11; 11; 11; 9; 8; 7; 7; 7; 5; 4; 4; 4; 2; 1], (1, [0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0], [3658; 3658; 6324; 6324; 186; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 1426; 806; 0; 0; 310; 186; 0; 0], 62, [(62, [10; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 3; 3; 2; 2]); (62, [9; 9; 9; 9; 7; 6; 6; 6; 5; 5; 4; 4; 3; 3; 1]); (434, [10; 10; 9; 9; 9; 7; 6; 6; 6; 5; 5; 4; 4; 2; 1]); (124, [10; 10; 9; 9; 9; 7; 7; 7; 6; 6; 4; 4; 4; 2; 1]); (2046, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (806, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 4; 4; 2; 1])]));
  ([12; 12; 11; 10; 9; 8; 7; 7; 7; 5; 4; 4; 4; 2; 1], (17, [0; 0; 0; 0; 0; 0; 0; 0; 0; 17; 17; 0; 0; 0; 0], [69192; 69192; 41850; 0; 0; 0; 0; 0; 5580; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2232; 1116; 0; 0], 558, [(558, [11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 3; 3; 3; 2; 2]); (558, [10; 10; 9; 8; 7; 6; 5; 5; 5; 4; 4; 4; 4; 3; 1]); (3348, [11; 11; 10; 9; 8; 7; 6; 6; 6; 5; 5; 4; 4; 2; 1]); (1674, [10; 10; 9; 8; 7; 7; 7; 7; 7; 6; 4; 4; 4; 2; 1]); (5580, [10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1]); (7254, [11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 4; 4; 2; 1]); (14508, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 4; 4; 2; 1]); (27342, [11; 11; 11; 11; 9; 8; 7; 7; 7; 5; 4; 4; 4; 2; 1])]));
  ([9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [13; 13; 13; 13; 16; 16; 16; 16; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 5; 3; 0; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1])]));
  ([10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [29; 29; 13; 13; 16; 16; 16; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 5; 3; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 3; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1]); (7, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 4; 4; 2; 1])]));
  ([10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [29; 29; 29; 29; 16; 16; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 5; 3; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1]); (8, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 4; 4; 2; 1])]));
  ([11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [90; 90; 37; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 32; 16; 0; 8; 0; 0; 2; 5; 3; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1]); (16, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 2; 1]); (45, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1])]));
  ([11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [53; 53; 21; 21; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 16; 8; 0; 0; 2; 5; 3; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1]); (24, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1])]));
  ([11; 11; 11; 11; 9; 8; 8; 8; 6; 5; 4; 4; 4; 2; 1], (1, [0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0], [6696; 6696; 7719; 7719; 1116; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 3348; 2139; 0; 0; 0; 465; 279; 0; 0], 93, [(93, [10; 10; 9; 9; 9; 7; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (93, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (651, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (279, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 4; 4; 2; 1]); (930, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (3534, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1])]));
  ([12; 12; 11; 10; 9; 8; 8; 8; 6; 5; 4; 4; 4; 2; 1], (61, [0; 0; 0; 0; 0; 0; 0; 0; 0; 61; 61; 0; 0; 0; 0], [78678; 78678; 45756; 0; 0; 0; 0; 7254; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 7254; 0; 0; 0; 0; 2232; 1116; 0; 0], 558, [(558, [11; 11; 10; 9; 8; 7; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (558, [10; 10; 9; 8; 7; 6; 6; 6; 4; 4; 4; 4; 4; 3; 1]); (3348, [11; 11; 10; 9; 8; 7; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (1674, [11; 11; 10; 9; 8; 7; 7; 7; 6; 6; 4; 4; 4; 2; 1]); (5580, [10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1]); (14508, [11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1]); (12834, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 4; 4; 2; 1]); (32922, [11; 11; 11; 11; 9; 8; 8; 8; 6; 5; 4; 4; 4; 2; 1])]));
  ([10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [21; 21; 24; 24; 24; 24; 16; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 5; 3; 0; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (3, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 2; 1])]));
  ([11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 4; 4; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [61; 61; 24; 24; 24; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 16; 0; 0; 0; 2; 5; 3; 0; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (3, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 2; 1]); (29, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 4; 4; 2; 1])]));
  ([11; 11; 11; 11; 9; 9; 9; 7; 6; 5; 4; 4; 4; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [63; 63; 70; 70; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 10; 20; 0; 0; 0; 0; 5; 3; 0; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 3; 3; 1]); (4, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (6, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (7, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 2; 1]); (18, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 4; 4; 2; 1])]));
  ([12; 12; 11; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 2; 1], (1, [0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 0; 0; 0; 0], [3348; 3348; 2232; 0; 0; 713; 713; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 124; 62; 0; 0], 31, [(31, [11; 11; 10; 9; 8; 8; 8; 6; 5; 4; 3; 3; 3; 2; 2]); (31, [10; 10; 9; 8; 7; 7; 7; 5; 4; 4; 4; 4; 4; 3; 1]); (186, [11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (93, [11; 11; 10; 9; 8; 8; 8; 6; 6; 6; 4; 4; 4; 2; 1]); (310, [11; 11; 10; 9; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (403, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 2; 1]); (713, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 4; 4; 2; 1]); (1116, [11; 11; 11; 11; 9; 9; 9; 7; 6; 5; 4; 4; 4; 2; 1])]));
  ([11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 4; 4; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [50; 50; 50; 50; 30; 30; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 5; 3; 0; 0], 1, [(1, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (4, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (6, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (6, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1]); (6, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 4; 4; 2; 1])]));
  ([12; 12; 11; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 2; 1], (14, [0; 0; 0; 0; 0; 0; 0; 0; 0; 14; 14; 0; 0; 0; 0], [26505; 26505; 16461; 0; 10044; 16461; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1116; 558; 0; 0], 279, [(279, [10; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 3; 3; 2; 2]); (279, [10; 10; 9; 8; 8; 8; 6; 5; 4; 4; 4; 4; 4; 3; 1]); (1674, [11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 1]); (558, [11; 11; 10; 9; 9; 9; 7; 6; 6; 6; 4; 4; 4; 2; 1]); (2790, [11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 4; 4; 2; 1]); (3627, [11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1]); (6417, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 4; 4; 2; 1]); (10044, [11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 4; 4; 2; 1])]));
  ([12; 12; 11; 11; 11; 9; 8; 7; 6; 5; 4; 4; 4; 2; 1], (29, [0; 0; 0; 0; 0; 0; 0; 0; 0; 29; 29; 0; 0; 0; 0], [17670; 17670; 10974; 10974; 17670; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 744; 372; 0; 0], 186, [(186, [11; 11; 10; 10; 10; 8; 7; 6; 5; 4; 3; 3; 3; 2; 2]); (186, [10; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 4; 4; 3; 1]); (1116, [11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 4; 4; 2; 1]); (558, [11; 11; 10; 10; 10; 8; 7; 6; 6; 6; 4; 4; 4; 2; 1]); (1860, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 4; 4; 2; 1]); (2418, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 4; 4; 2; 1]); (4278, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 4; 4; 2; 1]); (6696, [11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 4; 4; 2; 1])]));
  ([12; 12; 12; 12; 10; 9; 8; 7; 6; 5; 4; 4; 4; 2; 1], (32, [0; 0; 0; 0; 0; 0; 0; 0; 0; 32; 32; 0; 0; 0; 0], [19809; 19809; 29853; 29853; 0; 279; 6417; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1395; 837; 0; 0], 279, [(279, [10; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 3; 3; 2; 2]); (279, [10; 10; 10; 10; 9; 9; 7; 6; 5; 4; 4; 4; 3; 3; 1]); (1953, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 1]); (837, [10; 10; 10; 10; 9; 9; 7; 6; 6; 6; 4; 4; 4; 2; 1]); (2790, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 4; 4; 2; 1]); (3627, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1]); (10044, [12; 12; 11; 11; 11; 9; 8; 7; 6; 5; 4; 4; 4; 2; 1])]));
  ([9; 9; 9; 9; 8; 8; 6; 6; 6; 6; 6; 5; 3; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [32; 32; 32; 32; 19; 19; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 7; 10; 13; 16; 6; 0; 0; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 3; 3; 1]); (4, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1])]));
  ([10; 10; 9; 8; 8; 8; 6; 6; 6; 6; 6; 5; 3; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [102; 102; 32; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 38; 19; 0; 7; 10; 13; 16; 6; 0; 0; 0], 2, [(2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 3; 3; 1]); (4, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1]); (49, [9; 9; 9; 9; 8; 8; 6; 6; 6; 6; 6; 5; 3; 2; 1])]));
  ([10; 10; 9; 9; 9; 7; 6; 6; 6; 6; 6; 5; 3; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [51; 51; 32; 32; 38; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 7; 10; 13; 16; 6; 0; 0; 0], 2, [(2, [9; 9; 8; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 3; 3; 1]); (4, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1])]));
  ([10; 10; 10; 10; 8; 7; 6; 6; 6; 6; 6; 5; 3; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [51; 51; 70; 70; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 7; 10; 13; 16; 6; 0; 0; 0], 2, [(2, [9; 9; 8; 8; 8; 6; 5; 4; 4; 4; 4; 4; 3; 2; 2]); (2, [8; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 3; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1]); (2, [9; 9; 9; 9; 8; 8; 6; 6; 6; 6; 6; 5; 3; 2; 1]); (17, [10; 10; 9; 9; 9; 7; 6; 6; 6; 6; 6; 5; 3; 2; 1])]));
  ([11; 11; 10; 9; 8; 7; 6; 6; 6; 6; 6; 5; 3; 2; 1], (21, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [307; 307; 180; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 9; 18; 19; 20; 0; 0; 0; 0], 4, [(4, [9; 9; 9; 9; 7; 6; 5; 5; 5; 5; 5; 4; 2; 2; 2]); (4, [9; 9; 9; 9; 7; 6; 5; 5; 5; 5; 5; 4; 3; 3; 1]); (8, [9; 9; 8; 8; 8; 6; 6; 6; 5; 5; 5; 5; 4; 2; 1]); (12, [9; 9; 9; 9; 7; 6; 6; 6; 6; 6; 6; 6; 3; 2; 1]); (32, [9; 9; 9; 9; 8; 8; 6; 6; 6; 6; 6; 5; 3; 2; 1]); (45, [10; 10; 9; 9; 9; 7; 6; 6; 6; 6; 6; 5; 3; 2; 1]); (54, [10; 10; 10; 10; 8; 7; 6; 6; 6; 6; 6; 5; 3; 2; 1])]));
  ([8; 8; 8; 8; 8; 8; 8; 8; 6; 6; 5; 5; 3; 2; 1], (29, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 19; 0; 15; 0; 0; 0], 3, [(1, [7; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 2; 2]); (2, [8; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 3; 3; 2; 2]); (3, [8; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 3; 3; 1]); (3, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 4; 4; 2; 1]); (30, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 5; 5; 3; 2; 1])]));
  ([9; 9; 8; 8; 8; 8; 8; 7; 6; 6; 5; 5; 3; 2; 1], (8, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [13; 13; 4; 0; 2; 2; 5; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 2; 0; 0; 0; 0; 0; 3; 0; 5; 0; 0; 0], 1, [(1, [9; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 1]); (2, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (4, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 1])]));
  ([9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 5; 5; 3; 2; 1], (7, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [14; 14; 14; 14; 7; 7; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 2; 1; 5; 0; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 3; 3; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (2, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1])]));
  ([10; 10; 9; 8; 8; 8; 7; 7; 6; 6; 5; 5; 3; 2; 1], (7, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [42; 42; 14; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 14; 7; 0; 0; 0; 2; 0; 4; 0; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 6; 6; 5; 5; 4; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 6; 6; 5; 5; 5; 5; 4; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (14, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 5; 5; 3; 2; 1]); (3, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1])]));
  ([9; 9; 9; 9; 9; 9; 8; 6; 6; 6; 5; 5; 3; 2; 1], (21, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [62; 62; 62; 62; 62; 62; 41; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 1; 2; 3; 12; 0; 0; 0], 4, [(4, [7; 7; 7; 7; 7; 7; 6; 4; 4; 4; 4; 4; 3; 2; 2]); (4, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (4, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 5; 5; 4; 2; 1])]));
  ([10; 10; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 3; 2; 1], (21, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [165; 165; 62; 62; 62; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 41; 0; 1; 2; 3; 12; 0; 0; 0], 4, [(4, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (4, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (8, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (66, [9; 9; 9; 9; 9; 9; 8; 6; 6; 6; 5; 5; 3; 2; 1])]));
  ([10; 10; 10; 10; 8; 8; 8; 6; 6; 6; 5; 5; 3; 2; 1], (42, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [289; 289; 289; 289; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 41; 82; 0; 2; 4; 6; 24; 0; 0; 0], 8, [(8, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (8, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (16, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (91, [9; 9; 9; 9; 9; 9; 8; 6; 6; 6; 5; 5; 3; 2; 1])]));
  ([11; 11; 10; 9; 8; 8; 8; 6; 6; 6; 5; 5; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [75; 75; 54; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 22; 11; 0; 0; 0; 0; 3; 0; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (2, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (1, [9; 9; 8; 8; 8; 7; 7; 6; 6; 6; 6; 5; 3; 2; 1]); (28, [10; 10; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 3; 2; 1]); (16, [10; 10; 10; 10; 8; 8; 8; 6; 6; 6; 5; 5; 3; 2; 1])]));
  ([10; 10; 10; 10; 9; 9; 7; 6; 6; 6; 5; 5; 3; 2; 1], (21, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [103; 103; 103; 103; 62; 62; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 1; 2; 3; 12; 0; 0; 0], 4, [(4, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (4, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (8, [8; 8; 8; 8; 8; 8; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (4, [9; 9; 9; 9; 9; 9; 8; 6; 6; 6; 5; 5; 3; 2; 1])]));
  ([11; 11; 10; 9; 9; 9; 7; 6; 6; 6; 5; 5; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [86; 86; 27; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 32; 16; 0; 0; 0; 0; 0; 3; 0; 0; 0], 1, [(1, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 3; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 6; 6; 5; 3; 2; 1]); (6, [9; 9; 9; 9; 9; 9; 8; 6; 6; 6; 5; 5; 3; 2; 1]); (43, [10; 10; 10; 10; 9; 9; 7; 6; 6; 6; 5; 5; 3; 2; 1])]));
  ([11; 11; 10; 10; 10; 8; 7; 6; 6; 6; 5; 5; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [43; 43; 27; 27; 38; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 3; 0; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 4; 4; 3; 3; 1]); (2, [9; 9; 8; 8; 8; 7; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 6; 6; 6; 6; 6; 5; 3; 2; 1]); (2, [10; 10; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 3; 2; 1]); (10, [10; 10; 10; 10; 9; 9; 7; 6; 6; 6; 5; 5; 3; 2; 1])]));
  ([11; 11; 11; 11; 9; 8; 7; 6; 6; 6; 5; 5; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 4; 4; 4; 4; 0; 0; 0; 0], [37485; 37485; 58310; 58310; 1190; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 5950; 2975; 0; 1785; 0; 0; 0], 595, [(595, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 2; 2]); (595, [9; 9; 9; 9; 8; 8; 6; 5; 5; 5; 4; 4; 3; 3; 1]); (1190, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 5; 5; 4; 2; 1]); (3570, [10; 10; 9; 9; 9; 7; 6; 6; 6; 6; 6; 5; 3; 2; 1]); (8925, [10; 10; 9; 9; 9; 7; 7; 7; 6; 6; 5; 5; 3; 2; 1]); (6545, [10; 10; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 3; 2; 1]); (14875, [10; 10; 10; 10; 9; 9; 7; 6; 6; 6; 5; 5; 3; 2; 1])]));
  ([12; 12; 11; 10; 9; 8; 7; 6; 6; 6; 5; 5; 3; 2; 1], (7, [0; 0; 0; 0; 0; 0; 0; 7; 7; 7; 7; 0; 0; 0; 0], [23460; 23460; 14620; 0; 0; 0; 0; 0; 0; 510; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 850; 0; 0; 0], 170, [(170, [11; 11; 10; 9; 8; 7; 6; 5; 5; 5; 4; 4; 2; 2; 2]); (170, [11; 11; 10; 9; 8; 7; 6; 5; 5; 5; 4; 4; 3; 3; 1]); (340, [10; 10; 9; 8; 7; 6; 6; 6; 6; 6; 5; 4; 4; 2; 1]); (1360, [11; 11; 10; 9; 8; 7; 6; 6; 6; 6; 6; 5; 3; 2; 1]); (510, [10; 10; 9; 8; 7; 7; 7; 7; 7; 6; 5; 5; 3; 2; 1]); (2210, [11; 11; 10; 9; 8; 8; 8; 6; 6; 6; 5; 5; 3; 2; 1]); (3060, [11; 11; 10; 9; 9; 9; 7; 6; 6; 6; 5; 5; 3; 2; 1]); (5780, [11; 11; 10; 10; 10; 8; 7; 6; 6; 6; 5; 5; 3; 2; 1]); (8840, [11; 11; 11; 11; 9; 8; 7; 6; 6; 6; 5; 5; 3; 2; 1])]));
  ([9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 5; 5; 3; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [35; 35; 22; 22; 22; 22; 22; 22; 22; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 17; 15; 0; 0; 0], 3, [(3, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (3, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 1]); (3, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 2; 1])]));
  ([9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 5; 5; 3; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [35; 35; 44; 44; 22; 22; 22; 22; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 17; 15; 0; 0; 0], 3, [(3, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (3, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 1]); (3, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 2; 1])]));
  ([10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 5; 5; 3; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [167; 167; 44; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 88; 66; 44; 22; 0; 0; 17; 15; 0; 0; 0], 3, [(3, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 2; 2; 2]); (3, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 1]); (3, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 2; 1]); (3, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1]); (107, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 5; 5; 3; 2; 1])]));
  ([9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 5; 5; 3; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [35; 35; 44; 44; 44; 44; 22; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 17; 15; 0; 0; 0], 3, [(3, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (3, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 1]); (3, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 2; 1])]));
  ([10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [110; 110; 35; 35; 53; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 22; 0; 9; 0; 17; 15; 0; 0; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (6, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1]); (6, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 5; 5; 3; 2; 1]); (44, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 5; 5; 3; 2; 1])]));
  ([10; 10; 10; 10; 8; 8; 8; 7; 7; 5; 5; 5; 3; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [99; 99; 99; 99; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 11; 22; 0; 9; 0; 17; 15; 0; 0; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (6, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (12, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 5; 5; 3; 2; 1]); (27, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 10; 9; 8; 8; 8; 7; 7; 5; 5; 5; 3; 2; 1], (11, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [234; 234; 156; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 52; 26; 0; 15; 0; 13; 15; 0; 0; 0], 3, [(3, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 2; 2]); (3, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 3; 3; 1]); (6, [9; 9; 8; 8; 8; 7; 7; 6; 6; 5; 5; 4; 4; 2; 1]); (24, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 5; 5; 3; 2; 1]); (72, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 2; 1]); (37, [10; 10; 10; 10; 8; 8; 8; 7; 7; 5; 5; 5; 3; 2; 1])]));
  ([10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 5; 5; 3; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [75; 75; 75; 75; 35; 35; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 18; 9; 0; 17; 15; 0; 0; 0], 3, [(3, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 2; 2; 2]); (3, [8; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (6, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (15, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 5; 5; 3; 2; 1], (11, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [260; 260; 93; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 74; 37; 0; 30; 15; 0; 13; 15; 0; 0; 0], 3, [(3, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 2; 2; 2]); (3, [9; 9; 9; 9; 8; 8; 6; 6; 6; 4; 4; 4; 3; 3; 1]); (6, [8; 8; 8; 8; 8; 8; 7; 6; 6; 5; 5; 4; 4; 2; 1]); (39, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 5; 5; 3; 2; 1]); (105, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 5; 5; 3; 2; 1], (11, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [130; 130; 93; 93; 119; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 30; 15; 0; 13; 15; 0; 0; 0], 3, [(3, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 2; 2; 2]); (3, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (6, [9; 9; 9; 9; 8; 8; 6; 6; 6; 5; 5; 4; 4; 2; 1]); (39, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 2; 1]); (20, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 11; 11; 9; 8; 7; 7; 7; 5; 5; 5; 3; 2; 1], (11, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [130; 130; 212; 212; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 30; 15; 0; 13; 15; 0; 0; 0], 3, [(3, [8; 8; 7; 7; 7; 6; 6; 5; 5; 4; 4; 3; 3; 2; 2]); (3, [9; 9; 8; 8; 8; 7; 7; 6; 6; 4; 4; 4; 3; 3; 1]); (3, [9; 9; 8; 8; 8; 7; 7; 6; 6; 5; 5; 4; 4; 2; 1]); (36, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 2; 1]); (26, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 5; 5; 3; 2; 1]); (37, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 5; 5; 3; 2; 1])]));
  ([12; 12; 11; 10; 9; 8; 7; 7; 7; 5; 5; 5; 3; 2; 1], (25, [0; 0; 0; 0; 0; 0; 0; 0; 0; 25; 25; 0; 0; 0; 0], [38502; 38502; 23715; 0; 0; 0; 0; 0; 1395; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 2232; 1395; 0; 0; 0], 279, [(279, [11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 4; 4; 2; 2; 2]); (279, [11; 11; 10; 9; 8; 7; 6; 6; 6; 4; 4; 4; 3; 3; 1]); (558, [11; 11; 10; 9; 8; 7; 6; 6; 6; 5; 5; 4; 4; 2; 1]); (3069, [10; 10; 9; 8; 7; 7; 7; 7; 7; 6; 5; 5; 3; 2; 1]); (1395, [10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 5; 5; 3; 2; 1]); (4464, [11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 5; 5; 3; 2; 1]); (8928, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 5; 5; 3; 2; 1]); (14787, [11; 11; 11; 11; 9; 8; 7; 7; 7; 5; 5; 5; 3; 2; 1])]));
  ([9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 5; 5; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [12; 12; 12; 12; 12; 12; 12; 12; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 5; 5; 0; 0; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 3; 3; 1]); (1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 5; 5; 4; 4; 2; 1])]));
  ([10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [24; 24; 12; 12; 12; 12; 12; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 5; 5; 0; 0; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 2; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 3; 3; 1]); (1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 5; 5; 4; 4; 2; 1]); (1, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 4; 4; 2; 1]); (4, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 5; 5; 3; 2; 1])]));
  ([10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [24; 24; 24; 24; 12; 12; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 5; 5; 0; 0; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 2; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 3; 3; 1]); (1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 5; 5; 4; 4; 2; 1]); (1, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 4; 4; 2; 1]); (4, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1], (11, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [238; 238; 104; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 82; 41; 0; 26; 0; 0; 13; 15; 0; 0; 0], 3, [(3, [9; 9; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 2; 2]); (3, [9; 9; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 1]); (6, [9; 9; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 1]); (4, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 5; 5; 3; 2; 1]); (40, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 1]); (119, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1], (11, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [145; 145; 52; 52; 134; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 52; 26; 0; 0; 13; 15; 0; 0; 0], 3, [(3, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (3, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (4, [8; 8; 8; 8; 7; 7; 7; 7; 6; 5; 5; 4; 4; 2; 1]); (2, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (70, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 11; 11; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 3; 3; 3; 0; 0; 0; 0], [32338; 32338; 34523; 34523; 6992; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 16169; 9177; 0; 0; 3496; 2185; 0; 0; 0], 437, [(437, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (437, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (874, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (4807, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 5; 5; 3; 2; 1]); (2185, [10; 10; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 2; 1]); (16606, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1])]));
  ([12; 12; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1], (53, [0; 0; 0; 0; 0; 0; 0; 0; 53; 53; 53; 0; 0; 0; 0], [119738; 119738; 69046; 0; 0; 0; 0; 13984; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 13984; 0; 0; 0; 5244; 2622; 0; 0; 0], 874, [(874, [11; 11; 10; 9; 8; 7; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (874, [11; 11; 10; 9; 8; 7; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (1748, [10; 10; 9; 8; 7; 6; 6; 6; 5; 5; 5; 5; 4; 2; 1]); (7866, [11; 11; 10; 9; 8; 7; 7; 7; 6; 6; 5; 5; 3; 2; 1]); (4370, [10; 10; 9; 8; 8; 8; 8; 8; 7; 5; 5; 5; 3; 2; 1]); (27968, [11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (18354, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (50692, [11; 11; 11; 11; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1])]));
  ([10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 5; 5; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [16; 16; 20; 20; 20; 20; 12; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 5; 5; 0; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 2; 2]); (1, [9; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 3; 3; 1]); (1, [9; 9; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 1]); (1, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 2; 1]); (1, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1], (11, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [160; 160; 67; 67; 67; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 41; 0; 0; 0; 13; 15; 0; 0; 0], 3, [(3, [9; 9; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 2; 2]); (3, [9; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 3; 3; 1]); (6, [9; 9; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 1]); (4, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 5; 5; 3; 2; 1]); (6, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 1]); (75, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 11; 11; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1], (22, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [279; 279; 309; 309; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 41; 82; 0; 0; 0; 26; 30; 0; 0; 0], 6, [(6, [7; 7; 7; 7; 7; 7; 6; 5; 5; 4; 4; 3; 3; 2; 2]); (6, [9; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 3; 3; 1]); (6, [9; 9; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 1]); (2, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 5; 5; 3; 2; 1]); (24, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 1]); (109, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 5; 5; 3; 2; 1])]));
  ([12; 12; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1], (11, [0; 0; 0; 0; 0; 0; 0; 0; 11; 11; 11; 0; 0; 0; 0], [48507; 48507; 32338; 0; 0; 9177; 9177; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 2622; 1311; 0; 0; 0], 437, [(437, [11; 11; 10; 9; 8; 8; 8; 6; 5; 4; 4; 4; 2; 2; 2]); (437, [11; 11; 10; 9; 8; 8; 8; 6; 5; 4; 4; 4; 3; 3; 1]); (874, [10; 10; 9; 8; 7; 7; 7; 5; 5; 5; 5; 5; 4; 2; 1]); (3933, [11; 11; 10; 9; 8; 8; 8; 6; 6; 6; 5; 5; 3; 2; 1]); (2185, [11; 11; 10; 9; 8; 8; 8; 7; 7; 5; 5; 5; 3; 2; 1]); (6992, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 1]); (9177, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1]); (16169, [11; 11; 11; 11; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1])]));
  ([11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 1], (11, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [108; 108; 108; 108; 67; 67; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 13; 15; 0; 0; 0], 3, [(3, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 2; 2; 2]); (3, [9; 9; 9; 9; 8; 8; 7; 7; 5; 4; 4; 4; 3; 3; 1]); (6, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (4, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 5; 5; 3; 2; 1]); (3, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (26, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 5; 5; 3; 2; 1])]));
  ([12; 12; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 1], (27, [0; 0; 0; 0; 0; 0; 0; 0; 27; 27; 27; 0; 0; 0; 0], [83030; 83030; 50692; 0; 32338; 50692; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 5244; 2622; 0; 0; 0], 874, [(874, [11; 11; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 2; 2; 2]); (874, [11; 11; 10; 9; 9; 9; 7; 6; 5; 4; 4; 4; 3; 3; 1]); (1748, [10; 10; 9; 8; 8; 8; 6; 5; 5; 5; 5; 5; 4; 2; 1]); (7866, [11; 11; 10; 9; 9; 9; 7; 6; 6; 6; 5; 5; 3; 2; 1]); (4370, [11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 5; 5; 3; 2; 1]); (13984, [11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (18354, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1]); (32338, [11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 1])]));
  ([12; 12; 11; 11; 11; 9; 8; 7; 6; 5; 5; 5; 3; 2; 1], (85, [0; 0; 0; 0; 0; 0; 0; 0; 85; 85; 85; 0; 0; 0; 0], [83030; 83030; 50692; 50692; 83030; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 5244; 2622; 0; 0; 0], 874, [(874, [11; 11; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 2; 2; 2]); (874, [11; 11; 10; 10; 10; 8; 7; 6; 5; 4; 4; 4; 3; 3; 1]); (1748, [10; 10; 9; 9; 9; 7; 6; 5; 5; 5; 5; 5; 4; 2; 1]); (7866, [11; 11; 10; 10; 10; 8; 7; 6; 6; 6; 5; 5; 3; 2; 1]); (4370, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 5; 5; 3; 2; 1]); (13984, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (18354, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1]); (32338, [11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 1])]));
  ([12; 12; 12; 12; 10; 9; 8; 7; 6; 5; 5; 5; 3; 2; 1], (68, [0; 0; 0; 0; 0; 0; 0; 0; 68; 68; 68; 0; 0; 0; 0], [40641; 40641; 57684; 58558; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 2622; 1311; 0; 0; 0], 437, [(437, [10; 10; 10; 10; 9; 9; 7; 6; 5; 4; 4; 4; 2; 2; 2]); (437, [10; 10; 10; 10; 9; 9; 7; 6; 5; 4; 4; 4; 3; 3; 1]); (874, [10; 10; 9; 8; 7; 6; 6; 6; 5; 5; 5; 5; 4; 2; 1]); (3933, [10; 10; 10; 10; 9; 9; 7; 6; 6; 6; 5; 5; 3; 2; 1]); (2185, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 5; 5; 3; 2; 1]); (6118, [11; 11; 11; 11; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (9177, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 5; 5; 3; 2; 1]); (16169, [12; 12; 11; 11; 11; 9; 8; 7; 6; 5; 5; 5; 3; 2; 1])]));
  ([9; 9; 8; 8; 8; 8; 8; 8; 8; 6; 6; 4; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [14; 14; 8; 8; 8; 8; 8; 8; 9; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 3; 0; 2; 0; 0], 1, [(1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 5; 5; 3; 2; 2; 2]); (1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 5; 5; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 8; 8; 8; 8; 7; 7; 6; 4; 3; 2; 1])]));
  ([9; 9; 9; 9; 9; 9; 9; 9; 6; 6; 6; 4; 3; 2; 1], (24, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [64; 64; 64; 64; 64; 64; 64; 64; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 8; 16; 0; 9; 0; 0], 5, [(1, [7; 7; 7; 7; 7; 7; 7; 7; 4; 4; 4; 3; 3; 2; 2]); (4, [8; 8; 8; 8; 8; 8; 8; 8; 5; 5; 5; 3; 2; 2; 2]); (5, [8; 8; 8; 8; 8; 8; 8; 8; 5; 5; 5; 3; 3; 3; 1])]));
  ([10; 10; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 3; 2; 1], (24, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [128; 128; 64; 64; 64; 64; 64; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 8; 16; 0; 9; 0; 0], 5, [(5, [8; 8; 8; 8; 8; 8; 8; 8; 5; 5; 5; 3; 2; 2; 2]); (5, [8; 8; 8; 8; 8; 8; 8; 8; 5; 5; 5; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 5; 5; 4; 4; 2; 1]); (29, [9; 9; 9; 9; 9; 9; 9; 9; 6; 6; 6; 4; 3; 2; 1])]));
  ([10; 10; 10; 10; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1], (24, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [128; 128; 128; 128; 64; 64; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 8; 16; 0; 9; 0; 0], 5, [(5, [8; 8; 8; 8; 8; 8; 8; 8; 5; 5; 5; 3; 2; 2; 2]); (5, [8; 8; 8; 8; 8; 8; 8; 8; 5; 5; 5; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 5; 5; 4; 4; 2; 1]); (29, [9; 9; 9; 9; 9; 9; 9; 9; 6; 6; 6; 4; 3; 2; 1])]));
  ([11; 11; 10; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [102; 102; 39; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 40; 20; 0; 8; 0; 7; 5; 0; 0; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 8; 8; 7; 5; 5; 5; 3; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 8; 8; 7; 5; 5; 5; 3; 3; 3; 1]); (2, [9; 9; 8; 8; 8; 8; 8; 7; 5; 5; 5; 4; 4; 2; 1]); (9, [9; 9; 9; 9; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 1]); (12, [10; 10; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 3; 2; 1]); (51, [10; 10; 10; 10; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1])]));
  ([11; 11; 10; 10; 10; 8; 8; 8; 6; 6; 6; 4; 3; 2; 1], (24, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [232; 232; 88; 88; 208; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 80; 40; 0; 8; 16; 0; 9; 0; 0], 5, [(5, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 2; 2; 2]); (5, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (109, [10; 10; 10; 10; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1])]));
  ([11; 11; 11; 11; 9; 8; 8; 8; 6; 6; 6; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 4; 4; 0; 4; 0; 0; 0], [29716; 29716; 41078; 41078; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 14858; 11362; 0; 5681; 3496; 0; 0; 0; 0], 437, [(437, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 2; 2; 2]); (437, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 1]); (874, [10; 10; 9; 9; 9; 7; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (1311, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 5; 5; 3; 2; 1]); (7866, [10; 10; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 3; 2; 1]); (16169, [10; 10; 10; 10; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1]); (2622, [11; 11; 10; 10; 10; 8; 8; 8; 6; 6; 6; 4; 3; 2; 1])]));
  ([12; 12; 11; 10; 9; 8; 8; 8; 6; 6; 6; 4; 3; 2; 1], (1, [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 0], [2990; 2990; 1794; 0; 0; 0; 184; 184; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 299; 184; 0; 0; 0; 0], 23, [(23, [11; 11; 10; 9; 8; 7; 7; 7; 5; 5; 5; 3; 2; 2; 2]); (23, [11; 11; 10; 9; 8; 7; 7; 7; 5; 5; 5; 3; 3; 3; 1]); (46, [11; 11; 10; 9; 8; 7; 7; 7; 5; 5; 5; 4; 4; 2; 1]); (69, [11; 11; 10; 9; 8; 7; 7; 7; 6; 6; 5; 5; 3; 2; 1]); (414, [10; 10; 9; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 1]); (184, [11; 11; 10; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1]); (598, [11; 11; 10; 10; 10; 8; 8; 8; 6; 6; 6; 4; 3; 2; 1]); (1196, [11; 11; 11; 11; 9; 8; 8; 8; 6; 6; 6; 4; 3; 2; 1])]));
  ([10; 10; 10; 10; 10; 10; 9; 7; 6; 6; 6; 4; 3; 2; 1], (24, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [88; 88; 104; 104; 104; 104; 64; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 8; 16; 0; 9; 0; 0], 5, [(1, [8; 8; 8; 8; 8; 8; 7; 5; 4; 4; 4; 3; 3; 2; 2]); (4, [9; 9; 8; 8; 8; 8; 8; 7; 5; 5; 5; 3; 2; 2; 2]); (5, [9; 9; 8; 8; 8; 8; 8; 7; 5; 5; 5; 3; 3; 3; 1]); (7, [10; 10; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 3; 2; 1])]));
  ([11; 11; 10; 10; 10; 9; 9; 7; 6; 6; 6; 4; 3; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [71; 71; 28; 28; 28; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 20; 0; 0; 7; 5; 0; 0; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 8; 8; 7; 5; 5; 5; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 3; 3; 1]); (2, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (9, [9; 9; 9; 9; 9; 9; 8; 7; 7; 6; 6; 4; 3; 2; 1]); (4, [10; 10; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 3; 2; 1]); (28, [10; 10; 10; 10; 10; 10; 9; 7; 6; 6; 6; 4; 3; 2; 1])]));
  ([11; 11; 11; 11; 9; 9; 9; 7; 6; 6; 6; 4; 3; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [61; 61; 66; 66; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 10; 20; 0; 0; 7; 5; 0; 0; 0; 0], 1, [(1, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 3; 3; 1]); (2, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (9, [9; 9; 9; 9; 9; 9; 8; 7; 7; 6; 6; 4; 3; 2; 1]); (5, [10; 10; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 3; 2; 1]); (17, [10; 10; 10; 10; 10; 10; 9; 7; 6; 6; 6; 4; 3; 2; 1])]));
  ([12; 12; 11; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 2; 1], (17, [0; 0; 0; 0; 0; 0; 0; 0; 17; 17; 0; 17; 0; 0; 0], [55936; 55936; 29716; 0; 0; 0; 11362; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 4370; 2185; 0; 0; 0; 0], 437, [(437, [11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 2; 2; 2]); (437, [11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 3; 3; 3; 1]); (874, [11; 11; 10; 9; 8; 8; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (1311, [10; 10; 9; 8; 7; 7; 7; 6; 6; 6; 6; 5; 3; 2; 1]); (6555, [11; 11; 10; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 2; 1]); (3496, [10; 10; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 3; 2; 1]); (11362, [10; 10; 10; 10; 10; 10; 9; 7; 6; 6; 6; 4; 3; 2; 1]); (14858, [11; 11; 11; 11; 9; 9; 9; 7; 6; 6; 6; 4; 3; 2; 1])]));
  ([11; 11; 11; 11; 10; 10; 8; 7; 6; 6; 6; 4; 3; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [48; 48; 48; 48; 28; 28; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 7; 5; 0; 0; 0; 0], 1, [(1, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 7; 7; 5; 5; 5; 3; 3; 3; 1]); (2, [9; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 4; 4; 2; 1]); (9, [9; 9; 9; 9; 9; 9; 8; 7; 7; 6; 6; 4; 3; 2; 1]); (3, [10; 10; 10; 10; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1]); (6, [10; 10; 10; 10; 10; 10; 9; 7; 6; 6; 6; 4; 3; 2; 1])]));
  ([12; 12; 11; 10; 10; 10; 8; 7; 6; 6; 6; 4; 3; 2; 1], (13, [0; 0; 0; 0; 0; 0; 0; 0; 13; 13; 0; 13; 0; 0; 0], [41078; 41078; 26220; 0; 14858; 26220; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 4370; 2185; 0; 0; 0; 0], 437, [(437, [11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 2; 2; 2]); (437, [11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 3; 3; 3; 1]); (874, [11; 11; 10; 9; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 1]); (1311, [10; 10; 9; 8; 8; 8; 6; 6; 6; 6; 6; 5; 3; 2; 1]); (6555, [11; 11; 10; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 2; 1]); (3496, [11; 11; 10; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1]); (11362, [11; 11; 10; 10; 10; 9; 9; 7; 6; 6; 6; 4; 3; 2; 1]); (14858, [11; 11; 11; 11; 10; 10; 8; 7; 6; 6; 6; 4; 3; 2; 1])]));
  ([12; 12; 11; 11; 11; 9; 8; 7; 6; 6; 6; 4; 3; 2; 1], (97, [0; 0; 0; 0; 0; 0; 0; 0; 97; 97; 0; 97; 0; 0; 0], [151202; 151202; 91770; 91770; 151202; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 4370; 8740; 0; 0; 0; 0], 1748, [(1748, [11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 2; 2; 2]); (1748, [11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 3; 3; 1]); (3496, [11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 4; 4; 2; 1]); (5244, [10; 10; 9; 9; 9; 7; 6; 6; 6; 6; 6; 5; 3; 2; 1]); (13110, [10; 10; 9; 9; 9; 7; 7; 7; 7; 7; 6; 4; 3; 2; 1]); (13984, [11; 11; 10; 10; 10; 8; 8; 8; 6; 6; 6; 4; 3; 2; 1]); (32338, [11; 11; 10; 10; 10; 9; 9; 7; 6; 6; 6; 4; 3; 2; 1]); (59432, [11; 11; 11; 11; 10; 10; 8; 7; 6; 6; 6; 4; 3; 2; 1])]));
  ([12; 12; 12; 12; 10; 9; 8; 7; 6; 6; 6; 4; 3; 2; 1], (217, [0; 0; 0; 0; 0; 0; 0; 0; 217; 217; 0; 217; 0; 0; 0], [207138; 207138; 299782; 299782; 0; 0; 0; 0; 0; 0; 4370; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 4370; 0; 0; 0; 0; 0], 2622, [(2622, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 2; 2]); (2622, [11; 11; 10; 10; 10; 8; 7; 6; 5; 5; 5; 3; 3; 3; 1]); (5244, [10; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 4; 4; 2; 1]); (7866, [9; 9; 8; 8; 8; 7; 7; 6; 6; 6; 6; 5; 3; 2; 1]); (8740, [9; 9; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 3; 2; 1]); (8740, [10; 10; 10; 10; 9; 9; 7; 7; 7; 6; 6; 4; 3; 2; 1]); (20976, [10; 10; 10; 10; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1]); (38456, [10; 10; 10; 10; 10; 10; 9; 7; 6; 6; 6; 4; 3; 2; 1]); (73416, [12; 12; 11; 11; 11; 9; 8; 7; 6; 6; 6; 4; 3; 2; 1])]));
  ([9; 9; 9; 9; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [12; 12; 12; 12; 8; 8; 8; 8; 8; 8; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [7; 7; 7; 7; 6; 6; 6; 6; 6; 6; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 1])]));
  ([10; 10; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [72; 72; 12; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 48; 40; 32; 24; 16; 8; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 4; 4; 2; 1]); (53, [9; 9; 9; 9; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 1])]));
  ([9; 9; 9; 9; 9; 9; 8; 8; 8; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [12; 12; 12; 12; 16; 16; 8; 8; 8; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [7; 7; 7; 7; 6; 6; 6; 6; 6; 6; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 1])]));
  ([10; 10; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [52; 52; 12; 12; 16; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 24; 16; 8; 0; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 4; 4; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 1]); (32, [9; 9; 9; 9; 9; 9; 8; 8; 8; 7; 5; 4; 3; 2; 1])]));
  ([10; 10; 10; 10; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [40; 40; 40; 40; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 12; 24; 16; 8; 0; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 4; 4; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 1]); (20, [9; 9; 9; 9; 9; 9; 8; 8; 8; 7; 5; 4; 3; 2; 1])]));
  ([11; 11; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [80; 80; 60; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 32; 24; 16; 8; 0; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 4; 4; 2; 1]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 1]); (40, [10; 10; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (12, [10; 10; 10; 10; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1])]));
  ([9; 9; 9; 9; 9; 9; 9; 9; 7; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [12; 12; 12; 12; 16; 16; 16; 16; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [7; 7; 7; 7; 6; 6; 6; 6; 6; 6; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 1])]));
  ([10; 10; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [32; 32; 12; 12; 12; 12; 20; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 4; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 8; 8; 7; 7; 7; 6; 4; 4; 4; 2; 1]); (5, [9; 9; 9; 9; 9; 9; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (8, [9; 9; 9; 9; 9; 9; 9; 9; 7; 7; 5; 4; 3; 2; 1])]));
  ([10; 10; 10; 10; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [32; 32; 32; 32; 12; 12; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 4; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 8; 8; 8; 8; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (1, [8; 8; 8; 8; 8; 8; 7; 7; 7; 6; 4; 4; 4; 2; 1]); (5, [9; 9; 9; 9; 9; 9; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (8, [9; 9; 9; 9; 9; 9; 9; 9; 7; 7; 5; 4; 3; 2; 1])]));
  ([11; 11; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [98; 98; 46; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 26; 13; 0; 10; 0; 5; 0; 0; 0; 0; 0], 1, [(1, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 4; 4; 2; 1]); (2, [9; 9; 9; 9; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 1]); (10, [9; 9; 9; 9; 9; 9; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (20, [10; 10; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1]); (33, [10; 10; 10; 10; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1])]));
  ([11; 11; 10; 10; 10; 8; 8; 8; 7; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [52; 52; 24; 24; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 16; 8; 0; 4; 0; 0; 1; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 1]); (1, [9; 9; 8; 8; 8; 7; 7; 7; 7; 6; 4; 4; 4; 2; 1]); (5, [10; 10; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (24, [10; 10; 10; 10; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1])]));
  ([11; 11; 11; 11; 9; 8; 8; 8; 7; 7; 5; 4; 3; 2; 1], (1, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 0; 0; 0], [6324; 6324; 8277; 8277; 744; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 2418; 1209; 0; 744; 0; 0; 0; 0; 0], 93, [(93, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 3; 2; 2; 2]); (93, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 1]); (186, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 4; 4; 2; 1]); (279, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 5; 5; 3; 2; 1]); (465, [10; 10; 9; 9; 9; 7; 7; 7; 7; 7; 6; 4; 3; 2; 1]); (1488, [10; 10; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (2976, [10; 10; 10; 10; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 10; 9; 8; 8; 8; 7; 7; 5; 4; 3; 2; 1], (37, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 37; 37; 0; 0; 0], [71424; 71424; 45198; 0; 0; 0; 4464; 4464; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 7254; 0; 0; 0; 0; 0], 558, [(558, [10; 10; 9; 8; 7; 7; 7; 7; 7; 6; 4; 3; 2; 2; 2]); (558, [11; 11; 10; 9; 8; 7; 7; 7; 6; 6; 4; 3; 3; 3; 1]); (1116, [11; 11; 10; 9; 8; 7; 7; 7; 6; 6; 4; 4; 4; 2; 1]); (1674, [11; 11; 10; 9; 8; 7; 7; 7; 6; 6; 5; 5; 3; 2; 1]); (2790, [10; 10; 9; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 1]); (11160, [11; 11; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (4464, [11; 11; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (18972, [11; 11; 10; 10; 10; 8; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (26226, [11; 11; 11; 11; 9; 8; 8; 8; 7; 7; 5; 4; 3; 2; 1])]));
  ([10; 10; 10; 10; 10; 10; 9; 7; 7; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [16; 16; 28; 28; 28; 28; 12; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 8; 4; 0; 0; 1; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 1]); (1, [9; 9; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 2; 1]); (9, [10; 10; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1])]));
  ([11; 11; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [56; 56; 28; 28; 28; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 12; 0; 8; 4; 0; 0; 1; 0; 0], 1, [(1, [9; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 3; 3; 3; 1]); (1, [9; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 4; 4; 2; 1]); (12, [10; 10; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1]); (21, [10; 10; 10; 10; 10; 10; 9; 7; 7; 7; 5; 4; 3; 2; 1])]));
  ([11; 11; 11; 11; 9; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [111; 111; 145; 145; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 13; 26; 0; 20; 10; 0; 0; 0; 0; 0], 2, [(2, [8; 8; 7; 7; 7; 7; 7; 6; 5; 5; 3; 3; 3; 2; 2]); (2, [9; 9; 8; 8; 8; 8; 8; 7; 6; 6; 4; 3; 3; 3; 1]); (2, [9; 9; 8; 8; 8; 8; 8; 7; 6; 6; 4; 4; 4; 2; 1]); (4, [9; 9; 8; 8; 8; 8; 8; 7; 7; 7; 6; 4; 3; 2; 1]); (24, [10; 10; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1]); (39, [10; 10; 10; 10; 10; 10; 9; 7; 7; 7; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1], (2, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 2; 0; 0; 0], [3751; 3751; 2449; 0; 0; 403; 558; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 496; 248; 0; 0; 0; 0; 0], 31, [(31, [11; 11; 10; 9; 8; 8; 8; 6; 6; 6; 4; 3; 2; 2; 2]); (31, [11; 11; 10; 9; 8; 8; 8; 6; 6; 6; 4; 3; 3; 3; 1]); (62, [11; 11; 10; 9; 8; 8; 8; 6; 6; 6; 4; 4; 4; 2; 1]); (93, [11; 11; 10; 9; 8; 8; 8; 6; 6; 6; 5; 5; 3; 2; 1]); (155, [10; 10; 9; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 1]); (744, [10; 10; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1]); (403, [11; 11; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1]); (1302, [11; 11; 11; 11; 9; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1])]));
  ([11; 11; 11; 11; 10; 10; 8; 7; 7; 7; 5; 4; 3; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [46; 46; 46; 46; 33; 33; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 10; 5; 0; 0; 0; 0; 0], 1, [(1, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 3; 3; 3; 1]); (2, [9; 9; 9; 9; 8; 8; 7; 7; 6; 6; 4; 4; 4; 2; 1]); (2, [9; 9; 9; 9; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 1]); (11, [10; 10; 10; 10; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (10, [10; 10; 10; 10; 10; 10; 9; 7; 7; 7; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 5; 5; 0; 0; 0], [9021; 9021; 5115; 0; 3906; 5115; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 1488; 744; 0; 0; 0; 0; 0], 93, [(93, [11; 11; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 2; 2; 2]); (93, [11; 11; 10; 9; 9; 9; 7; 6; 6; 6; 4; 3; 3; 3; 1]); (186, [10; 10; 10; 10; 9; 9; 7; 6; 6; 6; 4; 4; 4; 2; 1]); (279, [11; 11; 10; 9; 9; 9; 7; 6; 6; 6; 5; 5; 3; 2; 1]); (465, [10; 10; 9; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 2; 1]); (2232, [11; 11; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (1209, [11; 11; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1]); (3720, [11; 11; 11; 11; 10; 10; 8; 7; 7; 7; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 11; 11; 9; 8; 7; 7; 7; 5; 4; 3; 2; 1], (49, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 49; 49; 0; 0; 0], [47430; 47430; 30690; 30690; 47430; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 2232; 4464; 0; 0; 0; 0; 0], 558, [(558, [11; 11; 10; 10; 10; 8; 7; 6; 6; 6; 4; 3; 2; 2; 2]); (558, [11; 11; 10; 10; 10; 8; 7; 6; 6; 6; 4; 3; 3; 3; 1]); (1116, [10; 10; 10; 10; 9; 9; 7; 6; 6; 6; 4; 4; 4; 2; 1]); (1674, [11; 11; 10; 10; 10; 8; 7; 6; 6; 6; 5; 5; 3; 2; 1]); (2790, [10; 10; 9; 9; 9; 7; 7; 7; 7; 7; 6; 4; 3; 2; 1]); (6696, [10; 10; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (7254, [11; 11; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1]); (15624, [11; 11; 11; 11; 10; 10; 8; 7; 7; 7; 5; 4; 3; 2; 1])]));
  ([12; 12; 12; 12; 10; 9; 8; 7; 7; 7; 5; 4; 3; 2; 1], (53, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 53; 53; 0; 0; 0], [29760; 29760; 42222; 42222; 0; 0; 0; 0; 0; 3162; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 2976; 0; 0; 0; 0; 0; 0], 372, [(372, [10; 10; 10; 10; 9; 9; 7; 6; 6; 6; 4; 3; 2; 2; 2]); (372, [9; 9; 9; 9; 7; 6; 6; 6; 6; 6; 5; 3; 3; 3; 1]); (744, [9; 9; 9; 9; 7; 6; 6; 6; 6; 6; 5; 4; 4; 2; 1]); (1116, [10; 10; 10; 10; 9; 9; 7; 6; 6; 6; 5; 5; 3; 2; 1]); (558, [10; 10; 9; 9; 9; 7; 7; 7; 7; 7; 6; 4; 3; 2; 1]); (186, [10; 10; 10; 10; 9; 9; 7; 7; 7; 6; 6; 4; 3; 2; 1]); (5952, [10; 10; 10; 10; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (4836, [10; 10; 10; 10; 10; 10; 9; 7; 7; 7; 5; 4; 3; 2; 1]); (11904, [12; 12; 11; 11; 11; 9; 8; 7; 7; 7; 5; 4; 3; 2; 1])]));
  ([10; 10; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [16; 16; 12; 12; 12; 12; 12; 12; 12; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [8; 8; 7; 7; 7; 7; 7; 7; 7; 4; 3; 3; 3; 2; 2]); (1, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 3; 3; 1])]));
  ([10; 10; 10; 10; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [16; 16; 24; 24; 12; 12; 12; 12; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 3; 3; 1]); (1, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 2; 1]); (5, [10; 10; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 3; 2; 1])]));
  ([11; 11; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [102; 102; 28; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 56; 43; 30; 15; 0; 0; 0; 0; 0; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 3; 3; 1]); (2, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 2; 1]); (2, [9; 9; 9; 9; 8; 8; 8; 8; 7; 6; 6; 4; 3; 2; 1]); (2, [9; 9; 9; 9; 9; 9; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (6, [10; 10; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 3; 2; 1]); (67, [10; 10; 10; 10; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1])]));
  ([10; 10; 10; 10; 10; 10; 9; 8; 8; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [16; 16; 24; 24; 24; 24; 12; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 2; 2; 2]); (1, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 3; 3; 3; 1]); (1, [9; 9; 8; 8; 8; 8; 8; 8; 8; 5; 4; 4; 4; 2; 1]); (5, [10; 10; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 3; 2; 1])]));
  ([11; 11; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [60; 60; 16; 16; 32; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 12; 0; 8; 0; 0; 0; 1; 0; 0], 1, [(1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1]); (13, [10; 10; 10; 10; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1]); (24, [10; 10; 10; 10; 10; 10; 9; 8; 8; 6; 5; 4; 3; 2; 1])]));
  ([11; 11; 11; 11; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [127; 127; 127; 127; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 15; 30; 0; 20; 0; 0; 0; 0; 0; 0], 2, [(2, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (2, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (4, [8; 8; 8; 8; 8; 8; 7; 7; 7; 6; 4; 4; 4; 2; 1]); (4, [9; 9; 9; 9; 9; 9; 8; 7; 7; 6; 6; 4; 3; 2; 1]); (36, [10; 10; 10; 10; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1]); (37, [10; 10; 10; 10; 10; 10; 9; 8; 8; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 10; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1], (12, [0; 0; 0; 0; 0; 0; 0; 0; 0; 12; 12; 12; 0; 0; 0], [50255; 50255; 29716; 0; 0; 9177; 9177; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 5681; 0; 0; 0; 0; 0; 0], 437, [(437, [10; 10; 9; 8; 7; 7; 7; 6; 6; 4; 3; 3; 3; 2; 2]); (437, [11; 11; 10; 9; 8; 8; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (437, [11; 11; 10; 9; 8; 8; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (1311, [11; 11; 10; 9; 8; 8; 8; 7; 7; 5; 5; 5; 3; 2; 1]); (2185, [11; 11; 10; 9; 8; 8; 8; 7; 7; 6; 6; 4; 3; 2; 1]); (3496, [11; 11; 10; 9; 8; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (11362, [11; 11; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1]); (9177, [11; 11; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1]); (20539, [11; 11; 11; 11; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1])]));
  ([11; 11; 11; 11; 10; 10; 8; 8; 8; 6; 5; 4; 3; 2; 1], (3, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [53; 53; 53; 53; 18; 18; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 20; 10; 0; 0; 0; 0; 0; 0], 1, [(1, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 3; 3; 1]); (2, [9; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 4; 4; 2; 1]); (2, [9; 9; 9; 9; 9; 9; 8; 7; 7; 6; 6; 4; 3; 2; 1]); (2, [9; 9; 9; 9; 9; 9; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (24, [10; 10; 10; 10; 10; 10; 9; 8; 8; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 2; 1], (29, [0; 0; 0; 0; 0; 0; 0; 0; 0; 29; 29; 29; 0; 0; 0], [55936; 55936; 29716; 0; 9177; 12673; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 11362; 5681; 0; 0; 0; 0; 0; 0], 437, [(437, [11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 3; 2; 2; 2]); (437, [11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 3; 3; 3; 1]); (874, [11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 4; 4; 4; 2; 1]); (1311, [11; 11; 10; 9; 9; 9; 7; 7; 7; 5; 5; 5; 3; 2; 1]); (2185, [11; 11; 10; 9; 9; 9; 7; 7; 7; 6; 6; 4; 3; 2; 1]); (3496, [10; 10; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (17043, [10; 10; 10; 10; 10; 10; 9; 8; 8; 6; 5; 4; 3; 2; 1]); (9177, [11; 11; 11; 11; 10; 10; 8; 8; 8; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 11; 11; 9; 8; 8; 8; 6; 5; 4; 3; 2; 1], (11, [0; 0; 0; 0; 0; 0; 0; 0; 0; 11; 11; 11; 0; 0; 0], [33212; 33212; 24035; 24035; 33212; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 437, [(437, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 3; 2; 2; 2]); (437, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 3; 3; 3; 1]); (874, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 4; 4; 2; 1]); (1311, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 5; 5; 3; 2; 1]); (2185, [11; 11; 10; 10; 10; 8; 7; 7; 7; 6; 6; 4; 3; 2; 1]); (3496, [10; 10; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 1]); (5681, [10; 10; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 3; 2; 1]); (9177, [11; 11; 11; 11; 10; 10; 8; 8; 8; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 12; 12; 10; 9; 8; 8; 8; 6; 5; 4; 3; 2; 1], (27, [0; 0; 0; 0; 0; 0; 0; 0; 0; 27; 27; 27; 0; 0; 0], [54188; 54188; 83904; 83904; 0; 5244; 0; 0; 18354; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 874, [(874, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 2; 2]); (874, [10; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 3; 3; 1]); (1748, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 4; 4; 4; 2; 1]); (2622, [11; 11; 10; 10; 10; 8; 7; 7; 7; 5; 5; 5; 3; 2; 1]); (4370, [10; 10; 10; 10; 9; 9; 7; 7; 7; 6; 6; 4; 3; 2; 1]); (6992, [10; 10; 10; 10; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (11362, [10; 10; 10; 10; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1]); (25346, [12; 12; 11; 11; 11; 9; 8; 8; 8; 6; 5; 4; 3; 2; 1])]));
  ([10; 10; 10; 10; 10; 10; 10; 10; 7; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [16; 16; 16; 16; 20; 20; 20; 20; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (1, [9; 9; 9; 9; 9; 9; 9; 9; 6; 5; 4; 4; 4; 2; 1]); (2, [10; 10; 10; 10; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1])]));
  ([11; 11; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 1], (4, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [36; 36; 16; 16; 20; 20; 20; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0], 1, [(1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 2; 2; 2]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (1, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 4; 4; 2; 1]); (1, [10; 10; 10; 10; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1]); (12, [10; 10; 10; 10; 10; 10; 10; 10; 7; 6; 5; 4; 3; 2; 1])]));
  ([11; 11; 11; 11; 10; 10; 9; 9; 7; 6; 5; 4; 3; 2; 1], (6, [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [86; 86; 86; 86; 50; 50; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 2, [(1, [8; 8; 8; 8; 7; 7; 7; 7; 6; 4; 3; 3; 3; 2; 2]); (1, [8; 8; 8; 8; 8; 8; 8; 8; 5; 5; 5; 3; 2; 2; 2]); (2, [9; 9; 9; 9; 8; 8; 8; 8; 7; 5; 4; 3; 3; 3; 1]); (3, [8; 8; 8; 8; 8; 8; 8; 8; 5; 5; 5; 4; 4; 2; 1]); (4, [9; 9; 9; 9; 9; 9; 9; 9; 7; 7; 5; 4; 3; 2; 1]); (11, [10; 10; 10; 10; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1]); (22, [10; 10; 10; 10; 10; 10; 10; 10; 7; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 2; 1], (27, [0; 0; 0; 0; 0; 0; 0; 0; 0; 27; 27; 27; 0; 0; 0], [96140; 96140; 48070; 0; 29716; 29716; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 874, [(874, [10; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 2; 2]); (874, [11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 4; 3; 3; 3; 1]); (1748, [11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 4; 4; 4; 2; 1]); (2622, [11; 11; 10; 9; 9; 9; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (4370, [11; 11; 10; 9; 9; 9; 8; 8; 6; 6; 6; 4; 3; 2; 1]); (6992, [11; 11; 10; 9; 9; 9; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (11362, [11; 11; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1]); (18354, [10; 10; 10; 10; 10; 10; 10; 10; 7; 6; 5; 4; 3; 2; 1]); (28842, [11; 11; 11; 11; 10; 10; 9; 9; 7; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 11; 11; 9; 9; 9; 7; 6; 5; 4; 3; 2; 1], (20, [0; 0; 0; 0; 0; 0; 0; 0; 0; 20; 20; 20; 0; 0; 0], [38893; 38893; 24035; 24035; 29716; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 437, [(437, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 2; 2; 2]); (437, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 3; 3; 1]); (874, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 4; 4; 2; 1]); (1311, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (2185, [11; 11; 10; 10; 10; 8; 8; 8; 6; 6; 6; 4; 3; 2; 1]); (3496, [11; 11; 10; 10; 10; 8; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (5681, [10; 10; 10; 10; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1]); (9177, [10; 10; 10; 10; 10; 10; 10; 10; 7; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 12; 12; 10; 9; 9; 9; 7; 6; 5; 4; 3; 2; 1], (54, [0; 0; 0; 0; 0; 0; 0; 0; 0; 54; 54; 54; 0; 0; 0], [38893; 38893; 53751; 53751; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 437, [(437, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 2; 2; 2]); (437, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 3; 3; 3; 1]); (874, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 4; 4; 4; 2; 1]); (1311, [11; 11; 10; 10; 10; 8; 8; 8; 6; 5; 5; 5; 3; 2; 1]); (2185, [11; 11; 10; 10; 10; 8; 8; 8; 6; 6; 6; 4; 3; 2; 1]); (3496, [11; 11; 10; 10; 10; 8; 8; 8; 7; 7; 5; 4; 3; 2; 1]); (5681, [10; 10; 10; 10; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1]); (9177, [10; 10; 10; 10; 10; 10; 10; 10; 7; 6; 5; 4; 3; 2; 1]); (6118, [12; 12; 11; 11; 11; 9; 9; 9; 7; 6; 5; 4; 3; 2; 1])]));
  ([11; 11; 11; 11; 11; 11; 10; 8; 7; 6; 5; 4; 3; 2; 1], (5, [0; 0; 0; 0; 0; 0; 0; 0; 0; 5; 5; 5; 0; 0; 0], [30153; 30153; 47633; 47633; 47633; 47633; 29716; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 874, [(874, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 2; 2]); (874, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 3; 3; 3; 1]); (1748, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 2; 1]); (2622, [10; 10; 9; 9; 9; 9; 9; 8; 6; 5; 5; 5; 3; 2; 1]); (4370, [10; 10; 9; 9; 9; 9; 9; 8; 6; 6; 6; 4; 3; 2; 1]); (6992, [10; 10; 9; 9; 9; 9; 9; 8; 7; 7; 5; 4; 3; 2; 1]); (11362, [10; 10; 10; 10; 10; 10; 9; 8; 8; 6; 5; 4; 3; 2; 1]); (437, [10; 10; 10; 10; 10; 10; 10; 10; 7; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 3; 2; 1], (55, [0; 0; 0; 0; 0; 0; 0; 0; 0; 55; 55; 55; 0; 0; 0], [76038; 76038; 46322; 46322; 48070; 0; 31464; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 874, [(874, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 2; 2; 2]); (874, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 4; 3; 3; 3; 1]); (1748, [10; 10; 10; 10; 9; 9; 7; 6; 6; 6; 4; 4; 4; 2; 1]); (2622, [11; 11; 10; 10; 10; 9; 9; 7; 6; 5; 5; 5; 3; 2; 1]); (4370, [11; 11; 10; 10; 10; 9; 9; 7; 6; 6; 6; 4; 3; 2; 1]); (5244, [11; 11; 10; 10; 10; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1]); (11362, [11; 11; 10; 10; 10; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1]); (18354, [11; 11; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 1]); (27968, [11; 11; 11; 11; 11; 11; 10; 8; 7; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 12; 12; 10; 10; 10; 8; 7; 6; 5; 4; 3; 2; 1], (22, [0; 0; 0; 0; 0; 0; 0; 0; 0; 22; 22; 22; 0; 0; 0], [29279; 29279; 35397; 35397; 0; 9614; 18354; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 437, [(437, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 2; 2]); (437, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 3; 3; 1]); (874, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 4; 4; 2; 1]); (1311, [10; 10; 10; 10; 10; 10; 9; 7; 6; 5; 5; 5; 3; 2; 1]); (2185, [10; 10; 10; 10; 10; 10; 9; 7; 6; 6; 6; 4; 3; 2; 1]); (3496, [10; 10; 10; 10; 10; 10; 9; 7; 7; 7; 5; 4; 3; 2; 1]); (5681, [10; 10; 10; 10; 9; 9; 9; 9; 8; 6; 5; 4; 3; 2; 1]); (3496, [12; 12; 11; 11; 11; 9; 9; 9; 7; 6; 5; 4; 3; 2; 1]); (2622, [12; 12; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 3; 2; 1])]));
  ([12; 12; 12; 12; 11; 11; 9; 8; 7; 6; 5; 4; 3; 2; 1], (24, [0; 0; 0; 0; 0; 0; 0; 0; 0; 24; 24; 24; 0; 0; 0], [20102; 20102; 25783; 27968; 31464; 33649; 0; 0; 0; 0; 0; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], 437, [(437, [11; 11; 11; 11; 10; 10; 8; 7; 6; 5; 4; 3; 2; 2; 2]); (437, [9; 9; 9; 9; 9; 9; 8; 6; 5; 4; 4; 4; 3; 3; 1]); (874, [8; 8; 8; 8; 8; 8; 8; 8; 6; 6; 4; 4; 4; 2; 1]); (874, [8; 8; 8; 8; 8; 8; 8; 8; 6; 6; 5; 5; 3; 2; 1]); (2185, [12; 12; 11; 10; 9; 8; 8; 8; 6; 6; 6; 4; 3; 2; 1]); (1748, [11; 11; 11; 11; 9; 9; 9; 7; 7; 7; 5; 4; 3; 2; 1]); (5681, [11; 11; 11; 11; 9; 9; 9; 8; 8; 6; 5; 4; 3; 2; 1]); (3496, [11; 11; 10; 10; 10; 10; 10; 9; 7; 6; 5; 4; 3; 2; 1]); (1748, [12; 12; 12; 12; 10; 10; 10; 8; 7; 6; 5; 4; 3; 2; 1])]))
].

Definition deltas (L d : list Z) : list Z := map (fun p => fst p - snd p) (combine L d).

Fixpoint lookup (d : list Z) (tbl : list (list Z * cert)) : option cert :=
  match tbl with
  | [] => None
  | (k, c) :: r => if list_eq_dec Z.eq_dec k d then Some c else lookup d r
  end.

(** The check of one depth profile: the per-position caps bound when it is at most 75, else a certificate. *)
Definition leaf75 (d : list Z) : bool :=
  Nat.eqb (length (repl 7 d)) (length d) &&
  (if bsum 0 316 (repl 7 d) d <=? 75 then true
   else match lookup d cert_table with Some c => cert_ok 75 d (deltas (repl 7 d) d) c | None => false end).

Lemma enum_ok75 : enum leaf75 12 1 4096 15 [] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dlt_dotn : forall f L d, length f = length d -> length L = length d ->
  dlt f L d = dotn (length d) f (deltas L d).
Proof.
  induction f as [|x f IH]; intros [|y L] [|z d] Hf HL; simpl in Hf, HL; try lia; [reflexivity|].
  cbn [dlt length]. unfold dotn. rewrite sumk_shift. rewrite IH by lia. reflexivity.
Qed.

Lemma dotn_combine : forall f d, length f = length d ->
  dotn (length d) f d = sumz (map (fun p => fst p * snd p) (combine f d)).
Proof.
  induction f as [|x f IH]; intros [|z d] Hf; simpl in Hf; try lia; [reflexivity|].
  cbn [length combine map sumz]. unfold dotn. rewrite sumk_shift. rewrite <- IH by lia. reflexivity.
Qed.

(** The cost of the repair on the bit-length tree with Huffman optimality: at most 75 bits when at most 15
    bit-length codes are used and the total weight is at most 316.  The lists are in heap-scan order: [f]
    nondecreasing, a more frequent leaf never deeper; the depths [d] form a complete code; the caps are those of
    [HuffAbs.huff_fib]; the last hypothesis is [HuffAbs.huff_opt] for codes with lengths at most 12. *)
Theorem bl_repair_cost_opt : forall (f d : list Z) (W D : Z),
  length f = length d -> (length d <= 15)%nat ->
  (forall k, (S k < length f)%nat -> nth k f 0 <= nth (S k) f 0) ->
  (forall i j, (i < length f)%nat -> (j < length f)%nat -> nth i f 0 < nth j f 0 -> nth j d 0 <= nth i d 0) ->
  (forall x, In x d -> 1 <= x <= D) -> sumz (map (fun x => 2 ^ (D - x)) d) = 2 ^ D ->
  sumz f = W -> W <= 316 ->
  (forall k, (k < length d)%nat -> 1 <= nth k f 0 /\ fib (nth k d 0 + 1) * nth k f 0 <= W) ->
  (forall e, length e = length d -> (forall x, In x e -> 0 <= x <= 12) ->
     sumz (map (fun x => 2 ^ (12 - x)) e) <= 4096 -> dotn (length d) f d <= dotn (length d) f e) ->
  dlt f (repl 7 d) d <= 75.
Proof.
  intros f d W D Hl Hn Hf Hx Hd Hk Hs HW Hc Hopt.
  destruct d as [|x0 d0] eqn:Ed; [destruct (repl 7 []), f; cbn [dlt]; lia|].
  assert (HD1 : 1 <= D) by (specialize (Hd x0 (or_introl eq_refl)); lia).
  rewrite <- Ed in *.
  destruct (rearrange f d Hl Hf Hx) as [d' [Hp [Hso [Hl' Hpc]]]].
  assert (Hin : forall x, In x d' -> In x d) by (intros; eapply Permutation_in; [apply Permutation_sym|]; eauto).
  assert (Hd' : forall x, In x d' -> 1 <= x <= D) by (intros x Hx'; apply Hd, Hin; auto).
  assert (Hk' : sumz (map (fun x => 2 ^ (D - x)) d') = 2 ^ D)
    by (rewrite <- Hk; apply sumz_perm, Permutation_map, Permutation_sym; auto).
  assert (Hc' : forall k, (k < length d')%nat -> 1 <= nth k f 0 /\ fib (nth k d' 0 + 1) * nth k f 0 <= W).
  { intros k Hk''. assert (Hin2 : In (nth k f 0, nth k d' 0) (combine f d')).
    { rewrite <- combine_nth by lia. apply nth_In. rewrite length_combine. lia. }
    apply (Permutation_in _ (Permutation_sym Hpc)) in Hin2.
    destruct (in_combine_nth f d _ _ Hl Hin2) as [i [Hi [Hfi Hdi]]].
    rewrite <- Hfi, <- Hdi. apply Hc. lia. }
  assert (Hc0 : forall k, (k < length d')%nat -> 1 <= nth k f 0 /\ fib (nth k d' 0 + 1 + 0) * nth k f 0 <= W)
    by (intros k Hk''; rewrite Z.add_0_r; auto).
  assert (H12 : forall x, In x d' -> x <= 12)
    by (apply (caps_depth12 0 f d' W); [lia|lia|auto|intros x Hx'; specialize (Hd' x Hx'); lia]).
  assert (Hdot : dotn (length d') f d' = dotn (length d) f d).
  { rewrite !dotn_combine by lia. apply sumz_perm, Permutation_map, Permutation_sym; auto. }
  assert (Hk12 : sumz (map (fun x => 2 ^ (12 - x)) d') = 4096).
  { apply (kraft_rescale d' D 12); auto; [intros x Hx'; split; [apply Hd'|apply H12]; auto|lia|lia]. }
  assert (Hleaf := enum_complete leaf75 12 1 4096 15 [] d' enum_ok75 ltac:(reflexivity) ltac:(lia) Hso
                     ltac:(intros y Hy; split; [apply Hd'|apply H12]; auto) Hk12 ltac:(lia)).
  rewrite app_nil_r in Hleaf. unfold leaf75 in Hleaf. apply andb_true_iff in Hleaf.
  destruct Hleaf as [Hlen Hleaf]. apply Nat.eqb_eq in Hlen.
  rewrite (repl_perm 7 d d' Hp).
  assert (E : dlt f (repl 7 d') d = dlt f (repl 7 d') d').
  { rewrite !dlt_split by lia. f_equal. apply sumz_perm, Permutation_map; auto. }
  rewrite E.
  destruct (Z.leb_spec (bsum 0 316 (repl 7 d') d') 75) as [Hb|Hb].
  - eapply Z.le_trans; [|exact Hb]. apply dlt_le_bsum; [lia|lia|lia|].
    intros k Hkl. destruct (Hc0 k Hkl) as [H1 H2]. split; [auto|split; [|lia]].
    assert (In (nth k d' 0) d') by (apply nth_In; auto). specialize (Hd' _ H). lia.
  - destruct (lookup d' cert_table) as [c|]; [|discriminate].
    rewrite dlt_dotn by lia.
    apply (cert_sound 75 d' _ c f Hleaf); [lia| | |lia|].
    + intros k Hkl. destruct (Hc' k Hkl). split; lia.
    + intros k Hkl. apply Hf. lia.
    + intros e He1 He2 He3. rewrite Hdot, Hl'. apply Hopt; auto; lia.
Qed.

(** The same, as costs: the repaired code costs at most 75 bits more than the Huffman code. *)
Corollary bl_repair_cost_opt' : forall (f d : list Z) (W D : Z),
  length f = length d -> (length d <= 15)%nat ->
  (forall k, (S k < length f)%nat -> nth k f 0 <= nth (S k) f 0) ->
  (forall i j, (i < length f)%nat -> (j < length f)%nat -> nth i f 0 < nth j f 0 -> nth j d 0 <= nth i d 0) ->
  (forall x, In x d -> 1 <= x <= D) -> sumz (map (fun x => 2 ^ (D - x)) d) = 2 ^ D ->
  sumz f = W -> W <= 316 ->
  (forall k, (k < length d)%nat -> 1 <= nth k f 0 /\ fib (nth k d 0 + 1) * nth k f 0 <= W) ->
  (forall e, length e = length d -> (forall x, In x e -> 0 <= x <= 12) ->
     sumz (map (fun x => 2 ^ (12 - x)) e) <= 4096 -> dotn (length d) f d <= dotn (length d) f e) ->
  length (repl 7 d) = length d /\
  sumz (map (fun p => fst p * snd p) (combine f (repl 7 d))) <=
  sumz (map (fun p => fst p * snd p) (combine f d)) + 75.
Proof.
  intros f d W D Hl Hn Hf Hx Hd Hk Hs HW Hc Hopt.
  assert (Hb := bl_repair_cost_opt f d W D Hl Hn Hf Hx Hd Hk Hs HW Hc Hopt).
  assert (Hlen : length (repl 7 d) = length d).
  { destruct (rearrange f d Hl Hf Hx) as [d' [Hp [Hso [Hl' Hpc]]]].
    rewrite (repl_perm 7 d d' Hp), <- Hl'.
    destruct d' as [|x0 d0] eqn:Ed'; [reflexivity|]. rewrite <- Ed' in *.
    assert (Hin : forall x, In x d' -> In x d) by (intros; eapply Permutation_in; [apply Permutation_sym|]; eauto).
    assert (Hd' : forall x, In x d' -> 1 <= x <= D) by (intros x Hx'; apply Hd, Hin; auto).
    assert (H12 : forall x, In x d -> x <= 12)
      by (apply (caps_depth12 0 f d W); [lia|lia| |intros x Hx'; specialize (Hd x Hx'); lia];
          intros k Hkl; rewrite Z.add_0_r; auto).
    assert (Hleaf := bl_leaf_ok 0 d' D (or_introl eq_refl) ltac:(lia) Hso Hd'
                       ltac:(rewrite <- Hk; apply sumz_perm, Permutation_map, Permutation_sym; auto)
                       ltac:(intros x Hx'; apply H12, Hin; auto) ltac:(congruence)).
    unfold leaf_ok in Hleaf. apply andb_true_iff in Hleaf. destruct Hleaf as [Hlen _]. apply Nat.eqb_eq. auto. }
  split; [auto|]. rewrite dlt_split in Hb by lia. lia.
Qed.
