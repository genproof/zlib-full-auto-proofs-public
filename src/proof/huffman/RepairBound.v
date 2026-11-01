(** * The overhead of gen_bitlen's length-limit repair at max length 15

    For depths [d] of a complete code, sorted nonincreasing (the leaves in heap-scan order, least frequent first),
    with frequencies [f] satisfying the Huffman caps f_k * fib (d_k + 1) <= W, the repaired lengths
    [Repair.repl 15 d] exceed the depths, weighted by the frequencies, by at most 2 n W / 540 (n leaves):

        540 * sum_k f_k * max 0 (L'_k - d_k) <= 2 n W.

    Proof idea (see the comment of [repair15_bound]):
    - per position, with x = min d 15 the clamped length and x' > x the repaired one,
      540 (x' - x) <= fib (x + 1) (2^(15-x) - 2^(15-x')) for 1 <= x < x' <= 15 (a finite check), so
      540 f (x' - x) <= W * gain, gain = 2^(15-x) - 2^(15-x');
    - the gains sum to I + Loss, I the number of repair iterations (the Kraft excess of the clamped code, < n) and
      Loss the Kraft mass of the positions whose length went down; these sit at levels strictly between bmin (the
      smallest level the loop ever split) and 15, where the loop keeps a total mass <= 2^(15-bmin), and a split at
      level b needs c_15 >= 2^(15-b) + (iterations to go), so 2^(15-bmin) < n. *)

From Coq Require Import ZArith List Lia Bool Permutation Sorted.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Repair.
Import ListNotations.
Local Open Scope Z_scope.

(** [dpl f L d] = sum_k f_k * max 0 (L_k - d_k). *)
Fixpoint dpl (f L d : list Z) : Z :=
  match f, L, d with x :: f', y :: L', z :: d' => x * Z.max 0 (y - z) + dpl f' L' d' | _, _, _ => 0 end.

Definition repair15_statement : Prop := forall (f d : list Z) (W D : Z),
  length f = length d -> (length d <= 286)%nat -> dsorted d ->
  15 <= D -> (forall x, In x d -> 1 <= x <= D) -> sumz (map (fun x => 2 ^ (D - x)) d) = 2 ^ D ->
  (forall k, (k < length d)%nat -> 1 <= nth k f 0 /\ fib (nth k d 0 + 1) * nth k f 0 <= W) ->
  length (repl 15 d) = length d /\ 540 * dpl f (repl 15 d) d <= 2 * Z.of_nat (length d) * W.

(** ** Part 1: the clamped depths, in handout order, are the sorted depths clamped *)

Lemma lsc_dsorted_filter : forall P e, dsorted e -> dsorted (filter P e).
Proof.
  intros P e; induction e as [|x r IH]; simpl; auto. intros [H1 H2].
  destruct (P x); simpl; auto. split; auto.
  intros y Hy. apply filter_In in Hy. apply H1; tauto.
Qed.

Lemma lsc_dsorted_map : forall f e, (forall a b, b <= a -> f b <= f a) -> dsorted e -> dsorted (map f e).
Proof.
  intros f e Hf; induction e as [|x r IH]; simpl; auto. intros [H1 H2]. split; auto.
  intros y Hy. apply in_map_iff in Hy. destruct Hy as [z [<- Hz]]. apply Hf, H1, Hz.
Qed.

Lemma lsc_below : forall K r, (forall y, In y r -> y < K) ->
  filter (fun x => x =? K) r = [] /\ filter (fun x => x <? K) r = r.
Proof.
  intros K r; induction r as [|x r IH]; simpl; intros H; auto.
  destruct IH as [E1 E2]; [intros; apply H; auto|].
  assert (x < K) by (apply H; auto).
  replace (x =? K) with false by lia. replace (x <? K) with true by lia. rewrite E1, E2; auto.
Qed.

Lemma lsc_split : forall K e, dsorted e -> (forall x, In x e -> x <= K) ->
  e = repeat K (length (filter (fun x => x =? K) e)) ++ filter (fun x => x <? K) e.
Proof.
  intros K e; induction e as [|x r IH]; simpl; auto. intros [H1 H2] HK.
  assert (x <= K) by (apply HK; auto).
  destruct (Z.eq_dec x K) as [->|Hne].
  - rewrite Z.eqb_refl, Z.ltb_irrefl. simpl. f_equal. apply IH; auto.
  - replace (x =? K) with false by lia. replace (x <? K) with true by lia.
    destruct (lsc_below K r) as [E1 E2]; [intros y Hy; specialize (H1 y Hy); lia|].
    rewrite E1, E2. reflexivity.
Qed.

Lemma lsc_cnt_filter : forall K l e, l < K ->
  cntz (fun x => x =? l) (filter (fun x => x <? K) e) = cntz (fun x => x =? l) e.
Proof.
  intros K l e Hl; induction e as [|x r IH]; simpl; auto.
  destruct (x <? K) eqn:E.
  - rewrite !cntz_cons. rewrite IH. reflexivity.
  - rewrite cntz_cons. replace (x =? l) with false by lia. lia.
Qed.

Lemma lsc_lseq : forall (k : nat) e c, dsorted e -> (forall x, In x e -> 1 <= x <= Z.of_nat k) ->
  (forall l, 1 <= l <= Z.of_nat k -> Znth l c = cntz (fun x => x =? l) e) -> lseq c k = e.
Proof.
  induction k as [|k IH]; intros e c Hs Hr Hc.
  - destruct e as [|x e]; [reflexivity|]. specialize (Hr x (or_introl eq_refl)). lia.
  - cbn [lseq]. rewrite (lsc_split (Z.of_nat (S k)) e Hs) by (intros x Hx; specialize (Hr x Hx); lia).
    rewrite Hc by lia. unfold cntz. rewrite Nat2Z.id. f_equal.
    apply IH.
    + apply lsc_dsorted_filter; auto.
    + intros x Hx. apply filter_In in Hx. destruct Hx as [Hx Hlt]. apply Z.ltb_lt in Hlt. specialize (Hr x Hx). lia.
    + intros l Hl. rewrite lsc_cnt_filter by lia. apply Hc. lia.
Qed.

Lemma lsc_cnt_map : forall (f : Z -> Z) l d,
  cntz (fun x => x =? l) (map f d) = cntz (fun x => f x =? l) d.
Proof.
  intros f l d; induction d as [|x r IH]; simpl; auto. rewrite !cntz_cons, IH. reflexivity.
Qed.

Lemma lseq_clampc : forall d, dsorted d -> (forall x, In x d -> 1 <= x) ->
  lens 15 (clampc 15 d) = map (fun x => Z.min x 15) d.
Proof.
  intros d Hs Hr. unfold lens. apply lsc_lseq.
  - apply lsc_dsorted_map; auto. intros; lia.
  - intros x Hx. apply in_map_iff in Hx. destruct Hx as [z [<- Hz]]. specialize (Hr z Hz). simpl. lia.
  - intros l Hl. simpl in Hl. rewrite Znth_clampc by lia. replace (l =? 0) with false by lia.
    rewrite lsc_cnt_map. reflexivity.
Qed.

(** ** Part 2: the k-th length of [lseq c K] exceeds v iff k is below the number of lengths > v *)

Lemma lseq_nth_gt : forall (K : nat) c k v, (forall l, 1 <= l <= Z.of_nat K -> 0 <= Znth l c) ->
  (k < length (lseq c K))%nat ->
  (v < nth k (lseq c K) 0 <-> Z.of_nat k < lsum (fun l => if v <? l then Znth l c else 0) K).
Proof.
  induction K as [|K IH]; intros c k v Hc Hk.
  - simpl in Hk. lia.
  - cbn [lseq] in *. rewrite lsum_S.
    set (n := Z.to_nat (Znth (Z.of_nat (S K)) c)) in *.
    rewrite app_length, repeat_length in Hk.
    assert (Hn : Z.of_nat n = Znth (Z.of_nat (S K)) c)
      by (subst n; rewrite Z2Nat.id; auto; apply Hc; lia).
    destruct (Nat.lt_ge_cases k n) as [Hkn|Hkn].
    + rewrite app_nth1 by (rewrite repeat_length; auto).
      assert (Hin : In (nth k (repeat (Z.of_nat (S K)) n) 0) (repeat (Z.of_nat (S K)) n))
        by (apply nth_In; rewrite repeat_length; auto).
      apply repeat_spec in Hin. rewrite Hin.
      destruct (Z.ltb_spec v (Z.of_nat (S K))).
      * assert (0 <= lsum (fun l => if v <? l then Znth l c else 0) K)
          by (apply lsum_nonneg; intros l Hl; destruct (v <? l); [apply Hc; lia | lia]).
        split; intros; lia.
      * rewrite (lsum_ext _ (fun _ => 0)) by (intros l Hl; destruct (Z.ltb_spec v l); lia).
        rewrite lsum_zero. split; intros; lia.
    + rewrite app_nth2 by (rewrite repeat_length; auto). rewrite repeat_length.
      specialize (IH c (k - n)%nat v ltac:(intros; apply Hc; lia) ltac:(lia)).
      destruct (Z.ltb_spec v (Z.of_nat (S K))).
      * rewrite IH. split; intros; lia.
      * assert (Hin : In (nth (k - n) (lseq c K) 0) (lseq c K)) by (apply nth_In; lia).
        apply lseq_range in Hin.
        rewrite (lsum_ext _ (fun _ => 0)) by (intros l Hl; destruct (Z.ltb_spec v l); lia).
        rewrite lsum_zero. split; intros; lia.
Qed.

(** ** Part 3: the invariant of the repair loop *)

(** [psum v c]: the number of lengths <= v. *)
Definition psum (v : Z) (c : list Z) : Z := lsum (fun l => if l <=? v then Znth l c else 0) 15.

(** [rmass bt c]: the Kraft mass of the levels strictly between bt and 15. *)
Definition rmass (bt : Z) (c : list Z) : Z :=
  lsum (fun l => if (bt <? l) && (l <? 15) then Znth l c * 2 ^ (15 - l) else 0) 15.

(** With J iterations to go from the initial counts c0, bt the smallest level split so far (15 before any). *)
Definition rbinv (c0 : list Z) (J bt : Z) (c : list Z) : Prop :=
  rinv 15 J c /\ tot 15 c = tot 15 c0 /\ (1 <= bt <= 15) /\
  (forall v, 1 <= v <= bt -> v <= 14 -> psum v c <= psum v c0) /\
  rmass bt c <= 2 ^ (15 - bt) /\ (bt < 15 -> 2 ^ (15 - bt) + 2 <= tot 15 c0).

Lemma rb_lsum_scale : forall a g k, lsum (fun l => a * g l) k = a * lsum g k.
Proof. intros a g k; induction k as [|k IH]; [simpl; ring|]. rewrite !lsum_S, IH. ring. Qed.

(** A split at level b (levels b+1..14 empty) needs c_15 >= 2^(15-b) + J + 1, so the total is >= 2^(15-b) + 2. *)
(* Sums over the levels are rewritten with the bound abstracted ([Z.of_nat k = 15]): with the literal bound the
   kernel's re-check of the same steps takes minutes. *)
Lemma rb_split_gen : forall (a : Z) (g h : Z -> Z) (c15 : Z) (k : nat), Z.of_nat k = 15 ->
  (forall l, 1 <= l <= 15 -> h l = a * g l + (if l =? 15 then c15 else 0)) -> lsum h k = a * lsum g k + c15.
Proof.
  intros a g h c15 k Hk H. rewrite (lsum_ext h (fun l => a * g l + (if l =? 15 then c15 else 0)))
    by (intros l Hl; apply H; lia).
  rewrite lsum_add, rb_lsum_scale, lsum_point, Hk. reflexivity.
Qed.

Lemma rb_kraft_split : forall c b, 1 <= b <= 14 -> (forall l, b < l <= 15 - 1 -> Znth l c = 0) ->
  kraftc 15 c = 2 ^ (15 - b) * lsum (fun l => if l <=? b then Znth l c * 2 ^ (b - l) else 0) (Z.to_nat 15)
                + Znth 15 c.
Proof.
  intros c b Hb Hz. unfold kraftc. apply rb_split_gen; [reflexivity|].
  intros l Hl.
  destruct (Z.leb_spec l b) as [H1|H1]; destruct (Z.eqb_spec l 15) as [H2|H2].
  - lia.
  - replace (15 - l) with ((15 - b) + (b - l)) by lia. rewrite Z.pow_add_r by lia. ring.
  - subst l. rewrite Z.sub_diag, Z.pow_0_r. ring.
  - rewrite Hz by lia. ring.
Qed.

Lemma rb_tot2_gen : forall (h : Z -> Z) b (k : nat), Z.of_nat k = 15 -> 1 <= b <= 14 ->
  (forall l, 1 <= l <= 15 -> 0 <= h l) -> h b + h 15 <= lsum h k.
Proof.
  intros h b k Hk Hb Hnn.
  transitivity (lsum (fun l => (if l =? b then h b else 0) + (if l =? 15 then h 15 else 0)) k).
  - rewrite lsum_add, !lsum_point, Hk.
    destruct (Z.leb_spec 1 b), (Z.leb_spec b 15); try lia. reflexivity.
  - apply lsum_le. intros l Hl. assert (Hl' : 1 <= l <= 15) by lia.
    specialize (Hnn l Hl'). destruct (Z.eqb_spec l b), (Z.eqb_spec l 15); subst; lia.
Qed.

Lemma rb_tot2 : forall c b, 1 <= b <= 14 -> (forall l, 1 <= l <= 15 -> 0 <= Znth l c) ->
  Znth b c + Znth 15 c <= tot 15 c.
Proof.
  intros c b Hb Hnn. unfold tot. apply (rb_tot2_gen (fun l => Znth l c)); auto.
Qed.

(** A split at level b (levels b+1..14 empty) needs c_15 >= 2^(15-b) + J + 1, so the total is >= 2^(15-b) + 2. *)
Lemma rb_room : forall J c b, 0 <= J -> rinv 15 (J + 1) c -> 1 <= b <= 14 -> 0 < Znth b c ->
  (forall l, b < l <= 15 - 1 -> Znth l c = 0) -> 2 ^ (15 - b) + 2 <= tot 15 c.
Proof.
  intros J c b HJ Hinv Hb Hcb Hz.
  destruct Hinv as [Hlen [Hnn [Htot [Htot' [Hk HcM]]]]].
  rewrite (rb_kraft_split c b Hb Hz) in Hk.
  assert (Ht := rb_tot2 c b Hb Hnn).
  generalize dependent (lsum (fun l => if l <=? b then Znth l c * 2 ^ (b - l) else 0) (Z.to_nat 15)).
  intros Q Hk.
  assert (HA : 0 < 2 ^ (15 - b)) by (apply Z.pow_pos_nonneg; lia).
  assert (HB : 2 ^ 15 = 2 ^ (15 - b) * 2 ^ b) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (H2 : 2 <= 2 ^ (15 - b)).
  { replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
  generalize dependent (2 ^ (15 - b)). generalize dependent (2 ^ b). intros B A HB HA Hk H2.
  change (2 ^ 15) with 32768 in *.
  assert (HQ : A * Q <= A * (B - 1)).
  { assert (Q < B) by nia. apply Z.mul_le_mono_nonneg_l; lia. }
  nia.
Qed.

(** The Kraft mass of the levels between x and 15 after a split at level b. *)
Lemma rmass_rstep_at : forall J c b x, 0 <= J -> rinv 15 (J + 1) c -> 1 <= b <= 14 -> 0 < Znth b c ->
  rmass x (rstep_at 15 c b) = rmass x c + (if (x <? b + 1) && (b + 1 <? 15) then 2 ^ (15 - b) else 0) -
                              (if (x <? b) && (b <? 15) then 2 ^ (15 - b) else 0).
Proof.
  intros J c b x HJ Hinv Hb Hcb.
  destruct (rstep_at_Znth 15 J c ltac:(lia) HJ Hinv b ltac:(lia) Hcb) as [_ HZ].
  assert (Hp : 2 ^ (15 - b) = 2 * 2 ^ (15 - (b + 1))).
  { replace (15 - b) with (Z.succ (15 - (b + 1))) by lia. apply Z.pow_succ_r. lia. }
  unfold rmass. assert (Hk : Z.of_nat 15%nat = 15) by reflexivity. revert Hk. generalize 15%nat. intros k Hk.
  rewrite (lsum_ext _ (fun l => (if (x <? l) && (l <? 15) then Znth l c * 2 ^ (15 - l) else 0) +
     ((if l =? b + 1 then (if (x <? b + 1) && (b + 1 <? 15) then 2 ^ (15 - b) else 0) else 0) +
      (if l =? b then (if (x <? b) && (b <? 15) then - 2 ^ (15 - b) else 0) else 0)))).
  2:{ intros l Hl. rewrite HZ by lia.
      destruct (Z.eqb_spec l 15) as [E3|E3].
      { subst l. rewrite Z.ltb_irrefl, !andb_false_r.
        replace (15 =? b) with false by (symmetry; apply Z.eqb_neq; lia).
        destruct (Z.eqb_spec 15 (b + 1)) as [E|E]; [rewrite <- E, Z.ltb_irrefl, andb_false_r|]; ring. }
      destruct (Z.eqb_spec l b) as [E1|E1]; destruct (Z.eqb_spec l (b + 1)) as [E2|E2]; try lia.
      - subst l. destruct ((x <? b) && (b <? 15)); ring.
      - subst l. destruct ((x <? b + 1) && (b + 1 <? 15)); [rewrite Hp|]; ring.
      - destruct ((x <? l) && (l <? 15)); ring. }
  rewrite !lsum_add, !lsum_point, Hk.
  destruct (Z.leb_spec 1 b), (Z.leb_spec b 15), (Z.leb_spec 1 (b + 1)),
    (Z.leb_spec (b + 1) 15); try lia; simpl.
  destruct ((x <? b + 1) && (b + 1 <? 15)), ((x <? b) && (b <? 15)); lia.
Qed.

(** One iteration keeps the invariant, with the smallest split level updated. *)
Lemma rb_step : forall J c0 bt c, 0 <= J -> rbinv c0 (J + 1) bt c ->
  exists bt', bt' <= 14 /\ rbinv c0 J bt' (rstep 15 c).
Proof.
  intros J c0 bt c HJ [Hinv [Htot [Hbt [Hps [Hrm Hroom]]]]].
  destruct (step_level 15 J c ltac:(lia) HJ Hinv) as [b [Eb [Hb [Hcb Hz]]]].
  unfold rstep. rewrite Eb.
  destruct (rstep_at_Znth 15 J c ltac:(lia) HJ Hinv b Hb Hcb) as [_ HZ].
  assert (HA : 0 < 2 ^ (15 - b)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hr0 : rmass b c = 0).
  { unfold rmass. transitivity (lsum (fun _ => 0) 15); [|apply lsum_zero].
    apply lsum_ext. intros l Hl. destruct (Z.ltb_spec b l), (Z.ltb_spec l 15); simpl; try reflexivity.
    rewrite Hz by lia. ring. }
  exists (Z.min bt b). split; [lia|].
  split; [apply (rstep_at_inv 15 J c); auto; lia|].
  split; [rewrite (rstep_at_tot 15 J c); auto; lia|].
  split; [lia|].
  split.
  { intros v Hv Hv14. eapply Z.le_trans; [|apply Hps; lia]. unfold psum. apply lsum_le.
    intros l Hl. destruct (Z.leb_spec l v); [|lia]. rewrite HZ by lia.
    destruct (Z.eqb_spec l b); destruct (Z.eqb_spec l (b + 1)); destruct (Z.eqb_spec l 15); lia. }
  split.
  { rewrite (rmass_rstep_at J c b) by auto.
    destruct (Z.ltb_spec b bt).
    - rewrite Z.min_r by lia. rewrite Hr0.
      destruct (Z.ltb_spec b (b + 1)), (Z.ltb_spec (b + 1) 15), (Z.ltb_spec b b), (Z.ltb_spec b 15);
        cbn [andb]; lia.
    - rewrite Z.min_l by lia. destruct (Z.eq_dec bt b) as [->|Hne].
      + rewrite Hr0. destruct (Z.ltb_spec b (b + 1)), (Z.ltb_spec (b + 1) 15), (Z.ltb_spec b b);
          cbn [andb]; lia.
      + assert (HA' : 0 < 2 ^ (15 - bt)) by (apply Z.pow_pos_nonneg; lia).
        destruct (Z.ltb_spec bt (b + 1)), (Z.ltb_spec (b + 1) 15), (Z.ltb_spec bt b), (Z.ltb_spec b 15);
          cbn [andb]; lia. }
  intros Hlt. destruct (Z.ltb_spec b bt).
  - rewrite Z.min_r by lia. rewrite <- Htot. apply (rb_room J c b); auto.
  - rewrite Z.min_l in * by lia. apply Hroom; lia.
Qed.

Lemma rb_iter : forall (J : nat) K c0 c bt, 0 <= K -> rbinv c0 (Z.of_nat J + K) bt c ->
  exists bt', rbinv c0 K bt' (Nat.iter J (rstep 15) c) /\ ((0 < J)%nat -> bt' < 15).
Proof.
  intros J; induction J as [|J IH]; intros K c0 c bt HK H.
  - exists bt. split; [|lia]. simpl. replace K with (Z.of_nat 0 + K) by lia. exact H.
  - destruct (IH (K + 1) c0 c bt ltac:(lia)) as [bt1 [H1 _]].
    { replace (Z.of_nat J + (K + 1)) with (Z.of_nat (S J) + K) by lia. exact H. }
    destruct (rb_step K c0 bt1 (Nat.iter J (rstep 15) c) HK H1) as [bt' [Hle H2]].
    exists bt'. split; [exact H2|lia].
Qed.

(** ** The assembly: the ratio, the gains, the losses and the assembly *)

Definition ratio_chk : bool :=
  forallb (fun a => forallb (fun b => (Z.of_nat b <=? Z.of_nat a) ||
    (540 * (Z.of_nat b - Z.of_nat a) <=? fib (Z.of_nat a + 1) * (2 ^ (15 - Z.of_nat a) - 2 ^ (15 - Z.of_nat b))))
    (seq 1 15)) (seq 1 15).

Lemma ratio_chk_true : ratio_chk = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ratio_ok : forall x y, 1 <= x < y -> y <= 15 ->
  540 * (y - x) <= fib (x + 1) * (2 ^ (15 - x) - 2 ^ (15 - y)).
Proof.
  intros x y Hxy Hy. assert (H := ratio_chk_true). unfold ratio_chk in H.
  rewrite forallb_forall in H. specialize (H (Z.to_nat x) ltac:(apply in_seq; lia)).
  rewrite forallb_forall in H. specialize (H (Z.to_nat y) ltac:(apply in_seq; lia)).
  rewrite !Z2Nat.id in H by lia. apply orb_true_iff in H. destruct H as [H|H]; [apply Z.leb_le in H; lia|].
  apply Z.leb_le in H. exact H.
Qed.

Lemma pt_bound : forall fk dk L W, 0 <= fk -> 1 <= dk -> 1 <= L <= 15 -> fib (dk + 1) * fk <= W ->
  540 * (fk * Z.max 0 (L - dk)) <= W * Z.max 0 (2 ^ (15 - Z.min dk 15) - 2 ^ (15 - L)).
Proof.
  intros fk dk L W Hf Hd HL Hc.
  assert (HF : 1 <= fib (dk + 1)) by (apply fib_pos; lia).
  assert (HW : 0 <= W) by nia.
  destruct (Z.le_gt_cases L dk) as [Hle|Hgt].
  - rewrite (Z.max_l 0 (L - dk)) by lia. rewrite Z.mul_0_r, Z.mul_0_r.
    apply Z.mul_nonneg_nonneg; lia.
  - rewrite Z.min_l by lia. rewrite (Z.max_r 0 (L - dk)) by lia.
    assert (Hp : 2 ^ (15 - L) <= 2 ^ (15 - dk)) by (apply Z.pow_le_mono_r; lia).
    rewrite (Z.max_r 0) by lia.
    assert (Hr := ratio_ok dk L ltac:(lia) ltac:(lia)).
    set (g := 2 ^ (15 - dk) - 2 ^ (15 - L)) in *.
    assert (0 <= g) by lia.
    assert (fk * (540 * (L - dk)) <= fk * (fib (dk + 1) * g)) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (fib (dk + 1) * fk * g <= W * g) by (apply Z.mul_le_mono_nonneg_r; lia).
    nia.
Qed.

(** The gains and the losses of the Kraft mass, per position. *)
Fixpoint gsum (L d : list Z) : Z :=
  match L, d with
  | y :: L', z :: d' => Z.max 0 (2 ^ (15 - Z.min z 15) - 2 ^ (15 - y)) + gsum L' d'
  | _, _ => 0
  end.

Fixpoint losum (L d : list Z) : Z :=
  match L, d with
  | y :: L', z :: d' => Z.max 0 (2 ^ (15 - y) - 2 ^ (15 - Z.min z 15)) + losum L' d'
  | _, _ => 0
  end.

Lemma dpl_gsum : forall W f L d, length f = length d -> length L = length d ->
  (forall x, In x L -> 1 <= x <= 15) -> (forall x, In x d -> 1 <= x) ->
  (forall k, (k < length d)%nat -> 1 <= nth k f 0 /\ fib (nth k d 0 + 1) * nth k f 0 <= W) ->
  540 * dpl f L d <= W * gsum L d.
Proof.
  intros W f L d; revert f L; induction d as [|z d IH]; intros [|a f] [|y L] Hf HL HLr Hd Hc;
    simpl in Hf, HL; try lia; cbn [dpl gsum]; [lia|].
  destruct (Hc O ltac:(simpl; lia)) as [H1 H2]. cbn [nth] in H1, H2.
  assert (Hp := pt_bound a z y W ltac:(lia) ltac:(apply Hd; left; auto) ltac:(apply HLr; left; auto) H2).
  assert (IH' := IH f L ltac:(lia) ltac:(lia) ltac:(intros; apply HLr; right; auto)
                   ltac:(intros; apply Hd; right; auto)
                   ltac:(intros k Hk; apply (Hc (S k)); simpl; lia)).
  lia.
Qed.

Lemma gsum_split : forall L d, length L = length d ->
  gsum L d = sumz (map (fun z => 2 ^ (15 - Z.min z 15)) d) - sumz (map (fun y => 2 ^ (15 - y)) L) + losum L d.
Proof.
  induction L as [|y L IH]; intros [|z d] H; simpl in H; try lia; [reflexivity|].
  cbn [gsum losum map sumz]. rewrite IH by lia. lia.
Qed.

Lemma losum_le : forall bt L d, length L = length d ->
  (forall x, In x L -> 1 <= x <= 15) -> (forall x, In x d -> 1 <= x) ->
  (forall k, (k < length d)%nat -> nth k L 0 < Z.min (nth k d 0) 15 -> bt < nth k L 0) ->
  losum L d <= sumz (map (fun y => if (bt <? y) && (y <? 15) then 2 ^ (15 - y) else 0) L).
Proof.
  intros bt; induction L as [|y L IH]; intros [|z d] Hl HL Hd Hst; simpl in Hl; try lia; [simpl; lia|].
  cbn [losum map sumz].
  assert (IH' := IH d ltac:(lia) ltac:(intros; apply HL; right; auto) ltac:(intros; apply Hd; right; auto)
                   ltac:(intros k Hk; apply (Hst (S k)); simpl; lia)).
  assert (Hy := HL y (or_introl eq_refl)). assert (Hz := Hd z (or_introl eq_refl)).
  enough (Z.max 0 (2 ^ (15 - y) - 2 ^ (15 - Z.min z 15)) <= (if (bt <? y) && (y <? 15) then 2 ^ (15 - y) else 0))
    by lia.
  assert (0 <= 2 ^ (15 - Z.min z 15)) by (apply Z.pow_nonneg; lia).
  destruct (Z.lt_ge_cases y (Z.min z 15)) as [Hlt|Hge].
  - specialize (Hst O ltac:(simpl; lia) Hlt). cbn [nth] in Hst.
    replace ((bt <? y) && (y <? 15)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
    lia.
  - assert (2 ^ (15 - y) <= 2 ^ (15 - Z.min z 15)) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.max_l by lia. destruct ((bt <? y) && (y <? 15)); [apply Z.pow_nonneg; lia|lia].
Qed.

Lemma lseq_wsum : forall g c K, (forall l, 1 <= l <= Z.of_nat K -> 0 <= Znth l c) ->
  sumz (map g (lseq c K)) = lsum (fun l => Znth l c * g l) K.
Proof.
  intros g c K; induction K as [|K IH]; intros H; [reflexivity|].
  cbn [lseq]. rewrite map_app, sumz_app, lsum_S, map_repeat, sumz_repeat. rewrite IH by (intros; apply H; lia).
  rewrite Z2Nat.id by (apply H; lia). lia.
Qed.

Lemma upper_psum : forall v c, lsum (fun l => if v <? l then Znth l c else 0) 15 = tot 15 c - psum v c.
Proof.
  intros v c. unfold tot, psum.
  replace (Z.to_nat 15) with 15%nat by reflexivity.
  rewrite <- (Z.add_simpl_r (lsum (fun l => if v <? l then Znth l c else 0) 15)
               (lsum (fun l => if l <=? v then Znth l c else 0) 15)).
  rewrite <- lsum_add. f_equal. apply lsum_ext. intros l _.
  destruct (Z.ltb_spec v l), (Z.leb_spec l v); lia.
Qed.

Lemma static_pos : forall c0 c bt k,
  (forall l, 1 <= l <= 15 -> 0 <= Znth l c0) -> (forall l, 1 <= l <= 15 -> 0 <= Znth l c) ->
  tot 15 c = tot 15 c0 -> (forall v, 1 <= v <= bt -> v <= 14 -> psum v c <= psum v c0) ->
  (k < length (lseq c0 15))%nat -> (k < length (lseq c 15))%nat ->
  nth k (lseq c 15) 0 < nth k (lseq c0 15) 0 -> bt < nth k (lseq c 15) 0.
Proof.
  intros c0 c bt k H0 H1 Ht Hp Hk0 Hk Hlt.
  set (v := nth k (lseq c 15) 0) in *.
  assert (Hv : 1 <= v <= 15) by (apply (lseq_range c 15); apply nth_In; auto).
  assert (Hv0 : nth k (lseq c0 15) 0 <= 15) by (apply (lseq_range c0 15); apply nth_In; auto).
  destruct (Z.lt_ge_cases bt v) as [|Hle]; [auto|exfalso].
  assert (A := proj1 (lseq_nth_gt 15 c0 k v ltac:(intros; apply H0; lia) Hk0) Hlt).
  assert (B : ~ (Z.of_nat k < lsum (fun l => if v <? l then Znth l c else 0) 15)).
  { intro HB. apply (proj2 (lseq_nth_gt 15 c k v ltac:(intros; apply H1; lia) Hk)) in HB. fold v in HB. lia. }
  rewrite upper_psum in A, B. specialize (Hp v ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma dpl_min : forall f d, dpl f (map (fun x => Z.min x 15) d) d = 0.
Proof.
  intros f d; revert f; induction d as [|z d IH]; intros [|a f]; cbn [map dpl]; auto.
  rewrite IH. rewrite Z.max_l by lia. ring.
Qed.

Lemma classic_deep : forall d, (exists x, In x d /\ 15 < x) \/ ~ (exists x, In x d /\ 15 < x).
Proof.
  induction d as [|z d [IH|IH]].
  - right. intros [x [[] _]].
  - left. destruct IH as [x [H1 H2]]. exists x; split; [right|]; auto.
  - destruct (Z.lt_ge_cases 15 z).
    + left. exists z; split; [left|]; auto.
    + right. intros [x [[<-|Hx] Hlt]]; [lia|]. apply IH; eauto.
Qed.

Lemma rmass_15 : forall c, rmass 15 c = 0.
Proof.
  intros c. unfold rmass. rewrite (lsum_ext _ (fun _ => 0)); [apply lsum_zero|].
  intros l Hl. destruct (Z.ltb_spec 15 l); simpl; [lia|reflexivity].
Qed.

Lemma W_nonneg : forall f d W, length f = length d -> (forall x, In x d -> 1 <= x) ->
  (forall k, (k < length d)%nat -> 1 <= nth k f 0 /\ fib (nth k d 0 + 1) * nth k f 0 <= W) ->
  d <> [] -> 0 <= W.
Proof.
  intros f d W Hlf Hd1 Hcap Hne. destruct d as [|z d']; [congruence|].
  destruct (Hcap O ltac:(simpl; lia)) as [H1 H2]. cbn [nth] in H1, H2.
  assert (1 <= fib (z + 1)) by (apply fib_pos; assert (1 <= z) by (apply Hd1; left; auto); lia).
  nia.
Qed.

Lemma repair15_shallow : forall (f d : list Z) (W D : Z),
  length f = length d -> dsorted d ->
  15 <= D -> (forall x, In x d -> 1 <= x <= D) -> sumz (map (fun x => 2 ^ (D - x)) d) = 2 ^ D ->
  (forall k, (k < length d)%nat -> 1 <= nth k f 0 /\ fib (nth k d 0 + 1) * nth k f 0 <= W) ->
  ~ (exists x, In x d /\ 15 < x) ->
  length (repl 15 d) = length d /\ 540 * dpl f (repl 15 d) d <= 2 * Z.of_nat (length d) * W.
Proof.
  intros f d W D Hlf Hs HD Hd Hk Hcap Hshallow.
  assert (Hd1 : forall x, In x d -> 1 <= x) by (intros x Hx; specialize (Hd x Hx); lia).
  assert (Hle : forall x, In x d -> x <= 15)
    by (intros x Hin; destruct (Z.le_gt_cases x 15); auto; exfalso; apply Hshallow; eauto).
  destruct (clamp_sums 15 d ltac:(lia) Hd1) as [Hkc _].
  assert (Hx : lens 15 (clampc 15 d) = map (fun x => Z.min x 15) d) by (apply lseq_clampc; auto).
  assert (Hk15 : kraftc 15 (clampc 15 d) = 2 ^ 15).
  { rewrite Hkc.
    assert (E : sumz (map (fun x => 2 ^ (15 - Z.min x 15)) d) = sumz (map (fun x => 2 ^ (15 - x)) d)).
    { f_equal. apply map_ext_in. intros x Hin. rewrite Z.min_l; auto. }
    rewrite E. apply (Z.mul_reg_l _ _ (2 ^ (D - 15))); [apply Z.pow_nonzero; lia|].
    rewrite <- sumz_scale, <- Z.pow_add_r by lia. replace (D - 15 + 15) with D by lia. rewrite <- Hk.
    f_equal. apply map_ext_in. intros x Hin. specialize (Hd x Hin). specialize (Hle x Hin).
    rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hrepl : repl 15 d = map (fun x => Z.min x 15) d).
  { unfold repl. rewrite Hk15, Z.sub_diag. change (Z.to_nat 0) with O. cbn [Nat.iter]. exact Hx. }
  rewrite Hrepl, length_map, dpl_min. split; [reflexivity|].
  destruct d as [|z d']; [simpl; lia|].
  assert (0 <= W) by (apply (W_nonneg f (z :: d')); auto; congruence). nia.
Qed.

Lemma repair15_deep : forall (f d : list Z) (W D : Z),
  length f = length d -> (length d <= 286)%nat -> dsorted d ->
  15 <= D -> (forall x, In x d -> 1 <= x <= D) -> sumz (map (fun x => 2 ^ (D - x)) d) = 2 ^ D ->
  (forall k, (k < length d)%nat -> 1 <= nth k f 0 /\ fib (nth k d 0 + 1) * nth k f 0 <= W) ->
  (exists x, In x d /\ 15 < x) ->
  length (repl 15 d) = length d /\ 540 * dpl f (repl 15 d) d <= 2 * Z.of_nat (length d) * W.
Proof.
  intros f d W D Hlf Hn Hs HD Hd Hk Hcap Hdeep.
  assert (Hd1 : forall x, In x d -> 1 <= x) by (intros x Hx; specialize (Hd x Hx); lia).
  assert (HZd : Zlength d = Z.of_nat (length d)) by apply Zlength_correct.
  assert (HW0 : 0 <= W).
  { apply (W_nonneg f d); auto. intro E. subst d. destruct Hdeep as [x [[] _]]. }
  destruct (clamp_sums 15 d ltac:(lia) Hd1) as [Hkc Htc].
  assert (Hx : lens 15 (clampc 15 d) = map (fun x => Z.min x 15) d) by (apply lseq_clampc; auto).
  destruct (clamp_rinv 15 D d ltac:(lia) HD Hd Hk ltac:(rewrite HZd; simpl; lia) ltac:(lia) Hdeep) as [HI Hinv].
  unfold repl.
  remember (clampc 15 d) as c0 eqn:Ec0.
  remember (kraftc 15 c0 - 2 ^ 15) as I eqn:EI.
  assert (Hstart : rbinv c0 (Z.of_nat (Z.to_nat I) + 0) 15 c0).
  { rewrite Z.add_0_r, Z2Nat.id by lia. split; [exact Hinv|]. split; [reflexivity|]. split; [lia|].
    split; [intros; lia|]. rewrite rmass_15. split; [simpl; lia|]. lia. }
  destruct (rb_iter (Z.to_nat I) 0 c0 c0 15 ltac:(lia) Hstart) as [bt [Hrb Hbt]].
  specialize (Hbt ltac:(lia)).
  remember (Nat.iter (Z.to_nat I) (rstep 15) c0) as c' eqn:Ec'.
  destruct Hrb as [[Hlen' [Hnn' [_ [_ [Hk' _]]]]] [Ht' [Hbt1 [Hps [Hrm Hroom]]]]].
  specialize (Hroom Hbt).
  destruct Hinv as [_ [Hnn0 [_ [_ [_ HI15]]]]].
  assert (H15 : Znth 15 c0 <= tot 15 c0) by (apply count_le_tot; auto; lia).
  change (lens 15 c') with (lseq c' 15). change (lens 15 c0) with (lseq c0 15) in Hx.
  assert (Hly : length (lseq c' 15) = length d).
  { rewrite lseq_length_nat by (intros l0 Hl0; apply Hnn'; change (Z.of_nat 15) with 15 in Hl0; lia).
    assert (E : tot 15 c' = lsum (fun l => Znth l c') 15) by (unfold tot; reflexivity). lia. }
  split; [exact Hly|].
  assert (Hyr : forall x, In x (lseq c' 15) -> 1 <= x <= 15) by (intros x Hin; apply lseq_range in Hin; lia).
  assert (Hdpl := dpl_gsum W f (lseq c' 15) d Hlf Hly Hyr Hd1 Hcap).
  rewrite gsum_split in Hdpl by exact Hly.
  assert (Hky : sumz (map (fun y => 2 ^ (15 - y)) (lseq c' 15)) = 2 ^ 15).
  { rewrite lseq_kraft by (intros l0 Hl0; apply Hnn'; change (Z.of_nat 15) with 15 in Hl0; lia).
    assert (E : kraftc 15 c' = lsum (fun l => Znth l c' * 2 ^ (15 - l)) 15) by (unfold kraftc; reflexivity).
    lia. }
  assert (Hlo : losum (lseq c' 15) d <=
                sumz (map (fun y => if (bt <? y) && (y <? 15) then 2 ^ (15 - y) else 0) (lseq c' 15))).
  { apply losum_le; auto. intros k Hk1 Hlt.
    assert (Hxk : Z.min (nth k d 0) 15 = nth k (lseq c0 15) 0).
    { rewrite Hx. rewrite <- (map_nth (fun x => Z.min x 15) d 0 k). apply nth_indep.
      rewrite length_map; auto. }
    rewrite Hxk in Hlt.
    apply (static_pos c0 c' bt k); auto; try (intros; apply Hnn0 || apply Hnn'; lia).
    - rewrite Hx, length_map; auto.
    - lia. }
  rewrite lseq_wsum in Hlo by (intros l0 Hl0; apply Hnn'; change (Z.of_nat 15) with 15 in Hl0; lia).
  replace (lsum (fun l => Znth l c' * (if (bt <? l) && (l <? 15) then 2 ^ (15 - l) else 0)) 15)
    with (rmass bt c') in Hlo.
  2:{ unfold rmass. apply lsum_ext. intros l _. destruct ((bt <? l) && (l <? 15)); ring. }
  assert (Hg : sumz (map (fun z => 2 ^ (15 - Z.min z 15)) d) - sumz (map (fun y => 2 ^ (15 - y)) (lseq c' 15))
               + losum (lseq c' 15) d <= 2 * Z.of_nat (length d)) by lia.
  assert (W * (sumz (map (fun z => 2 ^ (15 - Z.min z 15)) d) - sumz (map (fun y => 2 ^ (15 - y)) (lseq c' 15))
               + losum (lseq c' 15) d) <= W * (2 * Z.of_nat (length d)))
    by (apply Z.mul_le_mono_nonneg_l; lia).
  lia.
Qed.

Theorem repair15_bound : repair15_statement.
Proof.
  intros f d W D Hlf Hn Hs HD Hd Hk Hcap.
  destruct (classic_deep d) as [Hdeep|Hshallow].
  - apply (repair15_deep f d W D); auto.
  - apply (repair15_shallow f d W D); auto.
Qed.
