(** * Abstract Huffman merging: Kraft equality, cost, optimality, Fibonacci bound

    A pool is a list of items; an item is a list of leaves [(id, f, d)] (identifier, frequency, depth below the
    item's root).  A greedy step removes two items [a], [b] of least weights (a minimal, b minimal among the
    others) and adds their merge (all depths plus one).  [huff P R]: the pool [P] reduces to the single item
    [R] by greedy steps.  zlib's build_tree performs such steps (proved elsewhere); here: the Kraft equality of
    the final depths, the cost identity, optimality against every code satisfying the Kraft inequality, and the
    Fibonacci bound [fib (d+1) * f <= weight R] for a leaf at depth [d]. *)

From Coq Require Import ZArith List Lia Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Definition leaf := (Z * Z * Z)%type.   (* id, frequency, depth *)
Definition lid (x : leaf) : Z := fst (fst x).
Definition lf (x : leaf) : Z := snd (fst x).
Definition ld (x : leaf) : Z := snd x.

Definition item := list leaf.

Fixpoint sumZ (l : list Z) : Z := match l with [] => 0 | x :: r => x + sumZ r end.

Definition weight (I : item) : Z := sumZ (map lf I).
Definition cost (I : item) : Z := sumZ (map (fun x => lf x * ld x) I).

Definition deeper (x : leaf) : leaf := (fst x, ld x + 1).
Definition merge (a b : item) : item := map deeper (a ++ b).

Inductive huff : list item -> item -> Prop :=
| huff_one : forall I, huff [I] I
| huff_step : forall P a b rest R,
    Permutation P (a :: b :: rest) ->
    (forall J, In J (b :: rest) -> weight a <= weight J) ->
    (forall J, In J rest -> weight b <= weight J) ->
    huff (merge a b :: rest) R ->
    huff P R.

(** ** Basic list facts *)

Lemma sumZ_app : forall l1 l2, sumZ (l1 ++ l2) = sumZ l1 + sumZ l2.
Proof. induction l1; simpl; intros; [lia | rewrite IHl1; lia]. Qed.

Lemma sumZ_perm : forall l1 l2, Permutation l1 l2 -> sumZ l1 = sumZ l2.
Proof. intros l1 l2 H; induction H; simpl; lia. Qed.

Lemma sumZ_le : forall {A} (f g : A -> Z) l, (forall x, In x l -> f x <= g x) ->
  sumZ (map f l) <= sumZ (map g l).
Proof.
  intros A f g l; induction l as [|x r IH]; simpl; intros H; [lia|].
  specialize (IH (fun y Hy => H y (or_intror Hy))). specialize (H x (or_introl eq_refl)). lia.
Qed.

Lemma sumZ_nonneg : forall {A} (f : A -> Z) l, (forall x, In x l -> 0 <= f x) -> 0 <= sumZ (map f l).
Proof.
  intros A f l; induction l as [|x r IH]; simpl; intros H; [lia|].
  specialize (IH (fun y Hy => H y (or_intror Hy))). specialize (H x (or_introl eq_refl)). lia.
Qed.

Lemma weight_app : forall a b, weight (a ++ b) = weight a + weight b.
Proof. intros; unfold weight; rewrite map_app, sumZ_app; lia. Qed.

Lemma weight_map_deeper : forall a, weight (map deeper a) = weight a.
Proof. intros; unfold weight; rewrite map_map; reflexivity. Qed.

Lemma weight_merge : forall a b, weight (merge a b) = weight a + weight b.
Proof. intros; unfold merge; rewrite weight_map_deeper, weight_app; reflexivity. Qed.

Lemma cost_app : forall a b, cost (a ++ b) = cost a + cost b.
Proof. intros; unfold cost; rewrite map_app, sumZ_app; lia. Qed.

Lemma cost_map_deeper : forall a, cost (map deeper a) = cost a + weight a.
Proof.
  induction a as [|x r IH]; [reflexivity|].
  unfold cost, weight in *; simpl. unfold deeper, lf, ld in *; simpl in *. rewrite IH. lia.
Qed.

Lemma cost_merge : forall a b, cost (merge a b) = cost a + cost b + weight a + weight b.
Proof. intros; unfold merge; rewrite cost_map_deeper, cost_app, weight_app; lia. Qed.

Lemma in_merge : forall a b x, In x (merge a b) <-> exists y, x = deeper y /\ (In y a \/ In y b).
Proof.
  intros; unfold merge; rewrite in_map_iff; split.
  - intros [y [<- Hy]]; exists y; split; auto; apply in_app_or; auto.
  - intros [y [-> Hy]]; exists y; split; auto; apply in_or_app; auto.
Qed.

(** ** Pools: invariants preserved along a greedy reduction *)

(** A property of pools preserved by greedy steps holds at the end. *)
Lemma huff_ind_pool (Inv : list item -> Prop) :
  (forall P Q, Permutation P Q -> Inv P -> Inv Q) ->
  (forall a b rest, (forall J, In J (b :: rest) -> weight a <= weight J) ->
     (forall J, In J rest -> weight b <= weight J) ->
     Inv (a :: b :: rest) -> Inv (merge a b :: rest)) ->
  forall P R, huff P R -> Inv P -> Inv [R].
Proof.
  intros Hperm Hstep P R H; induction H as [I|P a b rest R Hp Ha Hb Hh IH]; intros HP; auto.
  apply IH. apply Hstep; auto. eapply Hperm; eauto.
Qed.

(** Every leaf of the final item comes from a leaf of the pool (with a larger or equal depth), and every pool
    leaf ends in the final item. *)
Definition leaves (P : list item) : list leaf := concat P.

Lemma leaves_perm : forall P Q, Permutation P Q -> Permutation (leaves P) (leaves Q).
Proof.
  intros P Q H; induction H; simpl; auto.
  - apply Permutation_app_head; auto.
  - rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - eapply Permutation_trans; eauto.
Qed.

(** The identifiers and frequencies of the leaves are preserved (only depths change). *)
Definition idf (x : leaf) : Z * Z := fst x.

Lemma map_idf_deeper : forall l, map idf (map deeper l) = map idf l.
Proof. intros; rewrite map_map; reflexivity. Qed.

Lemma huff_idf : forall P R, huff P R -> Permutation (map idf (leaves P)) (map idf R).
Proof.
  intros P R H; induction H as [I|P a b rest R Hp Ha Hb Hh IH].
  - simpl; rewrite app_nil_r; auto.
  - eapply Permutation_trans; [apply Permutation_map, leaves_perm, Hp|].
    eapply Permutation_trans; [|exact IH].
    unfold leaves; simpl. unfold merge. rewrite !map_app, !map_idf_deeper.
    rewrite app_assoc. apply Permutation_refl.
Qed.

(** ** Kraft equality *)

(** [kz D I] = sum over the leaves of 2^(D - depth). *)
Definition kz (D : Z) (I : item) : Z := sumZ (map (fun x => 2 ^ (D - ld x)) I).

Definition depths_ok (D : Z) (I : item) : Prop := forall x, In x I -> 0 <= ld x <= D.

Lemma kz_app : forall D a b, kz D (a ++ b) = kz D a + kz D b.
Proof. intros; unfold kz; rewrite map_app, sumZ_app; lia. Qed.

Lemma kz_map_deeper : forall D a, depths_ok (D - 1) a -> 2 * kz D (map deeper a) = kz D a.
Proof.
  intros D a; induction a as [|x r IH]; intros Hd; [reflexivity|].
  unfold kz in *; cbn [map sumZ]. unfold deeper, ld in *; cbn [fst snd].
  assert (Hx := Hd x (or_introl eq_refl)). unfold ld in Hx.
  rewrite <- IH by (intros y Hy; apply Hd; now right).
  assert (E : 2 ^ (D - snd x) = 2 * 2 ^ (D - (snd x + 1))).
  { replace (D - snd x) with (Z.succ (D - (snd x + 1))) by lia. rewrite Z.pow_succ_r by lia. lia. }
  rewrite E. lia.
Qed.

(** Depths only grow: if the final item has depths in [0, D] and the pool's depths are nonnegative, the
    pool's depths are in [0, D]. *)
Lemma huff_depths : forall P R, huff P R -> forall D,
  (forall I, In I P -> forall x, In x I -> 0 <= ld x) ->
  depths_ok D R -> forall I, In I P -> depths_ok D I.
Proof.
  intros P R H; induction H as [I|P a b rest R Hp Ha Hb Hh IH]; intros D H0 HD J HJ.
  - destruct HJ as [<-|[]]; exact HD.
  - assert (HJ' : In J (a :: b :: rest)) by (eapply Permutation_in; eauto).
    assert (H0' : forall I, In I (merge a b :: rest) -> forall x, In x I -> 0 <= ld x).
    { intros I [<-|HI] x Hx.
      - apply in_merge in Hx; destruct Hx as [y [-> Hy]]. unfold deeper, ld; simpl.
        assert (In y (a ++ b)) by (apply in_or_app; auto).
        assert (Hya : In a P /\ In b P).
        { split; eapply Permutation_in; [apply Permutation_sym; exact Hp| now left|
                                        apply Permutation_sym; exact Hp| right; now left]. }
        destruct Hy as [Hy|Hy]; [specialize (H0 a (proj1 Hya) y Hy)|specialize (H0 b (proj2 Hya) y Hy)];
          unfold ld in H0; lia.
      - apply (H0 I); auto. eapply Permutation_in; [apply Permutation_sym; exact Hp|]. right; right; auto. }
    intros x Hx. split.
    { apply (H0 J); auto. }
    destruct HJ' as [<-|[<-|HJ']].
    + assert (Hm := IH D H0' HD (merge a b) (or_introl eq_refl) (deeper x)).
      assert (In (deeper x) (merge a b)) by (apply in_merge; eauto).
      specialize (Hm H). unfold deeper, ld in *; simpl in *. lia.
    + assert (Hm := IH D H0' HD (merge a b) (or_introl eq_refl) (deeper x)).
      assert (In (deeper x) (merge a b)) by (apply in_merge; eauto).
      specialize (Hm H). unfold deeper, ld in *; simpl in *. lia.
    + exact (proj2 (IH D H0' HD J (or_intror HJ') x Hx)).
Qed.

Theorem huff_kraft : forall P R D, huff P R ->
  (forall I, In I P -> (forall x, In x I -> 0 <= ld x) /\ kz D I = 2 ^ D) ->
  depths_ok D R -> kz D R = 2 ^ D.
Proof.
  intros P R D H; revert D; induction H as [I|P a b rest R Hp Ha Hb Hh IH]; intros D HP HD.
  - apply (HP I (or_introl eq_refl)).
  - assert (Hin : forall J, In J (a :: b :: rest) -> In J P)
      by (intros; eapply Permutation_in; [apply Permutation_sym; exact Hp|auto]).
    assert (H0 : forall I, In I P -> forall x, In x I -> 0 <= ld x) by (intros; eapply HP; eauto).
    assert (Hdab : depths_ok D (merge a b)).
    { assert (H0' : forall I, In I (merge a b :: rest) -> forall x, In x I -> 0 <= ld x).
      { intros I [<-|HI] x Hx.
        - apply in_merge in Hx; destruct Hx as [y [-> [Hy|Hy]]]; unfold deeper, ld; simpl;
            [specialize (H0 a (Hin a (or_introl eq_refl)) y Hy)
            |specialize (H0 b (Hin b (or_intror (or_introl eq_refl))) y Hy)]; unfold ld in H0; lia.
        - apply (H0 I); [apply Hin; right; right; exact HI | exact Hx]. }
      exact (huff_depths _ _ Hh D H0' HD _ (or_introl eq_refl)). }
    apply IH; auto.
    intros I [<-|HI].
    + split.
      * intros x Hx; specialize (Hdab x Hx); lia.
      * assert (Hd1 : depths_ok (D - 1) (a ++ b)).
        { intros y Hy. assert (In (deeper y) (merge a b)) by (apply in_map; auto).
          specialize (Hdab _ H). unfold deeper, ld in *; simpl in *.
          split; [|lia].
          apply in_app_or in Hy; destruct Hy as [Hy|Hy];
            [exact (H0 a (Hin a (or_introl eq_refl)) y Hy)
            |exact (H0 b (Hin b (or_intror (or_introl eq_refl))) y Hy)]. }
        unfold merge. assert (E := kz_map_deeper D (a ++ b) Hd1).
        rewrite kz_app in E.
        rewrite (proj2 (HP a (Hin a (or_introl eq_refl)))) in E.
        rewrite (proj2 (HP b (Hin b (or_intror (or_introl eq_refl))))) in E. lia.
    + apply HP, Hin; right; right; auto.
Qed.


(** ** Optimality against every code satisfying the Kraft inequality *)

(** A code for a pool: each item with a length.  [kq D Q] = sum of 2^(D - l); the Kraft inequality is
    [kq D Q <= 2 ^ D] (lengths in [0, D]); [cq Q] = the cost of the pool's leaves when every item [I] is put at
    depth [l]: sum of [cost I + weight I * l]. *)
Definition kq (D : Z) (Q : list (item * Z)) : Z := sumZ (map (fun p => 2 ^ (D - snd p)) Q).
Definition cq (Q : list (item * Z)) : Z := sumZ (map (fun p => cost (fst p) + weight (fst p) * snd p) Q).
Definition lens_ok (D : Z) (Q : list (item * Z)) : Prop := forall p, In p Q -> 0 <= snd p <= D.

Lemma kq_app : forall D Q1 Q2, kq D (Q1 ++ Q2) = kq D Q1 + kq D Q2.
Proof. intros; unfold kq; rewrite map_app, sumZ_app; lia. Qed.
Lemma cq_app : forall Q1 Q2, cq (Q1 ++ Q2) = cq Q1 + cq Q2.
Proof. intros; unfold cq; rewrite map_app, sumZ_app; lia. Qed.
Lemma kq_perm : forall D Q1 Q2, Permutation Q1 Q2 -> kq D Q1 = kq D Q2.
Proof. intros; unfold kq; apply sumZ_perm, Permutation_map; auto. Qed.
Lemma cq_perm : forall Q1 Q2, Permutation Q1 Q2 -> cq Q1 = cq Q2.
Proof. intros; unfold cq; apply sumZ_perm, Permutation_map; auto. Qed.

Lemma split_gt : forall (Q : list (item * Z)) (l : Z),
  (forall p, In p Q -> snd p <= l) \/
  exists Q1 x lx Q2, Q = Q1 ++ (x, lx) :: Q2 /\ l < lx.
Proof.
  induction Q as [|[x lx] Q IH]; intros l.
  - left; intros p [].
  - destruct (Z_lt_le_dec l lx) as [Hlt|Hle].
    + right; exists [], x, lx, Q; auto.
    + destruct (IH l) as [Hall|[Q1 [y [ly [Q2 [-> Hy]]]]]].
      * left; intros p [<-|Hp]; auto.
      * right; exists ((x, lx) :: Q1), y, ly, Q2; split; auto.
Qed.

(** Swapping the lengths of a lighter item [a] (length [la]) and a heavier item [x] (length [lx > la]) does not
    increase the cost and keeps the Kraft sum. *)
Lemma swap_cost : forall a la x lx Q1 Q2,
  weight a <= weight x -> la <= lx ->
  cq ((a, lx) :: Q1 ++ (x, la) :: Q2) <= cq ((a, la) :: Q1 ++ (x, lx) :: Q2).
Proof.
  intros. unfold cq; cbn [map sumZ]. rewrite !map_app, !sumZ_app; cbn [map sumZ fst snd]. nia.
Qed.

Lemma swap_kq : forall D a la x lx Q1 Q2,
  kq D ((a, lx) :: Q1 ++ (x, la) :: Q2) = kq D ((a, la) :: Q1 ++ (x, lx) :: Q2).
Proof. intros. unfold kq; cbn [map sumZ]. rewrite !map_app, !sumZ_app; cbn [map sumZ fst snd]. lia. Qed.

Lemma lens_ok_swap : forall D a la x lx Q1 Q2,
  lens_ok D ((a, la) :: Q1 ++ (x, lx) :: Q2) -> lens_ok D ((a, lx) :: Q1 ++ (x, la) :: Q2).
Proof.
  intros D a la x lx Q1 Q2 H p Hp.
  assert (Ha := H (a, la) (or_introl eq_refl)).
  assert (Hx := H (x, lx) (or_intror (in_or_app _ _ _ (or_intror (in_eq _ _))))).
  simpl in Ha, Hx.
  destruct Hp as [<-|Hp]; [simpl; lia|].
  apply in_app_or in Hp; destruct Hp as [Hp|[<-|Hp]]; [| simpl; lia |];
    apply H; right; apply in_or_app; [left|right; right]; auto.
Qed.

Lemma divide_sumZ : forall {A} (f : A -> Z) l m, (forall x, In x l -> (m | f x)) -> (m | sumZ (map f l)).
Proof.
  intros A f l m; induction l as [|x r IH]; simpl; intros H.
  - apply Z.divide_0_r.
  - apply Z.divide_add_r; [apply H; auto | apply IH; intros; apply H; auto].
Qed.

Lemma kq_lengths : forall D Q1 Q2, Permutation (map snd Q1) (map snd Q2) -> kq D Q1 = kq D Q2.
Proof.
  intros D Q1 Q2 H. unfold kq.
  replace (map (fun p => 2 ^ (D - snd p)) Q1) with (map (fun l => 2 ^ (D - l)) (map snd Q1))
    by (rewrite map_map; reflexivity).
  replace (map (fun p => 2 ^ (D - snd p)) Q2) with (map (fun l => 2 ^ (D - l)) (map snd Q2))
    by (rewrite map_map; reflexivity).
  apply sumZ_perm, Permutation_map; auto.
Qed.

Lemma map_snd_swap : forall (x : item) (la lx : Z) (Q1 Q2 : list (item * Z)),
  Permutation (la :: map snd (Q1 ++ (x, lx) :: Q2)) (lx :: map snd (Q1 ++ (x, la) :: Q2)).
Proof.
  intros. rewrite !map_app; cbn [map snd].
  transitivity (la :: lx :: (map snd Q1 ++ map snd Q2)).
  { apply perm_skip. apply Permutation_sym, Permutation_middle. }
  transitivity (lx :: la :: (map snd Q1 ++ map snd Q2)). { apply perm_swap. }
  apply perm_skip. apply Permutation_middle.
Qed.

(** Phase 1: lift the length of a lightest item to the maximum. *)
Lemma lift_max : forall (n : nat) D a la T,
  D - la <= Z.of_nat n ->
  (forall p, In p T -> weight a <= weight (fst p)) ->
  lens_ok D ((a, la) :: T) ->
  exists la' T', map fst T' = map fst T /\ (forall p, In p T' -> snd p <= la') /\
    Permutation (la :: map snd T) (la' :: map snd T') /\
    cq ((a, la') :: T') <= cq ((a, la) :: T) /\ lens_ok D ((a, la') :: T').
Proof.
  induction n as [|n IH]; intros D a la T Hn Hw Hl.
  - exists la, T. destruct (split_gt T la) as [Hall|[Q1 [x [lx [Q2 [-> Hx]]]]]].
    + split; [reflexivity|]; split; [exact Hall|]; split; [apply Permutation_refl|]; split; [lia|exact Hl].
    + exfalso. assert (H := Hl (x, lx) (or_intror (in_or_app _ _ _ (or_intror (in_eq _ _))))).
      simpl in H. lia.
  - destruct (split_gt T la) as [Hall|[Q1 [x [lx [Q2 [-> Hx]]]]]].
    + exists la, T; split; [reflexivity|]; split; [exact Hall|]; split; [apply Permutation_refl|];
        split; [lia|exact Hl].
    + assert (Hxl := Hl (x, lx) (or_intror (in_or_app _ _ _ (or_intror (in_eq _ _))))). simpl in Hxl.
      assert (Hwx := Hw (x, lx) (in_or_app _ _ _ (or_intror (in_eq _ _)))). simpl in Hwx.
      destruct (IH D a lx (Q1 ++ (x, la) :: Q2)) as [la' [T' [Hf [Hm [Hp [Hc Hl']]]]]].
      * lia.
      * intros p Hp. apply in_app_or in Hp; destruct Hp as [Hp|[<-|Hp]]; [| simpl; lia |];
          apply Hw; apply in_or_app; [left|right; right]; auto.
      * apply lens_ok_swap; auto.
      * exists la', T'. split; [|split; [exact Hm|split; [|split; [|exact Hl']]]].
        -- rewrite Hf, !map_app; reflexivity.
        -- eapply Permutation_trans; [apply map_snd_swap|exact Hp].
        -- eapply Z.le_trans; [exact Hc|]. apply swap_cost; lia.
Qed.

(** Phase 2: a unique maximal length can be decreased by one, keeping the Kraft inequality. *)
Lemma kraft_lower : forall D a la T,
  (forall p, In p T -> 0 <= snd p < la) -> 1 <= la <= D ->
  kq D ((a, la) :: T) <= 2 ^ D -> kq D ((a, la - 1) :: T) <= 2 ^ D.
Proof.
  intros D a la T HT HD Hk.
  set (u := 2 ^ (D - la)).
  assert (Hu : 0 < u) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdiv : (2 * u | kq D T)).
  { apply divide_sumZ. intros p Hp. specialize (HT p Hp).
    exists (2 ^ (la - 1 - snd p)). unfold u.
    replace (D - snd p) with ((la - 1 - snd p) + (D - la) + 1) by lia.
    rewrite !Z.pow_add_r, Z.pow_1_r by lia. ring. }
  assert (HdD : (2 * u | 2 ^ D)).
  { exists (2 ^ (la - 1)). unfold u. replace D with ((la - 1) + (D - la) + 1) at 1 by lia.
    rewrite !Z.pow_add_r, Z.pow_1_r by lia. ring. }
  destruct Hdiv as [k Hk']. destruct HdD as [m Hm].
  assert (E1 : kq D ((a, la) :: T) = u + kq D T) by reflexivity.
  assert (E2 : kq D ((a, la - 1) :: T) = 2 * u + kq D T).
  { change (kq D ((a, la - 1) :: T)) with (2 ^ (D - (la - 1)) + kq D T). unfold u.
    replace (D - (la - 1)) with (Z.succ (D - la)) by lia. rewrite Z.pow_succ_r by lia. lia. }
  rewrite E1, Hk', Hm in Hk. rewrite E2, Hk', Hm.
  assert (k + 1 <= m) by nia. nia.
Qed.

(** Phase 3: lower the top length down to the next one. *)
Lemma lower_top : forall (n : nat) D a la lb T,
  la - lb <= Z.of_nat n -> 0 <= lb <= la -> la <= D -> 0 <= weight a ->
  (forall p, In p T -> 0 <= snd p <= lb) ->
  kq D ((a, la) :: T) <= 2 ^ D ->
  kq D ((a, lb) :: T) <= 2 ^ D /\ cq ((a, lb) :: T) <= cq ((a, la) :: T).
Proof.
  induction n as [|n IH]; intros D a la lb T Hn Hl HD Hw HT Hk.
  - replace lb with la by lia. split; lia.
  - destruct (Z.eq_dec la lb) as [->|Hne]; [split; lia|].
    assert (Hk' : kq D ((a, la - 1) :: T) <= 2 ^ D).
    { apply kraft_lower; auto; [|lia]. intros p Hp; specialize (HT p Hp); lia. }
    destruct (IH D a (la - 1) lb T) as [H1 H2]; auto; try lia.
    split; auto. eapply Z.le_trans; [exact H2|]. unfold cq; cbn [map sumZ fst snd]. nia.
Qed.

Lemma in_map_fst_eq : forall (Q1 Q2 : list (item * Z)) p, map fst Q1 = map fst Q2 -> In p Q1 ->
  exists q, In q Q2 /\ fst q = fst p.
Proof.
  intros Q1 Q2 p E Hp. assert (In (fst p) (map fst Q2)) by (rewrite <- E; apply in_map; auto).
  apply in_map_iff in H. destruct H as [q [Hq Hin]]; eauto.
Qed.

(** The exchange step: the two lightest items can be given the same, maximal length, without increasing the
    cost and keeping the Kraft inequality. *)
Lemma exchange : forall D a b la lb Qr,
  (forall p, In p ((b, lb) :: Qr) -> weight a <= weight (fst p)) ->
  (forall p, In p Qr -> weight b <= weight (fst p)) ->
  0 <= weight a -> 0 <= weight b ->
  lens_ok D ((a, la) :: (b, lb) :: Qr) ->
  kq D ((a, la) :: (b, lb) :: Qr) <= 2 ^ D ->
  exists M Qr', map fst Qr' = map fst Qr /\ 1 <= M /\
    lens_ok D ((a, M) :: (b, M) :: Qr') /\
    kq D ((a, M) :: (b, M) :: Qr') <= 2 ^ D /\
    cq ((a, M) :: (b, M) :: Qr') <= cq ((a, la) :: (b, lb) :: Qr).
Proof.
  intros D a b la lb Qr Hwa Hwb Ha0 Hb0 Hl Hk.
  assert (HD : 0 <= la <= D) by exact (Hl (a, la) (in_eq _ _)).
  (* phase 1 *)
  destruct (lift_max (Z.to_nat (D - la)) D a la ((b, lb) :: Qr)) as [la1 [T1 [Hf1 [Hm1 [Hp1 [Hc1 Hl1]]]]]];
    [lia | exact Hwa | exact Hl |].
  destruct T1 as [|[b' lb1] Qr1]; [discriminate|]. injection Hf1 as Eb HfQ. simpl in Eb; subst b'.
  (* phase 2 *)
  assert (Hlb : lens_ok D ((b, lb1) :: Qr1)) by (intros p Hp; apply Hl1; right; auto).
  assert (Hlb1 := Hlb (b, lb1) (in_eq _ _)). simpl in Hlb1.
  destruct (lift_max (Z.to_nat (D - lb1)) D b lb1 Qr1) as [lb2 [Qr2 [Hf2 [Hm2 [Hp2 [Hc2 Hl2]]]]]];
    [lia | | exact Hlb |].
  { intros p Hp. destruct (in_map_fst_eq _ _ _ HfQ Hp) as [q [Hq Eq]]. rewrite <- Eq. auto. }
  assert (Hall1 : forall l, In l (lb2 :: map snd Qr2) -> l <= la1).
  { intros l Hlin. apply (Permutation_in _ (Permutation_sym Hp2)) in Hlin.
    destruct Hlin as [<-|Hlin]; [apply (Hm1 (b, lb1)); left; auto|].
    apply in_map_iff in Hlin. destruct Hlin as [p [<- Hp]]. apply Hm1; right; auto. }
  assert (Hla1 := Hl1 (a, la1) (in_eq _ _)). simpl in Hla1.
  assert (Hlb2 := Hl2 (b, lb2) (in_eq _ _)). simpl in Hlb2.
  (* Kraft sum so far *)
  assert (Hk2 : kq D ((a, la1) :: (b, lb2) :: Qr2) <= 2 ^ D).
  { rewrite <- (kq_lengths D ((a, la) :: (b, lb) :: Qr)); auto.
    eapply Permutation_trans; [exact Hp1|]. simpl. apply perm_skip. exact Hp2. }
  (* phase 3 *)
  destruct (lower_top (Z.to_nat (la1 - lb2)) D a la1 lb2 ((b, lb2) :: Qr2)) as [Hk3 Hc3]; auto.
  - lia.
  - split; [lia|]. apply Hall1; left; auto.
  - lia.
  - intros p [<-|Hp]; simpl; [lia|]. split; [apply (Hl2 p); right; auto|]. apply Hm2; auto.
  - exists lb2, Qr2. split; [congruence|]. split.
    + destruct (Z_le_gt_dec 1 lb2) as [|Hz]; auto. exfalso.
      assert (lb2 = 0) by lia. subst lb2.
      unfold kq in Hk3; cbn [map sumZ snd] in Hk3. rewrite Z.sub_0_r in Hk3.
      assert (0 <= sumZ (map (fun p : item * Z => 2 ^ (D - snd p)) Qr2))
        by (apply sumZ_nonneg; intros; apply Z.pow_nonneg; lia).
      assert (0 < 2 ^ D) by (apply Z.pow_pos_nonneg; lia). lia.
    + split; [|split; [exact Hk3|]].
      * intros p [<-|[<-|Hp]]; simpl; try lia. apply Hl2; right; auto.
      * eapply Z.le_trans; [exact Hc3|]. eapply Z.le_trans; [|exact Hc1].
        unfold cq in *; cbn [map sumZ fst snd] in *. lia.
Qed.

Theorem huff_opt : forall P R, huff P R -> forall D Q,
  map fst Q = P -> lens_ok D Q -> kq D Q <= 2 ^ D -> (forall I, In I P -> 0 <= weight I) ->
  cost R <= cq Q.
Proof.
  intros P R H; induction H as [I|P a b rest R Hp Ha Hb Hh IH]; intros D Q HQ Hl Hk Hw.
  - destruct Q as [|[J l] [|q Q]]; try discriminate. injection HQ as ->.
    assert (Hl0 := Hl (I, l) (in_eq _ _)). assert (Hw0 := Hw I (in_eq _ _)). simpl in Hl0.
    unfold cq; cbn [map sumZ fst snd]. nia.
  - subst P. destruct (Permutation_map_inv _ _ (Permutation_sym Hp)) as [Q' [EQ' HQ']].
    destruct Q' as [|[a' la] [|[b' lb] Qr]]; try discriminate.
    injection EQ' as <- <- Erest.
    assert (Hin : forall J, In J (a :: b :: rest) -> In J (map fst Q))
      by (intros; eapply Permutation_in; [apply Permutation_sym; exact Hp|auto]).
    assert (Hwa : 0 <= weight a) by (apply Hw, Hin; left; auto).
    assert (Hwb : 0 <= weight b) by (apply Hw, Hin; right; left; auto).
    assert (Hl' : lens_ok D ((a, la) :: (b, lb) :: Qr))
      by (intros p Hp'; apply Hl; eapply Permutation_in; [apply Permutation_sym; exact HQ'|auto]).
    assert (Hk' : kq D ((a, la) :: (b, lb) :: Qr) <= 2 ^ D) by (rewrite <- (kq_perm D _ _ HQ'); auto).
    destruct (exchange D a b la lb Qr) as [M [Qr' [Hf [HM [Hl'' [Hk'' Hc'']]]]]]; auto.
    { intros p [<-|Hp']; [apply Ha; left; auto|].
      apply Ha; right. rewrite Erest. apply in_map; auto. }
    { intros p Hp'. apply Hb. rewrite Erest. apply in_map; auto. }
    assert (Hc : cost R <= cq ((merge a b, M - 1) :: Qr')).
    { apply (IH D).
      - simpl. f_equal. congruence.
      - intros p [<-|Hp']; simpl.
        + assert (H1 := Hl'' (a, M) (in_eq _ _)). simpl in H1. lia.
        + apply Hl''; right; right; auto.
      - unfold kq in *; cbn [map sumZ snd] in *.
        replace (D - (M - 1)) with (Z.succ (D - M)) by lia. rewrite Z.pow_succ_r by
          (assert (H1 := Hl'' (a, M) (in_eq _ _)); simpl in H1; lia). lia.
      - intros J [<-|HJ]; [rewrite weight_merge; lia|]. apply Hw, Hin; right; right; exact HJ. }
    eapply Z.le_trans; [exact Hc|]. rewrite (cq_perm _ _ HQ').
    eapply Z.le_trans; [|exact Hc''].
    unfold cq; cbn [map sumZ fst snd]. rewrite cost_merge, weight_merge. nia.
Qed.

(** ** The Fibonacci bound: a leaf of frequency [f] at depth [d] has [fib (d+1) * f <= total weight]. *)

Fixpoint fibn (n : nat) : Z :=
  match n with O => 0 | S O => 1 | S ((S m) as p) => fibn p + fibn m end.

Definition fib (d : Z) : Z := fibn (Z.to_nat d).

Lemma fibn_nonneg : forall n, 0 <= fibn n.
Proof.
  intro n. cut (0 <= fibn n /\ 0 <= fibn (S n)); [tauto|].
  induction n as [|n [IH1 IH2]]; simpl; [lia|]. split; auto. destruct n; simpl in *; lia.
Qed.

Lemma fib_succ_succ : forall d, 0 <= d -> fib (d + 2) = fib (d + 1) + fib d.
Proof.
  intros d Hd. unfold fib. replace (Z.to_nat (d + 2)) with (S (S (Z.to_nat d))) by lia.
  replace (Z.to_nat (d + 1)) with (S (Z.to_nat d)) by lia. reflexivity.
Qed.

Lemma fib_nonneg : forall d, 0 <= fib d.
Proof. intros; apply fibn_nonneg. Qed.

Lemma fib_0 : fib 0 = 0.
Proof. reflexivity. Qed.

Definition fib_inv (P : list item) : Prop :=
  (forall I, In I P -> forall x, In x I -> 0 <= ld x /\ 0 <= lf x) /\
  (forall I, In I P -> forall x, In x I -> fib (ld x + 1) * lf x <= weight I) /\
  (forall I J, In I P -> In J P -> forall x, In x I -> 1 <= ld x -> fib (ld x) * lf x <= weight J).

Lemma weight_nonneg : forall I, (forall x, In x I -> 0 <= lf x) -> 0 <= weight I.
Proof. intros; unfold weight; apply sumZ_nonneg; auto. Qed.

Lemma fib_inv_perm : forall P Q, Permutation P Q -> fib_inv P -> fib_inv Q.
Proof.
  intros P Q Hp [H0 [H1 H2]]. assert (Hin : forall I, In I Q -> In I P)
    by (intros; eapply Permutation_in; [apply Permutation_sym|]; eauto).
  split; [|split]; intros; [apply (H0 I)|apply (H1 I)|apply (H2 I J)]; auto.
Qed.

Lemma fib_inv_step : forall a b rest,
  (forall J, In J (b :: rest) -> weight a <= weight J) ->
  (forall J, In J rest -> weight b <= weight J) ->
  fib_inv (a :: b :: rest) -> fib_inv (merge a b :: rest).
Proof.
  intros a b rest Ha Hb [H0 [H1 H2]].
  assert (Hwa : 0 <= weight a) by (apply weight_nonneg; intros; apply (H0 a); simpl; auto).
  assert (Hwb : 0 <= weight b) by (apply weight_nonneg; intros; apply (H0 b); simpl; auto).
  assert (Hab : weight a <= weight b) by (apply Ha; left; auto).
  (* a leaf of the merge comes from a or b *)
  assert (Hm : forall x, In x (merge a b) -> exists y, x = deeper y /\ (In y a \/ In y b))
    by (intros; apply in_merge; auto).
  split; [|split].
  - intros I [<-|HI] x Hx.
    + destruct (Hm x Hx) as [y [-> [Hy|Hy]]]; unfold deeper, ld, lf; simpl;
        [destruct (H0 a (in_eq _ _) y Hy)|destruct (H0 b (or_intror (in_eq _ _)) y Hy)];
        unfold ld, lf in *; lia.
    + apply (H0 I); simpl; auto.
  - intros I [<-|HI] x Hx.
    + rewrite weight_merge. destruct (Hm x Hx) as [y [-> [Hy|Hy]]]; unfold deeper; unfold ld at 1, lf; simpl.
      * destruct (H0 a (in_eq _ _) y Hy) as [Hd Hf]. unfold ld, lf in Hd, Hf.
        unfold ld; replace (snd y + 1 + 1) with (snd y + 2) by lia. rewrite fib_succ_succ by lia.
        assert (E1 := H1 a (in_eq _ _) y Hy). unfold ld, lf in E1.
        destruct (Z.eq_dec (snd y) 0) as [Hz|Hz].
        { rewrite Hz, fib_0 in *. nia. }
        assert (E2 := H2 a b (in_eq _ _) (or_intror (in_eq _ _)) y Hy). unfold ld, lf in E2.
        assert (E2' := E2 ltac:(lia)). nia.
      * destruct (H0 b (or_intror (in_eq _ _)) y Hy) as [Hd Hf]. unfold ld, lf in Hd, Hf.
        unfold ld; replace (snd y + 1 + 1) with (snd y + 2) by lia. rewrite fib_succ_succ by lia.
        assert (E1 := H1 b (or_intror (in_eq _ _)) y Hy). unfold ld, lf in E1.
        destruct (Z.eq_dec (snd y) 0) as [Hz|Hz].
        { rewrite Hz, fib_0 in *. nia. }
        assert (E2 := H2 b a (or_intror (in_eq _ _)) (in_eq _ _) y Hy). unfold ld, lf in E2.
        assert (E2' := E2 ltac:(lia)). nia.
    + apply (H1 I); simpl; auto.
  - intros I J HI HJ x Hx Hd.
    (* weight of J is at least weight b (and weight a) when J is in rest, and wa + wb when J is the merge *)
    assert (HJw : weight b <= weight J /\ weight a <= weight J).
    { destruct HJ as [<-|HJ]; [rewrite weight_merge; lia|].
      split; [apply Hb; auto|apply Ha; right; auto]. }
    destruct HI as [<-|HI].
    + destruct (Hm x Hx) as [y [-> [Hy|Hy]]]; unfold deeper, ld, lf in *; simpl in *.
      * assert (E1 := H1 a (or_introl eq_refl) y Hy). lia.
      * assert (E1 := H1 b (or_intror (or_introl eq_refl)) y Hy). lia.
    + destruct HJ as [<-|HJ].
      * rewrite weight_merge.
        assert (E := H2 I a (or_intror (or_intror HI)) (in_eq _ _) x Hx Hd). lia.
      * apply (H2 I J); simpl; auto.
Qed.

Theorem huff_fib : forall P R, huff P R -> fib_inv P ->
  forall x, In x R -> fib (ld x + 1) * lf x <= weight R.
Proof.
  intros P R H HP x Hx.
  assert (HR := huff_ind_pool fib_inv fib_inv_perm fib_inv_step P R H HP).
  destruct HR as [_ [H1 _]]. apply (H1 R (in_eq _ _) x Hx).
Qed.

(** Initial pools: singletons at depth 0. *)
Definition singleton (id f : Z) : item := [(id, f, 0)].

Lemma fib_inv_init : forall l : list (Z * Z), (forall p, In p l -> 0 <= snd p) ->
  fib_inv (map (fun p => singleton (fst p) (snd p)) l).
Proof.
  intros l Hl. split; [|split].
  - intros I HI x Hx. apply in_map_iff in HI. destruct HI as [p [<- Hp]].
    destruct Hx as [<-|[]]; unfold ld, lf; simpl. split; [lia|]. apply Hl; auto.
  - intros I HI x Hx. apply in_map_iff in HI. destruct HI as [p [<- Hp]].
    destruct Hx as [<-|[]]; unfold ld, lf, weight, singleton, fib; cbn. rewrite Pos2Nat.inj_1. change (fibn 1) with 1. lia.
  - intros I J HI HJ x Hx Hd. apply in_map_iff in HI. destruct HI as [p [<- Hp]].
    destruct Hx as [<-|[]]; unfold ld in Hd; simpl in Hd. lia.
Qed.

(** ** Greedy reductions as sequences of steps (the form produced by a merge loop) *)

Inductive steps : list item -> list item -> Prop :=
| steps_refl : forall P, steps P P
| steps_snoc : forall P Q a b rest,
    steps P Q -> Permutation Q (a :: b :: rest) ->
    (forall J, In J (b :: rest) -> weight a <= weight J) ->
    (forall J, In J rest -> weight b <= weight J) ->
    steps P (merge a b :: rest).

Lemma steps_huff_gen : forall P Q, steps P Q -> forall R, huff Q R -> huff P R.
Proof.
  intros P Q H; induction H as [P|P Q a b rest H IH Hp Ha Hb]; intros R HR; auto.
  apply IH. eapply huff_step; eauto.
Qed.

Theorem steps_huff : forall P R, steps P [R] -> huff P R.
Proof. intros; eapply steps_huff_gen; eauto. constructor. Qed.

Theorem steps_huff_perm : forall P Q R, steps P Q -> Permutation Q [R] -> huff P R.
Proof.
  intros P Q R H Hp. apply Permutation_sym, Permutation_length_1_inv in Hp. subst. apply steps_huff; auto.
Qed.
