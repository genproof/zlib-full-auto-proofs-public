(** * pqdownheap: the sift-down of trees.c restores the heap property and permutes the heap *)

From Coq Require Import ZArith List Lia Bool Permutation.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The order [smaller] is a total preorder; it orders frequencies. *)

Section Order.
Variable t : tree.
Variable depth : list Z.

Definition le (n m : Z) : Prop := smaller t depth n m = true.

Lemma le_refl : forall n, le n n.
Proof. intros; unfold le, smaller. rewrite Z.ltb_irrefl, Z.eqb_refl, Z.leb_refl. reflexivity. Qed.

Lemma le_trans : forall a b c, le a b -> le b c -> le a c.
Proof.
  unfold le, smaller; intros a b c H1 H2.
  apply orb_true_iff in H1; apply orb_true_iff in H2; apply orb_true_iff.
  rewrite andb_true_iff, Z.ltb_lt, Z.eqb_eq, Z.leb_le in *.
  destruct H1 as [H1|[H1 H1']], H2 as [H2|[H2 H2']]; lia.
Qed.

Lemma le_total : forall a b, ~ le a b -> le b a.
Proof.
  unfold le, smaller; intros a b H.
  apply not_true_iff_false in H. apply orb_false_iff in H. apply orb_true_iff.
  rewrite andb_false_iff, Z.ltb_ge, Z.eqb_neq, Z.leb_gt in H.
  rewrite andb_true_iff, Z.ltb_lt, Z.eqb_eq, Z.leb_le. lia.
Qed.

Lemma le_freq : forall a b, le a b -> Znth a (fc t) <= Znth b (fc t).
Proof.
  unfold le, smaller; intros a b H. apply orb_true_iff in H.
  rewrite andb_true_iff, Z.ltb_lt, Z.eqb_eq, Z.leb_le in H. lia.
Qed.

(** Heap property on the edges whose parent index is at least [lo]. *)
Definition hp (heap : list Z) (len lo : Z) : Prop :=
  forall i, 2 <= i <= len -> lo <= i / 2 -> le (Znth (i / 2) heap) (Znth i heap).

End Order.

(** ** Index sequences and the heap region *)

Fixpoint zseq (a : Z) (n : nat) : list Z := match n with O => [] | S n' => a :: zseq (a + 1) n' end.

Lemma in_zseq : forall n a i, In i (zseq a n) <-> a <= i < a + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros a i; simpl; [lia|]. rewrite IH. lia.
Qed.

Lemma zseq_nodup : forall n a, NoDup (zseq a n).
Proof.
  induction n as [|n IH]; intros a; simpl; constructor; auto.
  rewrite in_zseq; lia.
Qed.

(** The heap region [heap[1 .. len]]. *)
Definition reg (heap : list Z) (len : Z) : list Z := map (fun i => Znth i heap) (zseq 1 (Z.to_nat len)).

Lemma perm_swap_mid : forall (A B C : list Z) x y,
  Permutation (A ++ x :: B ++ y :: C) (A ++ y :: B ++ x :: C).
Proof.
  intros. apply Permutation_app_head.
  transitivity (x :: y :: B ++ C); [apply perm_skip, Permutation_sym, Permutation_middle|].
  transitivity (y :: x :: B ++ C); [apply perm_swap|].
  apply perm_skip, Permutation_middle.
Qed.

Lemma map_eq_off : forall (g1 g2 : Z -> Z) (l : list Z) k j,
  ~ In k l -> ~ In j l -> (forall i, i <> k -> i <> j -> g2 i = g1 i) -> map g2 l = map g1 l.
Proof.
  intros g1 g2 l k j Hk Hj E. apply map_ext_in. intros i Hi.
  apply E; intros ->; auto.
Qed.

(** Two functions that agree on an index list except that they swap two values at two distinct indices of the
    list give permuted images. *)
Ltac in_app_solve :=
  match goal with
  | |- In ?x (?l1 ++ ?l2) => apply in_or_app; first [left; in_app_solve | right; in_app_solve]
  | |- In ?x (?a :: ?l) => first [left; reflexivity | right; in_app_solve]
  | H : In ?x ?l |- In ?x ?l => exact H
  end.

Lemma map_swap_perm : forall (idx : list Z) (g1 g2 : Z -> Z) k j,
  NoDup idx -> In k idx -> In j idx -> k <> j ->
  g2 k = g1 j -> g2 j = g1 k -> (forall i, i <> k -> i <> j -> g2 i = g1 i) ->
  Permutation (map g1 idx) (map g2 idx).
Proof.
  intros idx g1 g2 k j Hnd Hk Hj Hkj E1 E2 E3.
  destruct (in_split _ _ Hk) as [A [R ->]].
  apply in_app_or in Hj. destruct Hj as [Hj|[->|Hj]]; [| congruence |].
  - destruct (in_split _ _ Hj) as [A1 [A2 ->]].
    rewrite <- app_assoc in Hnd |- *. simpl in Hnd |- *.
    apply NoDup_remove in Hnd. destruct Hnd as [Hnd Hnj].
    rewrite app_assoc in Hnd. apply NoDup_remove in Hnd. destruct Hnd as [_ Hnk].
    assert (EA1 : map g2 A1 = map g1 A1)
      by (apply (map_eq_off g1 g2 A1 k j); auto; intro Hc; [apply Hnk|apply Hnj]; in_app_solve).
    assert (EA2 : map g2 A2 = map g1 A2)
      by (apply (map_eq_off g1 g2 A2 k j); auto; intro Hc; [apply Hnk|apply Hnj]; in_app_solve).
    assert (ER : map g2 R = map g1 R)
      by (apply (map_eq_off g1 g2 R k j); auto; intro Hc; [apply Hnk|apply Hnj]; in_app_solve).
    rewrite !map_app; simpl; rewrite !map_app; simpl. rewrite E1, E2, EA1, EA2, ER.
    apply perm_swap_mid.
  - destruct (in_split _ _ Hj) as [B [C ->]].
    apply NoDup_remove in Hnd. destruct Hnd as [Hnd Hnk].
    rewrite app_assoc in Hnd. apply NoDup_remove in Hnd. destruct Hnd as [_ Hnj].
    assert (EA : map g2 A = map g1 A)
      by (apply (map_eq_off g1 g2 A k j); auto; intro Hc; [apply Hnk|apply Hnj]; in_app_solve).
    assert (EB : map g2 B = map g1 B)
      by (apply (map_eq_off g1 g2 B k j); auto; intro Hc; [apply Hnk|apply Hnj]; in_app_solve).
    assert (EC : map g2 C = map g1 C)
      by (apply (map_eq_off g1 g2 C k j); auto; intro Hc; [apply Hnk|apply Hnj]; in_app_solve).
    rewrite !map_app; simpl; rewrite !map_app; simpl. rewrite E1, E2, EA, EB, EC.
    apply perm_swap_mid.
Qed.

(** ** Division facts for the heap indices *)

Lemma div2_children : forall i k, 1 <= k -> i / 2 = k -> i = 2 * k \/ i = 2 * k + 1.
Proof. intros. assert (H1 := Z.div_mod i 2 ltac:(lia)). assert (H2 := Z.mod_pos_bound i 2 ltac:(lia)). lia. Qed.

Lemma div2_2k : forall k, (2 * k) / 2 = k.
Proof. intros. rewrite Z.mul_comm, Z.div_mul; lia. Qed.

Lemma div2_2k1 : forall k, 0 <= k -> (2 * k + 1) / 2 = k.
Proof. intros. rewrite Z.add_comm, Z.mul_comm, Z.div_add by lia. simpl. lia. Qed.

Lemma div2_lt : forall i, 1 <= i -> i / 2 < i.
Proof. intros. apply Z.div_lt; lia. Qed.

Lemma div2_ge1 : forall i, 2 <= i -> 1 <= i / 2.
Proof. intros. apply Z.div_le_lower_bound; lia. Qed.

Lemma shiftl1 : forall k, Z.shiftl k 1 = 2 * k.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

(** ** The sift-down loop *)

Section Sift.
Variable t : tree.
Variable depth : list Z.
Variable heap0 : list Z.
Variable len k0 v : Z.

Hypothesis Hk0 : 1 <= k0 <= len.
Hypothesis Hlen : len < Zlength heap0.
Hypothesis Hv : Znth k0 heap0 = v.
Hypothesis Hhp : hp t depth heap0 len (k0 + 1).

Definition sinv (heap : list Z) (k : Z) : Prop :=
  Zlength heap = Zlength heap0 /\ k0 <= k <= len /\ (k = k0 \/ k0 <= k / 2) /\
  (forall i, 2 <= i <= len -> k0 <= i / 2 -> i / 2 <> k -> le t depth (Znth (i / 2) heap) (Znth i heap)) /\
  (k <> k0 -> forall i, 2 <= i <= len -> i / 2 = k -> le t depth (Znth (k / 2) heap) (Znth i heap)) /\
  (k <> k0 -> le t depth (Znth (k / 2) heap) v) /\
  Permutation (reg heap0 len) (reg (upd_Znth k heap v) len) /\
  (forall i, 0 <= i < Zlength heap0 -> i < k0 \/ len < i -> Znth i heap = Znth i heap0).

(** The final state of the sift: the heap property holds on all edges with parent at least k0. *)
Definition sfinal (heap : list Z) : Prop :=
  Zlength heap = Zlength heap0 /\
  hp t depth heap len k0 /\ Permutation (reg heap0 len) (reg heap len) /\
  (forall i, 0 <= i < Zlength heap0 -> i < k0 \/ len < i -> Znth i heap = Znth i heap0).

Lemma sinv_init : sinv heap0 k0.
Proof.
  split; [reflexivity|]. split; [lia|]. split; [left; reflexivity|].
  split; [intros i Hi Hlo Hne; apply Hhp; lia|].
  split; [intros H; congruence|]. split; [intros H; congruence|].
  split; [rewrite upd_Znth_triv; [apply Permutation_refl|lia|auto]|].
  intros; reflexivity.
Qed.

Lemma reg_ext : forall h1 h2, (forall i, 1 <= i <= len -> Znth i h1 = Znth i h2) -> reg h1 len = reg h2 len.
Proof.
  intros h1 h2 E. unfold reg. apply map_ext_in. intros i Hi. apply in_zseq in Hi. apply E. lia.
Qed.

(** Leaving the loop: no child, or v is not larger than the smallest child. *)
Lemma sift_exit : forall heap k,
  sinv heap k ->
  (len < 2 * k \/ (forall c, 2 <= c <= len -> c / 2 = k -> le t depth v (Znth c heap))) ->
  sfinal (upd_Znth k heap v).
Proof.
  intros heap k [HL [Hk [Hk1 [S1 [S2 [S3 [S4 S5]]]]]]] Hex.
  assert (Hkr : 0 <= k < Zlength heap) by lia.
  split; [|split; [|split]].
  - rewrite upd_Znth_Zlength; lia.
  - intros i Hi Hlo.
    assert (Hi2 := div2_lt i ltac:(lia)). assert (Hi1 := div2_ge1 i ltac:(lia)).
    destruct (Z.eq_dec i k) as [->|Hik].
    + (* edge (k/2, k) *)
      assert (Hne : k <> k0) by (intros ->; lia).
      rewrite upd_Znth_same by lia. rewrite upd_Znth_diff by lia. apply S3; auto.
    + destruct (Z.eq_dec (i / 2) k) as [Hik2|Hik2].
      * destruct Hex as [Hex|Hex]; [destruct (div2_children i k ltac:(lia) Hik2); lia|].
        rewrite Hik2, upd_Znth_same by lia. rewrite upd_Znth_diff by lia. apply Hex; auto.
      * rewrite !upd_Znth_diff by lia. apply S1; auto.
  - eapply Permutation_trans; [exact S4|]. apply Permutation_refl.
  - intros i Hi Hout. rewrite upd_Znth_diff by lia. apply S5; auto.
Qed.

(** One step of the loop. *)
Lemma sift_step : forall heap k jc,
  sinv heap k ->
  2 * k <= len -> jc / 2 = k -> 2 <= jc <= len ->
  (forall c, 2 <= c <= len -> c / 2 = k -> le t depth (Znth jc heap) (Znth c heap)) ->
  le t depth (Znth jc heap) v ->
  sinv (upd_Znth k heap (Znth jc heap)) jc.
Proof.
  intros heap k jc [HL [Hk [Hk1 [S1 [S2 [S3 [S4 S5]]]]]]] H2k Hjc Hjcr Hmin Hjv.
  assert (Hkjc : k < jc) by (destruct (div2_children jc k ltac:(lia) Hjc); lia).
  set (h' := upd_Znth k heap (Znth jc heap)).
  assert (Hh'k : Znth k h' = Znth jc heap) by (unfold h'; rewrite upd_Znth_same; lia).
  assert (Hh'o : forall i, 0 <= i < Zlength heap -> i <> k -> Znth i h' = Znth i heap)
    by (intros; unfold h'; rewrite upd_Znth_diff; lia).
  split; [unfold h'; rewrite upd_Znth_Zlength; lia|].
  split; [lia|]. split; [right; lia|].
  split; [|split; [|split; [|split]]].
  - intros i Hi Hlo Hne.
    assert (Hi2 := div2_lt i ltac:(lia)). assert (Hi1 := div2_ge1 i ltac:(lia)).
    destruct (Z.eq_dec i k) as [->|Hik].
    + rewrite Hh'k, Hh'o by lia. apply S2; [intros ->; lia| lia | auto].
    + destruct (Z.eq_dec (i / 2) k) as [Hik2|Hik2].
      * rewrite Hik2, Hh'k, Hh'o by lia. apply Hmin; auto.
      * rewrite !Hh'o by lia. apply S1; auto.
  - intros _ i Hi Hi2. rewrite Hjc, Hh'k.
    assert (Hi2' := div2_lt i ltac:(lia)).
    rewrite Hh'o by lia. rewrite <- Hi2. apply S1; lia.
  - intros _. rewrite Hjc, Hh'k. exact Hjv.
  - assert (ZL1 : Zlength (upd_Znth k heap v) = Zlength heap) by (rewrite upd_Znth_Zlength; lia).
    assert (ZL2 : Zlength h' = Zlength heap) by (unfold h'; rewrite upd_Znth_Zlength; lia).
    assert (ZL3 : Zlength (upd_Znth jc h' v) = Zlength heap) by (rewrite upd_Znth_Zlength; lia).
    eapply Permutation_trans; [exact S4|].
    unfold reg. apply (map_swap_perm _ _ _ k jc).
    + apply zseq_nodup.
    + apply in_zseq; lia.
    + apply in_zseq; lia.
    + lia.
    + rewrite upd_Znth_diff by lia. rewrite Hh'k. rewrite upd_Znth_diff by lia. reflexivity.
    + rewrite !upd_Znth_same by lia. reflexivity.
    + intros i Hi1 Hi2.
      destruct (Z_lt_ge_dec i 0) as [Hneg|Hnn]; [rewrite !Znth_underflow by lia; reflexivity|].
      destruct (Z_lt_ge_dec i (Zlength heap)) as [Hin|Hout];
        [|rewrite !Znth_overflow by lia; reflexivity].
      rewrite upd_Znth_diff by lia. rewrite Hh'o by lia. rewrite upd_Znth_diff by lia. reflexivity.
  - intros i Hi Hout. rewrite Hh'o by lia. apply S5; auto.
Qed.

End Sift.

Lemma pqloop_correct : forall t depth heap0 len k0 v,
  1 <= k0 <= len -> len < Zlength heap0 -> Znth k0 heap0 = v -> hp t depth heap0 len (k0 + 1) ->
  forall fuel heap k, sinv t depth heap0 len k0 v heap k -> len < k * 2 ^ Z.of_nat fuel ->
  let '(h', k') := pqdownheap_loop fuel t depth len v heap k (Z.shiftl k 1) in
  sfinal t depth heap0 len k0 (upd_Znth k' h' v).
Proof.
  intros t depth heap0 len k0 v Hk0 Hlen Hv Hhp fuel.
  induction fuel as [|fuel IH]; intros heap k Hinv Hf.
  - destruct Hinv as [_ [Hk _]]. simpl in Hf. lia.
  - assert (Hk : k0 <= k <= len) by (destruct Hinv as [_ [Hk _]]; exact Hk).
    assert (HL : Zlength heap = Zlength heap0) by (destruct Hinv as [HL _]; exact HL).
    cbn [pqdownheap_loop]. rewrite shiftl1.
    destruct (Z.leb_spec (2 * k) len) as [Hj|Hj].
    + set (jc := if (2 * k <? len) && smaller t depth (Znth (2 * k + 1) heap) (Znth (2 * k) heap)
                 then 2 * k + 1 else 2 * k).
      assert (Hjc : jc / 2 = k /\ 2 <= jc <= len).
      { unfold jc. destruct ((2 * k <? len) && _) eqn:E.
        - apply andb_true_iff in E; destruct E as [E _]. apply Z.ltb_lt in E.
          rewrite div2_2k1 by lia. lia.
        - rewrite div2_2k. lia. }
      assert (Hmin : forall c, 2 <= c <= len -> c / 2 = k -> le t depth (Znth jc heap) (Znth c heap)).
      { intros c Hc Hck. destruct (div2_children c k ltac:(lia) Hck) as [->| ->];
          unfold jc; destruct ((2 * k <? len) && _) eqn:E.
        - apply andb_true_iff in E; destruct E as [_ E]. exact E.
        - apply le_refl.
        - apply le_refl.
        - apply andb_false_iff in E. destruct E as [E|E].
          + apply Z.ltb_ge in E. lia.
          + apply le_total. unfold le; rewrite E; discriminate. }
      fold jc.
      destruct (smaller t depth v (Znth jc heap)) eqn:Hsv.
      * apply sift_exit; auto. right. intros c Hc Hck.
        eapply le_trans; [exact Hsv|]. apply Hmin; auto.
      * assert (Hjv : le t depth (Znth jc heap) v) by (apply le_total; unfold le; rewrite Hsv; discriminate).
        apply IH.
        -- apply sift_step; auto; tauto.
        -- rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia.
           destruct Hjc as [Hjc1 Hjc2]. destruct (div2_children jc k ltac:(lia) Hjc1); nia.
    + apply sift_exit; auto.
Qed.

Theorem pqdownheap_correct : forall t w k,
  let h := w_heap w in let len := w_heap_len w in let d := w_depth w in
  1 <= k <= len -> len < Zlength h -> len < 4096 -> hp t d h len (k + 1) ->
  let w' := pqdownheap t w k in
  w_heap_len w' = len /\ w_heap_max w' = w_heap_max w /\ w_depth w' = d /\ w_bl_count w' = w_bl_count w /\
  w_opt_len w' = w_opt_len w /\ w_static_len w' = w_static_len w /\
  Zlength (w_heap w') = Zlength h /\ hp t d (w_heap w') len k /\
  Permutation (reg h len) (reg (w_heap w') len) /\
  (forall i, 0 <= i < Zlength h -> i < k \/ len < i -> Znth i (w_heap w') = Znth i h).
Proof.
  intros t w k h len d Hk Hlen H4096 Hhp. unfold pqdownheap.
  assert (Hc := pqloop_correct t d h len k (Znth k h) Hk Hlen eq_refl Hhp pq_fuel h k).
  fold h len d.
  destruct (pqdownheap_loop pq_fuel t d len (Znth k h) h k (Z.shiftl k 1)) as [h' k'] eqn:E.
  destruct Hc as [HL [Hhp' [Hperm Hout]]].
  - apply sinv_init; auto.
  - unfold pq_fuel. simpl. nia.
  - unfold w_set_heap; simpl. repeat split; auto.
Qed.
