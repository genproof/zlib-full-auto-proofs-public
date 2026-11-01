(** * TREES part, BUILD: see RTDLTCTrKit.v for the statement and its purpose. *)
From Coq Require Import ZArith List Lia Bool Permutation.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCTrKit.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap Zlib.proof.huffman.BuildTree Zlib.proof.huffman.BuildPre Zlib.proof.huffman.Bitlen Zlib.proof.huffman.Repair Zlib.proof.huffman.GenCodes Zlib.proof.huffman.BuildThm.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The tables of the descriptors (what the checked reads of sd_extra / sd_stree need) *)

Definition desc_ok (sd : stat_desc) : Prop :=
  0 <= sd_base sd <= sd_elems sd /\ Zlength (sd_extra sd) = sd_elems sd - sd_base sd /\
  (forall st, sd_stree sd = Some st -> sd_elems sd <= Zlength st).

(** ** The checked build_tree up to gen_bitlen (the checked counterpart of BuildPre.bt_pre) *)

Definition c_bt_pre (sd : stat_desc) (t : tree) (w : work) : option (tree * work * Z) :=
  let w := w_set_heap_len w 0 in
  let w := w_set_heap_max w HEAP_SIZE in
  let* (t, w, max_code) := c_bt_init (Z.to_nat (sd_elems sd)) (sd_elems sd) t w (-1) 0 in
  let* (t, w, max_code) := c_bt_force 2 sd t w max_code in
  let* w := c_bt_heapify (Z.to_nat (w_heap_len w / 2)) t w (w_heap_len w / 2) in
  let* (t, w, _) := c_bt_merge (Z.to_nat (w_heap_len w)) t w (sd_elems sd) in
  let* top := rd (w_heap w) SMALLEST in
  let* w := c_store_removed w top in
  Some (t, w, max_code).

(** ** Parts (each proved separately) *)

(** pqdownheap runs when the sifted region [1, heap_len] holds valid node ids. *)
Definition pqdownheap_stmt : Prop := forall t w k,
  1 <= k <= w_heap_len w -> w_heap_len w < Zlength (w_heap w) -> Zlength (w_heap w) <= HEAP_SIZE ->
  (forall i, 1 <= i <= w_heap_len w ->
     0 <= Znth i (w_heap w) < Zlength (fc t) /\ Znth i (w_heap w) < Zlength (w_depth w)) ->
  c_pqdownheap t w k = Some (pqdownheap t w k).
Lemma pq_rd_ok (l : list Z) i : 0 <= i < Zlength l -> rd l i = Some (Znth i l).
Proof.
  intros H. unfold rd, in_range.
  assert (E1 : (0 <=? i) = true) by (apply Z.leb_le; lia).
  assert (E2 : (i <? Zlength l) = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2. reflexivity.
Qed.

Lemma pq_wr_ok (l : list Z) i v : 0 <= i < Zlength l -> wr l i v = Some (upd_Znth i l v).
Proof.
  intros H. unfold wr, in_range.
  assert (E1 : (0 <=? i) = true) by (apply Z.leb_le; lia).
  assert (E2 : (i <? Zlength l) = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2. reflexivity.
Qed.

Lemma pq_smaller_ok t depth n m :
  0 <= n < Zlength (fc t) -> n < Zlength depth -> 0 <= m < Zlength (fc t) -> m < Zlength depth ->
  c_smaller t depth n m = Some (smaller t depth n m).
Proof.
  intros. unfold c_smaller, smaller.
  rewrite (pq_rd_ok (fc t) n), (pq_rd_ok (fc t) m) by lia. cbn [bind].
  destruct (Znth n (fc t) <? Znth m (fc t)); [reflexivity|].
  destruct (Znth n (fc t) =? Znth m (fc t)); [|reflexivity].
  rewrite (pq_rd_ok depth n), (pq_rd_ok depth m) by lia. reflexivity.
Qed.

Lemma pq_loop_ok t depth hl v : forall fuel heap k j,
  hl < Zlength heap ->
  (forall i, 1 <= i <= hl -> 0 <= Znth i heap < Zlength (fc t) /\ Znth i heap < Zlength depth) ->
  0 <= v < Zlength (fc t) -> v < Zlength depth ->
  1 <= k <= hl -> j = 2 * k -> hl < j * 2 ^ Z.of_nat fuel ->
  c_pqdownheap_loop fuel t depth hl v heap k j = Some (pqdownheap_loop fuel t depth hl v heap k j) /\
  1 <= snd (pqdownheap_loop fuel t depth hl v heap k j) <= hl /\
  Zlength (fst (pqdownheap_loop fuel t depth hl v heap k j)) = Zlength heap.
Proof.
  induction fuel as [|f IH]; intros heap k j Hlen Hval Hv1 Hv2 Hk Hj Hf.
  - cbn [c_pqdownheap_loop pqdownheap_loop].
    change (2 ^ Z.of_nat 0) with 1 in Hf.
    assert (E : (j <=? hl) = false) by (apply Z.leb_gt; lia). rewrite E. cbn. split; [reflexivity|lia].
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia.
    assert (Hp : 0 < 2 ^ Z.of_nat f) by (apply Z.pow_pos_nonneg; lia).
    cbn [c_pqdownheap_loop pqdownheap_loop].
    destruct (j <=? hl) eqn:Ejh; [|cbn; split; [reflexivity|lia]].
    apply Z.leb_le in Ejh.
    assert (Tail : forall j', j <= j' <= hl ->
      (let* hj := rd heap j' in
       let* sm := c_smaller t depth v hj in
       if sm then Some (heap, k)
       else let* heap0 := wr heap k hj in
            c_pqdownheap_loop f t depth hl v heap0 j' (Z.shiftl j' 1)) =
      Some (if smaller t depth v (Znth j' heap) then (heap, k)
            else pqdownheap_loop f t depth hl v (upd_Znth k heap (Znth j' heap)) j' (Z.shiftl j' 1)) /\
      1 <= snd (if smaller t depth v (Znth j' heap) then (heap, k)
            else pqdownheap_loop f t depth hl v (upd_Znth k heap (Znth j' heap)) j' (Z.shiftl j' 1)) <= hl /\
      Zlength (fst (if smaller t depth v (Znth j' heap) then (heap, k)
            else pqdownheap_loop f t depth hl v (upd_Znth k heap (Znth j' heap)) j' (Z.shiftl j' 1))) =
      Zlength heap).
    { intros j' Hj'.
      destruct (Hval j') as [Hj1 Hj2]; [lia|].
      rewrite (pq_rd_ok heap j') by lia. cbn [bind].
      rewrite pq_smaller_ok by lia.
      destruct (smaller t depth v (Znth j' heap)).
      - cbn. split; [reflexivity|lia].
      - rewrite (pq_wr_ok heap k) by lia. cbn [bind].
        assert (Hl' : Zlength (upd_Znth k heap (Znth j' heap)) = Zlength heap)
          by (apply Zlength_upd_Znth_any).
        destruct (IH (upd_Znth k heap (Znth j' heap)) j' (Z.shiftl j' 1)) as [A [B C]].
        + lia.
        + intros i Hi. destruct (Z.eq_dec i k) as [->|Hne].
          * rewrite upd_Znth_same by lia. auto.
          * rewrite upd_Znth_diff by lia. auto.
        + auto.
        + auto.
        + lia.
        + rewrite Z.shiftl_mul_pow2 by lia. lia.
        + rewrite Z.shiftl_mul_pow2 by lia. nia.
        + rewrite A. split; [reflexivity|]. split; [exact B|]. rewrite C. exact Hl'. }
    destruct (j <? hl) eqn:Elt.
    + apply Z.ltb_lt in Elt.
      destruct (Hval j) as [Ha1 Ha2]; [lia|].
      destruct (Hval (j + 1)) as [Hb1 Hb2]; [lia|].
      rewrite (pq_rd_ok heap (j + 1)), (pq_rd_ok heap j) by lia. cbn [bind].
      rewrite pq_smaller_ok by lia. cbn [bind andb].
      destruct (smaller t depth (Znth (j + 1) heap) (Znth j heap)); apply Tail; lia.
    + apply Z.ltb_ge in Elt. cbn [bind andb]. apply Tail; lia.
Qed.

Lemma pqdownheap_part : pqdownheap_stmt.
Proof.
  intros t w k Hk Hlen Hsz Hval.
  unfold c_pqdownheap, pqdownheap.
  destruct (Hval k Hk) as [Hv1 Hv2].
  rewrite (pq_rd_ok (w_heap w) k) by lia. cbn [bind].
  destruct (pq_loop_ok t (w_depth w) (w_heap_len w) (Znth k (w_heap w)) pq_fuel (w_heap w) k (Z.shiftl k 1))
    as [A [B C]];
    [auto | auto | auto | auto | auto
    | rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 1) with 2; lia
    | unfold pq_fuel; rewrite Z.shiftl_mul_pow2 by lia; unfold HEAP_SIZE in *; simpl; lia
    | ].
  rewrite A. destruct (pqdownheap_loop pq_fuel t (w_depth w) (w_heap_len w) (Znth k (w_heap w))
                           (w_heap w) k (Z.shiftl k 1)) as [h k'] eqn:E.
    cbn [fst snd] in *. cbn [bind].
    rewrite (pq_wr_ok h k') by lia. reflexivity.
Qed.

(** The first loop of build_tree. *)
Definition bt_init_stmt : Prop := forall elems fuel t w mc n,
  0 <= n <= elems -> elems <= Z.of_nat fuel + n -> elems < HEAP_SIZE ->
  Zlength (w_heap w) = HEAP_SIZE -> Zlength (w_depth w) = HEAP_SIZE ->
  elems <= Zlength (fc t) -> elems <= Zlength (dl t) -> 0 <= w_heap_len w <= n ->
  c_bt_init fuel elems t w mc n = Some (bt_init fuel elems t w mc n).
Lemma bti_rd_eq l i : 0 <= i < Zlength l -> rd l i = Some (Znth i l).
Proof. intros H. unfold rd, in_range. replace ((0 <=? i) && (i <? Zlength l)) with true; [reflexivity|].
  symmetry. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. lia. Qed.

Lemma bti_wr_eq l i v : 0 <= i < Zlength l -> wr l i v = Some (upd_Znth i l v).
Proof. intros H. unfold wr, in_range. replace ((0 <=? i) && (i <? Zlength l)) with true; [reflexivity|].
  symmetry. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. lia. Qed.

Lemma bt_init_part : bt_init_stmt.
Proof.
  intros elems fuel. induction fuel as [|f IH]; intros t w mc n Hn Hf He Hh Hd Hfc Hdl Hl.
  - cbn [c_bt_init bt_init]. destruct (n <? elems) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity].
  - cbn [c_bt_init bt_init]. destruct (n <? elems) eqn:E; [|reflexivity].
    apply Z.ltb_lt in E. rewrite (bti_rd_eq (fc t) n) by lia. cbn [bind].
    destruct (negb (Znth n (fc t) =? 0)).
    + rewrite bti_wr_eq by (unfold HEAP_SIZE in *; cbn [w_heap w_set_heap_len]; lia). cbn [bind].
      rewrite bti_wr_eq by (cbn [w_depth w_set_heap w_set_heap_len]; unfold HEAP_SIZE in *; lia). cbn [bind].
      apply IH; unfold w_set_depth, w_set_heap, w_set_heap_len; cbn [w_heap w_depth w_heap_len];
        try (rewrite upd_Znth_Zlength by (unfold HEAP_SIZE in *; lia)); unfold HEAP_SIZE in *; lia.
    + unfold c_set_dl. rewrite bti_wr_eq by lia. cbn [bind].
      change (mkTree (fc t) (upd_Znth n (dl t) 0)) with (set_dl t n 0).
      apply IH; unfold set_dl; cbn [fc dl]; try (rewrite upd_Znth_Zlength by lia); lia.
Qed.

(** The forced nodes (at most two). *)
Definition bt_force_stmt : Prop := forall sd t w mc,
  3 <= sd_elems sd -> desc_ok sd ->
  Zlength (w_heap w) = HEAP_SIZE -> Zlength (w_depth w) = HEAP_SIZE -> sd_elems sd <= Zlength (fc t) ->
  0 <= w_heap_len w -> (w_heap_len w = 0 -> mc = -1) -> (w_heap_len w = 1 -> 0 <= mc < sd_elems sd) ->
  c_bt_force 2 sd t w mc = Some (bt_force 2 sd t w mc).
Lemma btf_rd_in l i : 0 <= i < Zlength l -> rd l i = Some (Znth i l).
Proof. intros H. unfold rd, in_range. replace ((0 <=? i) && (i <? Zlength l))%bool with true by lia. reflexivity. Qed.
Lemma btf_wr_in l i v : 0 <= i < Zlength l -> wr l i v = Some (upd_Znth i l v).
Proof. intros H. unfold wr, in_range. replace ((0 <=? i) && (i <? Zlength l))%bool with true by lia. reflexivity. Qed.
Lemma btf_set_fc_in t i v : 0 <= i < Zlength (fc t) -> c_set_fc t i v = Some (set_fc t i v).
Proof. intros H. unfold c_set_fc. rewrite btf_wr_in by exact H. reflexivity. Qed.

(** One forced node: both models take the same step. *)
Lemma btf_step f sd t w mc node mc' :
  w_heap_len w < 2 -> (if mc <? 2 then (mc + 1, mc + 1) else (0, mc)) = (node, mc') ->
  0 <= node < Zlength (fc t) -> node < Zlength (w_depth w) ->
  0 <= w_heap_len w + 1 < Zlength (w_heap w) ->
  (forall st, sd_stree sd = Some st -> node < Zlength st) ->
  c_bt_force (S f) sd t w mc =
  c_bt_force f sd (set_fc t node 1)
    (match sd_stree sd with
     | Some stree => fun w => w_set_static_len w (u64 (w_static_len w - Znth node stree))
     | None => fun w => w end
      (w_set_opt_len (w_set_depth (w_set_heap (w_set_heap_len w (w_heap_len w + 1))
         (upd_Znth (w_heap_len w + 1) (w_heap w) node)) (upd_Znth node (w_depth w) 0))
         (u64 (w_opt_len (w_set_depth (w_set_heap (w_set_heap_len w (w_heap_len w + 1))
         (upd_Znth (w_heap_len w + 1) (w_heap w) node)) (upd_Znth node (w_depth w) 0)) - 1)))) mc' /\
  bt_force (S f) sd t w mc =
  bt_force f sd (set_fc t node 1)
    (match sd_stree sd with
     | Some stree => fun w => w_set_static_len w (u64 (w_static_len w - Znth node stree))
     | None => fun w => w end
      (w_set_opt_len (w_set_depth (w_set_heap (w_set_heap_len w (w_heap_len w + 1))
         (upd_Znth (w_heap_len w + 1) (w_heap w) node)) (upd_Znth node (w_depth w) 0))
         (u64 (w_opt_len (w_set_depth (w_set_heap (w_set_heap_len w (w_heap_len w + 1))
         (upd_Znth (w_heap_len w + 1) (w_heap w) node)) (upd_Znth node (w_depth w) 0)) - 1)))) mc'.
Proof.
  intros Hl Hn Hnode Hd Hh Hst. cbn [c_bt_force bt_force].
  replace (w_heap_len w <? 2) with true by lia. rewrite Hn.
  split.
  - cbn [w_heap w_heap_len w_depth w_set_heap_len w_set_heap w_set_depth].
    rewrite btf_wr_in by exact Hh. cbn [bind].
    rewrite btf_set_fc_in by exact Hnode. cbn [bind].
    rewrite btf_wr_in by (cbn; lia). cbn [bind].
    destruct (sd_stree sd) as [st|] eqn:E.
    + rewrite btf_rd_in by (specialize (Hst st eq_refl); lia). reflexivity.
    + reflexivity.
  - destruct (sd_stree sd); reflexivity.
Qed.

Lemma btf_stop f sd t w mc : 2 <= w_heap_len w ->
  c_bt_force f sd t w mc = Some (t, w, mc) /\ bt_force f sd t w mc = (t, w, mc).
Proof.
  intros H. destruct f; cbn [c_bt_force bt_force]; replace (w_heap_len w <? 2) with false by lia; auto.
Qed.

Local Ltac btf_side Hst' :=
  first [ reflexivity | lia | (intros st E; specialize (Hst' st E); lia)
        | (unfold set_fc; cbn [fc]; rewrite upd_Znth_Zlength by lia; lia) ].

Lemma bt_force_part : bt_force_stmt.
Proof.
  intros sd t w mc He [Hb [Hx Hst]] Hh Hd Hfc H0 Hm0 Hm1.
  assert (Hst' : forall st, sd_stree sd = Some st -> 2 < Zlength st)
    by (intros st E; specialize (Hst st E); lia).
  unfold HEAP_SIZE in *.
  destruct (Z_lt_le_dec (w_heap_len w) 2) as [Hl|Hl].
  2: { destruct (btf_stop 2 sd t w mc Hl) as [-> ->]; reflexivity. }
  destruct (Z.eq_dec (w_heap_len w) 0) as [E0|E0].
  - specialize (Hm0 E0); subst mc.
    edestruct (btf_step 1 sd t w (-1) 0 0) as [Ec Eb]; try btf_side Hst'.
    rewrite Ec, Eb; clear Ec Eb.
    set (w1 := match sd_stree sd with Some _ => _ | None => _ end _).
    assert (Hw1 : w_heap_len w1 = 1 /\ Zlength (w_heap w1) = 573 /\ Zlength (w_depth w1) = 573).
    { subst w1. destruct (sd_stree sd); cbn; rewrite !upd_Znth_Zlength by lia; lia. }
    destruct Hw1 as (Hw1 & Hw2 & Hw3).
    edestruct (btf_step 0 sd (set_fc t 0 1) w1 0 1 1) as [Ec Eb]; try btf_side Hst'.
    rewrite Ec, Eb; clear Ec Eb.
    apply btf_stop. destruct (sd_stree sd); cbn; lia.
  - assert (E1 : w_heap_len w = 1) by lia. specialize (Hm1 E1).
    destruct (mc <? 2) eqn:Em.
    + edestruct (btf_step 1 sd t w mc (mc + 1) (mc + 1)) as [Ec Eb];
        try (rewrite Em; reflexivity); try btf_side Hst'.
      rewrite Ec, Eb; clear Ec Eb.
      edestruct btf_stop as [-> ->]; [|reflexivity]. destruct (sd_stree sd); cbn; lia.
    + edestruct (btf_step 1 sd t w mc 0 mc) as [Ec Eb];
        try (rewrite Em; reflexivity); try btf_side Hst'.
      rewrite Ec, Eb; clear Ec Eb.
      edestruct btf_stop as [-> ->]; [|reflexivity]. destruct (sd_stree sd); cbn; lia.
Qed.

(** The heap construction [for (n = s->heap_len/2; n >= 1; n--) pqdownheap(s, tree, n);]. *)
Definition bt_heapify_stmt : Prop := forall fuel t w k,
  0 <= k <= w_heap_len w -> k <= Z.of_nat fuel -> w_heap_len w < HEAP_SIZE -> Zlength (w_heap w) = HEAP_SIZE ->
  (forall i, 1 <= i <= w_heap_len w ->
     0 <= Znth i (w_heap w) < Zlength (fc t) /\ Znth i (w_heap w) < Zlength (w_depth w)) ->
  hp t (w_depth w) (w_heap w) (w_heap_len w) (k + 1) ->
  c_bt_heapify fuel t w k = Some (bt_heapify fuel t w k).
Lemma bt_heapify_part : pqdownheap_stmt -> bt_heapify_stmt.
Proof.
  intros Hpq. unfold bt_heapify_stmt.
  induction fuel as [|fuel IH]; intros t w k Hk Hf Hl Hh Hv Hhp.
  - cbn [c_bt_heapify bt_heapify]. assert (k = 0) by lia. subst k. reflexivity.
  - cbn [c_bt_heapify bt_heapify]. destruct (Z.geb_spec k 1) as [H1|H1].
    + rewrite (Hpq t w k) by (first [exact Hv | lia | unfold HEAP_SIZE in *; lia]). cbn [bind].
      destruct (pqdownheap_correct t w k) as [P1 [P2 [P3 [P4 [P5 [P6 [P7 [P8 [P9 P10]]]]]]]]];
        try (unfold HEAP_SIZE in *; lia); auto.
      set (w1 := pqdownheap t w k) in *.
      apply IH; try lia.
      * intros i Hi. rewrite P1 in Hi.
        assert (Hin : In (Znth i (w_heap w1)) (reg (w_heap w) (w_heap_len w))).
        { apply (Permutation_in _ (Permutation_sym P9)). apply in_reg. exists i. split; auto. }
        apply in_reg in Hin. destruct Hin as [j [Hj Ej]]. rewrite <- Ej, P3. apply Hv; exact Hj.
      * rewrite P1, P3. replace (k - 1 + 1) with k by lia. exact P8.
    + assert (k = 0) by lia. subst k. reflexivity.
Qed.

(** Helpers of [bt_merge_part]: the checked merge step under [minv]. *)
Lemma bm_rd_ok : forall l i, 0 <= i < Zlength l -> rd l i = Some (Znth i l).
Proof.
  intros l i H. unfold rd, in_range.
  replace ((0 <=? i) && (i <? Zlength l)) with true; [reflexivity|].
  symmetry. apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma bm_wr_ok : forall l i v, 0 <= i < Zlength l -> wr l i v = Some (upd_Znth i l v).
Proof.
  intros l i v H. unfold wr, in_range.
  replace ((0 <=? i) && (i <? Zlength l)) with true; [reflexivity|].
  symmetry. apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma bm_store_removed_ok : forall w x, 0 <= w_heap_max w - 1 < Zlength (w_heap w) ->
  c_store_removed w x = Some (store_removed w x).
Proof. intros w x H. unfold c_store_removed. rewrite bm_wr_ok by exact H. reflexivity. Qed.

Lemma bm_new_node_ok : forall t w n m node,
  0 <= n < Zlength (fc t) -> 0 <= m < Zlength (fc t) -> 0 <= node < Zlength (fc t) ->
  Zlength (dl t) = Zlength (fc t) -> Zlength (fc t) <= Zlength (w_depth w) ->
  c_new_node t w n m node = Some (new_node t w n m node).
Proof.
  intros t w n m node Hn Hm Hnode Hdl Hd. unfold c_new_node, c_set_fc, c_set_dl.
  rewrite (bm_rd_ok (fc t) n), (bm_rd_ok (fc t) m) by lia. cbn [bind].
  rewrite bm_wr_ok by lia. cbn [bind fc dl].
  rewrite (bm_rd_ok (w_depth w) n), (bm_rd_ok (w_depth w) m) by lia. cbn [bind].
  rewrite bm_wr_ok by lia. cbn [bind fc dl].
  rewrite bm_wr_ok by lia. cbn [bind fc dl].
  rewrite bm_wr_ok by (rewrite Zlength_upd; lia). reflexivity.
Qed.

Definition bm_ctail (t : tree) (n : Z) (w1 : work) (node : Z) : option (tree * work) :=
  let* m := rd (w_heap w1) SMALLEST in
  let* w2 := c_store_removed w1 n in
  let* w2 := c_store_removed w2 m in
  let* (t3, w3) := c_new_node t w2 n m node in
  let* heap := wr (w_heap w3) SMALLEST node in
  let* w4 := c_pqdownheap t3 (w_set_heap w3 heap) SMALLEST in
  Some (t3, w4).

Definition bm_tail (t : tree) (n : Z) (w1 : work) (node : Z) : tree * work :=
  let m := Znth SMALLEST (w_heap w1) in
  let w2 := store_removed (store_removed w1 n) m in
  let '(t3, w3) := new_node t w2 n m node in
  (t3, pqdownheap t3 (w_set_heap w3 (upd_Znth SMALLEST (w_heap w3) node)) SMALLEST).

Lemma bm_c_merge_body_eq : forall t w node,
  c_merge_body t w node = let* (n, w1) := c_pqremove t w in bm_ctail t n w1 node.
Proof. reflexivity. Qed.

Lemma bm_merge_body_eq : forall t w node,
  merge_body t w node = let '(n, w1) := pqremove t w in bm_tail t n w1 node.
Proof. reflexivity. Qed.

Lemma bm_pqremove_ok : pqdownheap_stmt -> forall t w,
  2 <= w_heap_len w -> w_heap_len w < Zlength (w_heap w) -> Zlength (w_heap w) <= HEAP_SIZE ->
  (forall i, 1 <= i <= w_heap_len w ->
     0 <= Znth i (w_heap w) < Zlength (fc t) /\ Znth i (w_heap w) < Zlength (w_depth w)) ->
  c_pqremove t w = Some (pqremove t w).
Proof.
  intros Hpq t w H2 HL HS Hreg. unfold c_pqremove, pqremove, SMALLEST.
  rewrite (bm_rd_ok (w_heap w) 1) by lia. cbn [bind].
  rewrite (bm_rd_ok (w_heap w) (w_heap_len w)) by lia. cbn [bind].
  rewrite (bm_wr_ok (w_heap w) 1) by lia. cbn [bind].
  rewrite Hpq; [reflexivity| | | |]; cbn [w_heap_len w_set_heap_len w_heap w_set_heap w_depth];
    rewrite ?Zlength_upd; try lia.
  intros i Hi. destruct (Z.eq_dec i 1) as [->|Hne].
  - rewrite upd_Znth_same by lia. apply Hreg; lia.
  - rewrite upd_Znth_diff by lia. apply Hreg; lia.
Qed.

Lemma bm_tail_ok : pqdownheap_stmt -> forall t n w1 node TS,
  Zlength (w_heap w1) = 573 -> Zlength (w_depth w1) = 573 ->
  Zlength (fc t) = TS -> Zlength (dl t) = TS ->
  1 <= w_heap_len w1 -> 2 * w_heap_len w1 + 3 <= w_heap_max w1 <= 573 ->
  0 <= n < node -> node + w_heap_len w1 + 1 <= TS <= 573 ->
  (forall i, 1 <= i <= w_heap_len w1 -> 0 <= Znth i (w_heap w1) < node) ->
  bm_ctail t n w1 node = Some (bm_tail t n w1 node).
Proof.
  intros Hpq t n w1 node TS Hh Hd Hfc Hdl Hlen Hroom Hn Hnode Hreg.
  unfold bm_ctail, bm_tail, SMALLEST.
  assert (Hm : 0 <= Znth 1 (w_heap w1) < node) by (apply Hreg; lia).
  rewrite (bm_rd_ok (w_heap w1) 1) by lia. cbn [bind].
  rewrite bm_store_removed_ok by lia. cbn [bind].
  rewrite bm_store_removed_ok
    by (unfold store_removed; cbn [w_heap_max w_set_heap w_set_heap_max w_heap]; rewrite Zlength_upd; lia).
  cbn [bind].
  set (m := Znth 1 (w_heap w1)) in *.
  set (w2 := store_removed (store_removed w1 n) m).
  assert (W2h : w_heap w2 = upd_Znth (w_heap_max w1 - 1 - 1) (upd_Znth (w_heap_max w1 - 1) (w_heap w1) n) m)
    by (unfold w2, store_removed; cbn [w_heap w_heap_max w_set_heap w_set_heap_max]; reflexivity).
  assert (W2l : w_heap_len w2 = w_heap_len w1)
    by (unfold w2, store_removed; cbn [w_heap_len w_set_heap w_set_heap_max]; reflexivity).
  assert (W2d : w_depth w2 = w_depth w1)
    by (unfold w2, store_removed; cbn [w_depth w_set_heap w_set_heap_max]; reflexivity).
  clearbody w2 m.
  rewrite bm_new_node_ok by (rewrite ?W2d; lia).
  assert (NN1 : Zlength (fc (fst (new_node t w2 n m node))) = TS)
    by (unfold new_node; cbn [fst fc set_dl set_fc]; rewrite Zlength_upd; exact Hfc).
  assert (NN2 : w_heap (snd (new_node t w2 n m node)) = w_heap w2)
    by (unfold new_node; cbn [snd w_heap w_set_depth]; reflexivity).
  assert (NN3 : w_heap_len (snd (new_node t w2 n m node)) = w_heap_len w2)
    by (unfold new_node; cbn [snd w_heap_len w_set_depth]; reflexivity).
  assert (NN4 : Zlength (w_depth (snd (new_node t w2 n m node))) = 573)
    by (unfold new_node; cbn [snd w_depth w_set_depth]; rewrite Zlength_upd, W2d; exact Hd).
  destruct (new_node t w2 n m node) as [t3 w3]. cbn [fst snd] in NN1, NN2, NN3, NN4. cbn [bind].
  assert (HL2 : Zlength (w_heap w2) = 573) by (rewrite W2h, !Zlength_upd; exact Hh).
  rewrite bm_wr_ok by (rewrite NN2; lia). cbn [bind].
  rewrite (Hpq t3); [reflexivity| | | |].
  { cbn [w_heap_len w_set_heap]. lia. }
  { cbn [w_heap_len w_heap w_set_heap]. rewrite Zlength_upd, NN2. lia. }
  { cbn [w_heap_len w_heap w_set_heap]. rewrite Zlength_upd, NN2. unfold HEAP_SIZE; lia. }
  cbn [w_heap_len w_heap w_set_heap w_depth]. intros i Hi.
  destruct (Z.eq_dec i 1) as [->|Hne].
  - rewrite upd_Znth_same by (rewrite NN2; lia). lia.
  - rewrite upd_Znth_diff by (rewrite ?NN2; lia). rewrite NN2, W2h.
    rewrite !upd_Znth_diff by (rewrite ?Zlength_upd; lia). specialize (Hreg i ltac:(lia)). lia.
Qed.

Lemma bm_body_ok : pqdownheap_stmt -> forall TS elems total S f0 t w node it Q,
  minv TS elems total S f0 t w node it Q -> 2 <= w_heap_len w ->
  c_merge_body t w node = Some (merge_body t w node).
Proof.
  intros Hpq TS elems total S f0 t w node it Q HI H2.
  destruct HI as [Hh Hd Hfc Hdl Hlen Hroom Hnode Hhp Hst Hperm Hpool Htot Hnd Hch Hrem Hleaf Hnonem Hdescs Hkind Hrkind Hunused].
  clear Hst Hperm Htot Hnd Hch Hrem Hleaf Hnonem Hdescs Hkind Hrkind Hunused.
  assert (Hreg_old : forall i, 1 <= i <= w_heap_len w -> 0 <= Znth i (w_heap w) < node)
    by (intros i Hi; apply Hpool, in_reg; exists i; split; [lia|reflexivity]).
  rewrite bm_c_merge_body_eq, bm_merge_body_eq.
  rewrite (bm_pqremove_ok Hpq) by (unfold HEAP_SIZE in *; first [lia | intros i Hi; specialize (Hreg_old i Hi); lia]).
  unfold pqremove, SMALLEST. cbn [bind].
  set (heap1 := upd_Znth 1 (w_heap w) (Znth (w_heap_len w) (w_heap w))).
  set (w0 := w_set_heap_len (w_set_heap w heap1) (w_heap_len w - 1)).
  assert (HL1 : Zlength heap1 = 573) by (unfold heap1; rewrite Zlength_upd; unfold HEAP_SIZE in *; lia).
  assert (Hreg1 : forall i, 1 <= i <= w_heap_len w - 1 -> 0 <= Znth i heap1 < node).
  { intros i Hi. unfold heap1. destruct (Z.eq_dec i 1) as [->|Hne].
    - rewrite upd_Znth_same by (unfold HEAP_SIZE in *; lia). apply Hreg_old; lia.
    - rewrite upd_Znth_diff by (unfold HEAP_SIZE in *; lia). apply Hreg_old; lia. }
  assert (Hhp1 : hp t (w_depth w) heap1 (w_heap_len w - 1) 2).
  { intros i Hi Hi2. unfold heap1. assert (Hd2 := div2_lt i ltac:(lia)).
    rewrite !upd_Znth_diff by (unfold HEAP_SIZE in *; lia). apply Hhp; lia. }
  destruct (pqdownheap_correct t w0 1) as [P1len [P1hm [P1dep [_ [_ [_ [P1L [_ [P1perm _]]]]]]]]].
  { unfold w0; cbn [w_heap_len w_set_heap_len]; lia. }
  { unfold w0; cbn [w_heap_len w_set_heap_len w_heap w_set_heap]; unfold HEAP_SIZE in *; lia. }
  { unfold w0; cbn [w_heap_len w_set_heap_len]; unfold HEAP_SIZE in *; lia. }
  { exact Hhp1. }
  assert (Hreg1' : forall i, 1 <= i <= w_heap_len w - 1 -> 0 <= Znth i (w_heap (pqdownheap t w0 1)) < node).
  { intros i Hi. assert (Hin : In (Znth i (w_heap (pqdownheap t w0 1))) (reg heap1 (w_heap_len w - 1))).
    { eapply Permutation_in; [apply Permutation_sym, P1perm|]. apply in_reg. exists i; split; [|reflexivity].
      unfold w0 in *; cbn [w_heap_len w_set_heap_len] in *. lia. }
    apply in_reg in Hin. destruct Hin as [j [Hj <-]]. apply Hreg1; lia. }
  revert P1len P1hm P1dep P1L Hreg1'. generalize (pqdownheap t w0 1) as w1. intros w1 P1len P1hm P1dep P1L Hreg1'.
  unfold w0 in P1len, P1hm, P1dep. cbn [w_heap_len w_heap_max w_depth w_set_heap_len w_set_heap] in P1len, P1hm, P1dep.
  unfold HEAP_SIZE in *.
  apply (bm_tail_ok Hpq) with (TS := TS); try lia.
  all: first [ rewrite P1L; exact HL1 | rewrite P1dep; exact Hd | intros i Hi; apply Hreg1'; lia | apply Hreg_old; lia ].
Qed.

(** The merge loop, under the merge invariant of BuildTree.v. *)
Definition bt_merge_stmt : Prop := forall TS elems total S f0, total < 65536 ->
  forall fuel t w node it Q,
  minv TS elems total S f0 t w node it Q -> 2 <= w_heap_len w -> (Z.to_nat (w_heap_len w - 1) <= fuel)%nat ->
  c_bt_merge fuel t w node = Some (bt_merge fuel t w node).
Lemma bt_merge_part : pqdownheap_stmt -> bt_merge_stmt.
Proof.
  intros Hpq TS elems total S f0 Htot fuel. induction fuel as [|fuel IH]; intros t w node it Q HI H2 Hf; [lia|].
  cbn [c_bt_merge]. rewrite (bm_body_ok Hpq TS elems total S f0 t w node it Q HI H2). cbn [bind].
  rewrite bt_merge_unfold.
  destruct (merge_step TS elems total S f0 t w node it Q HI H2 Htot) as [it1 [Q1 [HI1 Hlen1]]].
  destruct (merge_body t w node) as [t1 w1]. cbn [fst snd] in HI1, Hlen1.
  destruct (Z.geb_spec (w_heap_len w1) 2) as [Hge|Hlt].
  - apply (IH t1 w1 (node + 1) it1 Q1 HI1 Hge). lia.
  - reflexivity.
Qed.

(** build_tree up to gen_bitlen (follows BuildPre.bt_pre_spec). *)
Definition bt_pre_stmt : Prop := forall sd t w, bt_req sd t w -> desc_ok sd ->
  c_bt_pre sd t w = Some (bt_pre sd t w).
Lemma reg_In_Znth : forall heap len i, 1 <= i <= len -> In (Znth i heap) (reg heap len).
Proof.
  intros heap len i Hi. unfold reg. apply (in_map (fun i => Znth i heap)). apply in_zseq. lia.
Qed.

Lemma bt_pre_part : bt_init_stmt -> bt_force_stmt -> bt_heapify_stmt -> bt_merge_stmt -> bt_pre_stmt.
Proof.
  intros HI HF HH HM sd t w HR Hdesc.
  destruct HR as [[Hel [HM15 Hpow]] [HTS HTS2] [Hh [Hd [Hol Hsl]]] Hfr [Hfc0 Hsum] [Hxb Hst]].
  set (elems := sd_elems sd) in *.
  unfold c_bt_pre, bt_pre. fold elems.
  set (w0 := w_set_heap_max (w_set_heap_len w 0) HEAP_SIZE).
  assert (Hw0h : Zlength (w_heap w0) = HEAP_SIZE) by exact Hh.
  assert (Hw0d : Zlength (w_depth w0) = HEAP_SIZE) by exact Hd.
  rewrite (HI elems (Z.to_nat elems) t w0 (-1) 0) by (unfold HEAP_SIZE in *; cbn; lia).
  cbn [bind].
  assert (I := bt_init_spec elems (Z.to_nat elems) t w0 (-1) 0).
  specialize (I ltac:(lia) ltac:(lia) ltac:(unfold HEAP_SIZE in *; lia) Hw0h Hw0d ltac:(lia) eq_refl eq_refl
                ltac:(intros i Hi; lia) (or_introl (conj eq_refl eq_refl))).
  destruct (bt_init (Z.to_nat elems) elems t w0 (-1) 0) as [[t1 w1] mc1] eqn:Einit.
  destruct I as [I1 [I2 [I3 [I4 [I5 [I6 [I7 [I8 [I9 [I10 [I11 I12]]]]]]]]]]].
  (* bt_force *)
  assert (A4 : elems <= Zlength (fc t1)) by (rewrite I1; lia).
  assert (A5 : 0 <= w_heap_len w1) by (rewrite I3; apply Zlength_nonneg).
  rewrite (HF sd t1 w1 mc1); cycle 1.
  { lia. }
  { exact Hdesc. }
  { exact I9. }
  { exact I10. }
  { exact A4. }
  { exact A5. }
  { intros H0. destruct I12 as [[E _]|[Hin _]]; [exact E|].
    rewrite I3 in H0. apply Zlength_nil_inv in H0. rewrite H0 in Hin. destruct Hin. }
  { intros H1. destruct I12 as [[_ E]|[Hin _]].
    - rewrite I3, E in H1. discriminate.
    - apply in_nzl in Hin. lia. }
  cbn [bind].
  assert (Fz := bt_force_spec sd t1 w1 mc1).
  assert (A6 : 0 <= w_opt_len w1 < 18446744073709551616) by (rewrite I7; exact Hol).
  assert (A7 : 0 <= w_static_len w1 < 18446744073709551616) by (rewrite I8; exact Hsl).
  assert (A8 : NoDup (reg (w_heap w1) (w_heap_len w1))) by (rewrite I4; apply nzl_nodup).
  assert (A9 : forall x, In x (reg (w_heap w1) (w_heap_len w1)) -> 0 <= x < elems /\ Znth x (fc t1) <> 0)
    by (intros x Hx; rewrite I4 in Hx; rewrite I1; apply in_nzl in Hx; lia).
  assert (A10 : forall x, 0 <= x < elems -> Znth x (fc t1) <> 0 -> In x (reg (w_heap w1) (w_heap_len w1)))
    by (intros x Hx Hz; rewrite I4; rewrite I1 in Hz; apply in_nzl; lia).
  assert (A11 : mc1 = -1 /\ reg (w_heap w1) (w_heap_len w1) = [] \/
                In mc1 (reg (w_heap w1) (w_heap_len w1)) /\ forall i, In i (reg (w_heap w1) (w_heap_len w1)) -> i <= mc1)
    by (rewrite I4; exact I12).
  specialize (Fz Hel I9 I10 A4 A5 A6 A7 A8 A9 A10 A11). cbv zeta in Fz.
  destruct (bt_force 2 sd t1 w1 mc1) as [[t2 w2] mc2] eqn:Eforce.
  destruct Fz as [F [F1 [F2 [F3 [F4 [F5 [F6 [F7 [F8 [F9 [F10 [F11 [F12 [F13 [F14 [F15 [F16 [F17 F18]]]]]]]]]]]]]]]]]].
  rewrite I4 in F1, F5, F10, F11.
  set (S := nzl (fc t) elems ++ F) in *.
  assert (HSel : forall x, In x S -> 0 <= x < elems).
  { intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [apply in_nzl in Hx; lia|apply F6; auto]. }
  assert (HSlen : Zlength S <= elems).
  { assert (H := NoDup_incl_Zlength S (zseq 0 (Z.to_nat elems)) F5 ltac:(intros x Hx; apply in_zseq; specialize (HSel x Hx); lia)).
    rewrite (Zlength_correct (zseq _ _)), zseq_length in H. lia. }
  assert (Hlen2 : w_heap_len w2 = Zlength S) by (rewrite <- F1; symmetry; apply reg_len; lia).
  (* bt_heapify *)
  set (k := w_heap_len w2 / 2).
  assert (Hk : 0 <= k <= w_heap_len w2) by (unfold k; split; [apply Z.div_pos|apply Z.div_le_upper_bound]; lia).
  assert (Hent2 : forall i, 1 <= i <= w_heap_len w2 ->
     0 <= Znth i (w_heap w2) < Zlength (fc t2) /\ Znth i (w_heap w2) < Zlength (w_depth w2)).
  { intros i Hi. assert (Hin := reg_In_Znth (w_heap w2) (w_heap_len w2) i Hi). rewrite F1 in Hin.
    specialize (HSel _ Hin). rewrite F9, I1, F17. unfold HEAP_SIZE in *. lia. }
  rewrite (HH (Z.to_nat k) t2 w2 k Hk ltac:(lia) ltac:(unfold HEAP_SIZE in *; lia) F16 Hent2
             ltac:(unfold k; apply hp_half)).
  cbn [bind].
  assert (Hy := bt_heapify_spec (Z.to_nat k) t2 w2 k Hk ltac:(lia) ltac:(unfold HEAP_SIZE in *; lia) F16
                  ltac:(unfold k; apply hp_half)).
  cbv zeta in Hy.
  set (w3 := bt_heapify (Z.to_nat k) t2 w2 k) in *.
  destruct Hy as [Y1 [Y2 [Y3 [Y4 [Y5 [Y6 [Y7 [Y8 Y9]]]]]]]].
  (* initial invariant *)
  set (f0 := fun x => Znth x (fc t2)).
  assert (Hf0 : forall x, In x S -> 1 <= f0 x).
  { intros x Hx. unfold f0. rewrite F7. destruct (in_dec Z.eq_dec x F) as [|Hn]; [lia|].
    apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [|contradiction]. apply in_nzl in Hx. rewrite I1.
    specialize (Hfc0 x ltac:(lia)). lia. }
  assert (B1 : 3 <= elems) by lia.
  assert (B2 : 2 * elems + 1 <= Zlength (fc t2) <= HEAP_SIZE) by (rewrite F9, I1; lia).
  assert (B3 : Zlength (dl t2) = Zlength (fc t2)) by (rewrite F8, F9, I1, I2; lia).
  assert (B4 : Zlength (w_depth w3) = HEAP_SIZE) by (rewrite Y5; exact F17).
  assert (B5 : w_heap_max w3 = HEAP_SIZE) by (rewrite Y4, F14, I5; reflexivity).
  assert (B6 : 2 <= w_heap_len w3) by (rewrite Y3; lia).
  assert (B7 : Zlength S = w_heap_len w3) by (rewrite Y3; lia).
  assert (B8 : Permutation S (reg (w_heap w3) (w_heap_len w3))) by (rewrite Y3, <- F1; exact Y2).
  assert (B9 : forall x, In x S -> 0 <= x < elems /\ Znth x (fc t2) = f0 x /\ 0 <= f0 x)
    by (intros x Hx; specialize (Hf0 x Hx); split; [apply HSel; auto|split; [reflexivity|lia]]).
  assert (B10 : hp t2 (w_depth w3) (w_heap w3) (w_heap_len w3) 1) by (rewrite Y3, Y5; exact Y1).
  assert (B0 : forall c, 0 <= c < elems -> ~ In c S -> Znth c (dl t2) = 0).
  { intros c Hc HcS. rewrite F8. apply I11; auto. destruct (Z.eq_dec (Znth c (fc t)) 0) as [|Hne]; auto.
    exfalso. apply HcS. unfold S. apply in_or_app; left. apply in_nzl. split; auto. }
  assert (Hm0 := init_minv (Zlength (fc t2)) elems S f0 t2 w3 B0 B1 B2 eq_refl B3 Y9 B4 B5 B6 B7 B8 F5 B9 B10).
  assert (Hdisj : forall x, In x F -> ~ In x (nzl (fc t) elems)).
  { intros x HxF Hxn. exact (nodup_app_disj (nzl (fc t) elems) F x F5 Hxn HxF). }
  assert (Htot : sumZ (map f0 S) < 65536).
  { unfold S. rewrite map_app, sumZ_app.
    replace (map f0 (nzl (fc t) elems)) with (map (fun i => Znth i (fc t)) (nzl (fc t) elems)).
    2:{ apply map_ext_in. intros x Hx. unfold f0. rewrite F7, I1.
        destruct (in_dec Z.eq_dec x F) as [Hc|]; [exfalso; exact (Hdisj x Hc Hx)|reflexivity]. }
    unfold nzl. rewrite sumZ_filter_nz.
    replace (map f0 F) with (map (fun _ => 1) F).
    2:{ apply map_ext_in. intros x Hx. unfold f0. rewrite F7. destruct (in_dec Z.eq_dec x F); [reflexivity|contradiction]. }
    assert (sumZ (map (fun _ : Z => 1) F) = Zlength F).
    { clear. induction F as [|a F IH]; cbn [map sumZ]; [reflexivity|]. rewrite IH, Zlength_cons. lia. }
    lia. }
  (* the merge loop *)
  rewrite (HM (Zlength (fc t2)) elems (sumZ (map f0 S)) S f0 Htot
                      (Z.to_nat (w_heap_len w3)) t2 w3 elems _ _ Hm0 B6 ltac:(lia)).
  cbn [bind].
  assert (Hmerge := bt_merge_inv (Zlength (fc t2)) elems (sumZ (map f0 S)) S f0 Htot
                      (Z.to_nat (w_heap_len w3)) t2 w3 elems _ _ Hm0 B6 ltac:(lia)).
  destruct (bt_merge (Z.to_nat (w_heap_len w3)) t2 w3 elems) as [[t4 w4] node4] eqn:Emerge.
  destruct Hmerge as [it4 [Q4 [Hm4 [Hlen4 Hnode4]]]].
  assert (Hh4 := mi_heap _ _ _ _ _ _ _ _ _ _ Hm4).
  assert (Hroom4 := mi_room _ _ _ _ _ _ _ _ _ _ Hm4).
  unfold rd, in_range. rewrite Hh4. unfold SMALLEST, HEAP_SIZE. cbn [andb Z.leb Z.ltb Z.compare]. cbn [bind].
  change (1 <? 573) with true. cbn [bind]. unfold c_store_removed, wr, in_range. rewrite Hh4. rewrite Hlen4 in Hroom4.
  replace ((0 <=? w_heap_max w4 - 1) && (w_heap_max w4 - 1 <? HEAP_SIZE)) with true
    by (unfold HEAP_SIZE in *; symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  cbn [bind]. reflexivity.
Qed.

(** gen_bitlen's first pass, on the state before gen_bitlen (hypotheses of BuildThm's section Gen). *)
Definition pass1_stmt : Prop := forall sd t0 w0 S F R t w mc,
  pre_ok sd t0 w0 S F R t w mc ->
  1 <= sd_maxlen sd <= 15 -> 3 <= sd_elems sd <= 286 -> sd_elems sd <= Zlength (dl t) ->
  (forall n, 0 <= n < Zlength (dl t) -> 0 <= xb sd n <= 16) ->
  (forall st, sd_stree sd = Some st -> forall n, 0 <= n < Zlength (dl t) -> 0 <= Znth n st <= 16) ->
  (forall n, 0 <= n < Zlength (dl t) -> 0 <= Znth n (fc t) < 65536) ->
  0 <= w_opt_len w < 18446744073709551616 -> 0 <= w_static_len w < 18446744073709551616 ->
  sd_elems sd <= 2 ^ sd_maxlen sd ->
  desc_ok sd -> Zlength (fc t) = Zlength (dl t) ->
  c_gen_bitlen_pass1 (Z.to_nat HEAP_SIZE) sd mc (set_dl t (Znth (w_heap_max w) (w_heap w)) 0)
    (w_set_bl_count w (repeat 0 (Z.to_nat (MAX_BITS + 1)))) 0 (w_heap_max w + 1) =
  Some (gen_bitlen_pass1 (Z.to_nat HEAP_SIZE) sd mc (set_dl t (Znth (w_heap_max w) (w_heap w)) 0)
    (w_set_bl_count w (repeat 0 (Z.to_nat (MAX_BITS + 1)))) 0 (w_heap_max w + 1)).
(** Helpers of pass1_part. *)
Lemma p1_rd : forall l i, 0 <= i < Zlength l -> rd l i = Some (Znth i l).
Proof.
  intros l i Hi. unfold rd, in_range.
  replace ((0 <=? i) && (i <? Zlength l)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma p1_wr : forall l i v, 0 <= i < Zlength l -> wr l i v = Some (upd_Znth i l v).
Proof.
  intros l i v Hi. unfold wr, in_range.
  replace ((0 <=? i) && (i <? Zlength l)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

(** The facts of the pre-gen_bitlen state that the checked first pass needs. *)
Definition p1_ctx (sd : stat_desc) (mc hm : Z) (heap D0 fc0 : list Z) : Prop :=
  NoDup (removed heap hm) /\ 1 <= hm < HEAP_SIZE /\ Zlength heap = HEAP_SIZE /\
  (forall p, hm < p < HEAP_SIZE -> exists q, hm <= q < p /\ Znth q heap = Znth (Znth p heap) D0) /\
  1 <= sd_maxlen sd <= 15 /\
  (forall p, hm <= p < HEAP_SIZE -> 0 <= Znth p heap < Zlength D0) /\
  Zlength fc0 = Zlength D0 /\ desc_ok sd /\
  (forall p, hm < p < HEAP_SIZE -> Znth p heap <= mc -> Znth p heap < sd_elems sd).

(** What the checked reads need: processed nodes hold a length in [0, M], unprocessed ones their Dad. *)
Definition p1_inv (sd : stat_desc) (hm : Z) (heap D0 fc0 : list Z) (h : Z) (t : tree) (w : work) : Prop :=
  fc t = fc0 /\ Zlength (dl t) = Zlength D0 /\ w_heap w = heap /\ Zlength (w_bl_count w) = 16 /\
  (forall q, hm <= q < h -> 0 <= Znth (Znth q heap) (dl t) <= sd_maxlen sd) /\
  (forall p, h <= p < HEAP_SIZE -> Znth (Znth p heap) (dl t) = Znth (Znth p heap) D0).

Lemma p1_inv_set : forall sd mc hm heap D0 fc0, p1_ctx sd mc hm heap D0 fc0 -> forall h t w w' bits, hm < h < HEAP_SIZE -> p1_inv sd hm heap D0 fc0 h t w ->
  0 <= bits <= sd_maxlen sd -> w_heap w' = heap -> Zlength (w_bl_count w') = 16 ->
  p1_inv sd hm heap D0 fc0 (h + 1) (set_dl t (Znth h heap) (u16 bits)) w'.
Proof.
  intros sd mc hm heap D0 fc0 Hctx. pose proof Hctx as [Hnd [Hhm [Hheap [Hdad [HM [Hidx [Hfc [Hdesc Hleaf]]]]]]]].
  intros h t w w' bits Hh [I1 [I2 [I3 [I4 [I5 I6]]]]] Hb W1 W2.
  assert (Hn : 0 <= Znth h heap < Zlength (dl t)) by (rewrite I2; apply Hidx; lia).
  assert (Hu : u16 bits = bits) by (unfold u16; apply Z.mod_small; lia).
  unfold p1_inv, set_dl; simpl dl; simpl fc. rewrite Hu.
  split; [exact I1|]. split; [rewrite Zlength_upd_Znth_any; exact I2|]. split; [exact W1|]. split; [exact W2|].
  split.
  - intros q Hq. destruct (Z.eq_dec q h) as [->|Hne].
    + rewrite upd_Znth_same by lia. lia.
    + assert (Hq' : 0 <= Znth q heap < Zlength (dl t)) by (rewrite I2; apply Hidx; lia).
      rewrite upd_Znth_diff by (try lia; intros Hc; apply (removed_Znth_inj _ _ _ _ Hnd) in Hc; lia). apply I5; lia.
  - intros p Hp. assert (Hp' : 0 <= Znth p heap < Zlength (dl t)) by (rewrite I2; apply Hidx; lia).
    rewrite upd_Znth_diff by (try lia; intros Hc; apply (removed_Znth_inj _ _ _ _ Hnd) in Hc; lia). apply I6; lia.
Qed.

Lemma p1_checked : forall sd mc hm heap D0 fc0, p1_ctx sd mc hm heap D0 fc0 -> forall fuel h t w ovf,
  hm < h <= HEAP_SIZE -> (Z.to_nat (HEAP_SIZE - h) <= fuel)%nat -> p1_inv sd hm heap D0 fc0 h t w ->
  c_gen_bitlen_pass1 fuel sd mc t w ovf h = Some (gen_bitlen_pass1 fuel sd mc t w ovf h).
Proof.
  intros sd mc hm heap D0 fc0 Hctx. pose proof Hctx as [Hnd [Hhm [Hheap [Hdad [HM [Hidx [Hfc [Hdesc Hleaf]]]]]]]].
  induction fuel as [|fuel IH]; intros h t w ovf Hh Hf Hinv.
  - assert (h = HEAP_SIZE) by lia. subst h. reflexivity.
  - cbn [c_gen_bitlen_pass1 gen_bitlen_pass1].
    destruct (Z.ltb_spec h HEAP_SIZE) as [Hlt|Hge]; [|reflexivity].
    pose proof Hinv as [I1 [I2 [I3 [I4 [I5 I6]]]]].
    rewrite (p1_rd (w_heap w) h) by (rewrite I3; lia). cbn [bind]. rewrite I3.
    set (n := Znth h heap).
    assert (Hn : 0 <= n < Zlength (dl t)) by (rewrite I2; apply Hidx; lia).
    rewrite (p1_rd (dl t) n) by exact Hn. cbn [bind].
    destruct (Hdad h ltac:(lia)) as [q [Hq Eq]]. fold n in Eq.
    assert (Hd : Znth n (dl t) = Znth q heap) by (rewrite Eq; apply (I6 h); lia).
    assert (Hdr : 0 <= Znth n (dl t) < Zlength (dl t)) by (rewrite Hd, I2; apply Hidx; lia).
    rewrite (p1_rd (dl t) (Znth n (dl t))) by exact Hdr. cbn [bind].
    assert (Hld : 0 <= Znth (Znth n (dl t)) (dl t) <= sd_maxlen sd) by (rewrite Hd; apply I5; lia).
    destruct (if Znth (Znth n (dl t)) (dl t) + 1 >? sd_maxlen sd then (sd_maxlen sd, ovf + 1)
              else (Znth (Znth n (dl t)) (dl t) + 1, ovf)) as [bits ovf'] eqn:Hbo.
    assert (Hbits : 1 <= bits <= sd_maxlen sd).
    { destruct (Z.gtb_spec (Znth (Znth n (dl t)) (dl t) + 1) (sd_maxlen sd)); inversion Hbo; lia. }
    unfold c_set_dl. rewrite (p1_wr (dl t) n) by exact Hn. cbn [bind].
    change (mkTree (fc t) (upd_Znth n (dl t) (u16 bits))) with (set_dl t n (u16 bits)).
    destruct (Z.gtb_spec n mc) as [Hmc|Hmc].
    + apply IH; [lia|lia|]. apply (p1_inv_set sd mc hm heap D0 fc0 Hctx h t w w bits); auto; lia.
    +
      assert (Hne : n < sd_elems sd) by (apply Hleaf; [lia|exact Hmc]).
      destruct Hdesc as [D1 [D2 D3]].
      rewrite (p1_rd (w_bl_count w) bits) by lia. cbn [bind].
      rewrite (p1_wr (w_bl_count w) bits) by lia. cbn [bind].
      assert (Hxb : (if n >=? sd_base sd then rd (sd_extra sd) (n - sd_base sd) else Some 0) =
                    Some (if n >=? sd_base sd then Znth (n - sd_base sd) (sd_extra sd) else 0)).
      { destruct (Z.geb_spec n (sd_base sd)); [|reflexivity]. apply p1_rd. lia. }
      rewrite Hxb. cbn [bind].
      assert (Hfr : 0 <= n < Zlength (fc (set_dl t n (u16 bits)))) by (unfold set_dl; simpl fc; rewrite I1, Hfc, <- I2; lia).
      rewrite (p1_rd (fc (set_dl t n (u16 bits))) n) by exact Hfr. cbn [bind].
      destruct (sd_stree sd) as [st|] eqn:Est.
      * rewrite (p1_rd st n) by (specialize (D3 st eq_refl); lia). cbn [bind].
        apply IH; [lia|lia|]. apply (p1_inv_set sd mc hm heap D0 fc0 Hctx h t w); auto; try lia; simpl w_heap; simpl w_bl_count; auto.
        rewrite Zlength_upd_Znth_any; exact I4.
      * apply IH; [lia|lia|]. apply (p1_inv_set sd mc hm heap D0 fc0 Hctx h t w); auto; try lia; simpl w_heap; simpl w_bl_count; auto.
        rewrite Zlength_upd_Znth_any; exact I4.
Qed.


Lemma pass1_part : pass1_stmt.
Proof.
  intros sd t0 w0 S F R t w mc Hpre HM Hel Hdlen Hxb Hst Hfcr Hopt Hstl Hpow Hdesc Hfcl.
  assert (Hhm := po_hm _ _ _ _ _ _ _ _ _ Hpre).
  assert (Hheap := po_heap _ _ _ _ _ _ _ _ _ Hpre).
  assert (Hnd := po_nodup _ _ _ _ _ _ _ _ _ Hpre).
  assert (Hidx := pre_idx sd t0 w0 S F R t w mc Hpre Hel Hdlen).
  assert (Hroot := Hidx (w_heap_max w) ltac:(lia)).
  assert (Hctx : p1_ctx sd mc (w_heap_max w) (w_heap w) (dl t) (fc t)).
  { split; [exact Hnd|]. split; [lia|]. split; [exact Hheap|]. split.
    { intros p Hp. destruct (po_dad _ _ _ _ _ _ _ _ _ Hpre p Hp) as [q [Hq Eq]]. exists q. split; [exact Hq|exact Eq]. }
    split; [lia|]. split; [exact Hidx|]. split; [lia|]. split; [exact Hdesc|].
    intros p Hp Hle. destruct (po_mc _ _ _ _ _ _ _ _ _ Hpre) as [Hmc _].
      destruct (po_S _ _ _ _ _ _ _ _ _ Hpre) as [_ [_ [HSr _]]].
      assert (Hmc' := HSr _ Hmc).
      destruct (po_kind _ _ _ _ _ _ _ _ _ Hpre p ltac:(lia)) as [HS|HI].
      + apply HSr in HS. lia.
      + lia. }
  apply (p1_checked _ _ _ _ _ _ Hctx).
  - lia.
  - unfold HEAP_SIZE in *. lia.
  - unfold p1_inv, set_dl; simpl dl; simpl fc; simpl w_heap; simpl w_bl_count.
    split; [reflexivity|]. split; [apply Zlength_upd_Znth_any|]. split; [reflexivity|].
    split; [reflexivity|]. split.
    + intros q Hq. assert (q = w_heap_max w) by lia. subst q. rewrite upd_Znth_same by lia. lia.
    + intros p Hp. assert (Hp' := Hidx p ltac:(lia)).
      rewrite upd_Znth_diff by (try lia; intros Hc; apply (removed_Znth_inj _ _ _ _ Hnd) in Hc; lia).
      reflexivity.
Qed.

Lemma rp_rd : forall l i, 0 <= i < Zlength l -> rd l i = Some (Znth i l).
Proof.
  intros l i H. unfold rd, in_range.
  replace ((0 <=? i) && (i <? Zlength l)) with true by (symmetry; rewrite andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma rp_wr : forall l i v, 0 <= i < Zlength l -> wr l i v = Some (upd_Znth i l v).
Proof.
  intros l i v H. unfold wr, in_range.
  replace ((0 <=? i) && (i <? Zlength l)) with true by (symmetry; rewrite andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma rp_find : forall fuel c x,
  (exists y, 1 <= y <= x /\ Znth y c <> 0) -> x <= Z.of_nat fuel -> x < Zlength c ->
  c_find_nonzero_down fuel c x = Some (find_nonzero_down fuel c x).
Proof.
  induction fuel as [|f IH]; intros c x [y [Hy Hny]] Hx Hl; [lia|].
  cbn [c_find_nonzero_down find_nonzero_down]. rewrite rp_rd by lia. cbn [bind].
  destruct (Znth x c =? 0) eqn:E; [|reflexivity].
  apply Z.eqb_eq in E. assert (y <> x) by (intro; subst; contradiction).
  apply IH; [exists y; split; [lia|auto]|lia|lia].
Qed.

Lemma rp_step : forall f M J c ovf, 1 <= M <= 15 -> 0 <= J -> rinv M (J + 1) c ->
  c_gen_bitlen_repair (S f) M c ovf =
  if ovf - 2 >? 0 then c_gen_bitlen_repair f M (rstep M c) (ovf - 2) else Some (rstep M c).
Proof.
  intros f M J c ovf HM HJ Hinv.
  destruct (step_level M J c HM HJ Hinv) as [b [Hb [Hb1 [Hcb Hz]]]].
  pose proof Hinv as [Hlen _].
  cbn [c_gen_bitlen_repair].
  rewrite rp_find.
  2:{ exists b; split; [lia|]. lia. }
  2:{ simpl; lia. }
  2:{ lia. }
  rewrite Hb. cbn [bind].
  rewrite rp_rd by lia. cbn [bind].
  rewrite rp_wr by lia. cbn [bind].
  rewrite rp_rd by (rewrite !Zlength_upd_Znth_any; lia). cbn [bind].
  rewrite rp_wr by (rewrite !Zlength_upd_Znth_any; lia). cbn [bind].
  rewrite rp_rd by (rewrite !Zlength_upd_Znth_any; lia). cbn [bind].
  rewrite rp_wr by (rewrite !Zlength_upd_Znth_any; lia). cbn [bind].
  unfold rstep, rstep_at. rewrite Hb. reflexivity.
Qed.

Lemma rp_iter : forall M (J f : nat) c, 1 <= M <= 15 -> rinv M (Z.of_nat (S J)) c -> (J <= f)%nat ->
  c_gen_bitlen_repair (S f) M c (2 * Z.of_nat (S J)) = Some (gen_bitlen_repair (S f) M c (2 * Z.of_nat (S J))).
Proof.
  intros M J; induction J as [|J IH]; intros f c HM Hinv Hf.
  - rewrite (rp_step f M 0 c) by (auto; lia || (replace (0 + 1) with (Z.of_nat 1) by lia; exact Hinv)).
    rewrite repair_unfold. simpl. reflexivity.
  - rewrite (rp_step f M (Z.of_nat (S J)) c) by
      (auto; lia || (replace (Z.of_nat (S J) + 1) with (Z.of_nat (S (S J))) by lia; exact Hinv)).
    rewrite repair_unfold. destruct f as [|f]; [lia|].
    replace (2 * Z.of_nat (S (S J)) - 2 >? 0) with true by (symmetry; apply Z.gtb_lt; lia).
    replace (2 * Z.of_nat (S (S J)) - 2) with (2 * Z.of_nat (S J)) by lia.
    destruct (rstep_inv M (Z.of_nat (S J)) c HM ltac:(lia)) as [H1 _];
      [replace (Z.of_nat (S J) + 1) with (Z.of_nat (S (S J))) by lia; exact Hinv|].
    apply IH; auto; lia.
Qed.

(** The overflow repair loop, under Repair.rinv (Repair.repair_correct). *)
Definition repair_stmt : Prop := forall M c I, 1 <= M <= 15 -> 1 <= I -> rinv M I c ->
  c_gen_bitlen_repair (Z.to_nat HEAP_SIZE) M c (2 * I) = Some (gen_bitlen_repair (Z.to_nat HEAP_SIZE) M c (2 * I)).
Lemma repair_part : repair_stmt.
Proof.
  intros M c I HM HI Hinv.
  assert (Hfuel : (Z.to_nat I - 1 <= 572)%nat).
  { destruct Hinv as [_ [Hnn [_ [Ht [_ HcM]]]]].
    assert (Znth M c <= tot M c) by (apply count_le_tot; auto; lia). lia. }
  replace (Z.to_nat HEAP_SIZE) with (S 572) by reflexivity.
  replace I with (Z.of_nat (S (Z.to_nat I - 1))) by lia.
  apply rp_iter; [exact HM| |lia].
  replace (Z.of_nat (S (Z.to_nat I - 1))) with I by lia. exact Hinv.
Qed.

(** Helpers of [reassign_part]. *)
Lemma ra_rd_in : forall l i, 0 <= i < Zlength l -> rd l i = Some (Znth i l).
Proof.
  intros l i Hi. unfold rd, in_range.
  replace ((0 <=? i) && (i <? Zlength l)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  reflexivity.
Qed.

Lemma ra_set_dl_in : forall t i v, 0 <= i < Zlength (dl t) -> c_set_dl t i v = Some (set_dl t i v).
Proof.
  intros t i v Hi. unfold c_set_dl, wr, in_range.
  replace ((0 <=? i) && (i <? Zlength (dl t))) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  reflexivity.
Qed.

Lemma ra_lstep_len : forall m bits t opt, 0 <= m < Zlength (dl t) ->
  Zlength (dl (fst (lstep m bits t opt))) = Zlength (dl t) /\ fc (fst (lstep m bits t opt)) = fc t.
Proof.
  intros m bits t opt Hm. unfold lstep. destruct (negb (Znth m (dl t) =? bits)); cbn [fst]; [|auto].
  unfold set_dl; cbn [dl fc]. rewrite upd_Znth_Zlength by lia. auto.
Qed.

Lemma ra_apply_lens_len : forall ms ls t opt, (forall m, In m ms -> 0 <= m < Zlength (dl t)) ->
  Zlength (dl (fst (apply_lens ms ls t opt))) = Zlength (dl t) /\ fc (fst (apply_lens ms ls t opt)) = fc t.
Proof.
  induction ms as [|m ms IH]; intros [|l ls] t opt Hms; cbn [apply_lens]; auto.
  destruct (ra_lstep_len m l t opt ltac:(apply Hms; left; auto)) as [E1 E2].
  destruct (lstep m l t opt) as [t1 o1] eqn:El. cbn [fst] in E1, E2.
  destruct (IH ls t1 o1) as [F1 F2].
  - intros x Hx. rewrite E1. apply Hms. right; auto.
  - rewrite F1, F2, E1, E2. auto.
Qed.

Lemma ra_scan_range : forall heap mc h k m, In m (scan heap mc h k) ->
  (forall p, h - Z.of_nat k <= p < h -> 0 <= Znth p heap) -> 0 <= m <= mc.
Proof.
  intros heap mc h k; revert h; induction k as [|k IH]; intros h m Hin Hp; cbn [scan] in Hin; [contradiction|].
  destruct (Znth (h - 1) heap >? mc) eqn:E.
  - apply (IH (h - 1)); auto. intros p Hp'. apply Hp. lia.
  - destruct Hin as [<-|Hin].
    + rewrite Z.gtb_ltb, Z.ltb_ge in E. split; [apply Hp; lia | lia].
    + apply (IH (h - 1)); auto. intros p Hp'. apply Hp. lia.
Qed.

Lemma ra_inner_ok : forall mc bits heap f k h n t opt,
  (k <= f)%nat -> (n <= length (scan heap mc h k))%nat ->
  0 <= h - Z.of_nat k -> h <= Zlength heap ->
  (forall p, h - Z.of_nat k <= p < h -> 0 <= Znth p heap) ->
  mc < Zlength (dl t) -> mc < Zlength (fc t) ->
  c_gen_bitlen_reassign_inner f mc bits heap t opt h (Z.of_nat n) =
  Some (gen_bitlen_reassign_inner f mc bits heap t opt h (Z.of_nat n)).
Proof.
  intros mc bits heap f; induction f as [|f IH]; intros k h n t opt Hk Hn Hh0 Hh1 Hp Hdl Hfc.
  - assert (k = O) by lia; subst k. cbn [scan length] in Hn. assert (n = O) by lia; subst n. reflexivity.
  - rewrite inner_unfold. cbn [c_gen_bitlen_reassign_inner]. destruct n as [|n]; [reflexivity|].
    destruct k as [|k]; [cbn [scan length] in Hn; lia|].
    replace (Z.of_nat (S n) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (ra_rd_in heap (h - 1)) by lia. cbn [bind].
    cbn [scan] in Hn.
    destruct (Znth (h - 1) heap >? mc) eqn:E.
    + apply (IH k); auto; try lia. intros p Hp'. apply Hp. lia.
    + rewrite Z.gtb_ltb, Z.ltb_ge in E. assert (Hm0 : 0 <= Znth (h - 1) heap) by (apply Hp; lia).
      cbn [length] in Hn.
      rewrite (ra_rd_in (dl t)) by lia. cbn [bind].
      assert (Hmr : 0 <= Znth (h - 1) heap < Zlength (dl t)) by lia.
      assert (HL := ra_lstep_len (Znth (h - 1) heap) bits t opt Hmr).
      replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
      unfold lstep in HL |- *.
      destruct (negb (Znth (Znth (h - 1) heap) (dl t) =? bits)).
      * rewrite (ra_rd_in (fc t)) by lia. cbn [bind].
        rewrite ra_set_dl_in by lia. cbn [bind fst] in HL |- *. destruct HL as [HL1 HL2].
        apply (IH k); auto; try lia.
        all: try (intros p Hp'; apply Hp; lia).
        all: try (rewrite HL2; lia).
      * cbn [bind]. apply (IH k); auto; try lia. intros p Hp'. apply Hp. lia.
Qed.

Lemma ra_outer_ok : forall mc heap c (kb f : nat) k h t opt,
  (kb < f)%nat -> (k <= Z.to_nat HEAP_SIZE)%nat -> Zlength c = 16 -> (kb <= 15)%nat ->
  (forall l, 1 <= l <= Z.of_nat kb -> 0 <= Znth l c) ->
  (length (lseq c kb) <= length (scan heap mc h k))%nat ->
  0 <= h - Z.of_nat k -> h <= Zlength heap ->
  (forall p, h - Z.of_nat k <= p < h -> 0 <= Znth p heap) ->
  mc < Zlength (dl t) -> mc < Zlength (fc t) ->
  c_gen_bitlen_reassign f mc heap c t opt h (Z.of_nat kb) =
  Some (gen_bitlen_reassign f mc heap c t opt h (Z.of_nat kb)).
Proof.
  intros mc heap c kb; induction kb as [|kb IH]; intros f k h t opt Hf Hk Hc Hkb Hnn Hlen Hh0 Hh1 Hp Hdl Hfc.
  - destruct f as [|f]; [lia|]. reflexivity.
  - destruct f as [|f]; [lia|]. rewrite outer_unfold. cbn [c_gen_bitlen_reassign].
    replace (Z.of_nat (S kb) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite ra_rd_in by lia. cbn [bind].
    set (nn := Z.to_nat (Znth (Z.of_nat (S kb)) c)).
    assert (HcE : Znth (Z.of_nat (S kb)) c = Z.of_nat nn) by (unfold nn; rewrite Z2Nat.id; auto; apply Hnn; lia).
    rewrite HcE.
    assert (Hl : length (lseq c (S kb)) = (nn + length (lseq c kb))%nat).
    { cbn [lseq]. rewrite length_app, repeat_length. reflexivity. }
    rewrite Hl in Hlen.
    rewrite (ra_inner_ok mc (Z.of_nat (S kb)) heap (Z.to_nat HEAP_SIZE) k h nn t opt) by (auto; lia).
    cbn [bind].
    destruct (inner_spec mc (Z.of_nat (S kb)) heap (Z.to_nat HEAP_SIZE) k h nn t opt Hk ltac:(lia))
      as [k' [Hk' [E1 E2]]].
    rewrite E1. cbv beta iota. replace (Z.of_nat (S kb) - 1) with (Z.of_nat kb) by lia.
    destruct (ra_apply_lens_len (firstn nn (scan heap mc h k)) (repeat (Z.of_nat (S kb)) nn) t opt) as [L1 L2].
    { intros m Hm. apply firstn_In in Hm. destruct (ra_scan_range heap mc h k m Hm Hp). lia. }
    apply (IH f k'); try lia.
    + intros; apply Hnn; lia.
    + rewrite E2, length_skipn. lia.
    + intros p Hp'. apply Hp. lia.
    + rewrite L2; lia.
Qed.

(** The reassignment of the lengths along the heap scan (Repair.reassign_correct). *)
Definition reassign_stmt : Prop := forall mc heap c t opt M k,
  1 <= M <= 15 -> Zlength c = 16 -> (forall l, 1 <= l <= M -> 0 <= Znth l c) ->
  (k <= Z.to_nat HEAP_SIZE)%nat -> Zlength heap = HEAP_SIZE ->
  (forall p, HEAP_SIZE - Z.of_nat k <= p < HEAP_SIZE -> 0 <= Znth p heap) ->
  mc < Zlength (dl t) -> mc < Zlength (fc t) ->
  (Z.to_nat (tot M c) <= length (scan heap mc HEAP_SIZE k))%nat ->
  c_gen_bitlen_reassign 20 mc heap c t opt HEAP_SIZE M = Some (gen_bitlen_reassign 20 mc heap c t opt HEAP_SIZE M).
Lemma reassign_part : reassign_stmt.
Proof.
  intros mc heap c t opt M k HM Hc Hnn Hk Hheap Hp Hdl Hfc Hlen.
  replace M with (Z.of_nat (Z.to_nat M)) by lia.
  apply (ra_outer_ok mc heap c (Z.to_nat M) 20 k); try lia.
  - intros; apply Hnn; lia.
  - rewrite lseq_length_nat by (intros; apply Hnn; lia). unfold tot in Hlen. exact Hlen.
  - unfold HEAP_SIZE in *; lia.
  - intros p Hp'. apply Hp. lia.
Qed.

(** gen_bitlen on the state before it (follows BuildThm.g_genbitlen). *)
Definition gen_bitlen_stmt : Prop := forall sd t0 w0 S F R t w mc,
  pre_ok sd t0 w0 S F R t w mc ->
  1 <= sd_maxlen sd <= 15 -> 3 <= sd_elems sd <= 286 -> sd_elems sd <= Zlength (dl t) ->
  (forall n, 0 <= n < Zlength (dl t) -> 0 <= xb sd n <= 16) ->
  (forall st, sd_stree sd = Some st -> forall n, 0 <= n < Zlength (dl t) -> 0 <= Znth n st <= 16) ->
  (forall n, 0 <= n < Zlength (dl t) -> 0 <= Znth n (fc t) < 65536) ->
  0 <= w_opt_len w < 18446744073709551616 -> 0 <= w_static_len w < 18446744073709551616 ->
  sd_elems sd <= 2 ^ sd_maxlen sd ->
  desc_ok sd -> Zlength (fc t) = Zlength (dl t) ->
  c_gen_bitlen sd mc t w = Some (gen_bitlen sd mc t w).
Lemma gbp_rd : forall l i, 0 <= i < Zlength l -> rd l i = Some (Znth i l).
Proof.
  intros l i Hi. unfold rd, in_range.
  replace ((0 <=? i) && (i <? Zlength l)) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  reflexivity.
Qed.

Lemma gbp_set_dl : forall t i v, 0 <= i < Zlength (dl t) -> c_set_dl t i v = Some (set_dl t i v).
Proof.
  intros t i v Hi. unfold c_set_dl, wr, in_range.
  replace ((0 <=? i) && (i <? Zlength (dl t))) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  reflexivity.
Qed.

Lemma gen_bitlen_part : pass1_stmt -> repair_stmt -> reassign_stmt -> gen_bitlen_stmt.
Proof.
  intros P1 RP RA sd t0 w0 S F R t w mc Hpre HM Hel Hdlen Hxb Hst Hfc Hopt Hstl Hel2 Hdesc Hfl.
  assert (Hhm := pre_hm sd t0 w0 S F R t w mc Hpre).
  assert (Hheap := po_heap _ _ _ _ _ _ _ _ _ Hpre).
  assert (Hidx := pre_idx sd t0 w0 S F R t w mc Hpre Hel Hdlen).
  unfold c_gen_bitlen. rewrite gen_bitlen_eq. cbv zeta. cbn [w_heap w_heap_max w_set_bl_count].
  rewrite gbp_rd by lia. cbn [bind].
  rewrite gbp_set_dl by (apply Hidx; lia). cbn [bind].
  rewrite (P1 sd t0 w0 S F R t w mc Hpre HM Hel Hdlen Hxb Hst Hfc Hopt Hstl Hel2 Hdesc Hfl).
  assert (G := g_pass1 sd t0 w0 S F R t w mc Hpre HM Hel Hdlen Hxb Hst Hfc Hopt Hstl).
  destruct (gen_bitlen_pass1 _ _ _ _ _ _ _) as [[t2 w2] ovf]. cbn [bind].
  destruct G as [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 [G9 [G10 [G11 [G12 [G13 G14]]]]]]]]]]]]].
  destruct (Z.eqb_spec ovf 0) as [Hz|Hnz]; [reflexivity|].
  assert (HnD : ~ (forall l, In l R -> ld l <= sd_maxlen sd)).
  { intros HD. apply Hnz. rewrite G9, (g_noovf_ideep sd t0 w0 S F R t w mc Hpre HM HD). lia. }
  set (dl0 := dlist R w mc) in *.
  set (c := clampc (sd_maxlen sd) dl0).
  assert (Hbl : w_bl_count w2 = c).
  { apply Znth_eq_ext; [rewrite G11; unfold c; rewrite clampc_len; reflexivity|].
    intros b Hb. rewrite G11 in Hb. rewrite G12 by lia. apply (g_clampc sd t0 w0 S F R t w mc Hpre HM). lia. }
  assert (Hdr := g_d_range sd t0 w0 S F R t w mc Hpre HM). fold dl0 in Hdr.
  assert (Hdl : Zlength dl0 <= 2 ^ sd_maxlen sd /\ Zlength dl0 <= 573).
  { unfold dl0. rewrite (g_d_len sd t0 w0 S F R t w mc Hpre HM).
    pose proof (g_S_len sd t0 w0 S F R t w mc Hpre HM Hel); lia. }
  destruct (clamp_rinv (sd_maxlen sd) 600 dl0 HM ltac:(lia) Hdr (g_d_kraft sd t0 w0 S F R t w mc Hpre HM)
              (proj1 Hdl) (proj2 Hdl) (g_deep_exists sd t0 w0 S F R t w mc Hpre HM HnD)) as [HI1 Hinv].
  fold c in HI1, Hinv. set (I := kraftc (sd_maxlen sd) c - 2 ^ sd_maxlen sd) in *.
  assert (HI : I = Ideep sd t w) by (unfold I, c, dl0; rewrite (g_kraftc sd t0 w0 S F R t w mc Hpre HM); lia).
  assert (Hovf : ovf = 2 * I) by (rewrite G9, HI; reflexivity).
  rewrite Hbl, Hovf.
  rewrite (RP (sd_maxlen sd) c I HM HI1 Hinv). cbn [bind].
  destruct (repair_correct (sd_maxlen sd) c I HM HI1 Hinv) as [_ [R1 [R2 [R3 [R4 [R5 R6]]]]]].
  set (c' := gen_bitlen_repair (Z.to_nat HEAP_SIZE) (sd_maxlen sd) c (2 * I)) in *.
  assert (Htot : tot (sd_maxlen sd) c = Zlength dl0)
    by (apply (clamp_sums (sd_maxlen sd) dl0 HM); intros x Hx; apply Hdr; exact Hx).
  assert (Hord_len : Zlength (order w mc) = Zlength dl0) by (unfold dl0, dlist; rewrite Zlength_map; reflexivity).
  assert (Hscan : scan (w_heap (w_set_bl_count w2 c')) mc HEAP_SIZE (Z.to_nat (HEAP_SIZE - w_heap_max w - 1)) = order w mc)
    by (simpl; rewrite G3; reflexivity).
  rewrite (RA mc (w_heap w2) c' t2 (w_opt_len (w_set_bl_count w2 c')) (sd_maxlen sd)
             (Z.to_nat (HEAP_SIZE - w_heap_max w - 1)) HM R1).
  - cbn [bind]. destruct (gen_bitlen_reassign _ _ _ _ _ _ _ _); reflexivity.
  - intros; apply R2; lia.
  - unfold HEAP_SIZE in *; lia.
  - rewrite G3. exact Hheap.
  - intros p Hp. rewrite G3.
    assert (0 <= Znth p (w_heap w) < Zlength (dl t)) by (apply Hidx; unfold HEAP_SIZE in *; lia). lia.
  - rewrite G2. pose proof (g_mc_lt sd t0 w0 S F R t w mc Hpre). lia.
  - rewrite G1, Hfl. pose proof (g_mc_lt sd t0 w0 S F R t w mc Hpre). lia.
  - change (w_heap w2) with (w_heap (w_set_bl_count w2 c')).
    rewrite Hscan, R5, Htot, <- Hord_len, Zlength_correct. lia.
Qed.

(** gen_codes with lengths 0..15 up to max_code. *)
Definition gen_codes_stmt : Prop := forall t mc bl,
  0 <= mc < HEAP_SIZE -> mc < Zlength (fc t) -> mc < Zlength (dl t) -> 15 <= Zlength bl ->
  (forall i, 0 <= i <= mc -> 0 <= Znth i (dl t) <= 15) ->
  c_gen_codes t mc bl = Some (gen_codes t mc bl).
Lemma gc_rd_ok l i : 0 <= i < Zlength l -> rd l i = Some (Znth i l).
Proof. intros H. unfold rd, in_range. replace ((0 <=? i) && (i <? Zlength l)) with true; [reflexivity|]. symmetry. apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.

Lemma gc_wr_ok l i v : 0 <= i < Zlength l -> wr l i v = Some (upd_Znth i l v).
Proof. intros H. unfold wr, in_range. replace ((0 <=? i) && (i <? Zlength l)) with true; [reflexivity|]. symmetry. apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.

Lemma gc_bi_reverse_loop : forall f code res len, 1 <= len <= Z.of_nat f ->
  c_bi_reverse_loop f code res len = Some (bi_reverse_loop f code res len).
Proof.
  induction f; intros code res len H; [lia|].
  cbn [c_bi_reverse_loop bi_reverse_loop].
  destruct (len - 1 >? 0) eqn:E; [|reflexivity].
  apply Z.gtb_lt in E. apply IHf. lia.
Qed.

Lemma gc_bi_reverse code len : 1 <= len <= 15 -> c_bi_reverse code len = Some (bi_reverse code len).
Proof.
  intros H. unfold c_bi_reverse, bi_reverse.
  replace (1 <=? len) with true by (symmetry; apply Z.leb_le; lia). cbn [guard bind].
  rewrite gc_bi_reverse_loop by (cbn; lia). reflexivity.
Qed.

Lemma gc_next_code_len : forall f bl nc code bits, 1 <= bits -> Zlength nc = 16 ->
  Zlength (gen_next_code f bl nc code bits) = 16.
Proof.
  induction f; intros bl nc code bits Hb Hn; cbn [gen_next_code]; [exact Hn|].
  destruct (bits <=? MAX_BITS) eqn:E; [|exact Hn].
  apply Z.leb_le in E. unfold MAX_BITS in E.
  apply IHf; [lia|]. rewrite upd_Znth_Zlength; lia.
Qed.

Lemma gc_next_code : forall f bl nc code bits, 1 <= bits -> Zlength nc = 16 -> 15 <= Zlength bl ->
  16 <= Z.of_nat f + bits ->
  c_gen_next_code f bl nc code bits = Some (gen_next_code f bl nc code bits).
Proof.
  induction f; intros bl nc code bits Hb Hn Hbl Hf; cbn [c_gen_next_code gen_next_code].
  - replace (bits <=? MAX_BITS) with false by (symmetry; apply Z.leb_gt; unfold MAX_BITS; cbn in Hf; lia).
    reflexivity.
  - destruct (bits <=? MAX_BITS) eqn:E; [|reflexivity].
    apply Z.leb_le in E. unfold MAX_BITS in E. rewrite Nat2Z.inj_succ in Hf.
    rewrite gc_rd_ok by lia. cbn [bind].
    rewrite gc_wr_ok by lia. cbn [bind].
    apply IHf; [lia| rewrite upd_Znth_Zlength; lia | lia | lia].
Qed.

Lemma gc_codes_loop : forall f mc t nc n, 0 <= n -> Zlength nc = 16 ->
  mc < Zlength (fc t) -> mc < Zlength (dl t) ->
  (forall i, 0 <= i <= mc -> 0 <= Znth i (dl t) <= 15) ->
  mc < Z.of_nat f + n ->
  c_gen_codes_loop f mc t nc n = Some (gen_codes_loop f mc t nc n).
Proof.
  induction f; intros mc t nc n Hn Hnc Hfc Hdl Hl Hf; cbn [c_gen_codes_loop gen_codes_loop].
  - replace (n <=? mc) with false by (symmetry; apply Z.leb_gt; cbn in Hf; lia). reflexivity.
  - rewrite Nat2Z.inj_succ in Hf. destruct (n <=? mc) eqn:E; [|reflexivity].
    apply Z.leb_le in E.
    rewrite gc_rd_ok by lia. cbn [bind].
    destruct (Znth n (dl t) =? 0) eqn:E0.
    + apply IHf; auto; lia.
    + apply Z.eqb_neq in E0. pose proof (Hl n ltac:(lia)) as Hln.
      rewrite gc_rd_ok by lia. cbn [bind].
      rewrite gc_wr_ok by lia. cbn [bind].
      rewrite gc_bi_reverse by lia. cbn [bind].
      unfold c_set_fc. rewrite gc_wr_ok by lia. cbn [bind].
      apply (IHf mc (set_fc t n _)); unfold set_fc; cbn [fc dl]; auto;
        rewrite ?upd_Znth_Zlength; lia.
Qed.

Lemma gen_codes_part : gen_codes_stmt.
Proof.
  intros t mc bl Hmc Hfc Hdl Hbl Hl.
  unfold c_gen_codes, gen_codes.
  rewrite gc_next_code by (cbn; lia || reflexivity). cbn [bind].
  apply gc_codes_loop; auto; try lia.
Qed.

(** ** The parts, closed *)

Lemma c_pqdownheap_some : pqdownheap_stmt.
Proof. exact (pqdownheap_part). Qed.
Lemma c_bt_init_some : bt_init_stmt.
Proof. exact (bt_init_part). Qed.
Lemma c_bt_force_some : bt_force_stmt.
Proof. exact (bt_force_part). Qed.
Lemma c_bt_heapify_some : bt_heapify_stmt.
Proof. exact (bt_heapify_part c_pqdownheap_some). Qed.
Lemma c_bt_merge_some : bt_merge_stmt.
Proof. exact (bt_merge_part c_pqdownheap_some). Qed.
Lemma c_bt_pre_some : bt_pre_stmt.
Proof. exact (bt_pre_part c_bt_init_some c_bt_force_some c_bt_heapify_some c_bt_merge_some). Qed.
Lemma c_pass1_some : pass1_stmt.
Proof. exact (pass1_part). Qed.
Lemma c_repair_some : repair_stmt.
Proof. exact (repair_part). Qed.
Lemma c_reassign_some : reassign_stmt.
Proof. exact (reassign_part). Qed.
Lemma c_gen_bitlen_some : gen_bitlen_stmt.
Proof. exact (gen_bitlen_part c_pass1_some c_repair_some c_reassign_some). Qed.
Lemma c_gen_codes_some : gen_codes_stmt.
Proof. exact (gen_codes_part). Qed.

(** ** Assembly *)

Lemma desc_ok_static : forall sd,
  (sd = static_l_desc \/ sd = static_d_desc \/ sd = static_bl_desc) -> desc_ok sd.
Proof.
  intros sd [ -> | [ -> | -> ] ]; unfold desc_ok; cbn [sd_base sd_elems sd_extra sd_stree];
    (split; [vm_compute; split; discriminate|split; [reflexivity|]]);
    intros st Hst; inversion Hst; subst; vm_compute; discriminate.
Qed.

Lemma c_build_tree_eq : forall sd t w,
  c_build_tree sd t w =
  let* (t1, w1, mc) := c_bt_pre sd t w in
  let* (t2, w2) := c_gen_bitlen sd mc t1 w1 in
  let* t3 := c_gen_codes t2 mc (w_bl_count w2) in
  Some (t3, mc, w2).
Proof.
  intros sd t w. unfold c_build_tree, c_bt_pre.
  destruct (c_bt_init _ _ _ _ _ _) as [[[t1 w1] m1]|]; cbn [bind]; [|reflexivity].
  destruct (c_bt_force _ _ _ _ _) as [[[t2 w2] m2]|]; cbn [bind]; [|reflexivity].
  destruct (c_bt_heapify _ _ _ _) as [w3|]; cbn [bind]; [|reflexivity].
  destruct (c_bt_merge _ _ _ _) as [[[t4 w4] m4]|]; cbn [bind]; [|reflexivity].
  unfold c_store_removed. cbn [w_heap w_heap_max w_set_heap_max].
  destruct (rd _ _) as [top|]; cbn [bind]; [|reflexivity].
  destruct (wr _ _ _) as [hp4|]; cbn [bind]; reflexivity.
Qed.

Theorem bt_some : bt_some_statement.
Proof.
  intros sd t w Hsd HR. assert (Hdesc := desc_ok_static sd Hsd).
  assert (HR' := HR).
  destruct HR' as [[Hel [HM Hpow]] [HTS HTS2] [Hh [Hd [Hol Hsl]]] Hfr [Hfc0 Hsum] [Hxb Hst]].
  rewrite c_build_tree_eq, (c_bt_pre_some sd t w HR Hdesc), build_tree_eq.
  assert (BP := bt_pre_spec sd t w Hel HTS HTS2 Hh Hd Hol Hsl Hfc0 Hsum).
  assert (FR := bt_pre_fc sd t w Hfr).
  destruct (bt_pre sd t w) as [[t1 w1] mc] eqn:Ebp. cbn [bind].
  destruct BP as [S [F [R Hpo]]]. destruct FR as [Hfr1 Hfl1].
  destruct (po_len _ _ _ _ _ _ _ _ _ Hpo) as [PL1 [PL2 PL3]].
  assert (Hdlen : sd_elems sd <= Zlength (dl t1)) by lia.
  assert (Hxb1 : forall n, 0 <= n < Zlength (dl t1) -> 0 <= xb sd n <= 16) by (intros n Hn; apply Hxb; lia).
  assert (Hst1 : forall st, sd_stree sd = Some st -> forall n, 0 <= n < Zlength (dl t1) -> 0 <= Znth n st <= 16)
    by (intros st Hs n Hn; apply (Hst st Hs); lia).
  assert (Hfc1 : forall n, 0 <= n < Zlength (dl t1) -> 0 <= Znth n (fc t1) < 65536) by (intros n Hn; apply Hfr1; lia).
  assert (Hopt1 : 0 <= w_opt_len w1 < 18446744073709551616)
    by (rewrite (po_opt _ _ _ _ _ _ _ _ _ Hpo); unfold u64; apply Z.mod_pos_bound; lia).
  assert (Hstl1 : 0 <= w_static_len w1 < 18446744073709551616).
  { rewrite (po_static _ _ _ _ _ _ _ _ _ Hpo). destruct (sd_stree sd); [unfold u64; apply Z.mod_pos_bound; lia|lia]. }
  assert (Hfl : Zlength (fc t1) = Zlength (dl t1)) by lia.
  rewrite (c_gen_bitlen_some sd t w S F R t1 w1 mc Hpo HM Hel Hdlen Hxb1 Hst1 Hfc1 Hopt1 Hstl1 Hpow Hdesc Hfl).
  assert (G := g_genbitlen sd t w S F R t1 w1 mc Hpo HM Hel Hdlen Hxb1 Hst1 Hfc1 Hopt1 Hstl1 Hpow).
  destruct (gen_bitlen sd mc t1 w1) as [t3 w3] eqn:Egb. cbn [bind].
  destruct G as [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 [G9 [G10 [G11 [G12 G13]]]]]]]]]]]].
  assert (HSr := g_S sd t w S F R t1 w1 mc Hpo). destruct HSr as [HSe [HSnd HSr]].
  assert (Hmc := g_mc sd t w S F R t1 w1 mc Hpo).
  assert (Hmclt := g_mc_lt sd t w S F R t1 w1 mc Hpo).
  assert (Hmc0 : 0 <= mc) by (apply (HSr mc); apply Hmc).
  rewrite c_gen_codes_some; [reflexivity| unfold HEAP_SIZE; lia | rewrite G1; lia | lia | lia |].
  intros i Hi. destruct (in_dec Z.eq_dec i S) as [HiS|HiS]; [specialize (G8 i HiS); lia|].
  rewrite G7 by (auto; lia). lia.
Qed.
