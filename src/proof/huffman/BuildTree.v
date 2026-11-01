(** * build_tree performs greedy Huffman merges; gen_bitlen's lengths are the depths *)

From Coq Require Import ZArith List Lia Bool Permutation.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Heap facts: the top is a minimum; region bookkeeping *)

Lemma hp_top_min : forall t d heap len,
  hp t d heap len 1 -> forall i, 1 <= i <= len -> le t d (Znth 1 heap) (Znth i heap).
Proof.
  intros t d heap len H.
  assert (G : forall n : nat, forall i, (Z.to_nat i <= n)%nat -> 1 <= i <= len -> le t d (Znth 1 heap) (Znth i heap)).
  { induction n as [|n IH]; intros i Hn Hi; [lia|].
    destruct (Z.eq_dec i 1) as [->|Hx1]; [apply le_refl|].
    assert (Hp := div2_lt i ltac:(lia)). assert (Hp1 := div2_ge1 i ltac:(lia)).
    apply le_trans with (Znth (i / 2) heap); [apply IH; lia|]. apply H; lia. }
  intros i Hi; apply (G (Z.to_nat i)); lia.
Qed.

Lemma zseq_succ_r : forall n a, zseq a (S n) = zseq a n ++ [a + Z.of_nat n].
Proof.
  induction n as [|n IH]; intros a.
  - simpl. f_equal. f_equal. lia.
  - change (zseq a (S (S n))) with (a :: zseq (a + 1) (S n)). rewrite IH.
    change (zseq a (S n)) with (a :: zseq (a + 1) n). simpl. f_equal. f_equal. f_equal. lia.
Qed.

Lemma reg_cons : forall heap len, 1 <= len ->
  reg heap len = Znth 1 heap :: map (fun i => Znth i heap) (zseq 2 (Z.to_nat (len - 1))).
Proof.
  intros heap len H. unfold reg. replace (Z.to_nat len) with (S (Z.to_nat (len - 1))) by lia.
  reflexivity.
Qed.

(** Removing the top: [heap[1] = heap[len]; len--] keeps the multiset minus the old top. *)
Lemma map_zseq_ext : forall (g1 g2 : Z -> Z) n a, (forall i, a <= i < a + Z.of_nat n -> g1 i = g2 i) ->
  map g1 (zseq a n) = map g2 (zseq a n).
Proof. intros. apply map_ext_in. intros i Hi. apply in_zseq in Hi. auto. Qed.

Lemma reg_pqremove : forall heap len, 2 <= len -> len < Zlength heap ->
  Permutation (reg heap len) (Znth 1 heap :: reg (upd_Znth 1 heap (Znth len heap)) (len - 1)).
Proof.
  intros heap len H2 HL.
  rewrite (reg_cons heap len), (reg_cons _ (len - 1)) by lia.
  rewrite upd_Znth_same by lia. apply perm_skip.
  replace (Z.to_nat (len - 1)) with (S (Z.to_nat (len - 1 - 1))) at 1 by lia.
  rewrite zseq_succ_r, map_app. cbn [map].
  replace (2 + Z.of_nat (Z.to_nat (len - 1 - 1))) with len by lia.
  rewrite (map_zseq_ext (fun i => Znth i (upd_Znth 1 heap (Znth len heap))) (fun i => Znth i heap))
    by (intros i Hi; rewrite upd_Znth_diff by lia; reflexivity).
  apply Permutation_sym, Permutation_cons_append.
Qed.

(** Replacing the top. *)
Lemma reg_set_top : forall heap len x, 1 <= len -> len < Zlength heap ->
  reg (upd_Znth 1 heap x) len = x :: map (fun i => Znth i heap) (zseq 2 (Z.to_nat (len - 1))).
Proof.
  intros heap len x H1 HL. rewrite reg_cons by lia. rewrite upd_Znth_same by lia. f_equal.
  apply map_zseq_ext. intros i Hi. rewrite upd_Znth_diff by lia. reflexivity.
Qed.

(** Positions above [len] do not matter for the region and the heap property. *)
Lemma reg_frame : forall h1 h2 len, (forall i, 1 <= i <= len -> Znth i h1 = Znth i h2) -> reg h1 len = reg h2 len.
Proof.
  intros h1 h2 len E. unfold reg. apply map_ext_in. intros i Hi. apply in_zseq in Hi. apply E. lia.
Qed.

(** ** Dad chains *)

Fixpoint iter (dl : list Z) (e : nat) (x : Z) : Z :=
  match e with O => x | S e' => iter dl e' (Znth x dl) end.

Lemma iter_succ_r : forall dl e x, iter dl (S e) x = Znth (iter dl e x) dl.
Proof. induction e as [|e IH]; intros x; [reflexivity|]. change (iter dl (S (S e)) x) with (iter dl (S e) (Znth x dl)). rewrite IH. reflexivity. Qed.

(** If two Dad arrays agree on the first [d] nodes of a chain, the chains agree up to [d]. *)
Lemma iter_agree : forall dl1 dl2 d x,
  (forall e, (e < d)%nat -> Znth (iter dl1 e x) dl1 = Znth (iter dl1 e x) dl2) ->
  forall e, (e <= d)%nat -> iter dl2 e x = iter dl1 e x.
Proof.
  intros dl1 dl2 d x H e. induction e as [|e IH]; intros He; [reflexivity|].
  rewrite !iter_succ_r, IH by lia. symmetry. apply H. lia.
Qed.

(** The removed region [heap[heap_max .. 572]]. *)
Definition removed (heap : list Z) (hm : Z) : list Z := map (fun i => Znth i heap) (zseq hm (Z.to_nat (HEAP_SIZE - hm))).

Section Merge.
Variable TS elems total : Z.
Variable S : list Z.
Variable f0 : Z -> Z.

Definition P0 : list item := map (fun x => [(x, f0 x, 0)]) S.

Record minv (t : tree) (w : work) (node : Z) (it : Z -> item) (Q : list item) : Prop := {
  mi_heap : Zlength (w_heap w) = HEAP_SIZE;
  mi_depth : Zlength (w_depth w) = HEAP_SIZE;
  mi_fc : Zlength (fc t) = TS;
  mi_dl : Zlength (dl t) = TS;
  mi_len : 1 <= w_heap_len w;
  mi_room : 2 * w_heap_len w + 1 <= w_heap_max w <= HEAP_SIZE;
  mi_node : elems <= node /\ node + w_heap_len w <= TS /\ TS <= HEAP_SIZE;
  mi_hp : hp t (w_depth w) (w_heap w) (w_heap_len w) 1;
  mi_steps : steps P0 Q;
  mi_perm : Permutation Q (map it (reg (w_heap w) (w_heap_len w)));
  mi_pool : forall y, In y (reg (w_heap w) (w_heap_len w)) ->
              0 <= y < node /\ weight (it y) = Znth y (fc t) /\ 0 <= Znth y (fc t);
  mi_total : sumZ (map (fun y => Znth y (fc t)) (reg (w_heap w) (w_heap_len w))) = total;
  mi_nodup : NoDup (reg (w_heap w) (w_heap_len w) ++ removed (w_heap w) (w_heap_max w));
  mi_chain : forall y x, In y (reg (w_heap w) (w_heap_len w)) -> In x (it y) ->
              0 <= ld x /\ In (lid x) S /\ iter (dl t) (Z.to_nat (ld x)) (lid x) = y /\
              (forall e, (e < Z.to_nat (ld x))%nat -> In (iter (dl t) e (lid x)) (removed (w_heap w) (w_heap_max w)));
  mi_rem : forall p, w_heap_max w <= p < HEAP_SIZE ->
              0 <= Znth p (w_heap w) < node /\ Znth p (w_heap w) < Znth (Znth p (w_heap w)) (dl t) /\
              (In (Znth (Znth p (w_heap w)) (dl t)) (reg (w_heap w) (w_heap_len w)) \/
               exists q, w_heap_max w <= q < p /\ Znth q (w_heap w) = Znth (Znth p (w_heap w)) (dl t));
  mi_leaf_fc : forall x, In x S -> Znth x (fc t) = f0 x /\ 0 <= x < elems;
  mi_nonempty : forall y, In y (reg (w_heap w) (w_heap_len w)) -> it y <> [];
  mi_desc : forall p, w_heap_max w <= p < HEAP_SIZE -> exists x r, In x S /\
              iter (dl t) r x = Znth p (w_heap w) /\
              (forall e, (e < r)%nat -> In (iter (dl t) e x) (removed (w_heap w) (w_heap_max w)));
  mi_kind : forall y, In y (reg (w_heap w) (w_heap_len w)) ->
              (In y S /\ it y = [(y, f0 y, 0)]) \/ (elems <= y /\ forall x, In x (it y) -> 1 <= ld x);
  mi_rkind : forall p, w_heap_max w <= p < HEAP_SIZE -> In (Znth p (w_heap w)) S \/ elems <= Znth p (w_heap w);
  mi_unused : forall c, 0 <= c < elems -> ~ In c S -> Znth c (dl t) = 0
}.

End Merge.

Lemma bt_merge_unfold : forall f t w node,
  bt_merge (S f) t w node =
  let '(t', w') := merge_body t w node in
  if w_heap_len w' >=? 2 then bt_merge f t' w' (node + 1) else (t', w', node + 1).
Proof. reflexivity. Qed.

(** ** Helper facts for the merge step *)

Lemma Zlength_upd : forall {A} i (l : list A) v, Zlength (upd_Znth i l v) = Zlength l.
Proof.
  intros. destruct (Z_le_gt_dec 0 i); [destruct (Z_lt_ge_dec i (Zlength l))|].
  - apply upd_Znth_Zlength; lia.
  - rewrite upd_Znth_out_of_range; auto; lia.
  - rewrite upd_Znth_out_of_range; auto; lia.
Qed.

Lemma le_frame : forall t1 t2 d1 d2 x y,
  Znth x (fc t1) = Znth x (fc t2) -> Znth y (fc t1) = Znth y (fc t2) ->
  Znth x d1 = Znth x d2 -> Znth y d1 = Znth y d2 ->
  le t1 d1 x y -> le t2 d2 x y.
Proof. unfold le, smaller; intros t1 t2 d1 d2 x y E1 E2 E3 E4 H. rewrite <- E1, <- E2, <- E3, <- E4. exact H. Qed.

Lemma in_reg : forall heap len y, In y (reg heap len) <-> exists i, 1 <= i <= len /\ Znth i heap = y.
Proof.
  intros. unfold reg. rewrite in_map_iff. split.
  - intros [i [<- Hi]]. apply in_zseq in Hi. exists i; split; [lia|auto].
  - intros [i [Hi <-]]. exists i; split; auto. apply in_zseq; lia.
Qed.

Lemma removed_cons : forall heap hm, 1 <= hm <= HEAP_SIZE ->
  removed heap (hm - 1) = Znth (hm - 1) heap :: removed heap hm.
Proof.
  intros heap hm H. unfold removed. replace (Z.to_nat (HEAP_SIZE - (hm - 1))) with (S (Z.to_nat (HEAP_SIZE - hm))) by lia.
  simpl. f_equal. f_equal. f_equal. lia.
Qed.

Lemma in_removed : forall heap hm y, In y (removed heap hm) <-> exists p, hm <= p < HEAP_SIZE /\ Znth p heap = y.
Proof.
  intros. unfold removed. rewrite in_map_iff. split.
  - intros [i [<- Hi]]. apply in_zseq in Hi. exists i; split; [lia|auto].
  - intros [i [Hi <-]]. exists i; split; auto. apply in_zseq; lia.
Qed.

Lemma removed_frame : forall h1 h2 hm, (forall p, hm <= p < HEAP_SIZE -> Znth p h1 = Znth p h2) ->
  removed h1 hm = removed h2 hm.
Proof. intros. unfold removed. apply map_ext_in. intros i Hi. apply in_zseq in Hi. apply H. lia. Qed.

Lemma nodup_app_disj : forall (l1 l2 : list Z) x, NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  induction l1 as [|a l1 IH]; intros l2 x H Hx; [destruct Hx|].
  inversion H as [|? ? Hna Hnd]; subst. destruct Hx as [->|Hx].
  - intros Hc; apply Hna; apply in_or_app; right; auto.
  - eapply IH; eauto.
Qed.

Lemma sumZ_perm' : forall (g : Z -> Z) l1 l2, Permutation l1 l2 -> sumZ (map g l1) = sumZ (map g l2).
Proof. intros. apply sumZ_perm, Permutation_map; auto. Qed.

Lemma sumZ_nonneg_le : forall (g : Z -> Z) l x y, NoDup (x :: y :: l) -> (forall z, In z l -> 0 <= g z) ->
  g x + g y <= sumZ (map g (x :: y :: l)).
Proof. intros. simpl. assert (0 <= sumZ (map g l)) by (apply sumZ_nonneg; auto). lia. Qed.

(** ** The merge step preserves the invariant *)

Lemma merge_body_eq : forall t w node,
  merge_body t w node =
  let n := Znth 1 (w_heap w) in
  let w1 := pqdownheap t (w_set_heap_len (w_set_heap w (upd_Znth 1 (w_heap w) (Znth (w_heap_len w) (w_heap w))))
                                         (w_heap_len w - 1)) 1 in
  let m := Znth 1 (w_heap w1) in
  let w2 := store_removed (store_removed w1 n) m in
  let t3 := fst (new_node t w2 n m node) in
  let w3 := snd (new_node t w2 n m node) in
  (t3, pqdownheap t3 (w_set_heap w3 (upd_Znth 1 (w_heap w3) node)) 1).
Proof. reflexivity. Qed.

Lemma merge_step : forall TS elems total S f0 t w node it Q,
  minv TS elems total S f0 t w node it Q -> 2 <= w_heap_len w -> total < 65536 ->
  exists it' Q', minv TS elems total S f0 (fst (merge_body t w node)) (snd (merge_body t w node)) (node + 1) it' Q' /\
    w_heap_len (snd (merge_body t w node)) = w_heap_len w - 1.
Proof.
  intros TS elems total S f0 t w node it Q HI H2 Htot65.
  destruct HI as [Hh Hd Hfc Hdl Hlen Hroom Hnode Hhp Hst Hperm Hpool Htot Hnd Hch Hrem Hleaf Hnonem Hdescs Hkind Hrkind Hunused].
  rewrite merge_body_eq. cbn zeta. cbn [fst snd].
  set (heap := w_heap w) in *. set (len := w_heap_len w) in *. set (hm := w_heap_max w) in *.
  set (dep := w_depth w) in *.
  set (n := Znth 1 heap).
  set (heap1 := upd_Znth 1 heap (Znth len heap)).
  set (w0 := w_set_heap_len (w_set_heap w heap1) (len - 1)).
  (* first sift *)
  assert (Hhp1 : hp t dep heap1 (len - 1) 2).
  { intros i Hi Hi2. unfold heap1. assert (Hd2 := div2_lt i ltac:(lia)).
    rewrite !upd_Znth_diff by lia. apply Hhp; lia. }
  assert (HL1 : Zlength heap1 = HEAP_SIZE) by (unfold heap1; rewrite upd_Znth_Zlength; lia).
  destruct (pqdownheap_correct t w0 1) as [P1len [P1hm [P1dep [P1blc [P1ol [P1sl [P1L [P1hp [P1perm P1fr]]]]]]]]].
  { simpl; lia. } { simpl. rewrite HL1. unfold HEAP_SIZE in *; lia. } { simpl; unfold HEAP_SIZE in *; lia. }
  { exact Hhp1. }
  set (w1 := pqdownheap t w0 1) in *.
  set (heap1' := w_heap w1) in *.
  simpl in P1len, P1hm, P1dep, P1L, P1hp, P1perm, P1fr.
  set (m := Znth 1 heap1').
  set (heap2 := upd_Znth (hm - 1 - 1) (upd_Znth (hm - 1) heap1' n) m).
  assert (Ew2 : store_removed (store_removed w1 n) m =
                mkWork heap2 (len - 1) (hm - 1 - 1) dep (w_bl_count w1) (w_opt_len w1) (w_static_len w1)).
  { unfold store_removed, w_set_heap, w_set_heap_max; simpl. rewrite P1len, P1hm, P1dep. reflexivity. }
  rewrite Ew2.
  set (fcnm := u16 (Znth n (fc t) + Znth m (fc t))).
  set (dn := Znth n dep). set (dm := Znth m dep).
  set (dep3 := upd_Znth node dep (u8 ((if dn >=? dm then dn else dm) + 1))).
  set (t3 := set_dl (set_dl (set_fc t node fcnm) m (u16 node)) n (u16 node)).
  assert (Enn : new_node t (mkWork heap2 (len - 1) (hm - 1 - 1) dep (w_bl_count w1) (w_opt_len w1) (w_static_len w1)) n m node
                = (t3, mkWork heap2 (len - 1) (hm - 1 - 1) dep3 (w_bl_count w1) (w_opt_len w1) (w_static_len w1)))
    by reflexivity.
  rewrite Enn. cbn [fst snd w_heap w_set_heap].
  set (heap4 := upd_Znth 1 heap2 node).
  set (w4 := mkWork heap4 (len - 1) (hm - 1 - 1) dep3 (w_bl_count w1) (w_opt_len w1) (w_static_len w1)).
  change (w_set_heap (mkWork heap2 (len - 1) (hm - 1 - 1) dep3 (w_bl_count w1) (w_opt_len w1) (w_static_len w1)) heap4) with w4.
  assert (HLh1' : Zlength heap1' = HEAP_SIZE) by (rewrite P1L; exact HL1).
  assert (Hlen573 : 2 * len + 1 <= 573) by (unfold HEAP_SIZE in Hroom; lia).
  assert (HL2 : Zlength heap2 = HEAP_SIZE) by (unfold heap2; rewrite !Zlength_upd; exact HLh1').
  assert (HL4 : Zlength heap4 = HEAP_SIZE) by (unfold heap4; rewrite Zlength_upd; exact HL2).
  assert (E21 : forall i, 0 <= i <= len - 1 -> Znth i heap2 = Znth i heap1').
  { intros i Hi. unfold heap2. rewrite !upd_Znth_diff; unfold HEAP_SIZE in *; try lia; rewrite ?upd_Znth_Zlength; lia. }
  set (rest := map (fun i => Znth i heap1') (zseq 2 (Z.to_nat (len - 1 - 1)))).
  assert (Rh : Permutation (reg heap len) (n :: m :: rest)).
  { eapply Permutation_trans; [apply reg_pqremove; unfold HEAP_SIZE in *; lia|].
    apply perm_skip. fold heap1. eapply Permutation_trans; [exact P1perm|].
    rewrite reg_cons by lia. apply Permutation_refl. }
  assert (Rh4 : reg heap4 (len - 1) = node :: rest).
  { unfold heap4. rewrite reg_set_top by (unfold HEAP_SIZE in *; lia). f_equal.
    apply map_zseq_ext. intros i Hi. apply E21. lia. }
  (* membership and distinctness *)
  assert (Hin_old : forall y, In y (n :: m :: rest) -> In y (reg heap len))
    by (intros y Hy; eapply Permutation_in; [apply Permutation_sym, Rh|exact Hy]).
  assert (Hnd' : NoDup ((n :: m :: rest) ++ removed heap hm)).
  { eapply Permutation_NoDup; [|exact Hnd]. apply Permutation_app_tail. exact Rh. }
  assert (Hlt : forall y, In y (n :: m :: rest) -> 0 <= y < node) by (intros y Hy; apply Hpool, Hin_old, Hy).
  assert (Hrest_node : forall y, In y rest -> y <> node) by (intros y Hy Hc; subst; specialize (Hlt node (or_intror (or_intror Hy))); lia).
  (* minimality *)
  assert (Hmin_n : forall y, In y (m :: rest) -> le t dep n y).
  { intros y Hy. assert (Hy' : In y (reg heap len)) by (apply Hin_old; right; auto).
    apply in_reg in Hy'. destruct Hy' as [i [Hi <-]]. exact (hp_top_min t dep heap len Hhp i Hi). }
  assert (Hmin_m : forall y, In y rest -> le t dep m y).
  { intros y Hy. assert (Hy' : In y (reg heap1' (len - 1))) by (rewrite reg_cons by lia; right; exact Hy).
    apply in_reg in Hy'. destruct Hy' as [i [Hi <-]]. exact (hp_top_min t dep heap1' (len - 1) P1hp i Hi). }
  assert (Hnode0 : 0 <= node) by (specialize (Hlt n (in_eq _ _)); lia).
  assert (HTS : node < TS /\ TS <= 573) by (unfold HEAP_SIZE in Hnode; lia).
  (* tree t3: frequencies and Dad fields *)
  assert (Hfc3 : forall y, y <> node -> Znth y (fc t3) = Znth y (fc t)).
  { intros y Hy. unfold t3, set_dl, set_fc; simpl.
    destruct (Z_le_gt_dec 0 y); [destruct (Z_lt_ge_dec y (Zlength (fc t)))|].
    - rewrite upd_Znth_diff by lia. reflexivity.
    - rewrite !Znth_overflow by (rewrite ?Zlength_upd; lia). reflexivity.
    - rewrite !Znth_underflow by lia. reflexivity. }
  assert (Hdep3 : forall y, y <> node -> Znth y dep3 = Znth y dep).
  { intros y Hy. unfold dep3.
    destruct (Z_le_gt_dec 0 y); [destruct (Z_lt_ge_dec y (Zlength dep))|].
    - rewrite upd_Znth_diff by lia. reflexivity.
    - rewrite !Znth_overflow by (rewrite ?Zlength_upd; lia). reflexivity.
    - rewrite !Znth_underflow by lia. reflexivity. }
  (* second sift *)
  assert (Hhp4 : hp t3 dep3 heap4 (len - 1) 2).
  { intros i Hi Hi2. assert (Hd2 := div2_lt i ltac:(lia)).
    unfold heap4. rewrite !upd_Znth_diff by (unfold HEAP_SIZE in *; lia). rewrite !E21 by lia.
    assert (Ha : In (Znth (i / 2) heap1') rest /\ In (Znth i heap1') rest).
    { split; unfold rest; apply in_map_iff; [exists (i / 2)|exists i]; split; auto; apply in_zseq; lia. }
    apply le_frame with t dep.
    - symmetry; apply Hfc3, Hrest_node, Ha.
    - symmetry; apply Hfc3, Hrest_node, Ha.
    - symmetry; apply Hdep3, Hrest_node, Ha.
    - symmetry; apply Hdep3, Hrest_node, Ha.
    - apply P1hp; lia. }
  destruct (pqdownheap_correct t3 w4 1) as [P2len [P2hm [P2dep [P2blc [P2ol [P2sl [P2L [P2hp [P2perm P2fr]]]]]]]]].
  { simpl; lia. } { simpl. rewrite HL4. unfold HEAP_SIZE in *; lia. } { simpl; unfold HEAP_SIZE in *; lia. }
  { exact Hhp4. }
  set (w5 := pqdownheap t3 w4 1) in *. set (heap5 := w_heap w5) in *.
  simpl in P2len, P2hm, P2dep, P2L, P2hp, P2perm, P2fr.
  (* the removed region and the frames *)
  assert (R1 : forall p, hm <= p < HEAP_SIZE -> Znth p heap5 = Znth p heap).
  { intros p Hp. unfold HEAP_SIZE in *. rewrite P2fr by lia. unfold heap4.
    rewrite upd_Znth_diff by lia. unfold heap2. rewrite !upd_Znth_diff by (rewrite ?Zlength_upd; lia).
    rewrite P1fr by lia. unfold heap1. rewrite upd_Znth_diff by lia. reflexivity. }
  assert (R2n : Znth (hm - 1) heap5 = n).
  { unfold HEAP_SIZE in *. rewrite P2fr by lia. unfold heap4. rewrite upd_Znth_diff by lia.
    unfold heap2. rewrite upd_Znth_diff by (rewrite ?Zlength_upd; lia). rewrite upd_Znth_same by lia. reflexivity. }
  assert (R2m : Znth (hm - 1 - 1) heap5 = m).
  { unfold HEAP_SIZE in *. rewrite P2fr by lia. unfold heap4. rewrite upd_Znth_diff by lia.
    unfold heap2. rewrite upd_Znth_same by (rewrite ?Zlength_upd; lia). reflexivity. }
  assert (R3 : removed heap5 (hm - 1 - 1) = m :: n :: removed heap hm).
  { rewrite removed_cons by (unfold HEAP_SIZE in *; lia). rewrite R2m. f_equal.
    replace (hm - 1 - 1 + 1) with (hm - 1) by lia.
    rewrite removed_cons by (unfold HEAP_SIZE in *; lia). rewrite R2n. f_equal.
    replace (hm - 1 + 1) with hm by lia. apply removed_frame. exact R1. }
  assert (Rh5 : Permutation (reg heap5 (len - 1)) (node :: rest)) by (rewrite <- Rh4; apply Permutation_sym, P2perm).
  set (it' := fun y => if y =? node then merge (it n) (it m) else it y).
  exists it', (merge (it n) (it m) :: map it rest). split; [|exact P2len].
  (* more facts *)
  assert (Hnm : n <> m) by (intros Hc; inversion Hnd' as [|? ? Hni _]; apply Hni; left; auto).
  assert (Hit' : forall y, In y rest -> it' y = it y)
    by (intros y Hy; unfold it'; rewrite (proj2 (Z.eqb_neq y node) (Hrest_node y Hy)); reflexivity).
  assert (Hmap' : map it' rest = map it rest) by (apply map_ext_in; auto).
  assert (Hnodeit : it' node = merge (it n) (it m)) by (unfold it'; rewrite Z.eqb_refl; reflexivity).
  assert (Hpn := Hpool n (Hin_old n (in_eq _ _))).
  assert (Hpm := Hpool m (Hin_old m (or_intror (in_eq _ _)))).
  assert (Hsum : Znth n (fc t) + Znth m (fc t) + sumZ (map (fun y => Znth y (fc t)) rest) = total).
  { rewrite <- Htot. rewrite (sumZ_perm' _ _ _ Rh). simpl. lia. }
  assert (Hrest_nn : 0 <= sumZ (map (fun y => Znth y (fc t)) rest)).
  { apply sumZ_nonneg. intros y Hy. apply (Hpool y (Hin_old y (or_intror (or_intror Hy)))). }
  assert (Hfcnode : Znth node (fc t3) = Znth n (fc t) + Znth m (fc t)).
  { unfold t3, set_dl, set_fc; simpl. rewrite upd_Znth_same by lia. unfold fcnm, u16.
    apply Z.mod_small. lia. }
  assert (Hdl3 : forall y, y <> n -> y <> m -> Znth y (dl t3) = Znth y (dl t)).
  { intros y Hyn Hym. unfold t3, set_dl, set_fc; simpl.
    destruct (Z_le_gt_dec 0 y); [destruct (Z_lt_ge_dec y (Zlength (dl t)))|].
    - rewrite !upd_Znth_diff by (rewrite ?Zlength_upd; lia). reflexivity.
    - rewrite !Znth_overflow by (rewrite ?Zlength_upd; lia). reflexivity.
    - rewrite !Znth_underflow by lia. reflexivity. }
  assert (Hdl3n : Znth n (dl t3) = node).
  { unfold t3, set_dl, set_fc; simpl. rewrite upd_Znth_same by (rewrite ?Zlength_upd; lia).
    unfold u16; apply Z.mod_small; lia. }
  assert (Hdl3m : Znth m (dl t3) = node).
  { unfold t3, set_dl, set_fc; simpl. rewrite upd_Znth_diff by (rewrite ?Zlength_upd; lia).
    rewrite upd_Znth_same by lia. unfold u16; apply Z.mod_small; lia. }
  assert (Hreg5 : forall y, In y (reg heap5 (len - 1)) <-> y = node \/ In y rest).
  { intros y. split; intros Hy.
    - apply (Permutation_in _ Rh5) in Hy. destruct Hy; auto.
    - apply (Permutation_in _ (Permutation_sym Rh5)). destruct Hy as [->|Hy]; [left|right]; auto. }
  assert (Hrem5 : forall y, In y (removed heap5 (hm - 1 - 1)) <-> y = m \/ y = n \/ In y (removed heap hm))
    by (intros y; rewrite R3; simpl; intuition).
  constructor.
  - (* mi_heap *) exact (eq_trans P2L HL4).
  - (* mi_depth *) rewrite P2dep. unfold dep3. rewrite Zlength_upd. exact Hd.
  - (* mi_fc *) unfold t3, set_dl, set_fc; simpl. rewrite Zlength_upd. exact Hfc.
  - (* mi_dl *) unfold t3, set_dl, set_fc; simpl. rewrite !Zlength_upd. exact Hdl.
  - (* mi_len *) rewrite P2len; lia.
  - (* mi_room *) rewrite P2len, P2hm. unfold HEAP_SIZE in *; lia.
  - (* mi_node *) rewrite P2len. lia.
  - (* mi_hp *) rewrite P2len, P2dep. exact P2hp.
  - (* mi_steps *)
    eapply steps_snoc; [exact Hst| |intros J HJ|intros J HJ].
    + eapply Permutation_trans; [exact Hperm|]. change (it n :: it m :: map it rest) with (map it (n :: m :: rest)).
      apply Permutation_map, Rh.
    + destruct HJ as [<-|HJ]; [|apply in_map_iff in HJ; destruct HJ as [y [<- Hy]]].
      * rewrite (proj1 (proj2 Hpn)), (proj1 (proj2 Hpm)). apply le_freq with dep. apply Hmin_n; left; auto.
      * rewrite (proj1 (proj2 Hpn)), (proj1 (proj2 (Hpool y (Hin_old y (or_intror (or_intror Hy)))))).
        apply le_freq with dep. apply Hmin_n; right; auto.
    + apply in_map_iff in HJ; destruct HJ as [y [<- Hy]].
      rewrite (proj1 (proj2 Hpm)), (proj1 (proj2 (Hpool y (Hin_old y (or_intror (or_intror Hy)))))).
      apply le_freq with dep. apply Hmin_m; auto.
  - (* mi_perm *)
    rewrite P2len. eapply Permutation_trans; [|apply Permutation_map, Permutation_sym, Rh5].
    simpl. rewrite Hnodeit, Hmap'. apply Permutation_refl.
  - (* mi_pool *)
    rewrite P2len. intros y Hy. apply Hreg5 in Hy. destruct Hy as [->|Hy].
    + rewrite Hnodeit, weight_merge, Hfcnode, (proj1 (proj2 Hpn)), (proj1 (proj2 Hpm)). lia.
    + rewrite Hit', Hfc3 by auto. specialize (Hpool y (Hin_old y (or_intror (or_intror Hy)))). lia.
  - (* mi_total *)
    rewrite P2len, (sumZ_perm' _ _ _ Rh5). cbn [map sumZ]. rewrite Hfcnode.
    rewrite (map_ext_in (fun y => Znth y (fc t3)) (fun y => Znth y (fc t)) rest)
      by (intros y Hy; apply Hfc3, Hrest_node, Hy). lia.
  - (* mi_nodup *)
    rewrite P2len, P2hm. fold heap5. rewrite R3.
    eapply Permutation_NoDup; [apply Permutation_app_tail, Permutation_sym, Rh5|].
    simpl. constructor.
    + intros Hc. apply in_app_or in Hc. destruct Hc as [Hc|[Hc|[Hc|Hc]]].
      * specialize (Hlt node (or_intror (or_intror Hc))); lia.
      * specialize (Hlt node (or_intror (or_introl Hc))); lia.
      * specialize (Hlt node (or_introl Hc)); lia.
      * apply in_removed in Hc. destruct Hc as [p [Hp Hpe]]. specialize (Hrem p Hp). rewrite Hpe in Hrem. lia.
    + eapply Permutation_NoDup; [|exact Hnd']. simpl.
      eapply Permutation_trans; [apply perm_swap|].
      transitivity (m :: rest ++ n :: removed heap hm); [apply perm_skip, Permutation_middle|].
      apply Permutation_middle.
  - (* mi_chain *)
    assert (Hdisj : forall z, In z (removed heap hm) -> z <> n /\ z <> m /\ ~ In z rest).
    { intros z Hz. assert (Hz' : ~ In z (n :: m :: rest)).
      { intros Hc. exact (nodup_app_disj _ _ z Hnd' Hc Hz). }
      split; [|split]; intros Hc; apply Hz'; [left|right; left|right; right]; auto. }
    assert (Hchain_old : forall y x, In y (reg heap len) -> In x (it y) ->
      forall e, (e <= Z.to_nat (ld x))%nat -> iter (dl t3) e (lid x) = iter (dl t) e (lid x)).
    { intros y x Hy Hx. destruct (Hch y x Hy Hx) as [_ [_ [_ Hrm]]].
      apply iter_agree. intros e He. symmetry. apply Hdl3; apply (Hdisj _ (Hrm e He)). }
    rewrite P2len, P2hm. fold heap5. intros y x Hy Hx. apply Hreg5 in Hy.
    destruct Hy as [->|Hy].
    + rewrite Hnodeit in Hx. apply in_merge in Hx. destruct Hx as [z [-> Hz]].
      assert (Hz' : exists yy, (yy = n \/ yy = m) /\ In z (it yy) /\ In yy (reg heap len)).
      { destruct Hz as [Hz|Hz]; [exists n|exists m]; repeat split; auto; apply Hin_old; simpl; auto. }
      destruct Hz' as [yy [Hyy [Hz2 Hyyr]]].
      destruct (Hch yy z Hyyr Hz2) as [Hd0 [HS [Hit Hrm]]].
      unfold deeper, ld, lid in *; cbn [fst snd] in *.
      split; [lia|]. split; [exact HS|].
      replace (Z.to_nat (snd z + 1)) with (Datatypes.S (Z.to_nat (snd z))) by lia.
      split.
      * rewrite iter_succ_r. rewrite (Hchain_old yy z Hyyr Hz2) by lia. unfold ld, lid in *. rewrite Hit.
        destruct Hyy as [->| ->]; auto.
      * intros e He. rewrite Hrem5. destruct (Nat.eq_dec e (Z.to_nat (snd z))) as [->|Hne].
        -- rewrite (Hchain_old yy z Hyyr Hz2) by lia. unfold ld, lid in *. rewrite Hit.
           destruct Hyy as [->| ->]; auto.
        -- rewrite (Hchain_old yy z Hyyr Hz2) by lia. right; right. apply Hrm. lia.
    + rewrite Hit' in Hx by auto. assert (Hyr : In y (reg heap len)) by (apply Hin_old; right; right; auto).
      destruct (Hch y x Hyr Hx) as [Hd0 [HS [Hit0 Hrm]]].
      split; [lia|]. split; [exact HS|]. split.
      * rewrite (Hchain_old y x Hyr Hx) by lia. exact Hit0.
      * intros e He. rewrite (Hchain_old y x Hyr Hx) by lia. rewrite Hrem5. right; right. apply Hrm; auto.
  - (* mi_rem *)
    rewrite P2len, P2hm. fold heap5. intros p Hp.
    assert (Hdisj : forall z, In z (removed heap hm) -> z <> n /\ z <> m /\ ~ In z rest).
    { intros z Hz. assert (Hz' : ~ In z (n :: m :: rest)).
      { intros Hc. exact (nodup_app_disj _ _ z Hnd' Hc Hz). }
      split; [|split]; intros Hc; apply Hz'; [left|right; left|right; right]; auto. }
    destruct (Z.eq_dec p (hm - 1 - 1)) as [->|Hp1]; [|destruct (Z.eq_dec p (hm - 1)) as [->|Hp2]].
    + rewrite R2m, Hdl3m. split; [lia|]. split; [lia|]. left. apply Hreg5; left; auto.
    + rewrite R2n, Hdl3n. split; [lia|]. split; [lia|]. left. apply Hreg5; left; auto.
    + assert (Hp' : hm <= p < HEAP_SIZE) by lia. rewrite (R1 p Hp').
      assert (Hzr : In (Znth p heap) (removed heap hm)) by (apply in_removed; eauto).
      destruct (Hdisj _ Hzr) as [Hzn [Hzm Hzrest]].
      rewrite (Hdl3 _ Hzn Hzm). destruct (Hrem p Hp') as [H0 [H1 H2']].
      split; [lia|]. split; [lia|].
      destruct H2' as [Hin|[q [Hq Hqe]]].
      * apply (Permutation_in _ Rh) in Hin. destruct Hin as [Hin|[Hin|Hin]].
        -- right. exists (hm - 1). split; [lia|]. rewrite R2n. auto.
        -- right. exists (hm - 1 - 1). split; [lia|]. rewrite R2m. auto.
        -- left. apply Hreg5; right; auto.
      * right. exists q. split; [lia|]. rewrite R1 by lia. auto.
  - (* mi_leaf_fc *)
    intros x Hx. destruct (Hleaf x Hx) as [Hf Hr]. split; auto. rewrite Hfc3 by lia. exact Hf.
  - (* mi_nonempty *)
    rewrite P2len. fold heap5. intros y Hy. apply Hreg5 in Hy. destruct Hy as [->|Hy].
    + rewrite Hnodeit. unfold merge. assert (Hn' := Hnonem n (Hin_old n (in_eq _ _))).
      destruct (it n); [congruence|]. simpl. discriminate.
    + rewrite Hit' by auto. apply Hnonem, Hin_old; right; right; auto.
  - (* mi_desc *)
    rewrite P2hm. fold heap5. intros p Hp.
    assert (Hdisj : forall z, In z (removed heap hm) -> z <> n /\ z <> m /\ ~ In z rest).
    { intros z Hz. assert (Hz' : ~ In z (n :: m :: rest)).
      { intros Hc. exact (nodup_app_disj _ _ z Hnd' Hc Hz). }
      split; [|split]; intros Hc; apply Hz'; [left|right; left|right; right]; auto. }
    assert (Hagree : forall x r, (forall e, (e < r)%nat -> In (iter (dl t) e x) (removed heap hm)) ->
              forall e, (e <= r)%nat -> iter (dl t3) e x = iter (dl t) e x).
    { intros x r Hr. apply iter_agree. intros e He. symmetry. apply Hdl3; apply (Hdisj _ (Hr e He)). }
    assert (Hpool_desc : forall y, In y (reg heap len) -> exists x r, In x S /\ iter (dl t3) r x = y /\
              (forall e, (e < r)%nat -> In (iter (dl t3) e x) (removed heap5 (hm - 1 - 1)))).
    { intros y Hy. assert (Hy' := Hnonem y Hy). destruct (it y) as [|x0 rest0] eqn:Ei; [congruence|].
      assert (Hx0 : In x0 (it y)) by (rewrite Ei; left; auto).
      destruct (Hch y x0 Hy Hx0) as [Hd0 [HS [Hit0 Hrm]]].
      exists (lid x0), (Z.to_nat (ld x0)). split; [exact HS|]. split.
      - rewrite (Hagree _ _ Hrm) by lia. exact Hit0.
      - intros e He. rewrite (Hagree _ _ Hrm) by lia. rewrite Hrem5. right; right. apply Hrm; auto. }
    destruct (Z.eq_dec p (hm - 1 - 1)) as [->|Hp1]; [|destruct (Z.eq_dec p (hm - 1)) as [->|Hp2]].
    + rewrite R2m. apply Hpool_desc, Hin_old; right; left; auto.
    + rewrite R2n. apply Hpool_desc, Hin_old; left; auto.
    + assert (Hp' : hm <= p < HEAP_SIZE) by lia. rewrite (R1 p Hp').
      destruct (Hdescs p Hp') as [x [r [HS [Hit0 Hrm]]]].
      exists x, r. split; [exact HS|]. split.
      * rewrite (Hagree _ _ Hrm) by lia. exact Hit0.
      * intros e He. rewrite (Hagree _ _ Hrm) by lia. rewrite Hrem5. right; right. apply Hrm; auto.
  - (* mi_kind *)
    rewrite P2len. fold heap5. intros y Hy. apply Hreg5 in Hy. destruct Hy as [->|Hy].
    + right. split; [lia|]. rewrite Hnodeit. intros x Hx. apply in_merge in Hx. destruct Hx as [z [-> Hz]].
      unfold deeper, ld; simpl.
      assert (Hz0 : 0 <= ld z).
      { destruct Hz as [Hz|Hz]; [apply (Hch n z (Hin_old n (in_eq _ _)) Hz)
                                |apply (Hch m z (Hin_old m (or_intror (in_eq _ _))) Hz)]. }
      unfold ld in Hz0. lia.
    + rewrite Hit' by auto. apply Hkind, Hin_old; right; right; auto.
  - (* mi_rkind *)
    rewrite P2hm. fold heap5. intros p Hp.
    destruct (Z.eq_dec p (hm - 1 - 1)) as [->|Hp1]; [|destruct (Z.eq_dec p (hm - 1)) as [->|Hp2]].
    + rewrite R2m. destruct (Hkind m (Hin_old m (or_intror (in_eq _ _)))) as [[HS _]|[He _]]; auto.
    + rewrite R2n. destruct (Hkind n (Hin_old n (in_eq _ _))) as [[HS _]|[He _]]; auto.
    + rewrite R1 by lia. apply Hrkind. lia.
  - (* mi_unused *)
    intros c Hc HcS.
    assert (Hcn : c <> n) by (intros ->; destruct (Hkind n (Hin_old n (in_eq _ _))) as [[HS _]|[He _]]; [exact (HcS HS)|lia]).
    assert (Hcm : c <> m) by (intros ->; destruct (Hkind m (Hin_old m (or_intror (in_eq _ _)))) as [[HS _]|[He _]]; [exact (HcS HS)|lia]).
    rewrite (Hdl3 c Hcn Hcm). exact (Hunused c Hc HcS).
Qed.

(** ** The whole merge loop *)

Lemma pq_fields : forall t w k, w_opt_len (pqdownheap t w k) = w_opt_len w /\
  w_static_len (pqdownheap t w k) = w_static_len w /\ w_bl_count (pqdownheap t w k) = w_bl_count w.
Proof. intros. unfold pqdownheap. destruct (pqdownheap_loop _ _ _ _ _ _ _ _) as [h k']. repeat split; reflexivity. Qed.
Lemma merge_body_fields : forall t w node,
  w_opt_len (snd (merge_body t w node)) = w_opt_len w /\ w_static_len (snd (merge_body t w node)) = w_static_len w /\
  w_bl_count (snd (merge_body t w node)) = w_bl_count w.
Proof.
  intros. unfold merge_body.
  destruct (pqremove t w) as [n w1] eqn:E1.
  assert (F1 : w_opt_len w1 = w_opt_len w /\ w_static_len w1 = w_static_len w /\ w_bl_count w1 = w_bl_count w).
  { unfold pqremove in E1. injection E1 as _ E1. subst w1. destruct (pq_fields t (w_set_heap_len (w_set_heap w (upd_Znth SMALLEST (w_heap w) (Znth (w_heap_len w) (w_heap w)))) (w_heap_len w - 1)) SMALLEST) as [A [B C]].
    rewrite A, B, C. split; [|split]; reflexivity. }
  destruct (new_node t (store_removed (store_removed w1 n) (Znth SMALLEST (w_heap w1))) n (Znth SMALLEST (w_heap w1)) node) as [t3 w3] eqn:E3.
  assert (F3 : w_opt_len w3 = w_opt_len w1 /\ w_static_len w3 = w_static_len w1 /\ w_bl_count w3 = w_bl_count w1).
  { unfold new_node in E3. injection E3 as _ E3. subst w3. split; [|split]; reflexivity. }
  destruct (pq_fields t3 (w_set_heap w3 (upd_Znth SMALLEST (w_heap w3) node)) SMALLEST) as [A [B C]].
  change (snd (t3, pqdownheap t3 (w_set_heap w3 (upd_Znth SMALLEST (w_heap w3) node)) SMALLEST))
    with (pqdownheap t3 (w_set_heap w3 (upd_Znth SMALLEST (w_heap w3) node)) SMALLEST).
  rewrite A, B, C. split; [|split]; [apply (eq_trans (proj1 F3)), F1|apply (eq_trans (proj1 (proj2 F3))), F1|apply (eq_trans (proj2 (proj2 F3))), F1].
Qed.

Lemma bt_merge_fields : forall fuel t w node,
  w_opt_len (snd (fst (bt_merge fuel t w node))) = w_opt_len w /\
  w_static_len (snd (fst (bt_merge fuel t w node))) = w_static_len w /\
  w_bl_count (snd (fst (bt_merge fuel t w node))) = w_bl_count w.
Proof.
  induction fuel as [|fuel IH]; intros t w node; [repeat split; reflexivity|].
  rewrite bt_merge_unfold. destruct (merge_body_fields t w node) as [A [B C]].
  destruct (merge_body t w node) as [t1 w1] eqn:E. simpl in A, B, C.
  destruct (w_heap_len w1 >=? 2).
  - destruct (IH t1 w1 (node + 1)) as [A' [B' C']]. repeat split; congruence.
  - simpl. repeat split; auto.
Qed.


Lemma bt_merge_inv : forall TS elems total S f0, total < 65536 ->
  forall fuel t w node it Q,
  minv TS elems total S f0 t w node it Q -> 2 <= w_heap_len w -> (Z.to_nat (w_heap_len w - 1) <= fuel)%nat ->
  let '(t', w', node') := bt_merge fuel t w node in
  exists it' Q', minv TS elems total S f0 t' w' node' it' Q' /\ w_heap_len w' = 1 /\
    node' = node + w_heap_len w - 1.
Proof.
  intros TS elems total S f0 Htot fuel. induction fuel as [|fuel IH]; intros t w node it Q HI H2 Hf; [lia|].
  rewrite bt_merge_unfold.
  destruct (merge_step TS elems total S f0 t w node it Q HI H2 Htot) as [it1 [Q1 [HI1 Hlen1]]].
  destruct (merge_body t w node) as [t1 w1] eqn:E. simpl in HI1, Hlen1.
  destruct (Z.geb_spec (w_heap_len w1) 2) as [Hge|Hlt].
  - assert (Hf1 : (Z.to_nat (w_heap_len w1 - 1) <= fuel)%nat) by lia.
    specialize (IH t1 w1 (node + 1) it1 Q1 HI1 Hge Hf1).
    destruct (bt_merge fuel t1 w1 (node + 1)) as [[t' w'] node'].
    destruct IH as [it' [Q' [HI' [Hl' Hn']]]]. exists it', Q'. split; [exact HI'|]. split; [exact Hl'|].
    rewrite Hn', Hlen1. lia.
  - exists it1, Q1. split; [exact HI1|]. split; [lia|]. lia.
Qed.

