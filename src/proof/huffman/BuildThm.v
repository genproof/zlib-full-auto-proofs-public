(** * build_tree: the theorem (BtSpec.build_tree_statement) *)

From Coq Require Import ZArith List Lia Bool Permutation Sorted.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap
               Zlib.proof.huffman.Bits Zlib.proof.huffman.BuildTree Zlib.proof.huffman.BuildKids
               Zlib.proof.huffman.BuildPre Zlib.proof.huffman.Bitlen Zlib.proof.huffman.DCount
               Zlib.proof.huffman.GenCodes Zlib.proof.huffman.HuffFib2 Zlib.proof.huffman.Repair
               Zlib.proof.huffman.BtSpec.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Frequencies stay in [0, 65536) through bt_pre *)

Definition frange (l : list Z) : Prop := forall n, 0 <= n < Zlength l -> 0 <= Znth n l < 65536.

Lemma frange_upd : forall l i v, frange l -> 0 <= v < 65536 -> frange (upd_Znth i l v).
Proof.
  intros l i v H Hv n Hn. rewrite Zlength_upd in Hn.
  destruct (Z_le_gt_dec 0 i); [destruct (Z_lt_ge_dec i (Zlength l))|].
  - destruct (Z.eq_dec n i) as [->|Hne].
    + rewrite upd_Znth_same by lia. exact Hv.
    + rewrite upd_Znth_diff by lia. apply H. exact Hn.
  - rewrite upd_Znth_out_of_range by lia. apply H. exact Hn.
  - rewrite upd_Znth_out_of_range by lia. apply H. exact Hn.
Qed.

Lemma bt_init_fc : forall f elems t w mc n, fc (fst (fst (bt_init f elems t w mc n))) = fc t.
Proof.
  induction f as [|f IH]; intros elems t w mc n; [reflexivity|]. cbn [bt_init].
  destruct (n <? elems); [|reflexivity]. destruct (negb (Znth n (fc t) =? 0)).
  - apply IH.
  - rewrite IH. reflexivity.
Qed.

Lemma bt_force_fc : forall f sd t w mc, frange (fc t) ->
  frange (fc (fst (fst (bt_force f sd t w mc)))) /\ Zlength (fc (fst (fst (bt_force f sd t w mc)))) = Zlength (fc t).
Proof.
  induction f as [|f IH]; intros sd t w mc H; [split; [exact H|reflexivity]|].
  rewrite bt_force_step. destruct (w_heap_len w <? 2); [|split; [exact H|reflexivity]].
  destruct (IH sd (set_fc t (fst (force_node mc)) 1) (force_push sd w (fst (force_node mc))) (snd (force_node mc)))
    as [A B].
  - apply frange_upd; [exact H|lia].
  - split; [exact A|]. rewrite B. apply Zlength_upd.
Qed.

Lemma merge_body_fc : forall t w node, exists v, 0 <= v < 65536 /\
  fc (fst (merge_body t w node)) = upd_Znth node (fc t) v.
Proof.
  intros t w node. unfold merge_body.
  destruct (pqremove t w) as [n w1].
  destruct (new_node t (store_removed (store_removed w1 n) (Znth SMALLEST (w_heap w1))) n (Znth SMALLEST (w_heap w1)) node)
    as [t3 w3] eqn:E3.
  unfold new_node in E3. injection E3 as E3 _. subst t3.
  exists (u16 (Znth n (fc t) + Znth (Znth SMALLEST (w_heap w1)) (fc t))). split; [unfold u16; apply Z.mod_pos_bound; lia|].
  reflexivity.
Qed.

Lemma bt_merge_fc : forall f t w node, frange (fc t) ->
  frange (fc (fst (fst (bt_merge f t w node)))) /\ Zlength (fc (fst (fst (bt_merge f t w node)))) = Zlength (fc t).
Proof.
  induction f as [|f IH]; intros t w node H; [split; [exact H|reflexivity]|].
  rewrite bt_merge_unfold. destruct (merge_body_fc t w node) as [v [Hv Ev]].
  destruct (merge_body t w node) as [t1 w1] eqn:E. simpl in Ev.
  assert (H1 : frange (fc t1)) by (rewrite Ev; apply frange_upd; auto).
  assert (L1 : Zlength (fc t1) = Zlength (fc t)) by (rewrite Ev; apply Zlength_upd).
  destruct (w_heap_len w1 >=? 2).
  - destruct (IH t1 w1 (node + 1) H1) as [A B]. split; [exact A|]. rewrite B. exact L1.
  - split; [exact H1|exact L1].
Qed.

Lemma bt_pre_fc : forall sd t w, frange (fc t) ->
  let '(t', w', mc) := bt_pre sd t w in frange (fc t') /\ Zlength (fc t') = Zlength (fc t).
Proof.
  intros sd t w H. unfold bt_pre.
  assert (E1 := bt_init_fc (Z.to_nat (sd_elems sd)) (sd_elems sd) t
                  (w_set_heap_max (w_set_heap_len w 0) HEAP_SIZE) (-1) 0).
  destruct (bt_init _ _ _ _ _ _) as [[t1 w1] m1]. simpl in E1.
  assert (H1 : frange (fc t1)) by (rewrite E1; exact H).
  destruct (bt_force_fc 2 sd t1 w1 m1 H1) as [A2 B2].
  destruct (bt_force 2 sd t1 w1 m1) as [[t2 w2] m2]. simpl in A2, B2.
  destruct (bt_merge_fc (Z.to_nat (w_heap_len (bt_heapify (Z.to_nat (w_heap_len w2 / 2)) t2 w2 (w_heap_len w2 / 2))))
              t2 (bt_heapify (Z.to_nat (w_heap_len w2 / 2)) t2 w2 (w_heap_len w2 / 2)) (sd_elems sd) A2) as [A3 B3].
  destruct (bt_merge _ _ _ _) as [[t3 w3] m3]. simpl in A3, B3.
  split; [exact A3|]. rewrite B3, B2, E1. reflexivity.
Qed.

(** ** Leaves of a greedy tree: ids, depths *)

Lemma map_lid_leaves_P0 : forall S f0, map lid (leaves (P0 S f0)) = S.
Proof. intros S f0. rewrite leaves_P0, map_map. unfold lid. simpl. apply map_id. Qed.

Lemma huff_lid_perm : forall S f0 R, huff (P0 S f0) R -> Permutation S (map lid R).
Proof.
  intros S f0 R H. assert (Hp := huff_idf _ _ H). apply (Permutation_map fst) in Hp.
  rewrite !map_map in Hp. rewrite <- (map_lid_leaves_P0 S f0). exact Hp.
Qed.

Lemma find_lid : forall (R : item) l, NoDup (map lid R) -> In l R -> depth_of R (lid l) = ld l.
Proof.
  intros R l Hnd Hl. unfold depth_of. induction R as [|a R IH]; [destruct Hl|].
  simpl in Hnd. inversion Hnd as [|? ? Ha Hnd']; subst. simpl.
  destruct Hl as [<-|Hl].
  - rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec (lid a) (lid l)) as [E|E].
    + exfalso. apply Ha. rewrite E. apply in_map. exact Hl.
    + apply IH; auto.
Qed.

(** ** The heap scan of the reassignment *)

Lemma scan_eq : forall heap mc h k,
  scan heap mc h k = filter (fun m => m <=? mc) (map (fun i => Znth i heap) (rev (zseq (h - Z.of_nat k) k))).
Proof.
  intros heap mc h k. revert h. induction k as [|k IH]; intros h; [reflexivity|].
  cbn [scan]. rewrite IH. replace (h - Z.of_nat (S k)) with (h - 1 - Z.of_nat k) by lia.
  rewrite zseq_succ_r, rev_app_distr. cbn [rev app map filter].
  replace (h - 1 - Z.of_nat k + Z.of_nat k) with (h - 1) by lia.
  destruct (Z.gtb_spec (Znth (h - 1) heap) mc).
  - replace (Znth (h - 1) heap <=? mc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - replace (Znth (h - 1) heap <=? mc) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma filter_rev : forall {A} (f : A -> bool) l, filter f (rev l) = rev (filter f l).
Proof.
  intros A f l. induction l as [|a l IH]; [reflexivity|]. simpl. rewrite filter_app, IH. simpl.
  destruct (f a); simpl; [reflexivity|apply app_nil_r].
Qed.

(** Strongly sorted lists, by index. *)
Lemma SS_index : forall (Rl : Z -> Z -> Prop) l, StronglySorted Rl l ->
  forall i j, 0 <= i < j -> j < Zlength l -> Rl (Znth i l) (Znth j l).
Proof.
  intros Rl l H. induction H as [|a l Hs IH Hall]; intros i j Hij Hj; [rewrite Zlength_nil in Hj; lia|].
  rewrite Zlength_cons in Hj. destruct (Z.eq_dec i 0) as [->|Hi].
  - rewrite Znth_0_cons, Znth_pos_cons by lia. rewrite Forall_forall in Hall. apply Hall. apply Znth_In. lia.
  - rewrite !Znth_pos_cons by lia. apply IH; lia.
Qed.

Lemma SS_filter : forall (Rl : Z -> Z -> Prop) (f : Z -> bool) l, StronglySorted Rl l -> StronglySorted Rl (filter f l).
Proof.
  intros Rl f l H. induction H as [|a l Hs IH Hall]; [constructor|]. simpl. destruct (f a); [|exact IH].
  constructor; [exact IH|]. rewrite Forall_forall in *. intros x Hx. apply filter_In in Hx. apply Hall, Hx.
Qed.

Lemma SS_snoc : forall (Rl : Z -> Z -> Prop) l a, StronglySorted Rl l -> (forall x, In x l -> Rl x a) ->
  StronglySorted Rl (l ++ [a]).
Proof.
  intros Rl l a H. induction H as [|b l Hs IH Hall]; intros Ha; simpl.
  - repeat constructor.
  - constructor; [apply IH; intros; apply Ha; right; auto|].
    rewrite Forall_forall in *. intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|[<-|[]]]; [apply Hall; auto|].
    apply Ha. left; auto.
Qed.

Lemma SS_rev : forall (Rl : Z -> Z -> Prop) l, StronglySorted Rl l -> StronglySorted (fun x y => Rl y x) (rev l).
Proof.
  intros Rl l H. induction H as [|a l Hs IH Hall]; [constructor|]. simpl.
  apply SS_snoc; [exact IH|]. intros x Hx. rewrite Forall_forall in Hall. apply Hall. apply in_rev. exact Hx.
Qed.

Lemma SS_zseq : forall (Rl : Z -> Z -> Prop) (f : Z -> Z) n a,
  (forall i j, a <= i < j -> j < a + Z.of_nat n -> Rl (f i) (f j)) -> StronglySorted Rl (map f (zseq a n)).
Proof.
  intros Rl f n. induction n as [|n IH]; intros a H; [constructor|]. simpl. constructor.
  - apply IH. intros i j Hij Hj. apply H; lia.
  - rewrite Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as [j [<- Hj]]. apply in_zseq in Hj.
    apply H; lia.
Qed.

Lemma sumz_sumZ : forall l, sumz l = sumZ l.
Proof. induction l as [|a l IH]; simpl; auto. Qed.

Lemma fh_le : forall fuel D r y, 0 <= fh fuel D r y <= Z.of_nat fuel.
Proof.
  induction fuel as [|f IH]; intros D r y; [simpl; lia|]. cbn [fh]. rewrite Nat2Z.inj_succ.
  destruct (y =? r); [lia|]. specialize (IH D r (Znth y D)). lia.
Qed.

Lemma cntz_sumZ : forall (P : Z -> bool) l, cntz P l = sumZ (map (fun x => if P x then 1 else 0) l).
Proof. intros P l. unfold cntz. induction l as [|a l IH]; [reflexivity|]. simpl. destruct (P a); simpl length; lia. Qed.

Lemma dsum_map : forall ms (g : Z -> Z) D F,
  dsum ms (map g ms) D F = sumZ (map (fun m => (g m - Znth m D) * Znth m F) ms).
Proof. induction ms as [|m ms IH]; intros g D F; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma Znth_eq_ext : forall (l1 l2 : list Z), Zlength l1 = Zlength l2 ->
  (forall i, 0 <= i < Zlength l1 -> Znth i l1 = Znth i l2) -> l1 = l2.
Proof.
  intros l1 l2 HL H. apply (nth_ext l1 l2 0 0).
  - rewrite !Zlength_correct in HL. lia.
  - intros n Hn. specialize (H (Z.of_nat n) ltac:(rewrite Zlength_correct; lia)). unfold Znth in H.
    destruct (Z_lt_dec (Z.of_nat n) 0); [lia|]. rewrite Nat2Z.id in H. exact H.
Qed.

Ltac feed H := repeat match type of H with ?A -> _ =>
  let h := fresh in assert (h : A) by (first [assumption | eauto]); specialize (H h); clear h end.

(** ** gen_bitlen on the state before it *)

Section Gen.
Variable sd : stat_desc.
Variables (t0 : tree) (w0 : work) (S F : list Z) (R : item) (t : tree) (w : work) (mc : Z).
Hypothesis Hpre : pre_ok sd t0 w0 S F R t w mc.
Hypothesis HM : 1 <= sd_maxlen sd <= 15.
Hypothesis Hel : 3 <= sd_elems sd <= 286.
Hypothesis Hdlen : sd_elems sd <= Zlength (dl t).
Hypothesis Hxb_sd : forall n, 0 <= n < Zlength (dl t) -> 0 <= xb sd n <= 16.
Hypothesis Hst_sd : forall st, sd_stree sd = Some st -> forall n, 0 <= n < Zlength (dl t) -> 0 <= Znth n st <= 16.
Hypothesis Hfc_rng : forall n, 0 <= n < Zlength (dl t) -> 0 <= Znth n (fc t) < 65536.
Hypothesis Hopt : 0 <= w_opt_len w < 18446744073709551616.
Hypothesis Hstl : 0 <= w_static_len w < 18446744073709551616.
Hypothesis Hel2 : sd_elems sd <= 2 ^ sd_maxlen sd.

Let M := sd_maxlen sd.
Let elems := sd_elems sd.
Let hmp := w_heap_max w.
Let hp0 := w_heap w.

Lemma g_S : S = nzl (fc t0) elems ++ F /\ NoDup S /\ (forall x, In x S -> 0 <= x < elems).
Proof. destruct (po_S _ _ _ _ _ _ _ _ _ Hpre) as [A [B [C _]]]. auto. Qed.

Lemma g_huff : huff (P0 S (fun x => Znth x (fc t))) R.
Proof. exact (po_huff _ _ _ _ _ _ _ _ _ Hpre). Qed.

Lemma g_lid_nodup : NoDup (map lid R).
Proof. apply (Permutation_NoDup (huff_lid_perm _ _ _ g_huff)). apply g_S. Qed.

Lemma g_mc_lt : mc < sd_elems sd.
Proof. destruct (po_mc _ _ _ _ _ _ _ _ _ Hpre) as [Hm _]. destruct g_S as [_ [_ H]]. specialize (H mc Hm). unfold elems in H. lia. Qed.

Lemma sumZ_filter_if : forall (P : Z -> bool) (g : Z -> Z) l,
  HuffAbs.sumZ (map (fun v => if P v then g v else 0) l) = HuffAbs.sumZ (map g (filter P l)).
Proof. intros P g l. induction l as [|a l IH]; simpl; [reflexivity|]. destruct (P a); simpl; lia. Qed.

Lemma g_mc : In mc S /\ forall x, In x S -> x <= mc.
Proof. exact (po_mc _ _ _ _ _ _ _ _ _ Hpre). Qed.

Lemma g_Nn_leaf : forall v, In v (Nn w) -> (v <? sd_elems sd) = (v <=? mc).
Proof.
  intros v Hv. apply in_Nn in Hv. destruct Hv as [p [Hp <-]].
  assert (G := g_mc_lt). destruct g_mc as [_ Hle].
  destruct (region_kind _ _ _ _ _ _ _ _ _ Hpre p ltac:(lia)) as [HS|HI].
  - specialize (Hle _ HS). destruct g_S as [_ [_ HSr]]. specialize (HSr _ HS).
    apply eq_true_iff_eq. rewrite Z.ltb_lt, Z.leb_le. unfold elems in *. lia.
  - apply eq_true_iff_eq. rewrite Z.ltb_lt, Z.leb_le. unfold elems in *. lia.
Qed.

Lemma g_leaves_perm : Permutation (filter (fun v => v <=? mc) (Nn w)) S.
Proof.
  apply NoDup_Permutation.
  - apply NoDup_filter. assert (H := Nall_nodup _ _ _ _ _ _ _ _ _ Hpre).
    rewrite (Nall_cons _ _ _ _ _ _ _ _ _ Hpre) in H. inversion H; auto.
  - apply g_S.
  - intros x. rewrite filter_In, Z.leb_le. split.
    + intros [Hx Hle]. apply in_Nn in Hx. destruct Hx as [p [Hp <-]].
      destruct (region_kind _ _ _ _ _ _ _ _ _ Hpre p ltac:(lia)) as [HS|HI]; [exact HS|].
      exfalso. assert (G := g_mc_lt). unfold elems in G. lia.
    + intros Hx. split; [|apply g_mc; exact Hx].
      assert (Hr := po_inS _ _ _ _ _ _ _ _ _ Hpre x Hx). fold (Nall w) in Hr.
      rewrite (Nall_cons _ _ _ _ _ _ _ _ _ Hpre) in Hr. destruct Hr as [Hr|Hr]; [|exact Hr].
      exfalso. destruct (region_kind _ _ _ _ _ _ _ _ _ Hpre (w_heap_max w) ltac:(pose proof (pre_hm _ _ _ _ _ _ _ _ _ Hpre); lia)) as [HS|HI].
      * (* the root is not a leaf: leaves are at depth >= 1 *)
        destruct (huff_leaf_of S (fun x => Znth x (fc t)) R _ g_huff HS) as [l [Hl Hlid]].
        destruct (po_depth _ _ _ _ _ _ _ _ _ Hpre l Hl) as [H1 [H2 H3]].
        apply (H3 O ltac:(lia)). simpl. rewrite Hlid. reflexivity.
      * destruct g_S as [_ [_ HSr]]. specialize (HSr _ Hx). rewrite Hr in HI. unfold elems in HSr. lia.
Qed.

(** Every leaf of the region: its depth (distance to the root) is its depth in R. *)
Lemma g_leaf_depth : forall v, In v (Nn w) -> v <=? mc = true -> In v S /\ ev t w v = depth_of R v.
Proof.
  intros v Hv Hle.
  assert (HS : In v S) by (apply (Permutation_in _ g_leaves_perm); apply filter_In; auto).
  split; [exact HS|].
  destruct (huff_leaf_of S (fun x => Znth x (fc t)) R v g_huff HS) as [l [Hl Hlid]].
  destruct (E_leaf _ _ _ _ _ _ _ _ _ Hpre l Hl) as [q [Hq [Eq EE]]].
  rewrite <- Hlid, (find_lid R l g_lid_nodup Hl). rewrite <- EE. unfold E, ev. rewrite Eq. reflexivity.
Qed.



Lemma g_sum_leaves : forall (g : Z -> Z -> Z),
  sumZ (map (fun q => if Znth q (w_heap w) <=? mc then g (Znth q (w_heap w)) (E (w_heap_max w) (w_heap w) (dl t) q) else 0)
              (rng (w_heap_max w) HEAP_SIZE))
  = sumZ (map (fun x => g x (depth_of R x)) S).
Proof.
  intros g.
  transitivity (sumZ (map (fun v => if v <=? mc then g v (ev t w v) else 0) (Nn w))).
  { rewrite Nn_rng, map_map. reflexivity. }
  rewrite sumZ_filter_if.
  rewrite (sumZ_map_ext _ (fun v => g v (depth_of R v))).
  2:{ intros v Hv. apply filter_In in Hv. destruct Hv as [Hv Hle]. rewrite (proj2 (g_leaf_depth v Hv Hle)). reflexivity. }
  apply sumZ_perm'. exact g_leaves_perm.
Qed.

Lemma g_sum_R : forall (g : Z -> Z -> Z),
  sumZ (map (fun x => g x (depth_of R x)) S) = sumZ (map (fun l => g (lid l) (ld l)) R).
Proof.
  intros g. rewrite (sumZ_perm' _ _ _ (huff_lid_perm _ _ _ g_huff)), map_map.
  apply sumZ_map_ext. intros l Hl. rewrite (find_lid R l g_lid_nodup Hl). reflexivity.
Qed.

Lemma g_depth_pos : forall l, In l R -> 1 <= ld l.
Proof. intros l Hl. apply (po_depth _ _ _ _ _ _ _ _ _ Hpre l Hl). Qed.

Lemma g_kraft_R : forall D, 0 <= D -> (forall l, In l R -> ld l <= D) -> kz D R = 2 ^ D.
Proof.
  intros D HD0 HD. apply (huff_kraft _ _ D g_huff).
  - intros I HI. unfold P0 in HI. apply in_map_iff in HI. destruct HI as [x [<- _]].
    split; [intros y [<-|[]]; unfold ld; simpl; lia|]. unfold kz. simpl. unfold ld; simpl.
    rewrite Z.sub_0_r. lia.
  - intros l Hl. split; [assert (H := g_depth_pos l Hl); lia|apply HD; exact Hl].
Qed.

Lemma g_noovf_ideep : (forall l, In l R -> ld l <= sd_maxlen sd) -> Ideep sd t w = 0.
Proof.
  intros HD.
  assert (K := kraft_clamped _ _ _ _ _ _ _ _ _ Hpre HM).
  rewrite (sumZ_map_ext _ (fun v => if v <=? mc then gcl sd (ev t w v) else 0)) in K
    by (intros v Hv; rewrite (g_Nn_leaf v Hv); reflexivity).
  rewrite sumZ_filter_if in K.
  rewrite (sumZ_map_ext _ (fun v => gcl sd (depth_of R v))) in K.
  2:{ intros v Hv. apply filter_In in Hv. destruct Hv as [Hv Hle]. rewrite (proj2 (g_leaf_depth v Hv Hle)). reflexivity. }
  rewrite (sumZ_perm' _ _ _ g_leaves_perm) in K.
  rewrite (g_sum_R (fun _ d => gcl sd d)) in K.
  rewrite (sumZ_map_ext _ (fun l => 2 ^ (sd_maxlen sd - ld l))) in K.
  2:{ intros l Hl. unfold gcl. rewrite Z.min_l by (apply HD; exact Hl). reflexivity. }
  assert (Hk := g_kraft_R (sd_maxlen sd) ltac:(lia) HD). unfold kz in Hk. lia.
Qed.

(** The reassignment's scan order: the leaves from heap position HEAP_SIZE - 1 down. *)
Definition order : list Z := scan (w_heap w) mc HEAP_SIZE (Z.to_nat (HEAP_SIZE - w_heap_max w - 1)).

Lemma g_order_eq : order = rev (filter (fun v => v <=? mc) (Nn w)).
Proof.
  unfold order. rewrite scan_eq. pose proof (pre_hm _ _ _ _ _ _ _ _ _ Hpre).
  replace (HEAP_SIZE - Z.of_nat (Z.to_nat (HEAP_SIZE - w_heap_max w - 1))) with (w_heap_max w + 1)
    by (unfold HEAP_SIZE in *; lia).
  rewrite map_rev, filter_rev. unfold Nn, removed. do 4 f_equal. lia.
Qed.

Lemma g_order_perm : Permutation order S.
Proof. rewrite g_order_eq. eapply Permutation_trans; [apply Permutation_sym, Permutation_rev|apply g_leaves_perm]. Qed.

Lemma g_order_nodup : NoDup order.
Proof. apply (Permutation_NoDup (Permutation_sym g_order_perm)). apply g_S. Qed.

Lemma g_order_sorted : forall i j, 0 <= i <= j -> j < Zlength order ->
  Znth (Znth i order) (fc t) <= Znth (Znth j order) (fc t).
Proof.
  assert (H1 : StronglySorted (fun x y => Znth y (fc t) <= Znth x (fc t)) (Nn w)).
  { unfold Nn, removed. apply SS_zseq. intros i j Hij Hj.
    apply (po_sorted _ _ _ _ _ _ _ _ _ Hpre); lia. }
  assert (H2 := SS_rev _ _ (SS_filter _ (fun v => v <=? mc) _ H1)). rewrite <- g_order_eq in H2.
  intros i j Hij Hj. destruct (Z.eq_dec i j) as [->|Hne]; [lia|].
  apply (SS_index _ _ H2); lia.
Qed.

Lemma g_pass1 :
  let '(t2, w2, ovf) := gen_bitlen_pass1 (Z.to_nat HEAP_SIZE) sd mc (set_dl t (Znth (w_heap_max w) (w_heap w)) 0)
                          (w_set_bl_count w (repeat 0 (Z.to_nat (MAX_BITS + 1)))) 0 (w_heap_max w + 1) in
  fc t2 = fc t /\ Zlength (dl t2) = Zlength (dl t) /\ w_heap w2 = w_heap w /\ w_heap_max w2 = w_heap_max w /\
  w_heap_len w2 = w_heap_len w /\ w_depth w2 = w_depth w /\
  (forall x, In x S -> Znth x (dl t2) = Z.min (depth_of R x) (sd_maxlen sd)) /\
  (forall c, 0 <= c < sd_elems sd -> ~ In c S -> Znth c (dl t2) = 0) /\
  ovf = 2 * Ideep sd t w /\ (ovf = 0 -> forall l, In l R -> ld l <= sd_maxlen sd) /\
  Zlength (w_bl_count w2) = 16 /\
  (forall b, 0 <= b < 16 -> Znth b (w_bl_count w2) =
     sumZ (map (fun x => if Z.min (depth_of R x) (sd_maxlen sd) =? b then 1 else 0) S)) /\
  w_opt_len w2 = u64 (w_opt_len w + sumZ (map (fun x => Znth x (fc t) * (Z.min (depth_of R x) (sd_maxlen sd) + xb sd x)) S)) /\
  w_static_len w2 = match sd_stree sd with
                    | Some st => u64 (w_static_len w + sumZ (map (fun x => Znth x (fc t) * (Znth x st + xb sd x)) S))
                    | None => w_static_len w end.
Proof.
  assert (P := pass1_on_pre sd t0 w0 S F R t w mc Hpre HM Hel Hdlen Hxb_sd Hst_sd Hfc_rng Hopt Hstl).
  assert (L := pass1_lengths sd t0 w0 S F R t w mc Hpre HM Hel Hdlen Hxb_sd Hst_sd Hfc_rng Hopt Hstl).
  destruct (gen_bitlen_pass1 _ _ _ _ _ _ _) as [[t2 w2] ovf].
  destruct P as [I1 [I2 [I3 [I4 [I5 [I6 [I7 [I8 [I9 [I10 [I11 [I12 I13]]]]]]]]]]]].
  destruct L as [_ [_ [_ [_ [_ [_ [L7 [L8 L9]]]]]]]].
  split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
  split; [exact I6|].
  split.
  { intros x Hx. destruct (huff_leaf_of S (fun x => Znth x (fc t)) R x g_huff Hx) as [l [Hl Hlid]].
    rewrite <- Hlid, (find_lid R l g_lid_nodup Hl). apply L7; exact Hl. }
  split; [exact L8|].
  split.
  { rewrite I9. unfold cnt_ovf. rewrite <- (ovf_twice _ _ _ _ _ _ _ _ _ Hpre). rewrite Nn_rng, map_map. reflexivity. }
  split; [exact L9|].
  split; [exact I10|].
  split.
  { intros b Hb. rewrite I11 by exact Hb. unfold cnt_bl.
    rewrite (sumZ_map_ext _ (fun q => if Znth q (w_heap w) <=? mc then
                (fun x d => if Z.min d (sd_maxlen sd) =? b then 1 else 0) (Znth q (w_heap w)) (E (w_heap_max w) (w_heap w) (dl t) q)
                else 0)).
    2:{ intros q _. destruct (Znth q (w_heap w) <=? mc); reflexivity. }
    apply (g_sum_leaves (fun x d => if Z.min d (sd_maxlen sd) =? b then 1 else 0)). }
  split.
  { rewrite I12. f_equal. f_equal. apply (g_sum_leaves (fun x d => Znth x (fc t) * (Z.min d (sd_maxlen sd) + xb sd x))). }
  rewrite I13. destruct (sd_stree sd) as [st|]; [|reflexivity]. f_equal. f_equal.
  apply (g_sum_leaves (fun x d => Znth x (fc t) * (Znth x st + xb sd x))).
Qed.

Lemma g_ld_bound : forall l, In l R -> 1 <= ld l <= 600.
Proof.
  intros l Hl. split; [apply g_depth_pos; exact Hl|].
  destruct (E_leaf _ _ _ _ _ _ _ _ _ Hpre l Hl) as [q [_ [_ EE]]]. rewrite <- EE. unfold E.
  assert (H := fh_le 600 (dl t) (Znth (w_heap_max w) (w_heap w)) (Znth q (w_heap w))). simpl Z.of_nat in H. lia.
Qed.

Lemma g_depth_S : forall x, In x S -> exists l, In l R /\ lid l = x /\ depth_of R x = ld l.
Proof.
  intros x Hx. destruct (huff_leaf_of S (fun x => Znth x (fc t)) R x g_huff Hx) as [l [Hl Hlid]].
  exists l. split; [exact Hl|]. split; [exact Hlid|]. rewrite <- Hlid. apply find_lid; [apply g_lid_nodup|exact Hl].
Qed.

Definition dlist : list Z := map (depth_of R) order.

Lemma g_d_range : forall x, In x dlist -> 1 <= x <= 600.
Proof.
  intros x Hx. unfold dlist in Hx. apply in_map_iff in Hx. destruct Hx as [y [<- Hy]].
  apply (Permutation_in _ g_order_perm) in Hy. destruct (g_depth_S y Hy) as [l [Hl [_ ->]]]. apply g_ld_bound; exact Hl.
Qed.

Lemma g_sum_order : forall g : Z -> Z, sumZ (map g order) = sumZ (map g S).
Proof. intros g. apply sumZ_perm'. exact g_order_perm. Qed.

Lemma g_d_kraft : sumz (map (fun x => 2 ^ (600 - x)) dlist) = 2 ^ 600.
Proof.
  rewrite sumz_sumZ. unfold dlist. rewrite map_map. rewrite (g_sum_order (fun y => 2 ^ (600 - depth_of R y))).
  rewrite (g_sum_R (fun _ dd => 2 ^ (600 - dd))). assert (H := g_kraft_R 600 ltac:(lia) ltac:(intros l Hl; apply g_ld_bound; exact Hl)).
  unfold kz in H. exact H.
Qed.

Lemma g_d_len : Zlength dlist = Zlength S.
Proof. unfold dlist. rewrite Zlength_map. rewrite !Zlength_correct. f_equal. apply Permutation_length, g_order_perm. Qed.

Lemma g_clampc : forall b, 0 <= b < 16 ->
  sumZ (map (fun x => if Z.min (depth_of R x) (sd_maxlen sd) =? b then 1 else 0) S) = Znth b (clampc (sd_maxlen sd) dlist).
Proof.
  intros b Hb. rewrite Znth_clampc by exact Hb. destruct (Z.eqb_spec b 0) as [->|Hb0].
  - rewrite (sumZ_map_ext _ (fun _ => 0)); [apply sumZ_map_zero|].
    intros x Hx. destruct (g_depth_S x Hx) as [l [Hl [_ ->]]]. assert (H := g_ld_bound l Hl).
    destruct (Z.eqb_spec (Z.min (ld l) (sd_maxlen sd)) 0); lia.
  - rewrite cntz_sumZ. unfold dlist. rewrite map_map. symmetry. apply g_sum_order.
Qed.

Lemma g_kraftc : kraftc (sd_maxlen sd) (clampc (sd_maxlen sd) dlist) = 2 ^ sd_maxlen sd + Ideep sd t w.
Proof.
  destruct (clamp_sums (sd_maxlen sd) dlist HM) as [Hk _]; [intros x Hx; apply g_d_range; exact Hx|].
  rewrite Hk, sumz_sumZ. unfold dlist. rewrite map_map. rewrite (g_sum_order (fun y => 2 ^ (sd_maxlen sd - Z.min (depth_of R y) (sd_maxlen sd)))).
  assert (K := kraft_clamped _ _ _ _ _ _ _ _ _ Hpre HM).
  rewrite (sumZ_map_ext _ (fun v => if v <=? mc then gcl sd (ev t w v) else 0)) in K
    by (intros v Hv; rewrite (g_Nn_leaf v Hv); reflexivity).
  rewrite sumZ_filter_if in K.
  rewrite (sumZ_map_ext _ (fun v => gcl sd (depth_of R v))) in K.
  2:{ intros v Hv. apply filter_In in Hv. destruct Hv as [Hv Hle]. rewrite (proj2 (g_leaf_depth v Hv Hle)). reflexivity. }
  rewrite (sumZ_perm' _ _ _ g_leaves_perm) in K. unfold gcl in K. exact K.
Qed.

Lemma g_S_len : Zlength S <= sd_elems sd.
Proof.
  destruct g_S as [_ [Hnd Hr]].
  assert (H := NoDup_incl_Zlength S (zseq 0 (Z.to_nat (sd_elems sd))) Hnd
                 ltac:(intros x Hx; apply in_zseq; specialize (Hr x Hx); unfold elems in Hr; lia)).
  rewrite (Zlength_correct (zseq _ _)), zseq_length in H. lia.
Qed.

Lemma g_deep_exists : ~ (forall l, In l R -> ld l <= sd_maxlen sd) -> exists x, In x dlist /\ sd_maxlen sd < x.
Proof.
  intros HnD. destruct (existsb (fun l => sd_maxlen sd <? ld l) R) eqn:E.
  - apply existsb_exists in E. destruct E as [l [Hl Hle]]. apply Z.ltb_lt in Hle.
    exists (ld l). split; [|lia]. unfold dlist. apply in_map_iff. exists (lid l). split.
    + apply find_lid; [apply g_lid_nodup|exact Hl].
    + apply (Permutation_in _ (Permutation_sym g_order_perm)). apply (leaf_in_S _ _ _ _ _ _ _ _ _ Hpre l Hl).
  - exfalso. apply HnD. intros l Hl. destruct (Z.ltb_spec (sd_maxlen sd) (ld l)) as [Hlt|Hle]; [|exact Hle].
    assert (Ht : existsb (fun l => sd_maxlen sd <? ld l) R = true)
      by (apply existsb_exists; exists l; split; [exact Hl|apply Z.ltb_lt; exact Hlt]).
    congruence.
Qed.

Lemma g_genbitlen : let '(t3, w3) := gen_bitlen sd mc t w in
  fc t3 = fc t /\ Zlength (dl t3) = Zlength (dl t) /\ w_heap w3 = w_heap w /\ w_heap_max w3 = w_heap_max w /\
  w_depth w3 = w_depth w /\ Zlength (w_bl_count w3) = 16 /\
  (forall c, 0 <= c < sd_elems sd -> ~ In c S -> Znth c (dl t3) = 0) /\
  (forall x, In x S -> 1 <= Znth x (dl t3) <= sd_maxlen sd) /\
  ((forall l, In l R -> ld l <= sd_maxlen sd) -> forall x, In x S -> Znth x (dl t3) = depth_of R x) /\
  (~ (forall l, In l R -> ld l <= sd_maxlen sd) -> forall k, 0 <= k < Zlength order ->
      Znth (Znth k order) (dl t3) = Znth k (repl (sd_maxlen sd) dlist)) /\
  sumZ (map (fun x => 2 ^ (sd_maxlen sd - Znth x (dl t3))) S) = 2 ^ sd_maxlen sd /\
  w_opt_len w3 = u64 (w_opt_len w + sumZ (map (fun x => Znth x (fc t) * (Znth x (dl t3) + xb sd x)) S)) /\
  w_static_len w3 = match sd_stree sd with
                    | Some st => u64 (w_static_len w + sumZ (map (fun x => Znth x (fc t) * (Znth x st + xb sd x)) S))
                    | None => w_static_len w end.
Proof.
  rewrite gen_bitlen_eq. cbv zeta.
  assert (G := g_pass1).
  destruct (gen_bitlen_pass1 _ _ _ _ _ _ _) as [[t2 w2] ovf].
  destruct G as [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 [G9 [G10 [G11 [G12 [G13 G14]]]]]]]]]]]]].
  destruct (Z.eqb_spec ovf 0) as [Hz|Hnz].
  - (* no overflow *)
    assert (HD := G10 Hz).
    assert (Hlen : forall x, In x S -> Znth x (dl t2) = depth_of R x).
    { intros x Hx. rewrite G7 by exact Hx. destruct (g_depth_S x Hx) as [l [Hl [_ ->]]]. apply Z.min_l, HD, Hl. }
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G6|].
    split; [exact G11|]. split; [exact G8|].
    split.
    { intros x Hx. rewrite Hlen by exact Hx. destruct (g_depth_S x Hx) as [l [Hl [_ ->]]].
      split; [apply g_depth_pos; exact Hl|apply HD; exact Hl]. }
    split; [intros _; exact Hlen|].
    split; [intros Hc; exfalso; exact (Hc HD)|].
    split.
    { rewrite (sumZ_map_ext _ (fun x => 2 ^ (sd_maxlen sd - depth_of R x))) by (intros x Hx; rewrite Hlen by exact Hx; reflexivity).
      rewrite (g_sum_R (fun _ dd => 2 ^ (sd_maxlen sd - dd))).
      assert (H := g_kraft_R (sd_maxlen sd) ltac:(lia) HD). unfold kz in H. exact H. }
    split; [|exact G14].
    rewrite G13. f_equal. f_equal. apply sumZ_map_ext. intros x Hx. rewrite Hlen by exact Hx.
    destruct (g_depth_S x Hx) as [l [Hl [_ E]]]. rewrite E, Z.min_l by (apply HD; exact Hl). reflexivity.
  - (* overflow: the repair and the reassignment *)
    assert (HnD : ~ (forall l, In l R -> ld l <= sd_maxlen sd)).
    { intros HD. apply Hnz. rewrite G9, (g_noovf_ideep HD). lia. }
    set (c := clampc (sd_maxlen sd) dlist).
    assert (Hbl : w_bl_count w2 = c).
    { apply Znth_eq_ext; [rewrite G11; unfold c; rewrite clampc_len; reflexivity|].
      intros b Hb. rewrite G11 in Hb. rewrite G12 by lia. apply g_clampc. lia. }
    assert (Hdl : Zlength dlist <= 2 ^ sd_maxlen sd /\ Zlength dlist <= 573)
      by (rewrite g_d_len; pose proof g_S_len; lia).
    destruct (clamp_rinv (sd_maxlen sd) 600 dlist HM ltac:(lia) g_d_range g_d_kraft (proj1 Hdl) (proj2 Hdl)
                (g_deep_exists HnD)) as [HI1 Hinv].
    fold c in HI1, Hinv. set (I := kraftc (sd_maxlen sd) c - 2 ^ sd_maxlen sd) in *.
    assert (HI : I = Ideep sd t w) by (unfold I, c; rewrite g_kraftc; lia).
    assert (Hovf : ovf = 2 * I) by (rewrite G9, HI; reflexivity).
    rewrite Hbl, Hovf.
    destruct (repair_correct (sd_maxlen sd) c I HM HI1 Hinv) as [_ [R1 [R2 [R3 [R4 [R5 R6]]]]]].
    assert (Hrepl := repl_model (sd_maxlen sd) dlist I HM eq_refl HI1 Hinv). fold c in Hrepl.
    destruct (repaired_lens (sd_maxlen sd) c I HM HI1 Hinv) as [RL1 [RL2 RL3]].
    set (c' := gen_bitlen_repair (Z.to_nat HEAP_SIZE) (sd_maxlen sd) c (2 * I)) in *.
    rewrite Hrepl in RL1, RL2, RL3.
    assert (Htot : tot (sd_maxlen sd) c = Zlength dlist)
      by (apply (clamp_sums (sd_maxlen sd) dlist HM); intros x Hx; apply g_d_range; exact Hx).
    assert (Hord_len : Zlength order = Zlength dlist) by (unfold dlist; rewrite Zlength_map; reflexivity).
    assert (Hscan : scan (w_heap (w_set_bl_count w2 c')) mc HEAP_SIZE (Z.to_nat (HEAP_SIZE - w_heap_max w - 1)) = order)
      by (simpl; rewrite G3; reflexivity).
    rewrite (reassign_correct mc (w_heap (w_set_bl_count w2 c')) c' t2 (w_opt_len (w_set_bl_count w2 c')) (sd_maxlen sd)
               (Z.to_nat (HEAP_SIZE - w_heap_max w - 1)) HM); [| intros; apply R2; lia
               | pose proof (pre_hm _ _ _ _ _ _ _ _ _ Hpre); unfold HEAP_SIZE in *; lia
               | rewrite Hscan, R5, Htot, <- Hord_len, Zlength_correct; lia].
    rewrite Hscan, R5, Htot, <- Hord_len, ZtoNat_Zlength, firstn_all. fold (lens (sd_maxlen sd) c').
    rewrite Hrepl.
    assert (Hlens_len : length order = length (repl (sd_maxlen sd) dlist)).
    { apply Nat2Z.inj. rewrite <- !Zlength_correct. rewrite RL1, Htot. exact Hord_len. }
    destruct (apply_lens_spec order (repl (sd_maxlen sd) dlist) t2 (w_opt_len (w_set_bl_count w2 c')) g_order_nodup Hlens_len)
      as [A1 [A2 [A3 [A4 A5]]]].
    { intros m Hm. apply (Permutation_in _ g_order_perm) in Hm. destruct g_S as [_ [_ Hr]]. specialize (Hr m Hm).
      rewrite G2. unfold elems in Hr. lia. }
    { intros l Hl. specialize (RL2 l Hl). lia. }
    { simpl. unfold u64 in G13. rewrite G13. apply Z.mod_pos_bound. lia. }
    destruct (apply_lens order (repl (sd_maxlen sd) dlist) t2 (w_opt_len (w_set_bl_count w2 c'))) as [t3 opt3].
    cbn [fst snd] in A1, A2, A3, A4, A5.
    assert (Hmap : map (fun x => Znth x (dl t3)) order = repl (sd_maxlen sd) dlist).
    { apply Znth_eq_ext; [rewrite Zlength_map, !Zlength_correct, Hlens_len; reflexivity|].
      intros k Hk. rewrite Zlength_map in Hk. rewrite Znth_map by exact Hk. apply A3. exact Hk. }
    assert (Hin : forall x, In x S -> 1 <= Znth x (dl t3) <= sd_maxlen sd).
    { intros x Hx. apply (Permutation_in _ (Permutation_sym g_order_perm)) in Hx.
      apply RL2. rewrite <- Hmap. apply in_map_iff. exists x. split; auto. }
    split; [rewrite A1; exact G1|]. split; [rewrite A2; exact G2|].
    split; [simpl; exact G3|]. split; [simpl; exact G4|]. split; [simpl; exact G6|]. split; [simpl; exact R1|].
    split.
    { intros c0 Hc0 HcS. rewrite A4; [apply G8; auto|]. intros Hc. apply HcS. apply (Permutation_in _ g_order_perm). exact Hc. }
    split; [exact Hin|].
    split; [intros HD; exfalso; exact (HnD HD)|].
    split; [intros _ k Hk; apply A3; exact Hk|].
    split.
    { rewrite <- (g_sum_order (fun x => 2 ^ (sd_maxlen sd - Znth x (dl t3)))).
      rewrite <- (map_map (fun x => Znth x (dl t3)) (fun l => 2 ^ (sd_maxlen sd - l))), Hmap.
      rewrite <- sumz_sumZ. exact RL3. }
    split; [|simpl; exact G14].
    simpl. rewrite A5. change (w_opt_len (w_set_bl_count w2 c')) with (w_opt_len w2).
    rewrite <- Hmap, dsum_map. rewrite G13, u64_u64_add. f_equal.
    rewrite (g_sum_order (fun m => (Znth m (dl t3) - Znth m (dl t2)) * Znth m (fc t2))).
    rewrite <- Z.add_assoc, <- sumZ_map_add. f_equal. apply sumZ_map_ext. intros x Hx. rewrite G1, G7 by exact Hx. lia.
Qed.

End Gen.

(** ** The theorem *)

Lemma huff_single : forall x f R, huff [[(x, f, 0)]] R -> R = [(x, f, 0)].
Proof.
  intros x f R H. inversion H as [I|P a b rest R' Hp _ _ _]; subst; [reflexivity|].
  apply Permutation_length in Hp. simpl in Hp. lia.
Qed.

Theorem build_tree_correct : build_tree_statement.
Proof.
  intros sd t w HR. destruct HR as [[Hel [HM Hpow]] [HTS HTS2] [Hh [Hd [Hol Hsl]]] Hfr [Hfc0 Hsum] [Hxb Hst]].
  rewrite build_tree_eq.
  assert (BP := bt_pre_spec sd t w Hel HTS HTS2 Hh Hd Hol Hsl Hfc0 Hsum).
  assert (FR := bt_pre_fc sd t w Hfr).
  destruct (bt_pre sd t w) as [[t1 w1] mc] eqn:Ebp.
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
  assert (G := g_genbitlen sd t w S F R t1 w1 mc Hpo HM Hel Hdlen Hxb1 Hst1 Hfc1 Hopt1 Hstl1 Hpow).
  destruct (gen_bitlen sd mc t1 w1) as [t3 w3] eqn:Egb.
  destruct G as [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 [G9 [G10 [G11 [G12 G13]]]]]]]]]]]].
  assert (HSr := g_S sd t w S F R t1 w1 mc Hpo). destruct HSr as [HSe [HSnd HSr]].
  assert (Hmc := g_mc sd t w S F R t1 w1 mc Hpo).
  assert (Hmclt := g_mc_lt sd t w S F R t1 w1 mc Hpo).
  assert (Hlens : forall i, 0 <= i <= mc -> Znth i (dl t3) <> 0 -> 1 <= Znth i (dl t3) <= 15).
  { intros i Hi Hnz. destruct (in_dec Z.eq_dec i S) as [HiS|HiS]; [specialize (G8 i HiS); lia|].
    exfalso. apply Hnz. apply G7; [lia|exact HiS]. }
  assert (Hmc0 : 0 <= mc) by (apply (HSr mc); apply Hmc).
  destruct (gen_codes_spec t3 mc (w_bl_count w3) ltac:(unfold HEAP_SIZE; lia) Hlens) as [C1 [C2 [C3 C4]]].
  set (t4 := gen_codes t3 mc (w_bl_count w3)) in *.
  assert (Hfq : forall x, In x S -> Znth x (fc t1) = fq t F x)
    by (intros x Hx; rewrite (po_fc _ _ _ _ _ _ _ _ _ Hpo x Hx); reflexivity).
  exists S, F, (order w1 mc), R.
  destruct (po_S _ _ _ _ _ _ _ _ _ Hpo) as [PS1 [PS2 [PS3 [PS4 [PS5 PS6]]]]].
  constructor.
  - split; [exact PS1|]. split; [exact PS2|]. split; [exact PS3|]. split; [exact PS4|]. split; [exact PS5|].
    split; [exact PS6|].
    (* at least two leaves: every leaf of R is at depth >= 1 *)
    destruct S as [|x [|y S']] eqn:ES.
    + destruct Hmc as [[] _].
    + exfalso. assert (Hh1 := po_huff _ _ _ _ _ _ _ _ _ Hpo). simpl in Hh1. apply huff_single in Hh1.
      destruct (po_depth _ _ _ _ _ _ _ _ _ Hpo (x, Znth x (fc t1), 0)) as [Hd1 _]; [rewrite Hh1; left; reflexivity|].
      unfold ld in Hd1. simpl in Hd1. lia.
    + rewrite !Zlength_cons. pose proof (Zlength_nonneg S'). lia.
  - exact Hmc.
  - replace (map (fun x => [(x, fq t F x, 0)]) S) with (P0 S (fun x => Znth x (fc t1))).
    + exact (po_huff _ _ _ _ _ _ _ _ _ Hpo).
    + unfold P0. apply map_ext_in. intros x Hx. rewrite Hfq by exact Hx. reflexivity.
  - split; [exact (g_order_perm sd t w S F R t1 w1 mc Hpo HM)|].
    intros i j Hij Hj. assert (H := g_order_sorted sd t w S F R t1 w1 mc Hpo HM i j Hij Hj).
    assert (Hp := g_order_perm sd t w S F R t1 w1 mc Hpo HM).
    rewrite <- !Hfq; [exact H| |]; apply (Permutation_in _ Hp); apply Znth_In; lia.
  - intros c Hc HcS. rewrite C1. apply G7; auto.
  - intros c Hc. rewrite C1. apply G8; exact Hc.
  - intros HD x Hx. rewrite C1. apply G9; auto.
  - intros HnD k Hk. rewrite C1. apply G10; auto.
  - rewrite C1. exact G11.
  - intros x Hx. assert (Hx' := Hx). apply HSr in Hx'.
    apply C4; [assert (x <= mc) by (apply Hmc; exact Hx); lia| |].
    + specialize (G8 x Hx). lia.
    + rewrite G1. rewrite Hfl1. rewrite HTS. lia.
  - rewrite C1, G12, (po_opt _ _ _ _ _ _ _ _ _ Hpo), u64_u64_add. f_equal.
    f_equal. apply sumZ_map_ext. intros x Hx. rewrite Hfq by exact Hx. reflexivity.
  - rewrite G13, (po_static _ _ _ _ _ _ _ _ _ Hpo). destruct (sd_stree sd) as [st|]; [|reflexivity].
    rewrite u64_u64_add. f_equal. f_equal. apply sumZ_map_ext. intros x Hx. rewrite Hfq by exact Hx. reflexivity.
  - split; [rewrite C2, G1; exact Hfl1|]. split; [rewrite C1, G2; lia|].
    split; [rewrite G3; exact (po_heap _ _ _ _ _ _ _ _ _ Hpo)|]. split; [rewrite G5; exact PL3|]. exact G6.
Qed.
