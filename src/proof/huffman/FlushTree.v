(** * Lemma (i): facts about one tree built by build_tree (from BtSpec.bt_facts) *)

From Coq Require Import ZArith List Lia Bool Permutation.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap
               Zlib.proof.huffman.Bits Zlib.proof.huffman.BuildPre Zlib.proof.huffman.HuffFib2
               Zlib.proof.huffman.BtSpec Zlib.proof.huffman.Repair.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Generic list sums *)

Lemma sumZ_map_ext' : forall {A} (f g : A -> Z) l, (forall x, In x l -> f x = g x) -> sumZ (map f l) = sumZ (map g l).
Proof. intros. f_equal. apply map_ext_in. auto. Qed.

Lemma sumZ_map_perm : forall {A} (f : A -> Z) l1 l2, Permutation l1 l2 -> sumZ (map f l1) = sumZ (map f l2).
Proof. intros. apply sumZ_perm, Permutation_map; auto. Qed.

Lemma sumZ_map_add' : forall {A} (f g : A -> Z) l, sumZ (map (fun x => f x + g x) l) = sumZ (map f l) + sumZ (map g l).
Proof. intros A f g l. induction l as [|a l IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma sumZ_map_scal' : forall {A} (c : Z) (f : A -> Z) l, sumZ (map (fun x => c * f x) l) = c * sumZ (map f l).
Proof. intros A c f l. induction l as [|a l IH]; simpl; [lia|]. rewrite IH. lia. Qed.

(** A sum over [0 .. n-1] of a function vanishing off a duplicate-free list [S] inside the range = the sum over [S]. *)
Lemma zseq_sum_support : forall (S : list Z) (g : Z -> Z) n, NoDup S -> (forall x, In x S -> 0 <= x < n) ->
  (forall x, 0 <= x < n -> ~ In x S -> g x = 0) ->
  sumZ (map g (zseq 0 (Z.to_nat n))) = sumZ (map g S).
Proof.
  intros S g n Hnd Hr Hz.
  set (Z0 := zseq 0 (Z.to_nat n)).
  assert (Hsplit : sumZ (map g Z0) = sumZ (map g (filter (fun x => if in_dec Z.eq_dec x S then true else false) Z0)) +
                                      sumZ (map g (filter (fun x => if in_dec Z.eq_dec x S then false else true) Z0))).
  { clear. induction Z0 as [|a l IH]; simpl; [reflexivity|].
    destruct (in_dec Z.eq_dec a S); simpl; rewrite IH; lia. }
  assert (Hzero : sumZ (map g (filter (fun x => if in_dec Z.eq_dec x S then false else true) Z0)) = 0).
  { assert (G : forall l, (forall x, In x l -> 0 <= x < n) ->
              sumZ (map g (filter (fun x => if in_dec Z.eq_dec x S then false else true) l)) = 0).
    { induction l as [|a l IH]; intros Hl; simpl; [reflexivity|].
      destruct (in_dec Z.eq_dec a S) as [Ha|Ha]; simpl.
      - apply IH; intros; apply Hl; right; auto.
      - rewrite Hz by (auto; apply Hl; left; auto). rewrite IH by (intros; apply Hl; right; auto). lia. }
    apply G. intros x Hx. unfold Z0 in Hx. apply in_zseq in Hx. lia. }
  rewrite Hsplit, Hzero, Z.add_0_r. apply sumZ_map_perm.
  apply NoDup_Permutation.
  - apply NoDup_filter. apply zseq_nodup.
  - exact Hnd.
  - intros x. rewrite filter_In. split.
    + intros [_ Hx]. destruct (in_dec Z.eq_dec x S); [auto|discriminate].
    + intros Hx. split; [unfold Z0; apply in_zseq; specialize (Hr x Hx); lia|].
      destruct (in_dec Z.eq_dec x S); [reflexivity|contradiction].
Qed.

(** ** Lists aligned with a duplicate-free order *)

Fixpoint idx (x : Z) (l : list Z) : nat := match l with [] => O | y :: r => if y =? x then O else S (idx x r) end.

Lemma sumz_sumZ : forall l, sumz l = sumZ l.
Proof. induction l; simpl; auto. Qed.

Lemma nth_Znth0 : forall (l : list Z) k, nth k l 0 = Znth (Z.of_nat k) l.
Proof. intros. unfold Znth. destruct (Z_lt_dec (Z.of_nat k) 0); [lia|]. rewrite Nat2Z.id. reflexivity. Qed.

Lemma idx_nth : forall l k, NoDup l -> (k < length l)%nat -> idx (nth k l 0) l = k.
Proof.
  induction l as [|y r IH]; intros k Hnd Hk; [simpl in Hk; lia|].
  inversion Hnd as [|? ? Hy Hr]; subst. destruct k as [|k]; simpl; [rewrite Z.eqb_refl; reflexivity|].
  destruct (Z.eqb_spec y (nth k r 0)) as [E|E].
  - exfalso. apply Hy. rewrite E. apply nth_In. simpl in Hk. lia.
  - f_equal. apply IH; auto. simpl in Hk. lia.
Qed.

Lemma idx_lt : forall l x, In x l -> (idx x l < length l)%nat.
Proof.
  induction l as [|y r IH]; intros x Hx; [destruct Hx|]. simpl.
  destruct (Z.eqb_spec y x); [lia|]. destruct Hx as [->|Hx]; [congruence|]. specialize (IH x Hx). lia.
Qed.

Lemma dotn_order : forall (order e : list Z) (g : Z -> Z), NoDup order -> length e = length order ->
  dotn (length order) (map g order) e = sumZ (map (fun x => g x * nth (idx x order) e 0) order).
Proof.
  induction order as [|y r IH]; intros e g Hnd He; [reflexivity|].
  destruct e as [|z e']; [simpl in He; lia|]. inversion Hnd as [|? ? Hy Hr]; subst.
  simpl length. unfold dotn. rewrite sumk_shift. cbn [map nth sumZ idx]. rewrite Z.eqb_refl.
  fold (dotn (length r) (map g r) e'). rewrite IH by (auto; simpl in He; lia). f_equal.
  apply sumZ_map_ext'. intros x Hx. destruct (Z.eqb_spec y x) as [E|E]; [subst; contradiction|]. reflexivity.
Qed.

Lemma nth_map_order : forall (order : list Z) (g : Z -> Z) x, NoDup order -> In x order ->
  nth (idx x order) (map g order) 0 = g x.
Proof.
  induction order as [|y r IH]; intros g x Hnd Hx; [destruct Hx|]. inversion Hnd as [|? ? Hy Hr]; subst.
  simpl. destruct (Z.eqb_spec y x) as [E|E]; [subst; reflexivity|]. destruct Hx as [->|Hx]; [congruence|]. auto.
Qed.

Lemma combine_sum : forall (order L : list Z) (g h : Z -> Z), length L = length order ->
  (forall k, (k < length order)%nat -> h (nth k order 0) = nth k L 0) ->
  sumz (map (fun p => fst p * snd p) (combine (map g order) L)) = sumZ (map (fun x => g x * h x) order).
Proof.
  induction order as [|y r IH]; intros [|z L] g h HL Hk; simpl in HL; try lia; [reflexivity|].
  cbn [map combine sumz sumZ fst snd]. rewrite (IH L g h); [| lia |].
  - f_equal. f_equal. symmetry. apply (Hk O). simpl; lia.
  - intros k Hk'. apply (Hk (S k)). simpl; lia.
Qed.

Lemma sumZ_indicator2 : forall (S : list Z) a c, NoDup S -> In a S ->
  sumZ (map (fun x => if x =? a then c else 0) S) = c.
Proof.
  induction S as [|y r IH]; intros a c Hnd Ha; [destruct Ha|]. inversion Hnd as [|? ? Hy Hr]; subst. simpl.
  destruct Ha as [->|Ha].
  - rewrite Z.eqb_refl. rewrite (sumZ_map_ext' _ (fun _ => 0)).
    + clear. induction r; simpl; lia.
    + intros x Hx. destruct (Z.eqb_spec x a); [subst; contradiction|reflexivity].
  - destruct (Z.eqb_spec y a); [subst; contradiction|]. rewrite IH; auto.
Qed.

Lemma aligned_sum : forall (ord e : list Z) (phi : Z -> Z), NoDup ord -> length e = length ord ->
  sumZ (map (fun x => phi (nth (idx x ord) e 0)) ord) = sumZ (map phi e).
Proof.
  induction ord as [|y r IH]; intros e phi Hnd He; [destruct e; [reflexivity|simpl in He; lia]|].
  destruct e as [|z e']; [simpl in He; lia|]. inversion Hnd as [|? ? Hy Hr]; subst.
  cbn [map sumZ idx nth]. rewrite Z.eqb_refl. f_equal. rewrite <- (IH e' phi) by (auto; simpl in He; lia).
  apply sumZ_map_ext'. intros x Hx. destruct (Z.eqb_spec y x) as [E|E]; [subst; contradiction|]. reflexivity.
Qed.

(** ** One tree *)

Section Tree.
Variables (sd : stat_desc) (t : tree) (w : work) (S F order : list Z) (R : item) (t' : tree) (mc : Z) (w' : work).
Hypothesis HB : bt_facts sd t w S F order R t' mc w'.
Hypothesis Hfpos : forall x, 0 <= x < sd_elems sd -> 0 <= Znth x (fc t).

Definition fqt := fq t F.
Definition Pt := map (fun x => [(x, fqt x, 0)]) S.

Lemma S_props : NoDup S /\ (forall x, In x S -> 0 <= x < sd_elems sd) /\ 2 <= Zlength S.
Proof. destruct (bt_S _ _ _ _ _ _ _ _ _ _ HB) as [_ [A [B [_ [_ [_ C]]]]]]. auto. Qed.

Lemma fq_pos : forall x, In x S -> 1 <= fqt x.
Proof.
  intros x Hx. destruct (bt_S _ _ _ _ _ _ _ _ _ _ HB) as [ES [_ [Hr _]]].
  unfold fqt, fq. destruct (in_dec Z.eq_dec x F) as [|HF]; [lia|].
  rewrite ES in Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [|contradiction].
  apply in_nzl in Hx. destruct Hx as [Hxr Hne]. specialize (Hfpos x Hxr). lia.
Qed.

Lemma huffR : huff Pt R.
Proof. exact (bt_huff _ _ _ _ _ _ _ _ _ _ HB). Qed.

Lemma leaves_Pt : leaves Pt = map (fun x => (x, fqt x, 0)) S.
Proof. unfold leaves, Pt. generalize S. intros l. induction l as [|a l IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma idf_R : Permutation (map (fun x => (x, fqt x)) S) (map idf R).
Proof.
  assert (H := huff_idf _ _ huffR). rewrite leaves_Pt, map_map in H. exact H.
Qed.

Lemma ids_R : Permutation S (map lid R).
Proof.
  assert (H := Permutation_map fst idf_R). rewrite !map_map in H.
  replace (map (fun x => fst (x, fqt x)) S) with S in H by (rewrite map_ext with (g := fun x => x); [rewrite map_id; auto|reflexivity]).
  exact H.
Qed.

Lemma ids_nodup : NoDup (map lid R).
Proof. eapply Permutation_NoDup; [apply ids_R|]. apply S_props. Qed.

Lemma R_leaf : forall l, In l R -> In (lid l) S /\ lf l = fqt (lid l).
Proof.
  intros l Hl. assert (Hin : In (idf l) (map idf R)) by (apply in_map; auto).
  apply (Permutation_in _ (Permutation_sym idf_R)) in Hin. apply in_map_iff in Hin.
  destruct Hin as [x [Ex Hx]]. unfold idf in Ex. unfold lid, lf. rewrite <- Ex. simpl. auto.
Qed.

Lemma depth_of_leaf : forall l, In l R -> depth_of R (lid l) = ld l.
Proof.
  intros l Hl. unfold depth_of.
  assert (G : forall R', NoDup (map lid R') -> In l R' -> find (fun l' => lid l' =? lid l) R' = Some l).
  { induction R' as [|a R' IH]; intros Hnd Hin; [destruct Hin|].
    simpl in Hnd. inversion Hnd as [|? ? Hna Hnd']; subst. simpl.
    destruct (Z.eqb_spec (lid a) (lid l)) as [E|E].
    - destruct Hin as [<-|Hin]; [reflexivity|]. exfalso. apply Hna. rewrite E. apply in_map. auto.
    - destruct Hin as [<-|Hin]; [congruence|]. apply IH; auto. }
  rewrite (G R ids_nodup Hl). reflexivity.
Qed.

Lemma leaf_of : forall x, In x S -> exists l, In l R /\ lid l = x.
Proof.
  intros x Hx. apply (Permutation_in _ ids_R) in Hx. apply in_map_iff in Hx. destruct Hx as [l [E Hl]].
  exists l. auto.
Qed.

Lemma sum_over_R : forall (g : Z -> Z -> Z -> Z),
  sumZ (map (fun l => g (lid l) (lf l) (ld l)) R) = sumZ (map (fun x => g x (fqt x) (depth_of R x)) S).
Proof.
  intros g. transitivity (sumZ (map (fun x => g x (fqt x) (depth_of R x)) (map lid R))).
  - rewrite map_map. apply sumZ_map_ext'. intros l Hl. destruct (R_leaf l Hl) as [_ E].
    rewrite E, depth_of_leaf by auto. reflexivity.
  - apply sumZ_map_perm. apply Permutation_sym, ids_R.
Qed.

Lemma weight_R : weight R = sumZ (map fqt S).
Proof. unfold weight. apply (sum_over_R (fun x f d => f)). Qed.

Lemma cost_R : cost R = sumZ (map (fun x => fqt x * depth_of R x) S).
Proof. unfold cost. apply (sum_over_R (fun x f d => f * d)). Qed.

Lemma fib_inv_Pt : fib_inv Pt.
Proof.
  assert (E : Pt = map (fun p => singleton (fst p) (snd p)) (map (fun x => (x, fqt x)) S))
    by (unfold Pt, singleton; rewrite map_map; reflexivity).
  rewrite E. apply fib_inv_init. intros p Hp. apply in_map_iff in Hp. destruct Hp as [x [<- Hx]].
  simpl. pose proof (fq_pos x Hx). lia.
Qed.

Lemma R_nonneg : forall l, In l R -> 0 <= ld l /\ 0 <= lf l.
Proof.
  intros l Hl. assert (HR := huff_ind_pool fib_inv fib_inv_perm fib_inv_step Pt R huffR fib_inv_Pt).
  destruct HR as [H0 _]. apply (H0 R (in_eq _ _) l Hl).
Qed.

Lemma R_caps : forall x, In x S -> fqt x * fib (depth_of R x + 1) <= weight R.
Proof.
  intros x Hx. destruct (leaf_of x Hx) as [l [Hl <-]]. destruct (R_leaf l Hl) as [_ E].
  rewrite depth_of_leaf by auto. rewrite <- E. rewrite Z.mul_comm. apply (huff_fib Pt R huffR fib_inv_Pt l Hl).
Qed.

Lemma fib2_Pt : fib2_inv Pt.
Proof. apply fib2_inv_init. intros x Hx. apply fq_pos. auto. Qed.

Lemma R_depth_bound : forall D, 0 <= D -> weight R < fib (D + 2) -> forall x, In x S -> depth_of R x < D.
Proof.
  intros D HD HW x Hx. destruct (leaf_of x Hx) as [l [Hl <-]]. rewrite depth_of_leaf by auto.
  apply (huff_depth_bound Pt R D huffR fib2_Pt HW HD l Hl).
Qed.

Lemma kz_scale : forall (I : item) D1 D2, (forall x, In x I -> 0 <= ld x <= D1) -> D1 <= D2 ->
  kz D2 I = 2 ^ (D2 - D1) * kz D1 I.
Proof.
  intros I D1 D2 HI HD. unfold kz. rewrite <- sumZ_map_scal'. apply sumZ_map_ext'. intros x Hx.
  specialize (HI x Hx). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma R_kraft : forall D, 0 <= D -> (forall x, In x S -> depth_of R x <= D) ->
  sumZ (map (fun x => 2 ^ (D - depth_of R x)) S) = 2 ^ D.
Proof.
  intros D HD Hb.
  assert (Hb' : forall l, In l R -> 0 <= ld l <= D).
  { intros l Hl. destruct (R_leaf l Hl) as [Hs _]. specialize (Hb _ Hs). rewrite depth_of_leaf in Hb by auto.
    destruct (R_nonneg l Hl). lia. }
  set (Dm := fold_right Z.max D (map ld R)).
  assert (HDm : forall l, In l R -> ld l <= Dm).
  { unfold Dm. clear. induction R as [|a R' IH]; intros l Hl; [destruct Hl|].
    simpl. destruct Hl as [<-|Hl]; [lia|]. specialize (IH l Hl). lia. }
  assert (HDDm : D <= Dm) by (unfold Dm; clear; induction R as [|a R' IH]; simpl; lia).
  assert (HK : kz Dm R = 2 ^ Dm).
  { apply (huff_kraft Pt R Dm huffR).
    - intros I HI. unfold Pt in HI. apply in_map_iff in HI. destruct HI as [x [<- _]].
      split; [intros y [<-|[]]; unfold ld; simpl; lia|]. unfold kz, ld; cbn [map sumZ fst snd].
      rewrite Z.sub_0_r, Z.add_0_r. reflexivity.
    - intros l Hl. split; [apply R_nonneg; auto|apply HDm; auto]. }
  rewrite (kz_scale R D Dm Hb' HDDm) in HK.
  assert (HK' : kz D R = 2 ^ D).
  { assert (E : 2 ^ Dm = 2 ^ (Dm - D) * 2 ^ D) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite E in HK. apply Z.mul_cancel_l in HK; [exact HK|]. apply Z.pow_nonzero; lia. }
  unfold kz in HK'. rewrite <- HK'. symmetry. apply (sum_over_R (fun x f d => 2 ^ (D - d))).
Qed.

Lemma R_depth_pos : forall x, In x S -> 1 <= depth_of R x.
Proof.
  intros x Hx.
  destruct (leaf_of x Hx) as [l [Hl <-]]. rewrite depth_of_leaf by auto.
  destruct (R_nonneg l Hl) as [H0 _]. destruct (Z.eq_dec (ld l) 0) as [E|E]; [|lia]. exfalso.
  (* a leaf at depth 0 with another leaf breaks Kraft *)
  set (Dm := fold_right Z.max 0 (map (fun y => depth_of R y) S)).
  assert (HDm : forall y, In y S -> depth_of R y <= Dm).
  { unfold Dm. clear. induction S as [|a S' IH]; intros y Hy; [destruct Hy|].
    simpl. destruct Hy as [<-|Hy]; [lia|]. specialize (IH y Hy). lia. }
  assert (HDm0 : 0 <= Dm) by (unfold Dm; clear; induction S as [|a S' IH]; simpl; lia).
  assert (HK := R_kraft Dm HDm0 HDm).
  destruct S_props as [Hnd [_ Hlen]].
  assert (Hx' : In (lid l) S) by (apply R_leaf; auto).
  apply in_split in Hx'. destruct Hx' as [S1 [S2 ES]]. rewrite ES in HK. rewrite map_app in HK. cbn [map] in HK.
  rewrite sumZ_app in HK. cbn [sumZ] in HK. rewrite depth_of_leaf, E in HK by auto. rewrite Z.sub_0_r in HK.
  assert (Hrest : 0 < sumZ (map (fun x => 2 ^ (Dm - depth_of R x)) S1) + sumZ (map (fun x => 2 ^ (Dm - depth_of R x)) S2)).
  { rewrite ES in Hlen. rewrite Zlength_app, Zlength_cons in Hlen.
    assert (H1 : forall l', (forall y, In y l' -> 0 < 2 ^ (Dm - depth_of R y)) -> l' <> [] ->
               0 < sumZ (map (fun x => 2 ^ (Dm - depth_of R x)) l')).
    { intros l' Hp Hne. destruct l' as [|a l']; [congruence|]. simpl.
      assert (0 <= sumZ (map (fun x => 2 ^ (Dm - depth_of R x)) l')) by (apply sumZ_nonneg; intros y Hy; specialize (Hp y (or_intror Hy)); lia).
      specialize (Hp a (or_introl eq_refl)). lia. }
    assert (Hpos : forall y, In y (S1 ++ S2) -> 0 < 2 ^ (Dm - depth_of R y)).
    { intros y Hy. apply Z.pow_pos_nonneg; [lia|]. assert (In y S) by (rewrite ES; apply in_app_or in Hy; apply in_or_app; destruct Hy; [left|right; right]; auto).
      specialize (HDm y H). lia. }
    destruct S1 as [|a S1]; [destruct S2 as [|b S2]|].
    - rewrite Zlength_nil in Hlen. lia.
    - assert (0 <= sumZ (map (fun x => 2 ^ (Dm - depth_of R x)) [])) by (simpl; lia).
      assert (0 < sumZ (map (fun x => 2 ^ (Dm - depth_of R x)) (b :: S2))) by (apply H1; [intros; apply Hpos; auto|congruence]). lia.
    - assert (0 < sumZ (map (fun x => 2 ^ (Dm - depth_of R x)) (a :: S1))) by (apply H1; [intros; apply Hpos; apply in_or_app; left; auto|congruence]).
      assert (0 <= sumZ (map (fun x => 2 ^ (Dm - depth_of R x)) S2)) by (apply sumZ_nonneg; intros y Hy; specialize (Hpos y ltac:(apply in_or_app; right; auto)); lia).
      lia. }
  lia.
Qed.

(** Optimality against any code with Kraft sum at most 1 on [S]. *)
Lemma R_opt : forall D (e : Z -> Z), (forall x, In x S -> 0 <= e x <= D) ->
  sumZ (map (fun x => 2 ^ (D - e x)) S) <= 2 ^ D ->
  sumZ (map (fun x => fqt x * depth_of R x) S) <= sumZ (map (fun x => fqt x * e x) S).
Proof.
  intros D e He HK. rewrite <- cost_R.
  set (Q := map (fun x => ([(x, fqt x, 0)] : item, e x)) S).
  assert (Hc := huff_opt Pt R huffR D Q).
  assert (E1 : map fst Q = Pt) by (unfold Q, Pt; rewrite map_map; reflexivity).
  assert (E2 : lens_ok D Q) by (intros p Hp; unfold Q in Hp; apply in_map_iff in Hp; destruct Hp as [x [<- Hx]]; simpl; auto).
  assert (E3 : kq D Q <= 2 ^ D) by (unfold kq, Q; rewrite map_map; exact HK).
  assert (E4 : forall I, In I Pt -> 0 <= weight I).
  { intros I HI. unfold Pt in HI. apply in_map_iff in HI. destruct HI as [x [<- Hx]]. unfold weight; simpl.
    unfold lf; simpl. pose proof (fq_pos x Hx). lia. }
  specialize (Hc E1 E2 E3 E4). eapply Z.le_trans; [exact Hc|].
  unfold cq, Q. rewrite map_map. apply Z.eq_le_incl. apply sumZ_map_ext'. intros x _.
  unfold cost, weight; simpl. unfold lf, ld; simpl. lia.
Qed.

(** The lengths of [t'] on [S]. *)
Definition lenx (x : Z) : Z := Znth x (dl t').

Lemma lens_noovf : weight R < fib (sd_maxlen sd + 3) -> forall x, In x S -> lenx x = depth_of R x.
Proof.
  intros HW x Hx. apply (bt_noovf _ _ _ _ _ _ _ _ _ _ HB); auto.
  intros l Hl. destruct (R_leaf l Hl) as [Hs _].
  assert (H := R_depth_bound (sd_maxlen sd + 1) ltac:(destruct (bt_len_in _ _ _ _ _ _ _ _ _ _ HB x Hx); lia)
                 ltac:(replace (sd_maxlen sd + 1 + 2) with (sd_maxlen sd + 3) by lia; exact HW) _ Hs).
  rewrite depth_of_leaf in H by auto. lia.
Qed.

(** The Huffman code costs at most the actual lengths (they satisfy Kraft). *)
Lemma depth_le_len : sumZ (map (fun x => fqt x * depth_of R x) S) <= sumZ (map (fun x => fqt x * lenx x) S).
Proof.
  apply (R_opt (sd_maxlen sd)).
  - intros x Hx. destruct (bt_len_in _ _ _ _ _ _ _ _ _ _ HB x Hx). unfold lenx. lia.
  - unfold lenx. rewrite (bt_kraft _ _ _ _ _ _ _ _ _ _ HB). lia.
Qed.

(** ** The order of the heap scan *)

Lemma order_props : Permutation order S /\ NoDup order /\ length order = length S.
Proof.
  destruct (bt_order _ _ _ _ _ _ _ _ _ _ HB) as [Hp _]. split; [exact Hp|]. split.
  - eapply Permutation_NoDup; [apply Permutation_sym, Hp|apply S_props].
  - apply Permutation_length. exact Hp.
Qed.

Lemma sum_order : forall g : Z -> Z, sumZ (map g order) = sumZ (map g S).
Proof. intros g. apply sumZ_map_perm. apply order_props. Qed.

Lemma in_order : forall x, In x order <-> In x S.
Proof.
  intros x. destruct order_props as [Hp _]. split; intros H; [apply (Permutation_in _ Hp)|apply (Permutation_in _ (Permutation_sym Hp))]; auto.
Qed.



(** Optimality against any length list aligned with the scan order. *)
Lemma opt_list : forall D (e : list Z), length e = length order -> (forall v, In v e -> 0 <= v <= D) ->
  sumz (map (fun v => 2 ^ (D - v)) e) <= 2 ^ D ->
  dotn (length order) (map fqt order) (map (depth_of R) order) <= dotn (length order) (map fqt order) e.
Proof.
  intros D e Hl He HK. destruct order_props as [Hp [Hnd Hlen]].
  rewrite !dotn_order by (rewrite ?length_map; auto).
  rewrite (sumZ_map_ext' (fun x => fqt x * nth (idx x order) (map (depth_of R) order) 0) (fun x => fqt x * depth_of R x))
    by (intros x Hx; rewrite nth_map_order; auto).
  rewrite !sum_order.
  apply (R_opt D (fun x => nth (idx x order) e 0)).
  - intros x Hx. apply He. apply nth_In. rewrite Hl. apply idx_lt. apply in_order; auto.
  - rewrite <- sum_order. rewrite (aligned_sum order e (fun v => 2 ^ (D - v))) by auto.
    rewrite <- sumz_sumZ. exact HK.
Qed.

Lemma depth_le11 : weight R <= 316 -> forall x, In x S -> 1 <= depth_of R x <= 11.
Proof.
  intros HW x Hx. split; [apply R_depth_pos; auto|].
  assert (H := R_depth_bound 12 ltac:(lia) ltac:(change (fib (12 + 2)) with 377; lia) x Hx). lia.
Qed.

Lemma nth_map_in : forall (g : Z -> Z) k, (k < length order)%nat -> nth k (map g order) 0 = g (nth k order 0).
Proof.
  intros g k Hk. rewrite (nth_indep (map g order) 0 (g 0)) by (rewrite length_map; auto). apply map_nth.
Qed.

Lemma nth_order_in : forall k, (k < length order)%nat -> In (nth k order 0) S.
Proof. intros k Hk. apply in_order. apply nth_In. auto. Qed.

(** The bit-length tree: the repaired code costs at most 75 bits more than the Huffman code. *)
Lemma bl_cost : sd_maxlen sd = 7 -> Zlength S <= 15 -> weight R <= 316 ->
  sumZ (map (fun x => fqt x * lenx x) S) <= sumZ (map (fun x => fqt x * depth_of R x) S) + 75.
Proof.
  intros HM HS HW. destruct order_props as [Hp [Hnd Hlen]].
  destruct (Forall_dec (fun l => ld l <= 7) (fun l => Z_le_dec (ld l) 7) R) as [Hno|Hov].
  - rewrite Forall_forall in Hno.
    rewrite (sumZ_map_ext' (fun x => fqt x * lenx x) (fun x => fqt x * depth_of R x)); [lia|].
    intros x Hx. unfold lenx. rewrite (bt_noovf _ _ _ _ _ _ _ _ _ _ HB); auto. rewrite HM. auto.
  - assert (Hov' : ~ (forall l, In l R -> ld l <= sd_maxlen sd)) by (rewrite HM; intros H; apply Hov, Forall_forall, H).
    assert (Hrep := bt_ovf _ _ _ _ _ _ _ _ _ _ HB Hov'). rewrite HM in Hrep.
    set (f := map fqt order). set (d := map (depth_of R) order).
    assert (Hlf : length f = length order) by apply length_map.
    assert (Hld : length d = length order) by apply length_map.
    assert (HlenS : (length order <= 15)%nat) by (rewrite Hlen; rewrite Zlength_correct in HS; lia).
    assert (Hdep := depth_le11 HW).
    assert (Hf_nth : forall k, (k < length order)%nat -> nth k f 0 = fqt (nth k order 0)) by (intros; apply nth_map_in; auto).
    assert (Hd_nth : forall k, (k < length order)%nat -> nth k d 0 = depth_of R (nth k order 0)) by (intros; apply nth_map_in; auto).
    destruct (bl_repair_cost_opt' f d (weight R) 12) as [HlenL Hcost].
    + lia.
    + lia.
    + intros k Hk. rewrite !Hf_nth by lia. rewrite !nth_Znth0.
      destruct (bt_order _ _ _ _ _ _ _ _ _ _ HB) as [_ Ho]. apply Ho; [lia|]. rewrite Zlength_correct. lia.
    + intros i j Hi Hj Hfij. rewrite Hf_nth in Hfij by lia. rewrite Hf_nth in Hfij by lia. rewrite !Hd_nth by lia.
      set (oi := nth i order 0) in *. set (oj := nth j order 0) in *.
      destruct (Z_le_gt_dec (depth_of R oj) (depth_of R oi)) as [|Hgt]; [auto|exfalso].
      assert (Hij : oi <> oj) by (intros E; rewrite E in Hfij; lia).
      assert (Hoi : In oi S) by (apply nth_order_in; lia). assert (Hoj : In oj S) by (apply nth_order_in; lia).
      set (di := depth_of R oi). set (dj := depth_of R oj).
      set (e' := fun x => if x =? oi then dj else if x =? oj then di else depth_of R x).
      assert (Hopt := opt_list 12 (map e' order) ltac:(rewrite length_map; auto)).
      assert (He'r : forall x, In x S -> 1 <= e' x <= 11).
      { intros x Hx. unfold e'. destruct (x =? oi); [apply Hdep; auto|]. destruct (x =? oj); apply Hdep; auto. }
      assert (Hpt : forall (g : Z -> Z) x, In x S -> g (e' x) =
                g (depth_of R x) + (if x =? oi then g dj - g di else 0) + (if x =? oj then g di - g dj else 0)).
      { intros g x Hx. unfold e'. destruct (Z.eqb_spec x oi) as [E1|E1]; destruct (Z.eqb_spec x oj) as [E2|E2].
        - exfalso. apply Hij. congruence.
        - subst x. fold di. lia.
        - subst x. fold dj. lia.
        - lia. }
      assert (Hsplit : forall g : Z -> Z, sumZ (map (fun x => g (e' x)) S) = sumZ (map (fun x => g (depth_of R x)) S)).
      { intros g. rewrite (sumZ_map_ext' (fun x => g (e' x))
          (fun x => g (depth_of R x) + (if x =? oi then g dj - g di else 0) + (if x =? oj then g di - g dj else 0)))
          by (intros; apply Hpt; auto).
        rewrite !sumZ_map_add'. rewrite !sumZ_indicator2 by (auto; apply S_props). lia. }
      specialize (Hopt ltac:(intros v Hv; apply in_map_iff in Hv; destruct Hv as [x [<- Hx]];
                              specialize (He'r x ltac:(apply in_order; auto)); lia)).
      assert (HK : sumz (map (fun v => 2 ^ (12 - v)) (map e' order)) <= 2 ^ 12).
      { rewrite map_map, sumz_sumZ, sum_order. rewrite (Hsplit (fun v => 2 ^ (12 - v))).
        rewrite R_kraft; [lia|lia|intros y Hy; specialize (Hdep y Hy); lia]. }
      specialize (Hopt HK).
      rewrite !dotn_order in Hopt by (rewrite ?length_map; auto).
      rewrite (sumZ_map_ext' (fun x => fqt x * nth (idx x order) (map (depth_of R) order) 0) (fun x => fqt x * depth_of R x)) in Hopt
        by (intros x Hx; rewrite nth_map_order; auto).
      rewrite (sumZ_map_ext' (fun x => fqt x * nth (idx x order) (map e' order) 0) (fun x => fqt x * e' x)) in Hopt
        by (intros x Hx; rewrite nth_map_order; auto).
      rewrite !sum_order in Hopt.
      assert (Hd2 : sumZ (map (fun x => fqt x * e' x) S) = sumZ (map (fun x => fqt x * depth_of R x) S) +
                    fqt oi * (dj - di) + fqt oj * (di - dj)).
      { rewrite (sumZ_map_ext' (fun x => fqt x * e' x)
          (fun x => fqt x * depth_of R x + (if x =? oi then fqt oi * (dj - di) else 0) + (if x =? oj then fqt oj * (di - dj) else 0))).
        - rewrite !sumZ_map_add'. rewrite !sumZ_indicator2 by (auto; apply S_props). lia.
        - intros x Hx. unfold e'. destruct (Z.eqb_spec x oi) as [E1|E1]; destruct (Z.eqb_spec x oj) as [E2|E2].
          + exfalso. apply Hij. congruence.
          + subst x. fold di. lia.
          + subst x. fold dj. lia.
          + lia. }
      rewrite Hd2 in Hopt. fold di dj in Hgt. nia.
    + intros x Hx. unfold d in Hx. apply in_map_iff in Hx. destruct Hx as [y [<- Hy]].
      specialize (Hdep y ltac:(apply in_order; auto)). lia.
    + unfold d. rewrite map_map, sumz_sumZ, sum_order. apply R_kraft; [lia|]. intros y Hy; specialize (Hdep y Hy); lia.
    + unfold f. rewrite sumz_sumZ, sum_order. symmetry. apply weight_R.
    + exact HW.
    + intros k Hk. rewrite Hf_nth, Hd_nth by lia. assert (Hk' := nth_order_in k ltac:(lia)).
      split; [apply fq_pos; auto|]. rewrite Z.mul_comm. apply R_caps; auto.
    + intros e He1 He2 He3. rewrite Hld in He1. unfold f, d. rewrite length_map. apply (opt_list 12 e); auto.
    + unfold f in Hcost. rewrite (combine_sum order (repl 7 d) fqt lenx) in Hcost.
      * rewrite (combine_sum order d fqt (depth_of R)) in Hcost; [|auto|intros k Hk; symmetry; apply Hd_nth; auto].
        rewrite !sum_order in Hcost. exact Hcost.
      * lia.
      * intros k Hk. unfold lenx. rewrite nth_Znth0, nth_Znth0.
        apply Hrep. rewrite Zlength_correct. lia.
Qed.



End Tree.
