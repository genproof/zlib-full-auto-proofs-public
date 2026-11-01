(** * One tree of max length 15 (literal/length or distance): Huffman depths against the repaired lengths

    From [bt_facts] of a tree with max length 15: a depth function [dd] on the symbol set S (the Huffman depths of
    [R], rearranged among leaves of equal frequency so that they are sorted along the heap scan) with Kraft
    equality, the Fibonacci caps, the Huffman cost (optimal against every code with Kraft sum <= 1), and the
    repair overhead of the actual lengths [dl t'] over [dd] bounded by [RepairBound.repair15_bound].  Without
    overflow (W < fib 18) [dd] is the actual lengths. *)

From Coq Require Import ZArith List Lia Bool Permutation.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap
               Zlib.proof.huffman.Bits Zlib.proof.huffman.BuildPre Zlib.proof.huffman.HuffFib2
               Zlib.proof.huffman.BtSpec Zlib.proof.huffman.Repair Zlib.proof.huffman.FlushTree
               Zlib.proof.huffman.RepairBound.
Import ListNotations.
Local Open Scope Z_scope.

Definition tree_dd_statement : Prop := forall sd t w S F order R t' mc w',
  bt_facts sd t w S F order R t' mc w' ->
  (forall x, 0 <= x < sd_elems sd -> 0 <= Znth x (fc t)) ->
  sd_maxlen sd = 15 -> Zlength S <= 286 ->
  HuffAbs.sumZ (map (fq t F) S) < 75025 ->
  exists dd : Z -> Z,
    (forall x, In x S -> 1 <= dd x <= 22) /\
    HuffAbs.sumZ (map (fun x => 2 ^ (30 - dd x)) S) = 2 ^ 30 /\
    (forall x, In x S -> fq t F x * fib (dd x + 1) <= HuffAbs.sumZ (map (fq t F) S)) /\
    (forall e : Z -> Z, (forall x, In x S -> 0 <= e x <= 30) ->
       HuffAbs.sumZ (map (fun x => 2 ^ (30 - e x)) S) <= 2 ^ 30 ->
       HuffAbs.sumZ (map (fun x => fq t F x * dd x) S) <= HuffAbs.sumZ (map (fun x => fq t F x * e x) S)) /\
    HuffAbs.sumZ (map (fun x => fq t F x * dd x) S) <= HuffAbs.sumZ (map (fun x => fq t F x * Znth x (dl t')) S) /\
    540 * HuffAbs.sumZ (map (fun x => fq t F x * Z.max 0 (Znth x (dl t') - dd x)) S)
      <= 2 * Zlength S * HuffAbs.sumZ (map (fq t F) S) /\
    (HuffAbs.sumZ (map (fq t F) S) < fib 18 -> forall x, In x S -> dd x = Znth x (dl t')).


(** ** Helpers *)

Lemma nth_idx : forall (l : list Z) x, In x l -> nth (idx x l) l 0 = x.
Proof.
  induction l as [|y r IH]; intros x Hx; [destruct Hx|]. simpl.
  destruct (Z.eqb_spec y x) as [E|E]; [auto|]. destruct Hx as [->|Hx]; [congruence|]. auto.
Qed.

Lemma nth_map0 : forall (l : list Z) (g : Z -> Z) k, (k < length l)%nat -> nth k (map g l) 0 = g (nth k l 0).
Proof.
  intros l g k Hk. rewrite (nth_indep (map g l) 0 (g 0)) by (rewrite length_map; auto). apply map_nth.
Qed.

Lemma aligned_comb : forall (ord a e : list Z) (g : Z -> Z -> Z), NoDup ord -> length a = length ord ->
  length e = length ord ->
  sumZ (map (fun x => g (nth (idx x ord) a 0) (nth (idx x ord) e 0)) ord) =
  sumz (map (fun p => g (fst p) (snd p)) (combine a e)).
Proof.
  induction ord as [|y r IH]; intros a e g Hnd Ha He.
  - destruct a; [reflexivity|simpl in Ha; lia].
  - destruct a as [|u a']; [simpl in Ha; lia|]. destruct e as [|v e']; [simpl in He; lia|].
    inversion Hnd as [|? ? Hy Hr]; subst.
    cbn [map sumZ idx nth combine sumz fst snd]. rewrite Z.eqb_refl. f_equal.
    rewrite <- (IH a' e' g) by (auto; simpl in *; lia).
    apply sumZ_map_ext'. intros x Hx. destruct (Z.eqb_spec y x) as [E|E]; [subst; contradiction|]. reflexivity.
Qed.

Lemma aligned_dpl : forall (ord a b c : list Z), NoDup ord -> length a = length ord ->
  length b = length ord -> length c = length ord ->
  sumZ (map (fun x => nth (idx x ord) a 0 * Z.max 0 (nth (idx x ord) b 0 - nth (idx x ord) c 0)) ord) =
  dpl a b c.
Proof.
  induction ord as [|y r IH]; intros a b c Hnd Ha Hb Hc.
  - destruct a; [reflexivity|simpl in Ha; lia].
  - destruct a as [|u a']; [simpl in Ha; lia|]. destruct b as [|v b']; [simpl in Hb; lia|].
    destruct c as [|z c']; [simpl in Hc; lia|].
    inversion Hnd as [|? ? Hy Hr]; subst.
    cbn [map sumZ idx nth dpl]. rewrite Z.eqb_refl. f_equal.
    rewrite <- (IH a' b' c') by (auto; simpl in *; lia).
    apply sumZ_map_ext'. intros x Hx. destruct (Z.eqb_spec y x) as [E|E]; [subst; contradiction|]. reflexivity.
Qed.

Lemma dep_range : forall (sd : stat_desc) (t : tree) (w : work) (S F order : list Z) (R : item) (t' : tree) (mc : Z) (w' : work),
  bt_facts sd t w S F order R t' mc w' -> (forall x, 0 <= x < sd_elems sd -> 0 <= Znth x (fc t)) ->
  sumZ (map (fqt t F) S) < 75025 -> forall x, In x S -> 1 <= depth_of R x <= 22.
Proof.
  intros sd t w S F order R t' mc w' HB Hfpos HW x Hx. split; [apply (R_depth_pos _ _ _ _ _ _ _ _ _ _ HB Hfpos); auto|].
  assert (H := R_depth_bound _ _ _ _ _ _ _ _ _ _ HB Hfpos 23 ltac:(lia)
                 ltac:(rewrite (weight_R _ _ _ _ _ _ _ _ _ _ HB); change (fib (23 + 2)) with 75025; lia) x Hx).
  lia.
Qed.

(** The exchange property of the Huffman depths. *)
Lemma exch : forall (sd : stat_desc) (t : tree) (w : work) (S F order : list Z) (R : item) (t' : tree) (mc : Z) (w' : work),
  bt_facts sd t w S F order R t' mc w' -> (forall x, 0 <= x < sd_elems sd -> 0 <= Znth x (fc t)) ->
  sumZ (map (fqt t F) S) < 75025 -> forall oi oj, In oi S -> In oj S -> fqt t F oi < fqt t F oj -> depth_of R oj <= depth_of R oi.
Proof.
  intros sd t w S F order R t' mc w' HB Hfpos HW oi oj Hoi Hoj Hfij.
  assert (dep_range := dep_range _ _ _ _ _ _ _ _ _ _ HB Hfpos HW).
  destruct (Z_le_gt_dec (depth_of R oj) (depth_of R oi)) as [|Hgt]; [auto|exfalso].
  assert (Hij : oi <> oj) by (intros E; rewrite E in Hfij; lia).
  destruct (S_props _ _ _ _ _ _ _ _ _ _ HB) as [HndS _].
  set (di := depth_of R oi) in *. set (dj := depth_of R oj) in *.
  set (e' := fun x => if x =? oi then dj else if x =? oj then di else depth_of R x).
  assert (He'r : forall x, In x S -> 1 <= e' x <= 22).
  { intros x Hx. unfold e'. destruct (x =? oi); [apply dep_range; auto|]. destruct (x =? oj); apply dep_range; auto. }
  assert (Hsplit : forall g : Z -> Z, sumZ (map (fun x => g (e' x)) S) = sumZ (map (fun x => g (depth_of R x)) S)).
  { intros g. rewrite (sumZ_map_ext' (fun x => g (e' x))
      (fun x => g (depth_of R x) + (if x =? oi then g dj - g di else 0) + (if x =? oj then g di - g dj else 0))).
    - rewrite !sumZ_map_add'. rewrite !sumZ_indicator2 by auto. lia.
    - intros x Hx. unfold e'. destruct (Z.eqb_spec x oi) as [E1|E1]; destruct (Z.eqb_spec x oj) as [E2|E2].
      + exfalso. apply Hij. congruence.
      + subst x. fold di. lia.
      + subst x. fold dj. lia.
      + lia. }
  assert (Hopt := R_opt _ _ _ _ _ _ _ _ _ _ HB Hfpos 30 e'
                    ltac:(intros x Hx; specialize (He'r x Hx); lia)).
  rewrite (Hsplit (fun v => 2 ^ (30 - v))) in Hopt.
  rewrite (R_kraft _ _ _ _ _ _ _ _ _ _ HB Hfpos 30) in Hopt
    by (lia || (intros y Hy; specialize (dep_range y Hy); lia)).
  specialize (Hopt ltac:(lia)).
  assert (Hd2 : sumZ (map (fun x => fqt t F x * e' x) S) = sumZ (map (fun x => fqt t F x * depth_of R x) S) +
                fqt t F oi * (dj - di) + fqt t F oj * (di - dj)).
  { rewrite (sumZ_map_ext' (fun x => fqt t F x * e' x)
      (fun x => fqt t F x * depth_of R x + (if x =? oi then fqt t F oi * (dj - di) else 0) +
                (if x =? oj then fqt t F oj * (di - dj) else 0))).
    - rewrite !sumZ_map_add'. rewrite !sumZ_indicator2 by auto. lia.
    - intros x Hx. unfold e'. destruct (Z.eqb_spec x oi) as [E1|E1]; destruct (Z.eqb_spec x oj) as [E2|E2].
      + exfalso. apply Hij. congruence.
      + subst x. fold di. lia.
      + subst x. fold dj. lia.
      + lia. }
  rewrite Hd2 in Hopt. nia.
Qed.


Theorem tree_dd : repair15_statement -> tree_dd_statement.
Proof.
  intros Hrep sd t w S F order R t' mc w' HB Hfpos HM HS HW.
  change (fq t F) with (fqt t F) in *.
  set (W := sumZ (map (fqt t F) S)) in *.
  destruct (S_props _ _ _ _ _ _ _ _ _ _ HB) as [HndS [HrS HlS]].
  destruct (order_props _ _ _ _ _ _ _ _ _ _ HB) as [Hpo [Hndo Hlo]].
  assert (Hdr := dep_range _ _ _ _ _ _ _ _ _ _ HB Hfpos HW).
  assert (Hcap : forall x, In x S -> fqt t F x * fib (depth_of R x + 1) <= W)
    by (intros x Hx; unfold W; rewrite <- (weight_R _ _ _ _ _ _ _ _ _ _ HB); apply (R_caps _ _ _ _ _ _ _ _ _ _ HB Hfpos); auto).
  assert (Hkr : sumZ (map (fun x => 2 ^ (30 - depth_of R x)) S) = 2 ^ 30)
    by (apply (R_kraft _ _ _ _ _ _ _ _ _ _ HB Hfpos); [lia|intros y Hy; specialize (Hdr y Hy); lia]).
  assert (Hopt := R_opt _ _ _ _ _ _ _ _ _ _ HB Hfpos 30).
  assert (Hle := depth_le_len _ _ _ _ _ _ _ _ _ _ HB Hfpos). unfold lenx in Hle.
  assert (Hin_o : forall x, In x order <-> In x S)
    by (intros x; split; intros H; [apply (Permutation_in _ Hpo)|apply (Permutation_in _ (Permutation_sym Hpo))]; auto).
  assert (HW0 : 0 <= W) by (unfold W; apply sumZ_nonneg; intros x Hx;
                             pose proof (fq_pos _ _ _ _ _ _ _ _ _ _ HB Hfpos x Hx); lia).
  destruct (Forall_dec (fun l => ld l <= 15) (fun l => Z_le_dec (ld l) 15) R) as [Hno|Hov].
  - (* no overflow: the depths *)
    rewrite Forall_forall in Hno.
    assert (Hlen : forall x, In x S -> Znth x (dl t') = depth_of R x)
      by (intros x Hx; apply (bt_noovf _ _ _ _ _ _ _ _ _ _ HB); auto; rewrite HM; auto).
    exists (depth_of R). split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros x Hx. specialize (Hdr x Hx). lia.
    + exact Hkr.
    + exact Hcap.
    + intros e He HK. apply Hopt; auto.
    + exact Hle.
    + rewrite (sumZ_map_ext' _ (fun _ => 0)).
      * rewrite sumZ_map_scal' with (c := 0) (f := fun _ => 0) at 1. nia.
      * intros x Hx. rewrite Hlen by auto. rewrite Z.sub_diag. lia.
    + intros _ x Hx. symmetry. auto.
  - (* overflow: the depths rearranged along the scan *)
    assert (Hov' : ~ (forall l, In l R -> ld l <= sd_maxlen sd)) by (rewrite HM; intros H; apply Hov, Forall_forall, H).
    assert (Hrp := bt_ovf _ _ _ _ _ _ _ _ _ _ HB Hov'). rewrite HM in Hrp.
    set (f := map (fqt t F) order). set (d := map (depth_of R) order).
    assert (Hlf : length f = length order) by apply length_map.
    assert (Hld : length d = length order) by apply length_map.
    assert (Hf_nth : forall k, (k < length order)%nat -> nth k f 0 = fqt t F (nth k order 0)) by (intros; apply nth_map0; auto).
    assert (Hd_nth : forall k, (k < length order)%nat -> nth k d 0 = depth_of R (nth k order 0)) by (intros; apply nth_map0; auto).
    assert (Hoin : forall k, (k < length order)%nat -> In (nth k order 0) S) by (intros; apply Hin_o, nth_In; auto).
    destruct (rearrange f d ltac:(lia)) as [d' [Hp [Hso [Hl' Hpc]]]].
    + intros k Hk. rewrite !Hf_nth by lia. rewrite !nth_Znth0.
      destruct (bt_order _ _ _ _ _ _ _ _ _ _ HB) as [_ Ho]. apply Ho; [lia|]. rewrite Zlength_correct. lia.
    + intros i j Hi Hj Hfij. rewrite !Hf_nth in Hfij by lia. rewrite !Hd_nth by lia.
      apply (exch _ _ _ _ _ _ _ _ _ _ HB Hfpos HW); auto; apply Hoin; lia.
    + (* pairs of d' come from pairs of d *)
      assert (Hpair : forall k, (k < length order)%nat -> exists y, In y S /\ fqt t F y = nth k f 0 /\ depth_of R y = nth k d' 0).
      { intros k Hk. assert (Hin2 : In (nth k f 0, nth k d' 0) (combine f d')).
        { rewrite <- combine_nth by lia. apply nth_In. rewrite length_combine. lia. }
        apply (Permutation_in _ (Permutation_sym Hpc)) in Hin2.
        destruct (in_combine_nth f d _ _ ltac:(lia) Hin2) as [i [Hi [Hfi Hdi]]].
        exists (nth i order 0). rewrite <- Hfi, <- Hdi, Hf_nth, Hd_nth by lia. split; auto. apply Hoin; lia. }
      set (dd := fun x => nth (idx x order) d' 0).
      assert (Hidx : forall x, In x S -> (idx x order < length order)%nat) by (intros; apply idx_lt, Hin_o; auto).
      assert (Hfx : forall x, In x S -> nth (idx x order) f 0 = fqt t F x) by (intros; apply nth_map_order; auto; apply Hin_o; auto).
      assert (Hddp : forall x, In x S -> exists y, In y S /\ fqt t F y = fqt t F x /\ depth_of R y = dd x).
      { intros x Hx. destruct (Hpair _ (Hidx x Hx)) as [y [Hy [E1 E2]]]. exists y. rewrite Hfx in E1 by auto. auto. }
      assert (Hsum : forall g : Z -> Z -> Z,
                sumZ (map (fun x => g (fqt t F x) (dd x)) S) = sumZ (map (fun x => g (fqt t F x) (depth_of R x)) S)).
      { intros g. rewrite <- !(sum_order _ _ _ _ _ _ _ _ _ _ HB).
        rewrite (sumZ_map_ext' (fun x => g (fqt t F x) (dd x)) (fun x => g (nth (idx x order) f 0) (nth (idx x order) d' 0)))
          by (intros x Hx; rewrite Hfx by (apply Hin_o; auto); reflexivity).
        rewrite (sumZ_map_ext' (fun x => g (fqt t F x) (depth_of R x)) (fun x => g (nth (idx x order) f 0) (nth (idx x order) d 0)))
          by (intros x Hx; rewrite Hfx by (apply Hin_o; auto); unfold d; rewrite nth_map_order; auto).
        rewrite !aligned_comb by (auto; lia).
        symmetry. apply sumz_perm, Permutation_map. auto. }
      assert (Hdd_r : forall x, In x S -> 1 <= dd x <= 22)
        by (intros x Hx; destruct (Hddp x Hx) as [y [Hy [_ <-]]]; auto).
      assert (Hd'r : forall v, In v d' -> 1 <= v <= 22).
      { intros v Hv. apply (Permutation_in _ (Permutation_sym Hp)) in Hv. unfold d in Hv.
        apply in_map_iff in Hv. destruct Hv as [y [<- Hy]]. apply Hdr, Hin_o; auto. }
      destruct (Hrep f d' W 30) as [HlR Hbound].
      * lia.
      * rewrite Hl', Hld, Hlo. rewrite Zlength_correct in HS. lia.
      * exact Hso.
      * lia.
      * intros v Hv. specialize (Hd'r v Hv). lia.
      * rewrite <- (sumz_perm _ _ (Permutation_map _ Hp)). unfold d. rewrite map_map, sumz_sumZ.
        rewrite (sum_order _ _ _ _ _ _ _ _ _ _ HB (fun x => 2 ^ (30 - depth_of R x))). exact Hkr.
      * intros k Hk. destruct (Hpair k ltac:(lia)) as [y [Hy [E1 E2]]]. rewrite <- E1, <- E2.
        split; [apply (fq_pos _ _ _ _ _ _ _ _ _ _ HB Hfpos); auto|]. rewrite Z.mul_comm. apply Hcap; auto.
      * exists dd. split; [|split; [|split; [|split; [|split; [|split]]]]].
        -- exact Hdd_r.
        -- rewrite (Hsum (fun _ v => 2 ^ (30 - v))). exact Hkr.
        -- intros x Hx. destruct (Hddp x Hx) as [y [Hy [E1 <-]]]. rewrite <- E1. apply Hcap; auto.
        -- intros e He HK. rewrite (Hsum (fun a v => a * v)). apply Hopt; auto.
        -- rewrite (Hsum (fun a v => a * v)). exact Hle.
        -- assert (Hlx : forall x, In x S -> Znth x (dl t') = nth (idx x order) (repl 15 d') 0).
           { intros x Hx. assert (Hk := Hidx x Hx).
             assert (E := Hrp (Z.of_nat (idx x order)) ltac:(rewrite Zlength_correct; lia)).
             rewrite <- nth_Znth0, nth_idx in E by (apply Hin_o; auto). rewrite E, <- nth_Znth0.
             fold d. rewrite (repl_perm 15 d d' Hp). reflexivity. }
           rewrite <- (sum_order _ _ _ _ _ _ _ _ _ _ HB).
           rewrite (sumZ_map_ext' _ (fun x => nth (idx x order) f 0 *
                      Z.max 0 (nth (idx x order) (repl 15 d') 0 - nth (idx x order) d' 0))).
           ++ rewrite aligned_dpl by (auto; lia). rewrite Zlength_correct, <- Hlo, <- Hld, <- Hl'. exact Hbound.
           ++ intros x Hx. apply Hin_o in Hx. rewrite Hfx, Hlx by auto. reflexivity.
        -- intros HW18. exfalso. apply Hov. rewrite Forall_forall. intros l Hl.
           destruct (leaf_of _ _ _ _ _ _ _ _ _ _ HB (lid l)) as [l0 [Hl0 E]].
           ++ apply (R_leaf _ _ _ _ _ _ _ _ _ _ HB l Hl).
           ++ rewrite <- (depth_of_leaf _ _ _ _ _ _ _ _ _ _ HB l Hl).
              assert (H := R_depth_bound _ _ _ _ _ _ _ _ _ _ HB Hfpos 16 ltac:(lia)
                             ltac:(rewrite (weight_R _ _ _ _ _ _ _ _ _ _ HB); exact HW18) (lid l)
                             ltac:(apply (R_leaf _ _ _ _ _ _ _ _ _ _ HB l Hl))).
              lia.
Qed.
