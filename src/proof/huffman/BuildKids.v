(** * build_tree's merge loop: every internal node gets exactly two children, removal order sorts frequencies *)

From Coq Require Import ZArith List Lia Bool Permutation.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap
               Zlib.proof.huffman.BuildTree.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The shape of one merge step *)

Lemma merge_body_shape : forall TS elems total S f0 t w node it Q,
  minv TS elems total S f0 t w node it Q -> 2 <= w_heap_len w -> total < 65536 ->
  let n := Znth 1 (w_heap w) in
  let t' := fst (merge_body t w node) in let w' := snd (merge_body t w node) in
  exists m rest,
    Permutation (reg (w_heap w) (w_heap_len w)) (n :: m :: rest) /\
    (forall y, In y (m :: rest) -> le t (w_depth w) n y) /\ (forall y, In y rest -> le t (w_depth w) m y) /\
    w_heap_max w' = w_heap_max w - 2 /\ w_heap_len w' = w_heap_len w - 1 /\
    removed (w_heap w') (w_heap_max w') = m :: n :: removed (w_heap w) (w_heap_max w) /\
    Permutation (reg (w_heap w') (w_heap_len w')) (node :: rest) /\
    dl t' = upd_Znth n (upd_Znth m (dl t) (u16 node)) (u16 node) /\
    fc t' = upd_Znth node (fc t) (u16 (Znth n (fc t) + Znth m (fc t))).
Proof.
  intros TS elems total S f0 t w node it Q HI H2 Htot65.
  destruct HI as [Hh Hd Hfc Hdl Hlen Hroom Hnode Hhp Hst Hperm Hpool Htot Hnd Hch Hrem Hleaf Hnonem Hdescs Hkind Hrkind Hunused].
  cbv zeta. rewrite merge_body_eq. cbn zeta. cbn [fst snd].
  set (heap := w_heap w) in *. set (len := w_heap_len w) in *. set (hm := w_heap_max w) in *.
  set (dep := w_depth w) in *.
  set (n := Znth 1 heap).
  set (heap1 := upd_Znth 1 heap (Znth len heap)).
  set (w0 := w_set_heap_len (w_set_heap w heap1) (len - 1)).
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
  assert (Hin_old : forall y, In y (n :: m :: rest) -> In y (reg heap len))
    by (intros y Hy; eapply Permutation_in; [apply Permutation_sym, Rh|exact Hy]).
  assert (Hlt : forall y, In y (n :: m :: rest) -> 0 <= y < node) by (intros y Hy; apply Hpool, Hin_old, Hy).
  assert (Hrest_node : forall y, In y rest -> y <> node) by (intros y Hy Hc; subst; specialize (Hlt node (or_intror (or_intror Hy))); lia).
  assert (Hmin_n : forall y, In y (m :: rest) -> le t dep n y).
  { intros y Hy. assert (Hy' : In y (reg heap len)) by (apply Hin_old; right; auto).
    apply in_reg in Hy'. destruct Hy' as [i [Hi <-]]. exact (hp_top_min t dep heap len Hhp i Hi). }
  assert (Hmin_m : forall y, In y rest -> le t dep m y).
  { intros y Hy. assert (Hy' : In y (reg heap1' (len - 1))) by (rewrite reg_cons by lia; right; exact Hy).
    apply in_reg in Hy'. destruct Hy' as [i [Hi <-]]. exact (hp_top_min t dep heap1' (len - 1) P1hp i Hi). }
  assert (Hnode0 : 0 <= node) by (specialize (Hlt n (in_eq _ _)); lia).
  assert (HTS : node < TS /\ TS <= 573) by (unfold HEAP_SIZE in Hnode; lia).
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
  exists m, rest.
  split; [exact Rh|]. split; [exact Hmin_n|]. split; [exact Hmin_m|].
  split; [rewrite P2hm; lia|]. split; [exact P2len|].
  split; [rewrite P2hm; replace (hm - 2) with (hm - 1 - 1) by lia; exact R3|].
  split; [rewrite P2len; exact Rh5|].
  split; reflexivity.
Qed.

(** ** The invariant *)

(** The number of removed nodes whose Dad is [y]. *)
Definition kids (dl heap : list Z) (hm y : Z) : Z :=
  Zlength (filter (fun x => Znth x dl =? y) (removed heap hm)).

Record kinv (elems : Z) (t : tree) (w : work) (node : Z) : Prop := {
  ki_kids : forall y, kids (dl t) (w_heap w) (w_heap_max w) y = if (elems <=? y) && (y <? node) then 2 else 0;
  ki_sorted : forall i j, w_heap_max w <= i <= j -> j < HEAP_SIZE ->
                Znth (Znth j (w_heap w)) (fc t) <= Znth (Znth i (w_heap w)) (fc t);
  ki_below : forall p y, w_heap_max w <= p < HEAP_SIZE -> In y (reg (w_heap w) (w_heap_len w)) ->
                Znth (Znth p (w_heap w)) (fc t) <= Znth y (fc t)
}.

Lemma kids_cons : forall dl x r y,
  Zlength (filter (fun z => Znth z dl =? y) (x :: r)) =
  (if Znth x dl =? y then 1 else 0) + Zlength (filter (fun z => Znth z dl =? y) r).
Proof. intros. simpl. destruct (Znth x dl =? y); [rewrite Zlength_cons|]; lia. Qed.

Lemma filter_ext_in_Z : forall (f g : Z -> bool) l, (forall x, In x l -> f x = g x) -> filter f l = filter g l.
Proof.
  intros f g l H. induction l as [|a l IH]; simpl; auto.
  rewrite (H a (in_eq _ _)). rewrite IH by (intros; apply H; right; auto). reflexivity.
Qed.

Lemma le_fc : forall t d x y, le t d x y -> Znth x (fc t) <= Znth y (fc t).
Proof.
  unfold le, smaller. intros t d x y H. apply orb_true_iff in H. destruct H as [H|H].
  - apply Z.ltb_lt in H. lia.
  - apply andb_true_iff in H. destruct H as [H _]. apply Z.eqb_eq in H. lia.
Qed.

Lemma kinv_step : forall TS elems total S f0 t w node it Q,
  minv TS elems total S f0 t w node it Q -> kinv elems t w node -> 2 <= w_heap_len w -> total < 65536 ->
  kinv elems (fst (merge_body t w node)) (snd (merge_body t w node)) (node + 1).
Proof.
  intros TS elems total S f0 t w node it Q HI HK H2 Htot.
  destruct (merge_body_shape TS elems total S f0 t w node it Q HI H2 Htot)
    as [m [rest [Rh [Hmin_n [Hmin_m [Ehm [Elen [Erem [Rh' [Edl Efc]]]]]]]]]].
  set (n := Znth 1 (w_heap w)) in *.
  destruct (merge_body t w node) as [t' w'] eqn:E. cbn [fst snd] in *.
  destruct HI as [Hh Hd Hfc Hdl Hlen Hroom Hnode Hhp Hst Hperm Hpool Htot' Hnd Hch Hrem Hleaf Hnonem Hdescs Hkind Hrkind Hunused].
  destruct HK as [K1 K2 K3].
  set (R := removed (w_heap w) (w_heap_max w)) in *.
  assert (Hin_old : forall y, In y (n :: m :: rest) -> In y (reg (w_heap w) (w_heap_len w)))
    by (intros y Hy; eapply Permutation_in; [apply Permutation_sym, Rh|exact Hy]).
  assert (Hnd' : NoDup (n :: m :: rest ++ R)).
  { eapply Permutation_NoDup; [|exact Hnd]. change (n :: m :: rest ++ R) with ((n :: m :: rest) ++ R).
    apply Permutation_app_tail. exact Rh. }
  assert (Hnm : n <> m) by (intros Hc; inversion Hnd' as [|? ? Hni _]; apply Hni; left; auto).
  assert (HnR : ~ In n R) by (intros Hc; inversion Hnd' as [|? ? Hni _]; apply Hni; right; apply in_or_app; right; auto).
  assert (HmR : ~ In m R).
  { intros Hc. inversion Hnd' as [|? ? _ Hnd2]. inversion Hnd2 as [|? ? Hmi _]. apply Hmi. apply in_or_app; right; auto. }
  assert (Hpn := Hpool n (Hin_old n (in_eq _ _))).
  assert (Hpm := Hpool m (Hin_old m (or_intror (in_eq _ _)))).
  assert (HR_lt : forall x, In x R -> 0 <= x < node).
  { intros x Hx. apply in_removed in Hx. destruct Hx as [p [Hp <-]]. destruct (Hrem p Hp) as [Hr _]. exact Hr. }
  assert (Hu : u16 node = node) by (unfold u16; apply Z.mod_small; unfold HEAP_SIZE in Hnode; lia).
  rewrite Hu in Edl.
  assert (Hdl' : forall x, x <> n -> x <> m -> Znth x (dl t') = Znth x (dl t)).
  { intros x Hxn Hxm. rewrite Edl.
    destruct (Z_le_gt_dec 0 x); [destruct (Z_lt_ge_dec x (Zlength (dl t)))|].
    - rewrite !upd_Znth_diff by (rewrite ?Zlength_upd; lia). reflexivity.
    - rewrite !Znth_overflow by (rewrite ?Zlength_upd; lia). reflexivity.
    - rewrite !Znth_underflow by lia. reflexivity. }
  assert (Hdln : Znth n (dl t') = node) by (rewrite Edl; rewrite upd_Znth_same by (rewrite Zlength_upd; lia); reflexivity).
  assert (Hdlm : Znth m (dl t') = node).
  { rewrite Edl. rewrite upd_Znth_diff by (rewrite ?Zlength_upd; lia). rewrite upd_Znth_same by lia. reflexivity. }
  assert (Hfc' : forall x, x <> node -> Znth x (fc t') = Znth x (fc t)).
  { intros x Hx. rewrite Efc.
    destruct (Z_le_gt_dec 0 x); [destruct (Z_lt_ge_dec x (Zlength (fc t)))|].
    - rewrite upd_Znth_diff by lia. reflexivity.
    - rewrite !Znth_overflow by (rewrite ?Zlength_upd; lia). reflexivity.
    - rewrite !Znth_underflow by lia. reflexivity. }
  assert (Hsum : Znth n (fc t) + Znth m (fc t) <= total).
  { rewrite <- Htot'. rewrite (sumZ_perm' _ _ _ Rh). simpl.
    assert (0 <= sumZ (map (fun y => Znth y (fc t)) rest)).
    { apply sumZ_nonneg. intros y Hy. apply (Hpool y (Hin_old y (or_intror (or_intror Hy)))). }
    lia. }
  assert (Hfcnode : Znth node (fc t') = Znth n (fc t) + Znth m (fc t)).
  { rewrite Efc. rewrite upd_Znth_same by lia. unfold u16. apply Z.mod_small. lia. }
  assert (Hle_nm : Znth n (fc t) <= Znth m (fc t)) by (apply (le_fc t (w_depth w)), Hmin_n; left; auto).
  (* positions of the new removed region *)
  set (hm := w_heap_max w) in *.
  assert (Hpos : forall p, w_heap_max w' <= p < HEAP_SIZE ->
            (p = hm - 2 /\ Znth p (w_heap w') = m) \/ (p = hm - 1 /\ Znth p (w_heap w') = n) \/
            (hm <= p /\ Znth p (w_heap w') = Znth p (w_heap w))).
  { intros p Hp. rewrite Ehm in Hp.
    assert (Hr := Erem). unfold removed in Hr.
    replace (Z.to_nat (HEAP_SIZE - w_heap_max w')) with (Datatypes.S (Datatypes.S (Z.to_nat (HEAP_SIZE - hm)))) in Hr by lia.
    cbn [zseq map] in Hr. rewrite Ehm in Hr. injection Hr as Hr1 Hr2 Hr3.
    replace (hm - 2 + 1) with (hm - 1) in Hr2 by lia.
    destruct (Z.eq_dec p (hm - 2)) as [->|H2']; [left; auto|].
    destruct (Z.eq_dec p (hm - 1)) as [->|H1']; [right; left; auto|].
    right; right. split; [lia|].
    assert (Hr3' : map (fun i => Znth i (w_heap w')) (zseq hm (Z.to_nat (HEAP_SIZE - hm))) =
                   map (fun i => Znth i (w_heap w)) (zseq hm (Z.to_nat (HEAP_SIZE - hm)))).
    { replace (hm - 2 + 1 + 1) with hm in Hr3 by lia. exact Hr3. }
    assert (Hin : In p (zseq hm (Z.to_nat (HEAP_SIZE - hm)))) by (apply in_zseq; lia).
    clear -Hr3' Hin. induction (zseq hm (Z.to_nat (HEAP_SIZE - hm))) as [|a l IH]; [destruct Hin|].
    simpl in Hr3'. injection Hr3' as Ha Hl. destruct Hin as [<-|Hin]; auto. }
  (* fc of removed nodes (old ones and n, m) is unchanged *)
  assert (HnN : n <> node) by lia. assert (HmN : m <> node) by lia.
  assert (HxR_fc : forall p, hm <= p < HEAP_SIZE -> Znth (Znth p (w_heap w)) (fc t') = Znth (Znth p (w_heap w)) (fc t)).
  { intros p Hp. apply Hfc'. assert (Hx : In (Znth p (w_heap w)) R) by (apply in_removed; exists p; auto).
    specialize (HR_lt _ Hx). lia. }
  constructor.
  - (* kids *)
    intros y. unfold kids. rewrite Erem. rewrite !kids_cons.
    rewrite Hdlm, Hdln.
    rewrite (filter_ext_in_Z (fun x => Znth x (dl t') =? y) (fun x => Znth x (dl t) =? y)).
    2:{ intros x Hx. rewrite Hdl'; auto; intros ->; contradiction. }
    assert (K1y := K1 y). unfold kids in K1y. change (removed (w_heap w) hm) with R in K1y. rewrite K1y.
    destruct (Z.eqb_spec node y) as [<-|Hy].
    + replace ((elems <=? node) && (node <? node)) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
      replace ((elems <=? node) && (node <? node + 1)) with true
        by (symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      reflexivity.
    + replace ((elems <=? y) && (y <? node + 1)) with ((elems <=? y) && (y <? node)); [lia|].
      destruct (Z.ltb_spec y node), (Z.ltb_spec y (node + 1)); try lia; reflexivity.
  - (* sorted *)
    intros i j Hij Hj.
    assert (Hval : forall p, w_heap_max w' <= p < HEAP_SIZE ->
              Znth (Znth p (w_heap w')) (fc t') = Znth (Znth p (w_heap w')) (fc t)).
    { intros p Hp. destruct (Hpos p Hp) as [[_ ->]|[[_ ->]|[Hp' ->]]]; [apply Hfc'; lia|apply Hfc'; lia|].
      apply HxR_fc; lia. }
    rewrite !Hval by lia.
    destruct (Hpos i ltac:(lia)) as [[Ei Hi]|[[Ei Hi]|[Ei Hi]]]; destruct (Hpos j ltac:(lia)) as [[Ej Hj']|[[Ej Hj']|[Ej Hj']]];
      rewrite ?Hi, ?Hj'; try lia.
    + (* i = m, j old *) apply Z.le_trans with (Znth n (fc t)); [|exact Hle_nm].
      apply K3; [lia|]. apply Hin_old; left; auto.
    + (* i = n, j old *) apply K3; [lia|]. apply Hin_old; left; auto.
    + apply K2; lia.
  - (* below *)
    intros p y Hp Hy.
    assert (Hy' : In y (node :: rest)) by (eapply Permutation_in; [exact Rh'|exact Hy]).
    assert (Hfc_y : Znth m (fc t) <= Znth y (fc t')).
    { destruct Hy' as [<-|Hy'].
      - rewrite Hfcnode. lia.
      - assert (y <> node) by (intros ->; specialize (Hpool node (Hin_old node (or_intror (or_intror Hy')))); lia).
        rewrite Hfc' by auto. apply (le_fc t (w_depth w)), Hmin_m, Hy'. }
    destruct (Hpos p Hp) as [[_ ->]|[[_ ->]|[Hp' ->]]].
    + rewrite Hfc' by lia. exact Hfc_y.
    + rewrite Hfc' by lia. lia.
    + rewrite HxR_fc by lia. apply Z.le_trans with (Znth n (fc t)); [|lia].
      apply K3; [lia|]. apply Hin_old; left; auto.
Qed.

Lemma bt_merge_kinv : forall TS elems total S f0, total < 65536 ->
  forall fuel t w node it Q,
  minv TS elems total S f0 t w node it Q -> kinv elems t w node -> 2 <= w_heap_len w ->
  (Z.to_nat (w_heap_len w - 1) <= fuel)%nat ->
  let '(t', w', node') := bt_merge fuel t w node in kinv elems t' w' node'.
Proof.
  intros TS elems total S f0 Htot fuel. induction fuel as [|fuel IH]; intros t w node it Q HI HK H2 Hf; [lia|].
  rewrite bt_merge_unfold.
  assert (HK1 := kinv_step TS elems total S f0 t w node it Q HI HK H2 Htot).
  destruct (merge_step TS elems total S f0 t w node it Q HI H2 Htot) as [it1 [Q1 [HI1 Hlen1]]].
  destruct (merge_body t w node) as [t1 w1] eqn:E. simpl in HI1, Hlen1, HK1.
  destruct (Z.geb_spec (w_heap_len w1) 2) as [Hge|Hlt].
  - apply (IH t1 w1 (node + 1) it1 Q1 HI1 HK1 Hge). lia.
  - exact HK1.
Qed.

Lemma kinv_init : forall elems t w, w_heap_max w = HEAP_SIZE -> kinv elems t w elems.
Proof.
  intros elems t w Hhm. constructor.
  - intros y. unfold kids, removed. rewrite Hhm. replace (Z.to_nat (HEAP_SIZE - HEAP_SIZE)) with O by lia.
    simpl. destruct (Z.leb_spec elems y), (Z.ltb_spec y elems); simpl; try reflexivity; lia.
  - intros i j Hij Hj. lia.
  - intros p y Hp. lia.
Qed.
