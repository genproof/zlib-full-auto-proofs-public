(** * gen_bitlen's first pass computes the depths in the Huffman tree (clamped to max_length) *)

From Coq Require Import ZArith List Lia Bool Permutation.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap
               Zlib.proof.huffman.BuildTree Zlib.proof.huffman.BuildPre Zlib.proof.huffman.BuildKids
               Zlib.proof.huffman.DCount.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Distances to the root along the Dad pointers *)

(** [fh fuel D root y]: the number of Dad steps from [y] to [root] (within [fuel] steps). *)
Fixpoint fh (fuel : nat) (D : list Z) (root y : Z) : Z :=
  match fuel with O => 0 | S f => if y =? root then 0 else 1 + fh f D root (Znth y D) end.

Definition first_hit (D : list Z) (y root : Z) (e : nat) : Prop :=
  iter D e y = root /\ forall e', (e' < e)%nat -> iter D e' y <> root.

Lemma fh_first_hit : forall D root e y fuel, first_hit D y root e -> (e < fuel)%nat -> fh fuel D root y = Z.of_nat e.
Proof.
  intros D root e. induction e as [|e IH]; intros y fuel [H1 H2] Hf.
  - destruct fuel; [lia|]. simpl in *. subst. rewrite Z.eqb_refl. reflexivity.
  - destruct fuel; [lia|]. cbn [fh].
    assert (Hy : y <> root) by (specialize (H2 O ltac:(lia)); exact H2).
    rewrite (proj2 (Z.eqb_neq y root) Hy). rewrite (IH (Znth y D) fuel); [lia| |lia].
    split; [exact H1|]. intros e' He'. exact (H2 (S e') ltac:(lia)).
Qed.

Lemma first_hit_unique : forall D y root e1 e2, first_hit D y root e1 -> first_hit D y root e2 -> e1 = e2.
Proof.
  intros D y root e1 e2 [A1 B1] [A2 B2].
  destruct (Nat.lt_trichotomy e1 e2) as [H|[H|H]]; auto; exfalso; [apply (B2 e1)|apply (B1 e2)]; auto.
Qed.

Lemma first_hit_step : forall D y root e, y <> root -> first_hit D (Znth y D) root e -> first_hit D y root (S e).
Proof.
  intros D y root e Hy [A B]. split; [exact A|].
  intros e' He'. destruct e' as [|e']; [exact Hy|]. apply B. lia.
Qed.

(** ** Distances in the region of a pre_ok state *)

Lemma NoDup_map_inj : forall (f : Z -> Z) l a b, NoDup (map f l) -> In a l -> In b l -> f a = f b -> a = b.
Proof.
  intros f l. induction l as [|x l IH]; intros a b Hnd Ha Hb E; [destruct Ha|].
  simpl in Hnd. inversion Hnd as [|? ? Hx Hnd']; subst.
  destruct Ha as [<-|Ha], Hb as [<-|Hb]; auto.
  - exfalso. apply Hx. rewrite E. apply in_map. exact Hb.
  - exfalso. apply Hx. rewrite <- E. apply in_map. exact Ha.
Qed.

Lemma removed_Znth_inj : forall heap hm p1 p2, NoDup (removed heap hm) ->
  hm <= p1 < HEAP_SIZE -> hm <= p2 < HEAP_SIZE -> Znth p1 heap = Znth p2 heap -> p1 = p2.
Proof.
  intros heap hm p1 p2 Hnd H1 H2 E. unfold removed in Hnd.
  apply (NoDup_map_inj (fun i => Znth i heap) (zseq hm (Z.to_nat (HEAP_SIZE - hm)))); auto; apply in_zseq; lia.
Qed.

Section Region.
Variable sd : stat_desc.
Variables (t0 : tree) (w0 : work) (S F : list Z) (R : item) (t : tree) (w : work) (mc : Z).
Hypothesis Hpre : pre_ok sd t0 w0 S F R t w mc.

Definition hm := w_heap_max w.
Definition heap := w_heap w.
Definition root := Znth hm heap.
Definition D := dl t.

Lemma region_first_hit : forall p, hm <= p < HEAP_SIZE ->
  exists e, first_hit D (Znth p heap) root e /\ (e <= Z.to_nat (p - hm))%nat.
Proof.
  intros p Hp. remember (Z.to_nat (p - hm)) as k eqn:Ek. revert p Hp Ek.
  induction k as [k IH] using lt_wf_ind. intros p Hp Ek.
  destruct (Z.eq_dec p hm) as [->|Hne].
  - exists O. split; [split; [reflexivity|intros; lia]|lia].
  - destruct (po_dad _ _ _ _ _ _ _ _ _ Hpre p ltac:(unfold hm in *; lia)) as [q [Hq Eq]].
    destruct (IH (Z.to_nat (q - hm)) ltac:(lia) q ltac:(unfold hm in *; lia) eq_refl) as [e [He Hle]].
    exists (Datatypes.S e). split; [|lia].
    apply first_hit_step.
    + intros Hc. apply Hne. apply (removed_Znth_inj heap hm p hm); unfold hm, heap in *;
        try apply (po_nodup _ _ _ _ _ _ _ _ _ Hpre); try lia; auto.
    + unfold D, heap in *. rewrite <- Eq. exact He.
Qed.

End Region.

(** ** One step of the first pass *)

Definition xb (sd : stat_desc) (n : Z) : Z := if n >=? sd_base sd then Znth (n - sd_base sd) (sd_extra sd) else 0.

Definition leaf_upd (sd : stat_desc) (w : work) (n bits fr : Z) : work :=
  let w := w_set_bl_count w (upd_Znth bits (w_bl_count w) (u16 (Znth bits (w_bl_count w) + 1))) in
  let w := w_set_opt_len w (u64 (w_opt_len w + fr * u32 (bits + xb sd n))) in
  match sd_stree sd with
  | Some stree => w_set_static_len w (u64 (w_static_len w + fr * u32 (Znth n stree + xb sd n)))
  | None => w
  end.

Lemma leaf_upd_fields : forall sd w n bits fr,
  w_heap (leaf_upd sd w n bits fr) = w_heap w /\ w_heap_max (leaf_upd sd w n bits fr) = w_heap_max w /\
  w_heap_len (leaf_upd sd w n bits fr) = w_heap_len w /\ w_depth (leaf_upd sd w n bits fr) = w_depth w /\
  w_bl_count (leaf_upd sd w n bits fr) = upd_Znth bits (w_bl_count w) (u16 (Znth bits (w_bl_count w) + 1)) /\
  w_opt_len (leaf_upd sd w n bits fr) = u64 (w_opt_len w + fr * u32 (bits + xb sd n)) /\
  w_static_len (leaf_upd sd w n bits fr) =
    match sd_stree sd with
    | Some stree => u64 (w_static_len w + fr * u32 (Znth n stree + xb sd n))
    | None => w_static_len w
    end.
Proof. intros. unfold leaf_upd. destruct (sd_stree sd); repeat split; reflexivity. Qed.

Lemma pass1_step : forall f sd mc t w ovf h,
  gen_bitlen_pass1 (S f) sd mc t w ovf h =
  if h <? HEAP_SIZE then
    let n := Znth h (w_heap w) in
    let b0 := Znth (Znth n (dl t)) (dl t) + 1 in
    let bits := if b0 >? sd_maxlen sd then sd_maxlen sd else b0 in
    let ovf' := if b0 >? sd_maxlen sd then ovf + 1 else ovf in
    let t' := set_dl t n (u16 bits) in
    if n >? mc then gen_bitlen_pass1 f sd mc t' w ovf' (h + 1)
    else gen_bitlen_pass1 f sd mc t' (leaf_upd sd w n bits (Znth n (fc t))) ovf' (h + 1)
  else (t, w, ovf).
Proof.
  intros. cbn [gen_bitlen_pass1]. destruct (h <? HEAP_SIZE); [|reflexivity].
  destruct (Znth (Znth (Znth h (w_heap w)) (dl t)) (dl t) + 1 >? sd_maxlen sd); reflexivity.
Qed.

(** ** The first pass *)

Section Pass1.
Variable sd : stat_desc.
Variables (mc hm : Z) (heap D0 fc0 dep0 : list Z) (len0 opt0 st0 : Z).
Let M := sd_maxlen sd.
Let root := Znth hm heap.
Definition E (q : Z) : Z := fh 600 D0 root (Znth q heap).

Hypothesis Hnd : NoDup (removed heap hm).
Hypothesis Hhm : 1 <= hm < HEAP_SIZE.
Hypothesis Hheap : Zlength heap = HEAP_SIZE.
Hypothesis Hdist : forall p, hm <= p < HEAP_SIZE -> exists e, first_hit D0 (Znth p heap) root e /\ (e < 573)%nat.
Hypothesis Hdad : forall p, hm < p < HEAP_SIZE -> exists q, hm <= q < p /\ Znth q heap = Znth (Znth p heap) D0.
Hypothesis HM : 1 <= M <= 15.
Hypothesis Hidx : forall p, hm <= p < HEAP_SIZE -> 0 <= Znth p heap < Zlength D0.

Definition rng (h : Z) : list Z := zseq (hm + 1) (Z.to_nat (h - hm - 1)).
Definition cnt_ovf (h : Z) : Z := sumZ (map (fun q => if E q >? M then 1 else 0) (rng h)).
Definition cnt_bl (h b : Z) : Z :=
  sumZ (map (fun q => if (Znth q heap <=? mc) && (Z.min (E q) M =? b) then 1 else 0) (rng h)).
Definition acc_opt (h : Z) : Z :=
  sumZ (map (fun q => if Znth q heap <=? mc then Znth (Znth q heap) fc0 * (Z.min (E q) M + xb sd (Znth q heap)) else 0) (rng h)).
Definition acc_st (st : list Z) (h : Z) : Z :=
  sumZ (map (fun q => if Znth q heap <=? mc then Znth (Znth q heap) fc0 * (Znth (Znth q heap) st + xb sd (Znth q heap)) else 0) (rng h)).

Definition pinv (h : Z) (t : tree) (w : work) (ovf : Z) : Prop :=
  fc t = fc0 /\ Zlength (dl t) = Zlength D0 /\
  w_heap w = heap /\ w_heap_max w = hm /\ w_heap_len w = len0 /\ w_depth w = dep0 /\
  (forall q, hm <= q < h -> Znth (Znth q heap) (dl t) = Z.min (E q) M) /\
  (forall c, (forall q, hm <= q < h -> Znth q heap <> c) -> Znth c (dl t) = Znth c D0) /\
  ovf = cnt_ovf h /\
  Zlength (w_bl_count w) = 16 /\ (forall b, 0 <= b < 16 -> Znth b (w_bl_count w) = cnt_bl h b) /\
  w_opt_len w = u64 (opt0 + acc_opt h) /\
  w_static_len w = match sd_stree sd with Some st => u64 (st0 + acc_st st h) | None => st0 end.

Hypothesis Hxb : forall p, hm <= p < HEAP_SIZE -> 0 <= xb sd (Znth p heap) <= 16.
Hypothesis Hst : forall st, sd_stree sd = Some st -> forall p, hm <= p < HEAP_SIZE -> 0 <= Znth (Znth p heap) st <= 16.
Hypothesis Hfc0 : forall p, hm <= p < HEAP_SIZE -> 0 <= Znth (Znth p heap) fc0 < 65536.
Hypothesis Hopt0 : 0 <= opt0 < 18446744073709551616.
Hypothesis Hst0 : 0 <= st0 < 18446744073709551616.

Lemma rng_succ : forall h, hm < h -> rng (h + 1) = rng h ++ [h].
Proof.
  intros h Hh. unfold rng. replace (Z.to_nat (h + 1 - hm - 1)) with (S (Z.to_nat (h - hm - 1))) by lia.
  rewrite zseq_succ_r. f_equal. f_equal. lia.
Qed.

Lemma in_rng : forall h q, In q (rng h) <-> hm + 1 <= q < h.
Proof. intros. unfold rng. rewrite in_zseq. lia. Qed.

Lemma sumZ_snoc : forall (g : Z -> Z) l x, sumZ (map g (l ++ [x])) = sumZ (map g l) + g x.
Proof. intros. rewrite map_app, sumZ_app. simpl. lia. Qed.

Lemma cnt_bl_le : forall h b, cnt_bl h b <= Zlength (rng h).
Proof.
  intros h b. unfold cnt_bl. generalize (rng h). intros l. induction l as [|q l IH]; [rewrite Zlength_nil; simpl; lia|].
  cbn [map sumZ]. rewrite Zlength_cons. destruct (_ && _); lia.
Qed.

Lemma rng_len : forall h, hm < h -> Zlength (rng h) = h - hm - 1.
Proof. intros. unfold rng. rewrite Zlength_correct, zseq_length. lia. Qed.

Lemma heap_inj : forall p1 p2, hm <= p1 < HEAP_SIZE -> hm <= p2 < HEAP_SIZE -> Znth p1 heap = Znth p2 heap -> p1 = p2.
Proof. intros. apply (removed_Znth_inj heap hm); auto. Qed.

Lemma E_first_hit : forall p e, hm <= p < HEAP_SIZE -> first_hit D0 (Znth p heap) root e -> E p = Z.of_nat e.
Proof.
  intros p e Hp He. destruct (Hdist p Hp) as [e' [He' Hlt]].
  assert (e = e') by (eapply first_hit_unique; eauto). subst e'.
  unfold E. apply fh_first_hit; auto. lia.
Qed.

Lemma E_root : E hm = 0.
Proof. unfold E. apply (fh_first_hit D0 root O root 600). split; [reflexivity|intros; lia]. lia. Qed.

Lemma E_dad : forall p q, hm < p < HEAP_SIZE -> hm <= q < p -> Znth q heap = Znth (Znth p heap) D0 -> E p = E q + 1.
Proof.
  intros p q Hp Hq Eq. destruct (Hdist q ltac:(lia)) as [e [He _]].
  assert (Hn : Znth p heap <> root) by (intros Hc; unfold root in Hc; apply heap_inj in Hc; lia).
  assert (Hp' : first_hit D0 (Znth p heap) root (S e)) by (apply first_hit_step; auto; rewrite <- Eq; auto).
  rewrite (E_first_hit p (S e)) by (auto; lia). rewrite (E_first_hit q e) by (auto; lia). lia.
Qed.

Lemma pass1_correct : forall fuel h t w ovf,
  hm < h <= HEAP_SIZE -> (Z.to_nat (HEAP_SIZE - h) <= fuel)%nat -> pinv h t w ovf ->
  let '(t', w', ovf') := gen_bitlen_pass1 fuel sd mc t w ovf h in pinv HEAP_SIZE t' w' ovf'.
Proof.
  induction fuel as [|fuel IH]; intros h t w ovf Hh Hf Hinv.
  - assert (h = HEAP_SIZE) by lia. subst h. exact Hinv.
  - rewrite pass1_step. cbv zeta. destruct (Z.ltb_spec h HEAP_SIZE) as [Hlt|Hge]; [|assert (h = HEAP_SIZE) by lia; subst h; exact Hinv].
    destruct Hinv as [I1 [I2 [I3 [I4 [I5 [I6 [I7 [I8 [I9 [I10 [I11 [I12 I13]]]]]]]]]]]].
    rewrite I3. set (n := Znth h heap).
    assert (Hnq : forall q, hm <= q < h -> Znth q heap <> n) by (intros q Hq Hc; apply heap_inj in Hc; lia).
    rewrite (I8 n Hnq).
    destruct (Hdad h ltac:(lia)) as [q [Hq Eq]]. fold n in Eq. rewrite <- Eq. rewrite (I7 q Hq).
    assert (EE := E_dad h q ltac:(lia) Hq Eq).
    assert (Hn_rng : 0 <= n < Zlength (dl t)) by (rewrite I2; apply Hidx; lia).
    assert (HEq : 0 <= E q) by (unfold E; destruct (Hdist q ltac:(lia)) as [e [He Hlt0]];
                               rewrite (fh_first_hit D0 root e) by (auto; lia); lia).
    change (sd_maxlen sd) with M.
    set (b0 := Z.min (E q) M + 1).
    set (bits := if b0 >? M then M else b0).
    set (ovf' := if b0 >? M then ovf + 1 else ovf).
    assert (Hbits : bits = Z.min (E h) M /\ 1 <= bits <= 15).
    { unfold bits, b0. destruct (Z.gtb_spec (Z.min (E q) M + 1) M); lia. }
    assert (Hovf : ovf' = cnt_ovf (h + 1)).
    { unfold ovf', cnt_ovf. rewrite rng_succ by lia. rewrite sumZ_snoc. fold (cnt_ovf h). rewrite <- I9.
      unfold b0. destruct (Z.gtb_spec (Z.min (E q) M + 1) M), (Z.gtb_spec (E h) M); lia. }
    assert (Hu16 : u16 bits = bits) by (unfold u16; apply Z.mod_small; lia).
    set (t' := set_dl t n (u16 bits)).
    assert (Hdl' : forall c, c <> n -> Znth c (dl t') = Znth c (dl t)).
    { intros c Hc. unfold t', set_dl; simpl.
      destruct (Z_le_gt_dec 0 c); [destruct (Z_lt_ge_dec c (Zlength (dl t)))|].
      - rewrite upd_Znth_diff by lia. reflexivity.
      - rewrite !Znth_overflow by (rewrite ?Zlength_upd; lia). reflexivity.
      - rewrite !Znth_underflow by lia. reflexivity. }
    assert (Hdln : Znth n (dl t') = bits) by (unfold t', set_dl; simpl; rewrite upd_Znth_same by lia; exact Hu16).
    assert (Hcommon : forall w', w_heap w' = heap -> w_heap_max w' = hm -> w_heap_len w' = len0 -> w_depth w' = dep0 ->
      Zlength (w_bl_count w') = 16 -> (forall b, 0 <= b < 16 -> Znth b (w_bl_count w') = cnt_bl (h + 1) b) ->
      w_opt_len w' = u64 (opt0 + acc_opt (h + 1)) ->
      w_static_len w' = match sd_stree sd with Some st => u64 (st0 + acc_st st (h + 1)) | None => st0 end ->
      pinv (h + 1) t' w' ovf').
    { intros w' W1 W2 W3 W4 W5 W6 W7 W8. split; [unfold t', set_dl; simpl; exact I1|]. split; [unfold t', set_dl; simpl; rewrite Zlength_upd; exact I2|].
      split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|].
      split.
      { intros q' Hq'. destruct (Z.eq_dec q' h) as [->|Hne].
        - fold n. rewrite Hdln. apply Hbits.
        - rewrite Hdl' by (apply Hnq; lia). apply I7; lia. }
      split.
      { intros c Hc. rewrite Hdl' by (intros ->; apply (Hc h); [lia|reflexivity]). apply I8. intros q' Hq'. apply Hc. lia. }
      split; [exact Hovf|]. split; [exact W5|]. split; [exact W6|]. split; [exact W7|exact W8]. }
    destruct (Z.gtb_spec n mc) as [Hint|Hleaf].
    + apply IH; [lia|lia|]. apply Hcommon; auto.
      * intros b Hb. rewrite I11 by auto. unfold cnt_bl. rewrite rng_succ by lia. rewrite sumZ_snoc. fold n.
        replace (n <=? mc) with false by (symmetry; apply Z.leb_gt; lia). simpl. lia.
      * rewrite I12. unfold acc_opt. rewrite rng_succ by lia. rewrite sumZ_snoc. fold n.
        replace (n <=? mc) with false by (symmetry; apply Z.leb_gt; lia). f_equal. lia.
      * rewrite I13. destruct (sd_stree sd) as [st|]; auto. unfold acc_st. rewrite rng_succ by lia. rewrite sumZ_snoc. fold n.
        replace (n <=? mc) with false by (symmetry; apply Z.leb_gt; lia). f_equal. lia.
    + apply IH; [lia|lia|].
      assert (Hcnt := cnt_bl_le h bits). rewrite rng_len in Hcnt by lia.
      assert (Hfr : Znth n (fc t) = Znth n fc0) by (rewrite I1; reflexivity).
      assert (Hfc0n := Hfc0 h ltac:(lia)). fold n in Hfc0n.
      assert (Hxbn := Hxb h ltac:(lia)). fold n in Hxbn.
      destruct (leaf_upd_fields sd w n bits (Znth n (fc t))) as [L1 [L2 [L3 [L4 [L5 [L6 L7]]]]]].
      apply Hcommon.
      * rewrite L1. exact I3.
      * rewrite L2. exact I4.
      * rewrite L3. exact I5.
      * rewrite L4. exact I6.
      * rewrite L5, Zlength_upd. exact I10.
      * intros b Hb. rewrite L5.
        unfold cnt_bl. rewrite rng_succ by lia. rewrite sumZ_snoc. fold n. fold (cnt_bl h b).
        replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia). simpl andb.
        destruct (Z.eq_dec b bits) as [->|Hb'].
        -- rewrite upd_Znth_same by lia. rewrite I11 by lia. unfold u16.
           assert (Hcnt0 : 0 <= cnt_bl h bits) by (unfold cnt_bl; apply sumZ_nonneg; intros; destruct (_ && _); lia).
           rewrite Z.mod_small by (unfold HEAP_SIZE in *; lia).
           destruct Hbits as [Hb1 _]. rewrite <- Hb1, Z.eqb_refl. lia.
        -- rewrite upd_Znth_diff by lia. rewrite I11 by lia.
           destruct Hbits as [Hb1 _]. rewrite <- Hb1. replace (bits =? b) with false by (symmetry; apply Z.eqb_neq; lia). lia.
      * rewrite L6, I12. unfold acc_opt. rewrite rng_succ by lia. rewrite sumZ_snoc. fold n.
        replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia).
        rewrite Hfr. unfold u32, u64. rewrite (Z.mod_small (bits + xb sd n)) by lia.
        rewrite Zplus_mod_idemp_l. f_equal. destruct Hbits as [Hb1 _]. rewrite <- Hb1. lia.
      * rewrite L7. destruct (sd_stree sd) as [st|] eqn:Est; [|exact I13].
        rewrite I13. unfold acc_st. rewrite rng_succ by lia. rewrite sumZ_snoc. fold n.
        replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia).
        assert (Hstn := Hst st ltac:(first [exact Est | reflexivity]) h ltac:(lia)). fold n in Hstn.
        rewrite Hfr. unfold u32, u64. rewrite (Z.mod_small (Znth n st + xb sd n)) by lia.
        rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

End Pass1.

(** ** gen_bitlen without overflow: the lengths are the Huffman depths *)

Lemma gen_bitlen_eq : forall sd mc t w,
  gen_bitlen sd mc t w =
  let w1 := w_set_bl_count w (repeat 0 (Z.to_nat (MAX_BITS + 1))) in
  let t1 := set_dl t (Znth (w_heap_max w1) (w_heap w1)) 0 in
  let '(t2, w2, ovf) := gen_bitlen_pass1 (Z.to_nat HEAP_SIZE) sd mc t1 w1 0 (w_heap_max w1 + 1) in
  if ovf =? 0 then (t2, w2)
  else
    let bl_count := gen_bitlen_repair (Z.to_nat HEAP_SIZE) (sd_maxlen sd) (w_bl_count w2) ovf in
    let w3 := w_set_bl_count w2 bl_count in
    let '(t3, opt_len) := gen_bitlen_reassign 20 mc (w_heap w3) bl_count t2 (w_opt_len w3) HEAP_SIZE (sd_maxlen sd) in
    (t3, w_set_opt_len w3 opt_len).
Proof. reflexivity. Qed.

(** ** The first pass on a pre_ok state *)

Section OnPre.
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

Let hmp := w_heap_max w.
Let hp0 := w_heap w.
Let rootp := Znth hmp hp0.
Let w1 := w_set_bl_count w (repeat 0 (Z.to_nat (MAX_BITS + 1))).
Let t1 := set_dl t rootp 0.

Lemma pre_idx : forall p, hmp <= p < HEAP_SIZE -> 0 <= Znth p hp0 < Zlength (dl t).
Proof.
  intros p Hp. destruct (po_kind _ _ _ _ _ _ _ _ _ Hpre p Hp) as [HS|HI]; [|unfold hp0; lia].
  destruct (po_S _ _ _ _ _ _ _ _ _ Hpre) as [_ [_ [HSr _]]]. specialize (HSr _ HS). unfold hp0. lia.
Qed.

Lemma pre_hm : 1 <= hmp < HEAP_SIZE.
Proof. exact (po_hm _ _ _ _ _ _ _ _ _ Hpre). Qed.

Lemma pass1_start : pinv sd mc hmp hp0 (dl t) (fc t) (w_depth w) (w_heap_len w)
                         (w_opt_len w) (w_static_len w) (hmp + 1) t1 w1 0.
Proof.
  assert (Hr := pre_idx hmp ltac:(pose proof pre_hm; lia)). fold rootp in Hr.
  assert (Hrng : rng hmp (hmp + 1) = []) by (unfold rng; replace (Z.to_nat (hmp + 1 - hmp - 1)) with O by lia; reflexivity).
  split; [reflexivity|]. split; [unfold t1, set_dl; simpl; apply Zlength_upd|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { intros q Hq. assert (q = hmp) by lia. subst q. fold rootp.
    unfold t1, set_dl; simpl. rewrite upd_Znth_same by lia.
    rewrite E_root; [lia|exact sd]. }
  split.
  { intros c Hc. assert (Hc' : c <> rootp) by (intros ->; apply (Hc hmp); [lia|reflexivity]).
    unfold t1, set_dl; simpl.
    destruct (Z_le_gt_dec 0 c); [destruct (Z_lt_ge_dec c (Zlength (dl t)))|].
    - rewrite upd_Znth_diff by lia. reflexivity.
    - rewrite !Znth_overflow by (rewrite ?Zlength_upd; lia). reflexivity.
    - rewrite !Znth_underflow by lia. reflexivity. }
  split; [unfold cnt_ovf; rewrite Hrng; reflexivity|].
  split; [reflexivity|].
  split.
  { intros b Hb. unfold cnt_bl. rewrite Hrng.
    change (w_bl_count w1) with (repeat 0 (Z.to_nat (MAX_BITS + 1))).
    rewrite Znth_repeat_inrange by (unfold MAX_BITS; simpl; lia). reflexivity. }
  split; [unfold acc_opt; rewrite Hrng; simpl; unfold u64; rewrite Z.add_0_r; symmetry; apply Z.mod_small; exact Hopt|].
  destruct (sd_stree sd); [|reflexivity]. unfold acc_st. rewrite Hrng. simpl. unfold u64. rewrite Z.add_0_r.
  symmetry; apply Z.mod_small; exact Hstl.
Qed.

Lemma on_nd : NoDup (removed hp0 hmp).
Proof. exact (po_nodup _ _ _ _ _ _ _ _ _ Hpre). Qed.

Lemma on_heap : Zlength hp0 = HEAP_SIZE.
Proof. exact (po_heap _ _ _ _ _ _ _ _ _ Hpre). Qed.

Lemma on_dist : forall p, hmp <= p < HEAP_SIZE ->
  exists e, first_hit (dl t) (Znth p hp0) (Znth hmp hp0) e /\ (e < 573)%nat.
Proof.
  intros p Hp. destruct (region_first_hit sd t0 w0 S F R t w mc Hpre p Hp) as [e [He Hle]].
  exists e. split; [exact He|]. assert (Hle' : (e <= Z.to_nat (p - w_heap_max w))%nat) by exact Hle.
  pose proof pre_hm. unfold hmp in *. unfold HEAP_SIZE in *. lia.
Qed.

Lemma on_dad : forall p, hmp < p < HEAP_SIZE -> exists q, hmp <= q < p /\ Znth q hp0 = Znth (Znth p hp0) (dl t).
Proof.
  intros p Hp. destruct (po_dad _ _ _ _ _ _ _ _ _ Hpre p Hp) as [q [Hq Eq]]. exists q. split; [exact Hq|exact Eq].
Qed.

Lemma on_xb : forall p, hmp <= p < HEAP_SIZE -> 0 <= xb sd (Znth p hp0) <= 16.
Proof. intros p Hp. apply Hxb_sd. apply pre_idx; auto. Qed.

Lemma on_st : forall st, sd_stree sd = Some st -> forall p, hmp <= p < HEAP_SIZE -> 0 <= Znth (Znth p hp0) st <= 16.
Proof. intros st Hs p Hp. apply (Hst_sd st Hs). apply pre_idx; auto. Qed.

Lemma on_fc : forall p, hmp <= p < HEAP_SIZE -> 0 <= Znth (Znth p hp0) (fc t) < 65536.
Proof. intros p Hp. apply Hfc_rng. apply pre_idx; auto. Qed.

Lemma pass1_on_pre :
  let '(t2, w2, ovf) := gen_bitlen_pass1 (Z.to_nat HEAP_SIZE) sd mc t1 w1 0 (hmp + 1) in
  pinv sd mc hmp hp0 (dl t) (fc t) (w_depth w) (w_heap_len w) (w_opt_len w) (w_static_len w) HEAP_SIZE t2 w2 ovf.
Proof.
  pose proof on_nd as A1. pose proof pre_hm as A2. pose proof on_heap as A3. pose proof on_dist as A4.
  pose proof on_dad as A5. pose proof pre_idx as A6. pose proof on_xb as A7. pose proof on_st as A8.
  pose proof on_fc as A9. pose proof pass1_start as A10.
  eapply pass1_correct; eauto; unfold HEAP_SIZE in *; lia.
Qed.

(** The leaves: their positions in the region and their depths. *)
Lemma leaf_in_S : forall l, In l R -> In (lid l) S.
Proof.
  intros l Hl. assert (Hh := po_huff _ _ _ _ _ _ _ _ _ Hpre). assert (Hp := huff_idf _ _ Hh).
  assert (Hin : In (idf l) (map idf R)) by (apply in_map; exact Hl).
  apply (Permutation_in _ (Permutation_sym Hp)) in Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy Hin]].
  unfold leaves in Hin. apply in_concat in Hin. destruct Hin as [I [HyI HI]].
  apply in_map_iff in HI. destruct HI as [x [<- HxS]]. destruct HyI as [<-|[]].
  unfold idf in Hy. simpl in Hy. unfold lid. rewrite <- Hy. exact HxS.
Qed.

Lemma E_leaf : forall l, In l R ->
  exists q, hmp < q < HEAP_SIZE /\ Znth q hp0 = lid l /\ E hmp hp0 (dl t) q = ld l.
Proof.
  intros l Hl.
  destruct (po_depth _ _ _ _ _ _ _ _ _ Hpre l Hl) as [H1 [H2 H3]].
  assert (HlS := leaf_in_S l Hl).
  assert (Hrem := po_inS _ _ _ _ _ _ _ _ _ Hpre _ HlS).
  apply in_removed in Hrem. destruct Hrem as [q [Hq Eq]].
  assert (Hne : q <> hmp).
  { intros ->. apply (H3 O ltac:(lia)). simpl. unfold hmp, hp0 in Eq. rewrite Eq. reflexivity. }
  exists q. split; [unfold hmp in *; lia|]. split; [exact Eq|].
  assert (Hfh : first_hit (dl t) (Znth q hp0) (Znth hmp hp0) (Z.to_nat (ld l))).
  { unfold hp0, hmp in *. rewrite Eq. split; [exact H2|exact H3]. }
  destruct (on_dist q ltac:(unfold hmp in *; lia)) as [e [He Hlt]].
  assert (Ee := first_hit_unique _ _ _ _ _ Hfh He). subst e.
  unfold E. rewrite (fh_first_hit (dl t) (Znth hmp hp0) (Z.to_nat (ld l)) (Znth q hp0) 600 Hfh) by lia. lia.
Qed.

Lemma region_kind : forall p, hmp <= p < HEAP_SIZE -> In (Znth p hp0) S \/ sd_elems sd <= Znth p hp0.
Proof. intros p Hp. destruct (po_kind _ _ _ _ _ _ _ _ _ Hpre p Hp) as [H|H]; [left; exact H|right; unfold hp0; lia]. Qed.

Lemma sumZ_zero_each : forall (g : Z -> Z) l, (forall x, In x l -> 0 <= g x) -> HuffAbs.sumZ (map g l) = 0 ->
  forall x, In x l -> g x = 0.
Proof.
  intros g l Hg. induction l as [|a l IH]; intros Hs x Hx; [destruct Hx|].
  simpl in Hs. assert (H0 := sumZ_nonneg g l ltac:(intros; apply Hg; right; auto)).
  assert (Ha := Hg a (in_eq _ _)). destruct Hx as [<-|Hx]; [lia|]. apply IH; auto; [intros; apply Hg; right; auto|lia].
Qed.

(** The lengths after the first pass: the depth clamped to max_length; zero for unused symbols. *)
Theorem pass1_lengths :
  let '(t2, w2, ovf) := gen_bitlen_pass1 (Z.to_nat HEAP_SIZE) sd mc t1 w1 0 (hmp + 1) in
  fc t2 = fc t /\ Zlength (dl t2) = Zlength (dl t) /\
  w_heap w2 = hp0 /\ w_heap_max w2 = hmp /\ w_heap_len w2 = w_heap_len w /\ w_depth w2 = w_depth w /\
  (forall l, In l R -> Znth (lid l) (dl t2) = Z.min (ld l) (sd_maxlen sd)) /\
  (forall c, 0 <= c < sd_elems sd -> ~ In c S -> Znth c (dl t2) = 0) /\
  (ovf = 0 -> forall l, In l R -> ld l <= sd_maxlen sd).
Proof.
  assert (HP := pass1_on_pre).
  destruct (gen_bitlen_pass1 (Z.to_nat HEAP_SIZE) sd mc t1 w1 0 (hmp + 1)) as [[t2 w2] ovf].
  destruct HP as [I1 [I2 [I3 [I4 [I5 [I6 [I7 [I8 [I9 [I10 [I11 [I12 I13]]]]]]]]]]]].
  split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
  split; [exact I6|].
  split.
  { intros l Hl. destruct (E_leaf l Hl) as [q [Hq [Eq EE]]]. rewrite <- Eq, I7 by lia. unfold E in EE |- *.
    rewrite EE. reflexivity. }
  split.
  { intros c Hc HcS. rewrite I8.
    - apply (po_unused _ _ _ _ _ _ _ _ _ Hpre c Hc HcS).
    - intros q Hq Eq. destruct (region_kind q Hq) as [H|H]; rewrite Eq in H; [contradiction|lia]. }
  intros Hz l Hl. destruct (E_leaf l Hl) as [q [Hq [Eq EE]]].
  assert (Hc := sumZ_zero_each (fun q => if E hmp hp0 (dl t) q >? sd_maxlen sd then 1 else 0) (rng hmp HEAP_SIZE)).
  unfold cnt_ovf in I9. rewrite <- I9 in Hc. specialize (Hc ltac:(intros x _; destruct (_ >? _); lia) Hz q).
  assert (Hqr : In q (rng hmp HEAP_SIZE)) by (unfold rng; apply in_zseq; lia).
  specialize (Hc Hqr). simpl in Hc. rewrite EE in Hc. destruct (Z.gtb_spec (ld l) (sd_maxlen sd)); [discriminate|lia].
Qed.

(** ** The overflow count and the Kraft sum of the clamped lengths *)

Definition Nall := removed hp0 hmp.
Definition Nn := removed hp0 (hmp + 1).
Definition ev (v : Z) : Z := fh 600 (dl t) (Znth hmp hp0) v.
Definition dad (v : Z) : Z := Znth v (dl t).

Lemma Nall_cons : Nall = Znth hmp hp0 :: Nn.
Proof.
  unfold Nall, Nn. pose proof pre_hm. replace hmp with (hmp + 1 - 1) at 1 by lia.
  rewrite removed_cons by lia. f_equal. f_equal. lia.
Qed.

Lemma Nn_rng : Nn = map (fun q => Znth q hp0) (rng hmp HEAP_SIZE).
Proof. unfold Nn, removed, rng. f_equal. f_equal. lia. Qed.

Lemma in_Nn : forall v, In v Nn <-> exists p, hmp < p < HEAP_SIZE /\ Znth p hp0 = v.
Proof.
  intros v. unfold Nn. rewrite in_removed. split; intros [p [Hp E]]; exists p; split; auto; lia.
Qed.

Lemma Nall_nodup : NoDup Nall.
Proof. exact on_nd. Qed.

Lemma dad_in : forall v, In v Nn -> In (dad v) Nall.
Proof.
  intros v Hv. apply in_Nn in Hv. destruct Hv as [p [Hp <-]].
  destruct (on_dad p Hp) as [q [Hq Eq]]. unfold dad. rewrite <- Eq. unfold Nall. apply in_removed. exists q. split; [lia|reflexivity].
Qed.

Lemma ev_pos : forall p, hmp <= p < HEAP_SIZE -> exists e, first_hit (dl t) (Znth p hp0) (Znth hmp hp0) e /\ (e < 573)%nat /\ ev (Znth p hp0) = Z.of_nat e.
Proof.
  intros p Hp. destruct (on_dist p Hp) as [e [He Hlt]]. exists e. split; [exact He|]. split; [exact Hlt|].
  unfold ev. apply fh_first_hit; auto. lia.
Qed.

Lemma ev_dad : forall v, In v Nn -> ev v = ev (dad v) + 1.
Proof.
  intros v Hv. apply in_Nn in Hv. destruct Hv as [p [Hp <-]].
  destruct (on_dad p Hp) as [q [Hq Eq]].
  destruct (ev_pos q ltac:(lia)) as [e [He [Hlt Ee]]].
  assert (Hne : Znth p hp0 <> Znth hmp hp0).
  { intros Hc. apply (removed_Znth_inj hp0 hmp p hmp on_nd) in Hc; [lia|lia|]. pose proof pre_hm. lia. }
  assert (Hfh : first_hit (dl t) (Znth p hp0) (Znth hmp hp0) (Datatypes.S e))
    by (apply first_hit_step; auto; rewrite <- Eq; exact He).
  unfold dad. rewrite <- Eq. rewrite Ee. unfold ev. rewrite (fh_first_hit _ _ (Datatypes.S e)) by (auto; lia). lia.
Qed.

Lemma ev_root : ev (Znth hmp hp0) = 0.
Proof. unfold ev. apply (fh_first_hit (dl t) (Znth hmp hp0) O); [split; [reflexivity|intros; lia]|lia]. Qed.

Lemma ev_nonneg : forall v, In v Nall -> 0 <= ev v.
Proof.
  intros v Hv. unfold Nall in Hv. apply in_removed in Hv. destruct Hv as [p [Hp <-]].
  destruct (ev_pos p Hp) as [e [_ [_ ->]]]. lia.
Qed.

Lemma Zlength_filter_sumZ : forall (f : Z -> bool) l,
  Zlength (filter f l) = HuffAbs.sumZ (map (fun x => if f x then 1 else 0) l).
Proof.
  intros f l. induction l as [|a l IH]; [reflexivity|]. simpl. destruct (f a); rewrite ?Zlength_cons, IH; lia.
Qed.

Lemma nkids_kids : forall y, In y Nall -> nkids Nn dad y = if sd_elems sd <=? y then 2 else 0.
Proof.
  intros y Hy. rewrite <- (po_kids _ _ _ _ _ _ _ _ _ Hpre y Hy). unfold kids, nkids.
  rewrite Zlength_filter_sumZ. reflexivity.
Qed.

(** The number of internal nodes at depth >= max_length. *)
Definition Ideep : Z :=
  HuffAbs.sumZ (map (fun y => if (sd_elems sd <=? y) && (sd_maxlen sd <=? ev y) then 1 else 0) Nall).

Theorem ovf_twice : HuffAbs.sumZ (map (fun v => if ev v >? sd_maxlen sd then 1 else 0) Nn) = 2 * Ideep.
Proof.
  rewrite (sumZ_map_ext _ (fun v => (fun y => if ev y + 1 >? sd_maxlen sd then 1 else 0) (dad v)) Nn).
  2:{ intros v Hv. rewrite (ev_dad v Hv). reflexivity. }
  eapply eq_trans; [apply (double_count_const Nall Nn dad (fun y => if ev y + 1 >? sd_maxlen sd then 1 else 0) Nall_nodup dad_in)|].
  unfold Ideep. rewrite <- sumZ_map_scal. apply sumZ_map_ext. intros y Hy. rewrite nkids_kids by exact Hy.
  destruct (sd_elems sd <=? y), (Z.gtb_spec (ev y + 1) (sd_maxlen sd)), (Z.leb_spec (sd_maxlen sd) (ev y));
    simpl; lia.
Qed.

Definition gcl (x : Z) : Z := 2 ^ (sd_maxlen sd - Z.min x (sd_maxlen sd)).

Lemma gcl_twice : forall x, 0 <= x -> 2 * gcl (x + 1) = gcl x + (if sd_maxlen sd <=? x then 1 else 0).
Proof.
  intros x Hx. unfold gcl. destruct (Z.leb_spec (sd_maxlen sd) x).
  - rewrite !Z.min_r by lia. rewrite Z.sub_diag. simpl. lia.
  - rewrite !Z.min_l by lia. replace (sd_maxlen sd - x) with (Z.succ (sd_maxlen sd - (x + 1))) by lia.
    rewrite Z.pow_succ_r by lia. lia.
Qed.

Theorem kraft_clamped :
  HuffAbs.sumZ (map (fun v => if v <? sd_elems sd then gcl (ev v) else 0) Nn) = 2 ^ sd_maxlen sd + Ideep.
Proof.
  (* sum over Nn of gcl = sum over parents *)
  assert (E1 : HuffAbs.sumZ (map (fun v => gcl (ev v)) Nn) =
               HuffAbs.sumZ (map (fun y => if sd_elems sd <=? y then gcl (ev y) + (if sd_maxlen sd <=? ev y then 1 else 0) else 0) Nall)).
  { rewrite (sumZ_map_ext _ (fun v => (fun y => gcl (ev y + 1)) (dad v)) Nn).
    2:{ intros v Hv. rewrite (ev_dad v Hv). reflexivity. }
    eapply eq_trans; [apply (double_count_const Nall Nn dad (fun y => gcl (ev y + 1)) Nall_nodup dad_in)|].
    apply sumZ_map_ext. intros y Hy. rewrite nkids_kids by exact Hy.
    destruct (sd_elems sd <=? y); [|lia]. rewrite <- gcl_twice by (apply ev_nonneg; exact Hy). lia. }
  (* split the sum over Nn into leaves and internal nodes *)
  assert (E2 : HuffAbs.sumZ (map (fun v => gcl (ev v)) Nn) =
               HuffAbs.sumZ (map (fun v => if v <? sd_elems sd then gcl (ev v) else 0) Nn) +
               HuffAbs.sumZ (map (fun v => if sd_elems sd <=? v then gcl (ev v) else 0) Nn)).
  { rewrite <- sumZ_map_add. apply sumZ_map_ext. intros v _. destruct (Z.ltb_spec v (sd_elems sd)), (Z.leb_spec (sd_elems sd) v); lia. }
  (* the parents' sum: the root plus the internal nodes of Nn *)
  assert (Hroot_int : sd_elems sd <= Znth hmp hp0).
  { destruct (region_kind hmp ltac:(pose proof pre_hm; lia)) as [HS|HI]; [|exact HI].
    exfalso. (* the root is not a leaf: every leaf of R is at depth >= 1 below the root *)
    destruct (huff_leaf_of S (fun x => Znth x (fc t)) R (Znth hmp hp0) (po_huff _ _ _ _ _ _ _ _ _ Hpre) HS) as [l [Hl Hlid]].
    destruct (po_depth _ _ _ _ _ _ _ _ _ Hpre l Hl) as [H1 [H2 H3]].
    apply (H3 O ltac:(lia)). simpl. rewrite Hlid. reflexivity. }
  assert (E3a : forall l, HuffAbs.sumZ (map (fun y => if sd_elems sd <=? y then gcl (ev y) + (if sd_maxlen sd <=? ev y then 1 else 0) else 0) l)
     = HuffAbs.sumZ (map (fun y => if sd_elems sd <=? y then gcl (ev y) else 0) l) +
       HuffAbs.sumZ (map (fun y => if (sd_elems sd <=? y) && (sd_maxlen sd <=? ev y) then 1 else 0) l)).
  { intros l. rewrite <- sumZ_map_add. apply sumZ_map_ext. intros y _.
    destruct (sd_elems sd <=? y), (sd_maxlen sd <=? ev y); simpl; lia. }
  assert (E3b : HuffAbs.sumZ (map (fun y => if sd_elems sd <=? y then gcl (ev y) else 0) Nall)
     = 2 ^ sd_maxlen sd + HuffAbs.sumZ (map (fun v => if sd_elems sd <=? v then gcl (ev v) else 0) Nn)).
  { rewrite Nall_cons. cbn [map HuffAbs.sumZ].
    replace (sd_elems sd <=? Znth hmp hp0) with true by (symmetry; apply Z.leb_le; exact Hroot_int).
    rewrite ev_root. unfold gcl at 1. replace (Z.min 0 (sd_maxlen sd)) with 0 by lia. rewrite Z.sub_0_r. reflexivity. }
  specialize (E3a Nall). unfold Ideep. lia.
Qed.

End OnPre.
