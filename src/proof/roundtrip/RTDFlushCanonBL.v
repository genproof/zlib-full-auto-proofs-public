(* RT-D FLUSH part CANON, sub-part BL: after build_tree, bl_count (the w_bl_count the final
   gen_codes call of build_tree uses) holds exactly the number of symbols of the tree of each length. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.BtSpec.
From Coq Require Import Permutation.
Require Import Zlib.proof.huffman.Heap Zlib.proof.huffman.Bits Zlib.proof.huffman.BuildTree Zlib.proof.huffman.BuildKids Zlib.proof.huffman.BuildPre Zlib.proof.huffman.Bitlen Zlib.proof.huffman.DCount Zlib.proof.huffman.GenCodes Zlib.proof.huffman.HuffFib2 Zlib.proof.huffman.Repair Zlib.proof.huffman.BuildThm.
Import ListNotations.
Local Open Scope Z_scope.

(** The number of copies of [b] in [lseq c k]. *)
Lemma lseq_count : forall c k b, (forall l, 1 <= l <= Z.of_nat k -> 0 <= Znth l c) ->
  cntz (fun x => x =? b) (lseq c k) = if (1 <=? b) && (b <=? Z.of_nat k) then Znth b c else 0.
Proof.
  intros c k b; induction k as [|k IH]; intros H.
  - unfold cntz. simpl length. destruct (Z.leb_spec 1 b); destruct (Z.leb_spec b (Z.of_nat 0)); simpl; try reflexivity; lia.
  - cbn [lseq]. unfold cntz in *. rewrite filter_app, app_length, Nat2Z.inj_add, IH by (intros; apply H; lia).
    assert (Hr : forall n v, filter (fun x => x =? b) (repeat v n) = if v =? b then repeat v n else []).
    { intros n v. induction n as [|n IHn]; simpl; [destruct (v =? b); reflexivity|].
      rewrite IHn. destruct (v =? b); reflexivity. }
    rewrite Hr. destruct (Z.eqb_spec (Z.of_nat (S k)) b) as [<-|Hne].
    + rewrite repeat_length, Z2Nat.id by (apply H; lia).
      replace ((1 <=? Z.of_nat (S k)) && (Z.of_nat (S k) <=? Z.of_nat k)) with false
        by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
      replace ((1 <=? Z.of_nat (S k)) && (Z.of_nat (S k) <=? Z.of_nat (S k))) with true
        by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
      lia.
    + simpl length. rewrite Z.add_0_l.
      destruct (1 <=? b) eqn:E1; [rewrite !andb_true_l|reflexivity].
      destruct (Z.leb_spec b (Z.of_nat k)), (Z.leb_spec b (Z.of_nat (S k))); try reflexivity; lia.
Qed.

(** g_genbitlen's bl_count: the number of symbols of each length, under the assumptions of BuildThm.g_genbitlen. *)
Lemma g_genbitlen_bl : forall sd (t0 : tree) (w0 : work) (S F : list Z) (R : item) (t : tree) (w : work) (mc : Z),
  pre_ok sd t0 w0 S F R t w mc ->
  1 <= sd_maxlen sd <= 15 ->
  3 <= sd_elems sd <= 286 ->
  sd_elems sd <= Zlength (dl t) ->
  (forall n, 0 <= n < Zlength (dl t) -> 0 <= xb sd n <= 16) ->
  (forall st, sd_stree sd = Some st -> forall n, 0 <= n < Zlength (dl t) -> 0 <= Znth n st <= 16) ->
  (forall n, 0 <= n < Zlength (dl t) -> 0 <= Znth n (fc t) < 65536) ->
  0 <= w_opt_len w < 18446744073709551616 ->
  0 <= w_static_len w < 18446744073709551616 ->
  sd_elems sd <= 2 ^ sd_maxlen sd ->
  let '(t3, w3) := gen_bitlen sd mc t w in
  forall b, 0 <= b < 16 -> Znth b (w_bl_count w3) = sumZ (map (fun x => if Znth x (dl t3) =? b then 1 else 0) S).
Proof.
  intros sd t0 w0 S F R t w mc Hpre HM Hel Hdlen Hxb_sd Hst_sd Hfc_rng Hopt Hstl Hel2.
  rewrite gen_bitlen_eq. cbv zeta.
  assert (G := g_pass1 sd t0 w0 S F R t w mc Hpre HM Hel Hdlen Hxb_sd Hst_sd Hfc_rng Hopt Hstl).
  destruct (gen_bitlen_pass1 _ _ _ _ _ _ _) as [[t2 w2] ovf].
  destruct G as [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 [G9 [G10 [G11 [G12 [G13 G14]]]]]]]]]]]]].
  destruct (Z.eqb_spec ovf 0) as [Hz|Hnz].
  - (* no overflow *)
    intros b Hb. rewrite G12 by exact Hb. apply sumZ_map_ext. intros x Hx. rewrite G7 by exact Hx. reflexivity.
  - (* overflow: the repair and the reassignment *)
    assert (HnD : ~ (forall l, In l R -> ld l <= sd_maxlen sd)).
    { intros HD. apply Hnz. rewrite G9, (g_noovf_ideep sd t0 w0 S F R t w mc Hpre HM HD). lia. }
    set (c := clampc (sd_maxlen sd) (BuildThm.dlist R w mc)).
    assert (Hbl : w_bl_count w2 = c).
    { apply Znth_eq_ext; [rewrite G11; unfold c; rewrite clampc_len; reflexivity|].
      intros b Hb. rewrite G11 in Hb. rewrite G12 by lia. apply (g_clampc sd t0 w0 S F R t w mc Hpre HM). lia. }
    assert (Hdl : Zlength (BuildThm.dlist R w mc) <= 2 ^ sd_maxlen sd /\ Zlength (BuildThm.dlist R w mc) <= 573)
      by (rewrite (g_d_len sd t0 w0 S F R t w mc Hpre HM); pose proof (g_S_len sd t0 w0 S F R t w mc Hpre HM Hel); lia).
    destruct (clamp_rinv (sd_maxlen sd) 600 (BuildThm.dlist R w mc) HM ltac:(lia) (g_d_range sd t0 w0 S F R t w mc Hpre HM)
                (g_d_kraft sd t0 w0 S F R t w mc Hpre HM) (proj1 Hdl) (proj2 Hdl)
                (g_deep_exists sd t0 w0 S F R t w mc Hpre HM HnD)) as [HI1 Hinv].
    fold c in HI1, Hinv. set (I := kraftc (sd_maxlen sd) c - 2 ^ sd_maxlen sd) in *.
    assert (HI : I = Ideep sd t w) by (unfold I, c; rewrite (g_kraftc sd t0 w0 S F R t w mc Hpre HM); lia).
    assert (Hovf : ovf = 2 * I) by (rewrite G9, HI; reflexivity).
    rewrite Hbl, Hovf.
    destruct (repair_correct (sd_maxlen sd) c I HM HI1 Hinv) as [_ [R1 [R2 [R3 [R4 [R5 R6]]]]]].
    assert (Hrepl := repl_model (sd_maxlen sd) (BuildThm.dlist R w mc) I HM eq_refl HI1 Hinv). fold c in Hrepl.
    destruct (repaired_lens (sd_maxlen sd) c I HM HI1 Hinv) as [RL1 [RL2 RL3]].
    set (c' := gen_bitlen_repair (Z.to_nat HEAP_SIZE) (sd_maxlen sd) c (2 * I)) in *.
    rewrite Hrepl in RL1, RL2, RL3.
    assert (Htot : tot (sd_maxlen sd) c = Zlength (BuildThm.dlist R w mc))
      by (apply (clamp_sums (sd_maxlen sd) (BuildThm.dlist R w mc) HM); intros x Hx; apply (g_d_range sd t0 w0 S F R t w mc Hpre HM); exact Hx).
    assert (Hord_len : Zlength (BuildThm.order w mc) = Zlength (BuildThm.dlist R w mc)) by (unfold BuildThm.dlist; rewrite Zlength_map; reflexivity).
    assert (Hscan : scan (w_heap (w_set_bl_count w2 c')) mc HEAP_SIZE (Z.to_nat (HEAP_SIZE - w_heap_max w - 1)) = (BuildThm.order w mc))
      by (simpl; rewrite G3; reflexivity).
    rewrite (reassign_correct mc (w_heap (w_set_bl_count w2 c')) c' t2 (w_opt_len (w_set_bl_count w2 c')) (sd_maxlen sd)
               (Z.to_nat (HEAP_SIZE - w_heap_max w - 1)) HM); [| intros; apply R2; lia
               | pose proof (pre_hm _ _ _ _ _ _ _ _ _ Hpre); unfold HEAP_SIZE in *; lia
               | rewrite Hscan, R5, Htot, <- Hord_len, Zlength_correct; lia].
    rewrite Hscan, R5, Htot, <- Hord_len, ZtoNat_Zlength, firstn_all. fold (lens (sd_maxlen sd) c').
    assert (Hlc := lseq_count c' (Z.to_nat (sd_maxlen sd))). fold (lens (sd_maxlen sd) c') in Hlc.
    rewrite Hrepl in Hlc |- *.
    assert (Hlens_len : length (BuildThm.order w mc) = length (repl (sd_maxlen sd) (BuildThm.dlist R w mc))).
    { apply Nat2Z.inj. rewrite <- !Zlength_correct. rewrite RL1, Htot. exact Hord_len. }
    destruct (apply_lens_spec (BuildThm.order w mc) (repl (sd_maxlen sd) (BuildThm.dlist R w mc)) t2 (w_opt_len (w_set_bl_count w2 c'))
                (g_order_nodup sd t0 w0 S F R t w mc Hpre HM) Hlens_len)
      as [A1 [A2 [A3 [A4 A5]]]].
    { intros m Hm. apply (Permutation_in _ (g_order_perm sd t0 w0 S F R t w mc Hpre HM)) in Hm.
      destruct (g_S sd t0 w0 S F R t w mc Hpre) as [_ [_ Hr]]. specialize (Hr m Hm).
      rewrite G2. lia. }
    { intros l Hl. specialize (RL2 l Hl). lia. }
    { simpl. unfold u64 in G13. rewrite G13. apply Z.mod_pos_bound. lia. }
    destruct (apply_lens (BuildThm.order w mc) (repl (sd_maxlen sd) (BuildThm.dlist R w mc)) t2 (w_opt_len (w_set_bl_count w2 c'))) as [t3 opt3].
    cbn [fst snd] in A1, A2, A3, A4, A5.
    assert (Hmap : map (fun x => Znth x (dl t3)) (BuildThm.order w mc) = repl (sd_maxlen sd) (BuildThm.dlist R w mc)).
    { apply Znth_eq_ext; [rewrite Zlength_map, !Zlength_correct, Hlens_len; reflexivity|].
      intros k Hk. rewrite Zlength_map in Hk. rewrite Znth_map by exact Hk. apply A3. exact Hk. }
    intros b Hb. cbn [w_bl_count w_set_opt_len w_set_bl_count].
    rewrite <- (g_sum_order sd t0 w0 S F R t w mc Hpre HM (fun x => if Znth x (dl t3) =? b then 1 else 0)).
    rewrite <- (map_map (fun x => Znth x (dl t3)) (fun l => if l =? b then 1 else 0)), Hmap, <- cntz_sumZ.
    rewrite Hlc by (intros; apply R2; lia). rewrite Z2Nat.id by lia.
    destruct ((1 <=? b) && (b <=? sd_maxlen sd)) eqn:Eb; [reflexivity|].
    rewrite R6 by (first [exact Hb | apply andb_false_iff in Eb; destruct Eb as [E|E]; apply Z.leb_gt in E; lia]).
    unfold c. rewrite <- (g_clampc sd t0 w0 S F R t w mc Hpre HM) by exact Hb.
    rewrite (sumZ_map_ext _ (fun _ => 0)); [apply sumZ_map_zero|].
    intros x Hx. destruct (g_depth_S sd t0 w0 S F R t w mc Hpre x Hx) as [l [Hl [_ ->]]].
    assert (H := g_ld_bound sd t0 w0 S F R t w mc Hpre l Hl).
    apply andb_false_iff in Eb.
    destruct (Z.eqb_spec (Z.min (ld l) (sd_maxlen sd)) b); [|reflexivity].
    destruct Eb as [E|E]; apply Z.leb_gt in E; lia.
Qed.

(* BuildThm.build_tree_correct, plus: bl_count[b] = #{x in S : Len x = b} for 0 <= b < 16.
   No overflow: counted by gen_bitlen's first pass (BuildThm.g_pass1, conjunct on w_bl_count, with
   Len x = min(depth, max_length) = depth).  Overflow: bl_count is the repaired count c' (gen_bitlen_repair) and
   gen_bitlen_reassign hands out the lengths Repair.lens M c' along the heap order (BuildThm.g_genbitlen's proof:
   Hrepl, reassign_correct, apply_lens_spec, Hmap: map Len order = lens M c'); count of b in lseq c' M is c'[b]. *)
Definition bt_counts_stmt : Prop :=
  forall sd t w, bt_req sd t w ->
    let '(t', mc, w') := build_tree sd t w in
    exists S F order R, bt_facts sd t w S F order R t' mc w' /\
      forall b, 0 <= b < 16 ->
        Znth b (w_bl_count w') = HuffAbs.sumZ (map (fun x => if Znth x (dl t') =? b then 1 else 0) S).

Theorem bt_counts_ok : bt_counts_stmt.
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
  assert (GB := g_genbitlen_bl sd t w S F R t1 w1 mc Hpo HM Hel Hdlen Hxb1 Hst1 Hfc1 Hopt1 Hstl1 Hpow).
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
  split.
  2:{ intros b Hb. rewrite GB by exact Hb. apply sumZ_map_ext. intros x _. rewrite C1. reflexivity. }
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
