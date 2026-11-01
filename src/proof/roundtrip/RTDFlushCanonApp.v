(* RT-D FLUSH part CANON: from the sub-parts GC (gen_codes is canonical given exact counts) and BL
   (build_tree's bl_count is the count of its lengths): the trees flush_prep builds carry canonical codes. *)
From Coq Require Import ZArith List Lia Bool Permutation.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap Zlib.proof.huffman.Bits Zlib.proof.huffman.Overlay Zlib.proof.huffman.BuildPre Zlib.proof.huffman.Repair Zlib.proof.huffman.BtSpec Zlib.proof.huffman.BuildThm Zlib.proof.huffman.GenCodes Zlib.proof.huffman.FlushDyn.
Require Zlib.proof.huffman.Header Zlib.proof.huffman.FlushTree.
Require Zlib.proof.huffman.Cert Zlib.proof.huffman.FlushStream Zlib.proof.huffman.FlushHdr.
Require Import Zlib.proof.roundtrip.RTDFlushCanonGC Zlib.proof.roundtrip.RTDFlushCanonBL.
Module Hd := Zlib.proof.huffman.Header.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Generic facts *)

Lemma gcl_dl : forall f mc t nc n, dl (gen_codes_loop f mc t nc n) = dl t.
Proof.
  induction f as [|f IH]; intros mc t nc n; simpl; [reflexivity|].
  destruct (n <=? mc); [|reflexivity]. destruct (Znth n (dl t) =? 0); rewrite IH; reflexivity.
Qed.

Lemma build_tree_shape0 : forall sd t w, exists t3,
  fst (fst (build_tree sd t w)) = gen_codes t3 (snd (fst (build_tree sd t w))) (w_bl_count (snd (build_tree sd t w))).
Proof.
  intros sd t w. unfold build_tree.
  repeat match goal with |- context [match ?e with pair _ _ => _ end] => destruct e end.
  eexists; reflexivity.
Qed.

Lemma build_tree_shape : forall sd t w,
  let '(t', mc, w') := build_tree sd t w in exists t3, t' = gen_codes t3 mc (w_bl_count w').
Proof.
  intros sd t w. destruct (build_tree_shape0 sd t w) as [t3 E].
  destruct (build_tree sd t w) as [[t' mc] w']. exists t3. exact E.
Qed.

Lemma filter_map_len : forall (p : Z -> bool) (f : Z -> Z) l,
  Zlength (filter p (map f l)) = sumZ (map (fun i => if p (f i) then 1 else 0) l).
Proof.
  intros p f l. induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (p (f a)); rewrite ?Zlength_cons; lia.
Qed.

Lemma sublist_zseq : forall (lens : list Z) n a, 0 <= a -> a + Z.of_nat n <= Zlength lens ->
  sublist a (a + Z.of_nat n) lens = map (fun i => Znth i lens) (zseq a n).
Proof.
  intros lens n. induction n as [|n IH]; intros a Ha Hn.
  - simpl. rewrite Z.add_0_r, sublist_nil. reflexivity.
  - simpl. rewrite (sublist_split a (a + 1) (a + Z.of_nat (S n))) by lia.
    rewrite sublist_one by lia. rewrite <- IH by lia. simpl. f_equal. f_equal. lia.
Qed.

Lemma sumZ_zero : forall (g : Z -> Z) l, (forall x, In x l -> g x = 0) -> sumZ (map g l) = 0.
Proof.
  intros g l H. induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite H by (left; auto). rewrite IH by (intros; apply H; right; auto). lia.
Qed.

Lemma count_conv : forall (Sx lens : list Z) mc b,
  NoDup Sx -> (forall x, In x Sx -> 0 <= x <= mc) -> mc < Zlength lens ->
  (forall x, 0 <= x <= mc -> ~ In x Sx -> Znth x lens = 0) ->
  (forall x, In x Sx -> 1 <= Znth x lens) ->
  sumZ (map (fun x => if Znth x lens =? b then 1 else 0) Sx) = F.count_of (sublist 0 (mc + 1) lens) b.
Proof.
  intros Sx lens mc b Hnd Hr Hlt Hout Hin. unfold F.count_of.
  destruct (Z.eqb_spec b 0) as [-> | Hb].
  - apply sumZ_zero. intros x Hx. specialize (Hin x Hx). destruct (Z.eqb_spec (Znth x lens) 0); lia.
  - assert (Hmc : 0 <= mc \/ Sx = []).
    { destruct Sx as [|y rest]; [right; reflexivity|left]. specialize (Hr y (or_introl eq_refl)). lia. }
    destruct Hmc as [Hmc| ->].
    2:{ simpl. destruct (Z_lt_dec mc 0).
        - rewrite sublist_nil_gen by lia. reflexivity.
        - replace (mc + 1) with (0 + Z.of_nat (Z.to_nat (mc + 1))) by lia. rewrite sublist_zseq by lia.
          rewrite filter_map_len. symmetry. apply sumZ_zero. intros x Hx. apply in_zseq in Hx.
          rewrite Hout by (simpl; lia). destruct (Z.eqb_spec 0 b); lia. }
    replace (mc + 1) with (0 + Z.of_nat (Z.to_nat (mc + 1))) by lia. rewrite sublist_zseq by lia.
    rewrite filter_map_len. symmetry. replace (0 + Z.of_nat (Z.to_nat (mc + 1))) with (mc + 1) by lia.
    apply (FlushTree.zseq_sum_support Sx (fun x => if Znth x lens =? b then 1 else 0) (mc + 1) Hnd).
    + intros x Hx. specialize (Hr x Hx). lia.
    + intros x Hx HxS. rewrite Hout by (auto; lia). destruct (Z.eqb_spec 0 b); lia.
Qed.

Lemma count_of_app0 : forall lens z l, (forall y, In y z -> y = 0) -> F.count_of (lens ++ z) l = F.count_of lens l.
Proof.
  intros lens z l Hz. unfold F.count_of. destruct (Z.eqb_spec l 0) as [_|Hl]; [reflexivity|].
  rewrite filter_app. replace (filter (fun x => x =? l) z) with (@nil Z).
  - rewrite app_nil_r. reflexivity.
  - induction z as [|a z IH]; simpl; [reflexivity|].
    rewrite (Hz a (or_introl eq_refl)). destruct (Z.eqb_spec 0 l); [lia|]. apply IH. intros; apply Hz; right; auto.
Qed.

Lemma next_code_n_ext : forall a b n, (forall l, F.count_of a l = F.count_of b l) -> F.next_code_n a n = F.next_code_n b n.
Proof. intros a b n H. induction n as [|n IH]; simpl; [reflexivity|]. rewrite IH, H. reflexivity. Qed.

Lemma send_sym_app0 : forall lens z x, 0 <= x < Zlength lens -> (forall y, In y z -> y = 0) ->
  F.send_sym (lens ++ z) x = F.send_sym lens x.
Proof.
  intros lens z x Hx Hz. unfold F.send_sym, F.code.
  rewrite app_Znth1 by lia. rewrite sublist_app1 by lia.
  rewrite (next_code_n_ext (lens ++ z) lens) by (intros; apply count_of_app0; auto). reflexivity.
Qed.

(** ** One built tree *)

Lemma bt_canon : forall sd t w, bt_req sd t w ->
  let '(t', mc, w') := build_tree sd t w in
  forall x, 0 <= x <= mc -> Znth x (dl t') <> 0 ->
    F.bits_le (Znth x (fc t')) (Znth x (dl t')) = F.send_sym (sublist 0 (mc + 1) (dl t')) x.
Proof.
  intros sd t w HR. assert (B := bt_counts_ok sd t w HR). assert (Sh := build_tree_shape sd t w).
  destruct (build_tree sd t w) as [[t' mc] w'].
  destruct Sh as [t3 E]. destruct B as [S [F0 [ord [R [BF Hc]]]]].
  destruct HR as [[Hel [HM Hpow]] [HTS HTS2] _ _ _ _].
  destruct (bt_lens _ _ _ _ _ _ _ _ _ _ BF ltac:(lia)) as [Hmc Hll].
  assert (Hdl : dl t' = dl t3) by (rewrite E; unfold gen_codes; apply gcl_dl).
  destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ BF) as [Z1 [Z2 _]].
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ BF) as [_ [Hnd [HSr _]]].
  destruct (bt_mc _ _ _ _ _ _ _ _ _ _ BF) as [_ HSm].
  assert (Hlen3 : forall i, 0 <= i <= mc -> Znth i (dl t3) <> 0 -> 1 <= Znth i (dl t3) <= 15).
  { intros i Hi Hnz. rewrite <- Hdl in *. specialize (Hll i Hi). lia. }
  destruct (gen_codes_spec t3 mc (w_bl_count w') ltac:(unfold HEAP_SIZE; lia) Hlen3) as [C1 [C2 _]].
  rewrite <- E in C1, C2.
  intros x Hx Hnz. rewrite E at 1. rewrite Hdl in *.
  assert (A1 : 0 <= mc < HEAP_SIZE) by (unfold HEAP_SIZE; lia).
  assert (A2 : mc < Zlength (fc t3)) by (rewrite <- C2, Z1; lia).
  assert (A3 : mc < Zlength (dl t3)) by (rewrite Z2; lia).
  assert (A4 : forall l, 0 <= l <= 15 -> Znth l (w_bl_count w') = F.count_of (sublist 0 (mc + 1) (dl t3)) l).
  { intros l Hl. rewrite Hc by lia. apply count_conv; auto.
    + intros y Hy. split; [apply HSr in Hy; lia|apply HSm; exact Hy].
    + intros y Hy HyS. rewrite <- Hdl. apply (bt_len_out _ _ _ _ _ _ _ _ _ _ BF); [lia|exact HyS].
    + intros y Hy. rewrite <- Hdl. apply (bt_len_in _ _ _ _ _ _ _ _ _ _ BF y Hy). }
  exact (gc_canon_ok t3 mc (w_bl_count w') A1 A2 A3 Hll A4 x Hx Hnz).
Qed.

(** ** The three trees of flush_prep (the proof follows FlushDyn.dyn_prep's) *)

Definition canon_concl (s' : tstate) : Prop :=
  (forall x, 0 <= x <= tr_lmax s' -> Znth x (dl (tr_ltree s')) <> 0 ->
     F.bits_le (Znth x (fc (tr_ltree s'))) (Znth x (dl (tr_ltree s'))) =
     F.send_sym (sublist 0 (tr_lmax s' + 1) (dl (tr_ltree s'))) x) /\
  (forall x, 0 <= x <= tr_dmax s' -> Znth x (dl (tr_dtree s')) <> 0 ->
     F.bits_le (Znth x (fc (tr_dtree s'))) (Znth x (dl (tr_dtree s'))) =
     F.send_sym (sublist 0 (tr_dmax s' + 1) (dl (tr_dtree s'))) x) /\
  (forall x, 0 <= x < 19 -> Znth x (dl (tr_bltree s')) <> 0 ->
     F.bits_le (Znth x (fc (tr_bltree s'))) (Znth x (dl (tr_bltree s'))) =
     F.send_sym (sublist 0 19 (dl (tr_bltree s'))) x).

Theorem canon_prep : forall s syms stored_len, flush_pre s syms -> 0 < tr_level s ->
  let '(s', olb, slb, mbi) := flush_prep s stored_len in canon_concl s'.
Proof.
  intros s syms stored_len Hfp Hlev.
  destruct Hfp as [HL [Hok [Hp0 [Hbv Hob]]] [Hsn [Hsl [Hval Hsy]]] [Hl1 [Hl2 [Hl3 Hl4]]] [Hd1 [Hd2 [Hd3 Hd4]]]
                  [Hb1 [Hb2 [Hb3 Hb4]]] [Hw1 [Hw2 [Hw3 [Hw4 Hw5]]]]].
  assert (HLB : tr_lit_bufsize s <= 32768).
  { destruct HL as [ml [Hml E]]. rewrite E. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  pose proof (Zlength_nonneg syms) as Hn0.
  unfold flush_prep. replace (tr_level s >? 0) with true by (symmetry; apply Z.gtb_lt; lia).
  set (s0 := if tr_data_type s =? Z_UNKNOWN then set_data_type s (detect_data_type (fc (tr_ltree s))) else s).
  assert (E0 : tr_ltree s0 = tr_ltree s /\ tr_dtree s0 = tr_dtree s /\ tr_bltree s0 = tr_bltree s /\
               tr_wk s0 = tr_wk s /\ tr_out s0 = tr_out s /\ tr_lit_bufsize s0 = tr_lit_bufsize s /\
               tr_sym_next s0 = tr_sym_next s /\ tr_strategy s0 = tr_strategy s)
    by (unfold s0; destruct (tr_data_type s =? Z_UNKNOWN); repeat split).
  clearbody s0. destruct E0 as [E1 [E2 [E3 [E4 [E5 [E6 [E7 E8]]]]]]].
  rewrite E1, E4.
  (* the literal/length tree *)
  assert (RL : bt_req static_l_desc (tr_ltree s) (tr_wk s)).
  { constructor.
    - cbn; unfold L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; cbn; lia.
    - cbn. unfold HEAP_SIZE in *. lia.
    - rewrite Hw1, Hw2, Hw4, Hw5. unfold HEAP_SIZE. lia.
    - rewrite Hl1. exact Hl3.
    - split.
      + intros x Hx. cbn in Hx. apply Hl3. unfold HEAP_SIZE, L_CODES in *. lia.
      + cbn [sd_elems static_l_desc].
        rewrite (map_ext_in _ (fun x => lfreq syms x)) by (intros x Hx; apply in_zseq in Hx; apply Hl4; lia).
        rewrite lfreq_sum by exact Hval. lia.
    - rewrite Hl2. exact (tabs_ok_spec _ _ tabs_l). }
  assert (BL := build_tree_correct _ _ _ RL).
  assert (CL := bt_canon _ _ _ RL).
  destruct (build_tree static_l_desc (tr_ltree s) (tr_wk s)) as [[lt lmax] w1] eqn:EL.
  destruct BL as [Sl [Fl [ordl [Rl BL]]]].
  cbn [tr_dtree tr_wk set_wk set_lmax set_ltree]. rewrite E2.
  destruct (bt_lens _ _ _ _ _ _ _ _ _ _ BL ltac:(simpl; unfold MAX_BITS; lia)) as [Hlm Hll].
  cbn [sd_elems static_l_desc] in Hlm. unfold L_CODES in Hlm.
  (* the distance tree *)
  assert (RD : bt_req static_d_desc (tr_dtree s) w1).
  { destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ BL) as [_ [_ [W1 [W2 _]]]].
    assert (O1 := bt_opt _ _ _ _ _ _ _ _ _ _ BL). assert (O2 := bt_static _ _ _ _ _ _ _ _ _ _ BL).
    cbn [sd_stree static_l_desc] in O2.
    constructor.
    - cbn; unfold L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; cbn; lia.
    - cbn. unfold HEAP_SIZE, D_CODES in *. lia.
    - rewrite W1, W2, O1, O2. unfold u64. repeat split; try lia; apply Z.mod_pos_bound; lia.
    - rewrite Hd1. exact Hd3.
    - split.
      + intros x Hx. cbn in Hx. apply Hd3. unfold D_CODES in *. lia.
      + cbn [sd_elems static_d_desc].
        rewrite (map_ext_in _ (fun x => dfreq syms x)) by (intros x Hx; apply in_zseq in Hx; apply Hd4; lia).
        assert (H := dfreq_sum syms Hval). lia.
    - rewrite Hd2. exact (tabs_ok_spec _ _ tabs_d). }
  assert (BD := build_tree_correct _ _ _ RD).
  assert (CD := bt_canon _ _ _ RD).
  destruct (build_tree static_d_desc (tr_dtree s) w1) as [[dt dmax] w2] eqn:ED.
  destruct BD as [Sd [Fd [ordd [Rd BD]]]].
  destruct (bt_lens _ _ _ _ _ _ _ _ _ _ BD ltac:(simpl; unfold MAX_BITS; lia)) as [Hdm Hdl].
  cbn [sd_elems static_d_desc] in Hdm. unfold D_CODES in Hdm.
  unfold build_bl_tree. cbn [tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_wk set_wk set_dmax set_dtree set_lmax set_ltree].
  rewrite E3.
  (* the two streams *)
  set (l1 := Hd.tree_syms (dl (set_dl lt (lmax + 1) 65535)) lmax).
  set (l2 := Hd.tree_syms (dl (set_dl dt (dmax + 1) 65535)) dmax).
  assert (K1 : Hd.syms_ok l1 /\ Z.of_nat (length l1) <= lmax + 1).
  { split; [|apply FlushHdr.tree_syms_length; lia].
    apply Hd.tree_syms_ok; [lia|]. intros i Hi. cbn [dl set_dl]. rewrite Hd.Znth_upd_other by lia. auto. }
  assert (K2 : Hd.syms_ok l2 /\ Z.of_nat (length l2) <= dmax + 1).
  { split; [|apply FlushHdr.tree_syms_length; lia].
    apply Hd.tree_syms_ok; [lia|]. intros i Hi. cbn [dl set_dl]. rewrite Hd.Znth_upd_other by lia. auto. }
  destruct K1 as [K1a K1b]. destruct K2 as [K2a K2b].
  assert (NW1 : Hd.no_wrap (fc (tr_bltree s)) l1).
  { apply no_wrap_of; auto. intros c Hc. rewrite Hb4 by lia. lia. }
  destruct (Hd.scan_tree_counts lt lmax (tr_bltree s) ltac:(lia) NW1) as [S1a [S1b [S1c S1d]]].
  destruct (scan_tree lt lmax (tr_bltree s)) as [lt' bl1] eqn:ES1. cbn [fst snd] in S1a, S1b, S1c, S1d. subst lt'. fold l1 in S1d.
  assert (NW2 : Hd.no_wrap (fc bl1) l2).
  { apply no_wrap_of; auto; [lia| |].
    - intros n Hn. rewrite S1d by lia. destruct (Z_lt_dec n 19).
      + rewrite Hb4 by (unfold BL_CODES; lia). pose proof (cnt_le_length n l1). pose proof (Hd.cnt_nonneg n l1). lia.
      + rewrite (cnt_out n l1 K1a) by lia. specialize (Hb3 n Hn). lia.
    - intros c Hc. rewrite S1d by (unfold BL_CODES in *; lia). rewrite Hb4 by lia.
      pose proof (cnt_le_length c l1). lia. }
  destruct (Hd.scan_tree_counts dt dmax bl1 ltac:(lia) NW2) as [S2a [S2b [S2c S2d]]].
  destruct (scan_tree dt dmax bl1) as [dt' bl2] eqn:ES2. cbn [fst snd] in S2a, S2b, S2c, S2d. subst dt'. fold l2 in S2d.
  assert (HZ : Zlength (fc bl2) = 2 * BL_CODES + 1) by lia.
  assert (HF : forall n, 0 <= n < 2 * BL_CODES + 1 ->
                 Znth n (fc bl2) = Znth n (fc (tr_bltree s)) + Hd.cnt n l1 + Hd.cnt n l2).
  { intros n Hn. rewrite S2d by lia. rewrite S1d by lia. lia. }
  assert (HR : forall n, 0 <= n < 2 * BL_CODES + 1 -> 0 <= Znth n (fc bl2) < 65536).
  { intros n Hn. rewrite HF by lia. destruct (Z_lt_dec n 19).
    - rewrite Hb4 by (unfold BL_CODES; lia).
      pose proof (cnt_le_length n l1). pose proof (Hd.cnt_nonneg n l1).
      pose proof (cnt_le_length n l2). pose proof (Hd.cnt_nonneg n l2). lia.
    - rewrite (cnt_out n l1 K1a), (cnt_out n l2 K2a) by lia. specialize (Hb3 n Hn). lia. }
  (* the bit length tree *)
  assert (RB : bt_req static_bl_desc bl2 w2).
  { destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ BD) as [_ [_ [W1 [W2 _]]]].
    assert (O1 := bt_opt _ _ _ _ _ _ _ _ _ _ BD). assert (O2 := bt_static _ _ _ _ _ _ _ _ _ _ BD).
    cbn [sd_stree static_d_desc] in O2.
    constructor.
    - cbn; unfold L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; cbn; lia.
    - rewrite HZ, S2b, S1b, Hb2. cbn. unfold HEAP_SIZE. lia.
    - rewrite W1, W2, O1, O2. unfold u64. repeat split; try lia; apply Z.mod_pos_bound; lia.
    - rewrite HZ. exact HR.
    - split.
      + intros x Hx. cbn in Hx. apply HR. unfold BL_CODES in *. lia.
      + cbn [sd_elems static_bl_desc].
        rewrite (map_ext_in _ (fun x => Hd.cnt x l1 + Hd.cnt x l2)).
        2:{ intros x Hx. apply in_zseq in Hx. cbn in Hx. rewrite HF by (unfold BL_CODES; lia).
            rewrite Hb4 by (unfold BL_CODES; lia). lia. }
        rewrite Cert.hsum_map_add. change (Z.to_nat BL_CODES) with 19%nat.
        rewrite !FlushStream.sum_cnt_length by (intros q Hq; first [apply (K1a q Hq) | apply (K2a q Hq)]).
        lia.
    - rewrite S2b, S1b, Hb2. exact (tabs_ok_spec _ _ tabs_bl). }
  assert (BB := build_tree_correct _ _ _ RB).
  assert (CB := bt_canon _ _ _ RB).
  destruct (build_tree static_bl_desc bl2 w2) as [[bl3 blmax] w3] eqn:EB.
  destruct BB as [Sb [Fb [ordb [Rb BB]]]].
  cbn beta iota.
  unfold canon_concl.
  cbn [tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax set_wk set_blmax set_bltree set_dtree set_ltree
       set_dmax set_lmax].
  destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ BL) as [_ [ZL _]].
  destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ BD) as [_ [ZD _]].
  destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ BB) as [_ [ZB _]].
  destruct (bt_lens _ _ _ _ _ _ _ _ _ _ BB ltac:(simpl; unfold MAX_BL_BITS; lia)) as [Hbm Hbl].
  cbn [sd_elems static_bl_desc] in Hbm. unfold BL_CODES in Hbm.
  split; [|split].
  - intros x Hx Hnz. cbn [fc dl set_dl] in *. rewrite Hd.Znth_upd_other in * by lia.
    rewrite sublist_upd_Znth_l by (unfold HEAP_SIZE in *; lia). apply CL; auto.
  - intros x Hx Hnz. cbn [fc dl set_dl] in *. rewrite Hd.Znth_upd_other in * by lia.
    rewrite sublist_upd_Znth_l by (unfold D_CODES in *; lia). apply CD; auto.
  - intros x Hx Hnz.
    assert (Hz : forall y, blmax < y < 19 -> Znth y (dl bl3) = 0).
    { intros y Hy. apply (bt_len_out _ _ _ _ _ _ _ _ _ _ BB); [cbn; unfold BL_CODES; lia|].
      intros Hin. destruct (bt_mc _ _ _ _ _ _ _ _ _ _ BB) as [_ Hle]. specialize (Hle y Hin). lia. }
    assert (Hxm : x <= blmax) by (destruct (Z_le_gt_dec x blmax); [auto|exfalso; apply Hnz, Hz; lia]).
    assert (HZB : Zlength (dl bl3) = 39) by (rewrite ZB, S2b, S1b, Hb2; reflexivity).
    rewrite CB by lia.
    rewrite (sublist_split 0 (blmax + 1) 19) by lia.
    rewrite send_sym_app0; [reflexivity|rewrite Zlength_sublist by lia; lia|].
    intros y Hy. apply In_Znth in Hy. destruct Hy as [i [Hi Hy]]. rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_sublist in Hy by lia. rewrite <- Hy. apply Hz. lia.
Qed.
