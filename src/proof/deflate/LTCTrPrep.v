(** * TREES part, sub-part PREP: see LTCTrKit.v for the statement and its purpose. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCTrKit.
Require Import Zlib.proof.huffman.BuildPre Zlib.proof.huffman.BuildThm Zlib.proof.huffman.FlushDyn.
Require Zlib.proof.huffman.Header.
Require Import Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Checked reads / writes in range *)

Lemma rd_ok l i : 0 <= i < Zlength l -> rd l i = Some (Znth i l).
Proof.
  intros H. unfold rd, in_range.
  replace ((0 <=? i) && (i <? Zlength l)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma wr_ok l i v : 0 <= i < Zlength l -> wr l i v = Some (upd_Znth i l v).
Proof.
  intros H. unfold wr, in_range.
  replace ((0 <=? i) && (i <? Zlength l)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

(** ** detect_data_type *)

Lemma c_dd_block_ok : forall fuel lf n, 0 <= n -> 32 <= n + Z.of_nat fuel -> 32 <= Zlength lf ->
  c_dd_block fuel lf n = Some (dd_block fuel lf n).
Proof.
  induction fuel as [|f IH]; intros lf n H0 H1 H2.
  - cbn [c_dd_block dd_block]. replace (n <=? 31) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - cbn [c_dd_block dd_block]. destruct (n <=? 31) eqn:En; [|reflexivity]. apply Z.leb_le in En.
    destruct (block_listed n); cbn [bind andb].
    + rewrite rd_ok by lia. cbn [bind]. destruct (negb (Znth n lf =? 0)); cbn [orb]; [reflexivity|].
      apply IH; lia.
    + apply IH; lia.
Qed.

Lemma c_dd_allow_ok : forall fuel lf n, 0 <= n -> 256 <= n + Z.of_nat fuel -> 256 <= Zlength lf ->
  c_dd_allow fuel lf n = Some (dd_allow fuel lf n).
Proof.
  induction fuel as [|f IH]; intros lf n H0 H1 H2.
  - cbn [c_dd_allow dd_allow]. replace (n <? LITERALS) with false by (symmetry; apply Z.ltb_ge; unfold LITERALS; lia).
    reflexivity.
  - cbn [c_dd_allow dd_allow]. destruct (n <? LITERALS) eqn:En; [|reflexivity]. apply Z.ltb_lt in En.
    unfold LITERALS in En. rewrite rd_ok by lia. cbn [bind].
    destruct (negb (Znth n lf =? 0)); cbn [orb]; [reflexivity|]. apply IH; lia.
Qed.

Lemma c_detect_ok : forall lf, 256 <= Zlength lf -> c_detect_data_type lf = Some (detect_data_type lf).
Proof.
  intros lf H. unfold c_detect_data_type, detect_data_type.
  rewrite c_dd_block_ok by (cbn; lia). cbn [bind].
  destruct (dd_block 32 lf 0); [reflexivity|].
  rewrite (rd_ok lf 9), (rd_ok lf 10), (rd_ok lf 13) by lia. cbn [bind].
  rewrite c_dd_allow_ok by (cbn; lia). cbn [bind].
  destruct (negb (Znth 9 lf =? 0)); cbn [orb]; [reflexivity|].
  destruct (negb (Znth 10 lf =? 0)); cbn [orb]; [reflexivity|].
  destruct (negb (Znth 13 lf =? 0)); cbn [orb]; reflexivity.
Qed.


(** ** scan_tree *)

Lemma c_scan_loop_ok : forall fuel t mc blf n prevlen nextlen count maxc minc,
  0 <= n -> n + Z.of_nat fuel = mc + 1 -> mc + 1 < Zlength (dl t) ->
  (forall i, 0 <= i <= mc -> 0 <= Znth i (dl t) <= 15) ->
  (n <= mc -> nextlen = Znth n (dl t)) -> 19 <= Zlength blf ->
  c_scan_tree_loop fuel t mc blf n prevlen nextlen count maxc minc =
  Some (scan_tree_loop fuel t mc blf n prevlen nextlen count maxc minc).
Proof.
  induction fuel as [|f IH]; intros t mc blf n prevlen nextlen count maxc minc H0 H1 H2 H3 H4 H5.
  - cbn [c_scan_tree_loop scan_tree_loop]. replace (n <=? mc) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity.
  - cbn [c_scan_tree_loop scan_tree_loop]. replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia).
    rewrite (rd_ok (dl t) (n + 1)) by lia. cbn [bind].
    assert (Hc : 0 <= nextlen <= 15) by (rewrite H4 by lia; apply H3; lia).
    destruct ((count + 1 <? maxc) && (nextlen =? Znth (n + 1) (dl t))).
    { apply IH; auto; lia. }
    match goal with |- bind ?c _ = Some ?r => match r with context [scan_tree_loop _ _ _ ?m _ _ _ _ _ _] =>
      assert (C : c = Some m /\ Zlength m = Zlength blf) end end.
    { unfold REP_3_6, REPZ_3_10, REPZ_11_138.
      destruct (count + 1 <? minc); [|destruct (negb (nextlen =? 0)); [destruct (negb (nextlen =? prevlen))|
                                                                        destruct (count + 1 <=? 10)]]; cbn [bind];
      repeat (first [rewrite rd_ok by (rewrite ?Zlength_upd_Znth_any; lia)
                    |rewrite wr_ok by (rewrite ?Zlength_upd_Znth_any; lia)]; cbn [bind]);
      (split; [reflexivity|rewrite ?Zlength_upd_Znth_any; reflexivity]). }
    destruct C as [C L]. rewrite C. cbn [bind].
    destruct (if Znth (n + 1) (dl t) =? 0 then (138, 3)
              else if nextlen =? Znth (n + 1) (dl t) then (6, 3) else (7, 4)) as [mx mn].
    apply IH; auto; lia.
Qed.

Lemma c_scan_tree_ok : forall t mc bl, 0 <= mc -> mc < 2147483647 -> mc + 1 < Zlength (dl t) ->
  (forall i, 0 <= i <= mc -> 0 <= Znth i (dl t) <= 15) -> 19 <= Zlength (fc bl) ->
  c_scan_tree t mc bl = Some (scan_tree t mc bl).
Proof.
  intros t mc bl H0 H1 H2 H3 H4. unfold c_scan_tree, scan_tree.
  replace (mc <? 2147483647) with true by (symmetry; apply Z.ltb_lt; lia). cbn [guard bind].
  rewrite (rd_ok (dl t) 0) by lia. cbn [bind].
  unfold c_set_dl. rewrite wr_ok by lia. cbn [bind].
  destruct (if Znth 0 (dl t) =? 0 then (138, 3) else (7, 4)) as [mx mn].
  rewrite c_scan_loop_ok; [reflexivity|lia|rewrite Z2Nat.id by lia; lia|..].
  - cbn [dl]. rewrite Zlength_upd_Znth_any. lia.
  - intros i Hi. cbn [dl]. rewrite upd_Znth_diff by lia. auto.
  - intros _. cbn [dl]. rewrite upd_Znth_diff by lia. reflexivity.
  - exact H4.
Qed.

(** ** find_max_blindex *)

Lemma bl_order_ok : Zlength bl_order = 19 /\ forall i, 0 <= i < 19 -> 0 <= Znth i bl_order < 19.
Proof.
  split; [reflexivity|].
  assert (E : forallb (fun i => (0 <=? Znth i bl_order) && (Znth i bl_order <? 19)) (zseq 0 19%nat) = true)
    by (vm_compute; reflexivity).
  intros i Hi. assert (E' := proj1 (forallb_forall _ _) E i ltac:(apply in_zseq; lia)).
  rewrite andb_true_iff, Z.leb_le, Z.ltb_lt in E'. lia.
Qed.

Lemma c_fmb_ok : forall fuel bl i, i <= 18 -> i - 3 < Z.of_nat fuel -> 19 <= Zlength (dl bl) ->
  c_find_max_blindex fuel bl i = Some (find_max_blindex fuel bl i).
Proof.
  destruct bl_order_ok as [BL BR].
  induction fuel as [|f IH]; intros bl i H0 H1 H2.
  - cbn [c_find_max_blindex]. replace (i >=? 3) with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia).
    reflexivity.
  - cbn [c_find_max_blindex find_max_blindex]. destruct (i >=? 3) eqn:E; [|reflexivity].
    apply Z.geb_le in E. rewrite (rd_ok bl_order i) by lia. cbn [bind].
    specialize (BR i ltac:(lia)). rewrite rd_ok by lia. cbn [bind].
    destruct (negb (Znth (Znth i bl_order) (dl bl) =? 0)); [reflexivity|]. apply IH; lia.
Qed.

(** ** build_tree keeps the Freq/Code fields below 2^16 *)

Lemma pass1_fc : forall f sd mc t w ov h, fc (fst (fst (gen_bitlen_pass1 f sd mc t w ov h))) = fc t.
Proof.
  induction f as [|f IH]; intros sd mc t w ov h; [reflexivity|]. cbn [gen_bitlen_pass1].
  destruct (h <? HEAP_SIZE); [|reflexivity].
  destruct (Znth (Znth (Znth h (w_heap w)) (dl t)) (dl t) + 1 >? sd_maxlen sd);
    (destruct (Znth h (w_heap w) >? mc); rewrite IH; reflexivity).
Qed.

Lemma reassign_inner_fc : forall f mc bits heap t ol h n,
  fc (fst (fst (gen_bitlen_reassign_inner f mc bits heap t ol h n))) = fc t.
Proof.
  induction f as [|f IH]; intros mc bits heap t ol h n; [reflexivity|]. cbn [gen_bitlen_reassign_inner].
  destruct (n =? 0); [reflexivity|]. destruct (Znth (h - 1) heap >? mc); [apply IH|].
  destruct (negb (Znth (Znth (h - 1) heap) (dl t) =? bits)); rewrite IH; reflexivity.
Qed.

Lemma reassign_fc : forall f mc heap blc t ol h bits,
  fc (fst (gen_bitlen_reassign f mc heap blc t ol h bits)) = fc t.
Proof.
  induction f as [|f IH]; intros mc heap blc t ol h bits; [reflexivity|]. cbn [gen_bitlen_reassign].
  destruct (bits =? 0); [reflexivity|].
  assert (E := reassign_inner_fc (Z.to_nat HEAP_SIZE) mc bits heap t ol h (Znth bits blc)).
  destruct (gen_bitlen_reassign_inner _ _ _ _ _ _ _ _) as [[t1 o1] h1]. cbn [fst] in E.
  rewrite IH. exact E.
Qed.

Lemma gen_bitlen_fc : forall sd mc t w, fc (fst (gen_bitlen sd mc t w)) = fc t.
Proof.
  intros sd mc t w. unfold gen_bitlen.
  match goal with |- context [gen_bitlen_pass1 ?a ?b ?c ?d ?e ?g ?h] =>
    assert (E := pass1_fc a b c d e g h); destruct (gen_bitlen_pass1 a b c d e g h) as [[t1 w1] ov] end.
  cbn [fst fc set_dl] in E |- *. destruct (ov =? 0); [exact E|].
  match goal with |- context [gen_bitlen_reassign ?a ?b ?c ?d ?e ?g ?h ?i] =>
    assert (E2 := reassign_fc a b c d e g h i); destruct (gen_bitlen_reassign a b c d e g h i) as [t2 o2] end.
  cbn [fst] in E2 |- *. congruence.
Qed.

Lemma gen_codes_loop_frange : forall f mc t nc n, frange (fc t) -> frange (fc (gen_codes_loop f mc t nc n)).
Proof.
  induction f as [|f IH]; intros mc t nc n H; [exact H|]. cbn [gen_codes_loop].
  destruct (n <=? mc); [|exact H]. destruct (Znth n (dl t) =? 0); apply IH; [exact H|].
  apply frange_upd; [exact H|]. unfold u16. apply Z.mod_pos_bound. lia.
Qed.

Lemma bt_frange : forall sd t w, frange (fc t) ->
  frange (fc (fst (fst (build_tree sd t w)))).
Proof.
  intros sd t w H. rewrite build_tree_eq.
  assert (P := bt_pre_fc sd t w H). destruct (bt_pre sd t w) as [[t1 w1] mc]. destruct P as [P _].
  assert (G := gen_bitlen_fc sd mc t1 w1). destruct (gen_bitlen sd mc t1 w1) as [t2 w2]. cbn [fst] in G |- *.
  unfold gen_codes. apply gen_codes_loop_frange. rewrite G. exact P.
Qed.

Module Hd := Zlib.proof.huffman.Header.

Theorem prep_some : bt_some_statement -> prep_statement.
Proof.
  intros Hbt s syms stored_len Hfp Hlev.
  destruct Hfp as [HL [Hok [Hp0 [Hbv Hob]]] [Hsn [Hsl [Hval Hsy]]] [Hl1 [Hl2 [Hl3 Hl4]]] [Hd1 [Hd2 [Hd3 Hd4]]]
                  [Hb1 [Hb2 [Hb3 Hb4]]] [Hw1 [Hw2 [Hw3 [Hw4 Hw5]]]]].
  assert (HLB : tr_lit_bufsize s <= 32768).
  { destruct HL as [ml [Hml E]]. rewrite E. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  pose proof (Zlength_nonneg syms) as Hn0.
  unfold c_flush_prep, flush_prep. replace (tr_level s >? 0) with true by (symmetry; apply Z.gtb_lt; lia).
  set (s0 := if tr_data_type s =? Z_UNKNOWN then set_data_type s (detect_data_type (fc (tr_ltree s))) else s).
  match goal with |- bind ?c _ = _ /\ _ => assert (C0 : c = Some s0) end.
  { unfold s0. destruct (tr_data_type s =? Z_UNKNOWN); [|reflexivity].
    rewrite c_detect_ok by (rewrite Hl1; unfold HEAP_SIZE; lia). reflexivity. }
  rewrite C0. cbn [bind].
  assert (E0 : tr_ltree s0 = tr_ltree s /\ tr_dtree s0 = tr_dtree s /\ tr_bltree s0 = tr_bltree s /\
               tr_wk s0 = tr_wk s /\ tr_cfg s0 = tr_cfg s /\ tr_out s0 = tr_out s /\
               tr_sym_next s0 = tr_sym_next s /\ tr_matches s0 = tr_matches s)
    by (unfold s0; destruct (tr_data_type s =? Z_UNKNOWN); repeat split).
  clearbody s0. destruct E0 as [E1 [E2 [E3 [E4 [E5 [E6 [E7 E8]]]]]]].
  clear C0. rewrite E1, E4.
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
  rewrite (Hbt _ _ _ (or_introl eq_refl) RL).
  assert (BL := build_tree_correct _ _ _ RL).
  assert (FL := bt_frange static_l_desc (tr_ltree s) (tr_wk s) ltac:(intros n Hn; apply Hl3; lia)).
  destruct (build_tree static_l_desc (tr_ltree s) (tr_wk s)) as [[lt lmax] w1] eqn:EL.
  cbn [bind fst] in FL |- *.
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
  rewrite (Hbt _ _ _ (or_intror (or_introl eq_refl)) RD).
  assert (BD := build_tree_correct _ _ _ RD).
  assert (FD := bt_frange static_d_desc (tr_dtree s) w1 ltac:(intros n Hn; apply Hd3; lia)).
  destruct (build_tree static_d_desc (tr_dtree s) w1) as [[dt dmax] w2] eqn:ED.
  cbn [bind fst] in FD |- *.
  destruct BD as [Sd [Fd [ordd [Rd BD]]]].
  destruct (bt_lens _ _ _ _ _ _ _ _ _ _ BD ltac:(simpl; unfold MAX_BITS; lia)) as [Hdm Hdl].
  cbn [sd_elems static_d_desc] in Hdm. unfold D_CODES in Hdm.
  unfold c_build_bl_tree at 1. unfold build_bl_tree.
  cbn [tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_wk set_wk set_dmax set_dtree set_lmax set_ltree].
  rewrite E3.
  destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ BL) as [ZL1 [ZL2 [ZL3 [ZL4 ZL5]]]].
  destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ BD) as [ZD1 [ZD2 [ZD3 [ZD4 ZD5]]]].
  rewrite (c_scan_tree_ok lt lmax (tr_bltree s)) by first [exact Hll | unfold HEAP_SIZE, BL_CODES in *; lia].
  cbn [bind].
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
  rewrite (c_scan_tree_ok dt dmax bl1) by first [exact Hdl | unfold BL_CODES, D_CODES in *; lia].
  cbn [bind].
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
  { assert (O1 := bt_opt _ _ _ _ _ _ _ _ _ _ BD). assert (O2 := bt_static _ _ _ _ _ _ _ _ _ _ BD).
    cbn [sd_stree static_d_desc] in O2.
    constructor.
    - cbn; unfold L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; cbn; lia.
    - rewrite HZ, S2b, S1b, Hb2. cbn. unfold HEAP_SIZE. lia.
    - rewrite ZD3, ZD4, O1, O2. unfold u64. repeat split; try lia; apply Z.mod_pos_bound; lia.
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
  rewrite (Hbt _ _ _ (or_intror (or_intror eq_refl)) RB).
  assert (BB := build_tree_correct _ _ _ RB).
  assert (FB := bt_frange static_bl_desc bl2 w2 ltac:(intros n Hn; apply HR; lia)).
  destruct (build_tree static_bl_desc bl2 w2) as [[bl3 blmax] w3] eqn:EB.
  cbn [bind fst] in FB |- *.
  destruct BB as [Sb [Fb [ordb [Rb BB]]]].
  destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ BB) as [ZB1 [ZB2 [ZB3 [ZB4 ZB5]]]].
  rewrite c_fmb_ok by (rewrite ?ZB2, ?S2b, ?S1b, ?Hb2; unfold BL_CODES in *; cbn; lia).
  cbn [bind].
  split; [reflexivity|].
  cbn [fst tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_wk tr_out tr_sym_next tr_matches set_wk set_blmax
       set_bltree set_dtree set_ltree set_dmax set_lmax w_heap w_depth w_bl_count w_set_opt_len fc dl set_dl].
  unfold tr_cfg in *.
  cbn [tr_lit_bufsize tr_sym_end tr_level tr_strategy set_wk set_blmax set_bltree set_dtree set_ltree set_dmax set_lmax].
  rewrite ?Zlength_upd_Znth_any, ZB1, ZB2, S2b, S1b, HZ, Hb2, ZL1, ZL2, ZD1, ZD2, Hl1, Hl2, Hd1, Hd2, ZB3, ZB4, ZB5.
  split; [exact E5|]. split; [exact E6|]. split; [exact E7|]. split; [exact E8|].
  split; [reflexivity|]. split; [reflexivity|]. split; [intros n Hn; apply FL; rewrite ZL1, Hl1; exact Hn|].
  split; [reflexivity|]. split; [reflexivity|]. split; [intros n Hn; apply FD; rewrite ZD1, Hd1; exact Hn|].
  split; [reflexivity|]. split; [reflexivity|]. split; [intros n Hn; apply FB; rewrite ZB1, HZ; exact Hn|].
  split; [reflexivity|]. split; [reflexivity|]. reflexivity.
Qed.
